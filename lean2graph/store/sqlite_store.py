from __future__ import annotations

import json
import sqlite3
from pathlib import Path
from typing import Iterable


SCHEMA_VERSION = "2"


class RawStore:
    def __init__(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.connection = sqlite3.connect(path)
        self.connection.row_factory = sqlite3.Row
        self._initialize()

    def close(self) -> None:
        self.connection.close()

    def __enter__(self) -> "RawStore":
        return self

    def __exit__(self, *args: object) -> None:
        self.close()

    def _initialize(self) -> None:
        self.connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS project_run (
                id TEXT PRIMARY KEY,
                schema_version TEXT NOT NULL,
                status TEXT NOT NULL,
                manifest_json TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS module (
                id TEXT PRIMARY KEY,
                project_id TEXT NOT NULL,
                name TEXT NOT NULL,
                file_path TEXT NOT NULL,
                origin TEXT NOT NULL DEFAULT 'lean_env',
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS module_import (
                project_id TEXT NOT NULL,
                module TEXT NOT NULL,
                imported_module TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL,
                PRIMARY KEY (project_id, module, imported_module)
            );
            CREATE TABLE IF NOT EXISTS declaration (
                id TEXT PRIMARY KEY,
                project_id TEXT NOT NULL,
                module TEXT NOT NULL,
                name TEXT NOT NULL,
                kind TEXT NOT NULL,
                is_instance INTEGER NOT NULL,
                is_matcher INTEGER NOT NULL,
                is_auxiliary INTEGER NOT NULL,
                is_private INTEGER NOT NULL,
                is_unsafe INTEGER NOT NULL,
                is_partial INTEGER NOT NULL,
                type_pretty TEXT NOT NULL,
                value_pretty TEXT,
                range_json TEXT,
                docstring TEXT,
                truncated INTEGER NOT NULL DEFAULT 0,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL,
                type_expr_id TEXT,
                is_class INTEGER NOT NULL DEFAULT 0,
                is_projection INTEGER NOT NULL DEFAULT 0,
                is_auto_generated INTEGER NOT NULL DEFAULT 0,
                folded_into TEXT,
                aux_claims_json TEXT NOT NULL DEFAULT '[]',
                statement_context_json TEXT NOT NULL DEFAULT '{}'
            );
            CREATE TABLE IF NOT EXISTS decl_axiom (
                project_id TEXT NOT NULL,
                decl_id TEXT NOT NULL,
                axiom_name TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL,
                PRIMARY KEY (decl_id, axiom_name)
            );
            CREATE TABLE IF NOT EXISTS const_ref (
                decl_id TEXT NOT NULL,
                const_name TEXT NOT NULL,
                origin TEXT NOT NULL,
                usage_kind TEXT NOT NULL,
                occurrence_count INTEGER NOT NULL DEFAULT 1,
                schema_version TEXT NOT NULL,
                PRIMARY KEY (decl_id, const_name, origin, usage_kind)
            );
            CREATE TABLE IF NOT EXISTS expr_node (
                id TEXT PRIMARY KEY,
                decl_id TEXT NOT NULL,
                origin TEXT NOT NULL,
                kind TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS tactic_node (
                id TEXT PRIMARY KEY,
                decl_id TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS goal_state (
                id TEXT PRIMARY KEY,
                decl_id TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS mvar_assignment (
                id TEXT PRIMARY KEY,
                decl_id TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS step (
                id TEXT PRIMARY KEY,
                decl_id TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS source_text (
                project_id TEXT NOT NULL,
                file_path TEXT NOT NULL,
                sha256 TEXT NOT NULL,
                content TEXT,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL,
                PRIMARY KEY (project_id, file_path)
            );
            CREATE TABLE IF NOT EXISTS error (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                project_id TEXT NOT NULL,
                scope TEXT NOT NULL,
                name TEXT,
                message TEXT NOT NULL,
                origin TEXT NOT NULL,
                schema_version TEXT NOT NULL
            );
            """
        )
        declaration_columns = {
            row[1] for row in self.connection.execute("PRAGMA table_info(declaration)")
        }
        migrations = {
            "type_expr_id": "TEXT",
            "is_class": "INTEGER NOT NULL DEFAULT 0",
            "is_projection": "INTEGER NOT NULL DEFAULT 0",
            "is_auto_generated": "INTEGER NOT NULL DEFAULT 0",
            "folded_into": "TEXT",
            "aux_claims_json": "TEXT NOT NULL DEFAULT '[]'",
            "statement_context_json": "TEXT NOT NULL DEFAULT '{}'",
        }
        for column, definition in migrations.items():
            if column not in declaration_columns:
                self.connection.execute(
                    f"ALTER TABLE declaration ADD COLUMN {column} {definition}"
                )

    def put_project(self, project_id: str, status: str, manifest: dict) -> None:
        self.connection.execute(
            "INSERT OR REPLACE INTO project_run VALUES (?, ?, ?, ?)",
            (project_id, SCHEMA_VERSION, status, json.dumps(manifest, sort_keys=True)),
        )

    def put_module(self, project_id: str, name: str, file_path: str) -> None:
        self.connection.execute(
            "INSERT OR REPLACE INTO module VALUES (?, ?, ?, ?, ?, ?)",
            (
                f"module:{project_id}:{name}",
                project_id,
                name,
                file_path,
                "lean_env",
                SCHEMA_VERSION,
            ),
        )

    def put_source(self, project_id: str, file_path: str, sha256: str, content: str) -> None:
        self.connection.execute(
            "INSERT OR REPLACE INTO source_text VALUES (?, ?, ?, ?, ?, ?)",
            (
                project_id,
                file_path,
                sha256,
                content,
                "source_text",
                SCHEMA_VERSION,
            ),
        )

    def put_declaration(self, project_id: str, module: str, record: dict) -> str:
        name = record["name"]
        decl_id = f"decl:{project_id}:{name}"
        self.connection.execute(
            """
            INSERT OR REPLACE INTO declaration (
                id, project_id, module, name, kind, is_instance, is_matcher,
                is_auxiliary, is_private, is_unsafe, is_partial, type_pretty,
                value_pretty, range_json, docstring, truncated, origin,
                schema_version, type_expr_id, is_class, is_projection,
                is_auto_generated, folded_into, aux_claims_json, statement_context_json
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                decl_id,
                project_id,
                module,
                name,
                record["kind"],
                int(record.get("is_instance", False)),
                int(record.get("is_matcher", False)),
                int(record.get("is_auxiliary", False)),
                int(record.get("is_private", False)),
                int(record.get("is_unsafe", False)),
                int(record.get("is_partial", False)),
                record.get("type_pretty", ""),
                record.get("value_pretty"),
                json.dumps(record.get("range"), sort_keys=True) if record.get("range") else None,
                record.get("docstring"),
                int(record.get("truncated", False)),
                "lean_env",
                SCHEMA_VERSION,
                record.get("type_expr_id"),
                int(record.get("is_class", False)),
                int(record.get("is_projection", False)),
                int(record.get("is_auto_generated", False)),
                record.get("folded_into"),
                json.dumps(record.get("aux_claims", []), ensure_ascii=False, sort_keys=True),
                json.dumps(record.get("statement_context") or {}, ensure_ascii=False, sort_keys=True),
            ),
        )
        if record.get("type_expr_id") and record.get("type_expr_raw"):
            self.put_expression(
                record["type_expr_id"],
                decl_id,
                "declaration_type",
                record["type_expr_raw"],
                record.get("type_pretty", ""),
            )
        statement_context = record.get("statement_context") or {}
        context_expressions = [
            *statement_context.get("variables", []),
            *statement_context.get("assumptions", []),
        ]
        context_expressions.extend(
            [
                {
                    "type_expr_id": statement_context.get("goal_expr_id"),
                    "type_expr_raw": statement_context.get("goal_expr_raw"),
                    "type_pretty": statement_context.get("goal_pretty", ""),
                }
            ]
        )
        for expression in context_expressions:
            if expression.get("type_expr_id") and expression.get("type_expr_raw"):
                self.put_expression(
                    expression["type_expr_id"],
                    decl_id,
                    "statement_context",
                    expression["type_expr_raw"],
                    expression.get("type_pretty", ""),
                )
        for axiom_name in record.get("axioms", []):
            self.connection.execute(
                "INSERT OR IGNORE INTO decl_axiom VALUES (?, ?, ?, ?, ?)",
                (project_id, decl_id, axiom_name, "lean_env", SCHEMA_VERSION),
            )
        for ref in record.get("const_refs", []):
            self.connection.execute(
                """
                INSERT INTO const_ref
                    (decl_id, const_name, origin, usage_kind, occurrence_count, schema_version)
                VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(decl_id, const_name, origin, usage_kind)
                DO UPDATE SET occurrence_count = occurrence_count + excluded.occurrence_count
                """,
                (
                    decl_id,
                    ref["const_name"],
                    ref["origin"],
                    ref["usage_kind"],
                    ref.get("count", 1),
                    SCHEMA_VERSION,
                ),
            )
            if ref.get("type_expr_id") and ref.get("type_expr_raw"):
                ref_decl_id = (
                    f"decl:external:{ref['const_name']}"
                    if ref["type_expr_id"].startswith("expr:external:")
                    else f"decl:{project_id}:{ref['const_name']}"
                )
                self.put_expression(
                    ref["type_expr_id"],
                    ref_decl_id,
                    "referenced_type",
                    ref["type_expr_raw"],
                    ref.get("statement_pretty", ""),
                )
        self.connection.commit()
        return decl_id

    def put_expression(
        self,
        expr_id: str,
        decl_id: str,
        kind: str,
        raw_expression: str,
        pretty: str,
    ) -> None:
        self.connection.execute(
            "INSERT OR REPLACE INTO expr_node(id, decl_id, origin, kind, payload_json, schema_version) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (
                expr_id,
                decl_id,
                "lean_env",
                kind,
                json.dumps(
                    {"raw_expression": raw_expression, "statement_pretty": pretty},
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                SCHEMA_VERSION,
            ),
        )

    def update_declaration_projection(
        self,
        project_id: str,
        folded_into: dict[str, str],
        aux_claims: dict[str, list[dict]],
    ) -> None:
        for name, parent in folded_into.items():
            self.connection.execute(
                """
                UPDATE declaration
                SET folded_into = ?,
                    range_json = (
                        SELECT parent.range_json
                        FROM declaration AS parent
                        WHERE parent.project_id = ? AND parent.name = ?
                    )
                WHERE id = ?
                """,
                (parent, project_id, parent, f"decl:{project_id}:{name}"),
            )
        for parent, claims in aux_claims.items():
            self.connection.execute(
                "UPDATE declaration SET aux_claims_json = ? WHERE id = ?",
                (
                    json.dumps(claims, ensure_ascii=False, sort_keys=True),
                    f"decl:{project_id}:{parent}",
                ),
            )
        self.connection.commit()

    def put_error(self, project_id: str, scope: str, name: str | None, message: str) -> None:
        self.connection.execute(
            "INSERT INTO error(project_id, scope, name, message, origin, schema_version) VALUES (?, ?, ?, ?, ?, ?)",
            (project_id, scope, name, message, "lean_env", SCHEMA_VERSION),
        )
        self.connection.commit()

    def clear_infotree_module(self, project_id: str, module: str) -> None:
        decl_id = f"decl:{project_id}:{module}"
        self.connection.execute("DELETE FROM tactic_node WHERE decl_id = ?", (decl_id,))
        self.connection.execute("DELETE FROM mvar_assignment WHERE decl_id = ?", (decl_id,))
        self.connection.execute("DELETE FROM step WHERE decl_id = ?", (decl_id,))
        self.connection.execute(
            "DELETE FROM expr_node WHERE decl_id = ? AND origin = 'lean_infotree'",
            (decl_id,),
        )
        self.connection.commit()

    def put_tactic(self, project_id: str, module: str, record: dict) -> str:
        ordinal = record["ordinal"]
        record_index = record.get("record_index", ordinal)
        decl_id = f"decl:{project_id}:{module}"
        node_id = f"tactic:{project_id}:{module}:{record_index}"
        self.connection.execute(
            "INSERT OR REPLACE INTO tactic_node(id, decl_id, payload_json, origin, schema_version) VALUES (?, ?, ?, ?, ?)",
            (
                node_id,
                decl_id,
                json.dumps(record, ensure_ascii=False, sort_keys=True),
                "lean_infotree",
                SCHEMA_VERSION,
            ),
        )
        for index, assignment in enumerate(record.get("assignments", [])):
            self.connection.execute(
                "INSERT OR REPLACE INTO mvar_assignment(id, decl_id, payload_json, origin, schema_version) VALUES (?, ?, ?, ?, ?)",
                (
                    f"mvar:{project_id}:{module}:{record_index}:{index}",
                    decl_id,
                    json.dumps(assignment, ensure_ascii=False, sort_keys=True),
                    "lean_infotree",
                    SCHEMA_VERSION,
                ),
            )
            if assignment.get("expr_id") and assignment.get("expr_raw"):
                self.put_expression(
                    assignment["expr_id"],
                    decl_id,
                    "proof_term",
                    assignment["expr_raw"],
                    assignment.get("expr_pretty") or "",
                )
        for state_key in ("goals_before", "goals_after"):
            for goal in record.get(state_key, []):
                if not isinstance(goal, dict):
                    continue
                if goal.get("target_expr_id") and goal.get("target_expr_raw"):
                    self.put_expression(
                        goal["target_expr_id"],
                        decl_id,
                        "goal_type",
                        goal["target_expr_raw"],
                        goal.get("target_pretty") or "",
                    )
                for local in goal.get("locals", []):
                    if local.get("type_expr_id") and local.get("type_expr_raw"):
                        self.put_expression(
                            local["type_expr_id"],
                            decl_id,
                            "local_type",
                            local["type_expr_raw"],
                            local.get("type_pretty") or "",
                        )
        partial = any(
            assignment["kind"] in {"delayed", "unassigned"}
            for assignment in record.get("assignments", [])
        ) or bool(record.get("goals_after"))
        status = "partial" if partial else "complete"
        self.connection.execute(
            "INSERT OR REPLACE INTO step(id, decl_id, payload_json, origin, schema_version) VALUES (?, ?, ?, ?, ?)",
            (
                f"step:{decl_id}:{record_index}",
                decl_id,
                json.dumps(
                    {
                        "module": module,
                        "ordinal": ordinal,
                        "record_index": record_index,
                        "status": status,
                        "record": "tactic",
                        "origin": "lean_infotree",
                        "schema_version": SCHEMA_VERSION,
                    },
                    sort_keys=True,
                ),
                "lean_infotree",
                SCHEMA_VERSION,
            ),
        )
        self.connection.commit()
        return node_id

    def put_infotree_record(self, project_id: str, module: str, record: dict) -> str:
        ordinal = record["ordinal"]
        record_index = record.get("record_index", ordinal)
        decl_id = f"decl:{project_id}:{module}"
        record_kind = record["record"]
        node_id = f"{record_kind}:{project_id}:{module}:{record_index}"
        table = "tactic_node" if record_kind == "tactic" else "expr_node"
        if table == "expr_node":
            self.connection.execute(
                "INSERT OR REPLACE INTO expr_node(id, decl_id, origin, kind, payload_json, schema_version) VALUES (?, ?, ?, ?, ?, ?)",
                (
                    node_id,
                    decl_id,
                    "lean_infotree",
                    record_kind,
                    json.dumps(record, ensure_ascii=False, sort_keys=True),
                    SCHEMA_VERSION,
                ),
            )
            if record.get("expr_id") and record.get("expr_raw"):
                self.put_expression(
                    record["expr_id"],
                    decl_id,
                    "term_expression",
                    record["expr_raw"],
                    record.get("expr_pretty") or "",
                )
            if record.get("expected_type_expr_id") and record.get("expected_type_expr_raw"):
                self.put_expression(
                    record["expected_type_expr_id"],
                    decl_id,
                    "term_expected_type",
                    record["expected_type_expr_raw"],
                    record.get("expected_type_pretty") or "",
                )
            self.connection.commit()
        return node_id
