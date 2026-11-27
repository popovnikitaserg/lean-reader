from __future__ import annotations

import json
import re
import sqlite3
from dataclasses import dataclass
from pathlib import Path


TOKEN_RE = re.compile(r"(?:_[A-Za-z]+\.\d+|[A-Za-z_][A-Za-z0-9_.]*)")
INFRASTRUCTURE_PREFIXES = (
    "Eq.",
    "id",
    "of_eq_true",
    "congr",
    "congrArg",
    "propext",
    "Classical.",
    "instDecidable",
)


@dataclass
class TraceResult:
    live_count: int
    dead_count: int
    partial_count: int
    coverage: float
    mismatches: list[str]


class TraceMatcher:
    def __init__(self, store_path: Path) -> None:
        self.store_path = store_path
        self.connection = sqlite3.connect(store_path)

    def close(self) -> None:
        self.connection.close()

    def __enter__(self) -> "TraceMatcher":
        return self

    def __exit__(self, *args: object) -> None:
        self.close()

    def _tokens(self, text: str) -> set[str]:
        return set(TOKEN_RE.findall(text or ""))

    def _is_infrastructure(self, name: str) -> bool:
        return any(name.startswith(prefix) for prefix in INFRASTRUCTURE_PREFIXES)

    def match_all(self) -> TraceResult:
        tactic_rows = self.connection.execute(
            "SELECT id, decl_id, payload_json FROM tactic_node"
        ).fetchall()
        declarations = self.connection.execute(
            "SELECT id, name, value_pretty FROM declaration WHERE kind IN ('thm', 'theorem')"
        ).fetchall()
        declaration_by_module: dict[str, list[tuple[str, str | None]]] = {}
        for decl_id, name, value_pretty in declarations:
            module = name.rsplit(".", 1)[0] if "." in name else name
            declaration_by_module.setdefault(module, []).append((name, value_pretty))

        live_count = 0
        dead_count = 0
        partial_count = 0
        evidence_tokens: set[str] = set()
        final_tokens: set[str] = set()
        mismatches: list[str] = []

        for node_id, decl_id, payload_json in tactic_rows:
            payload = json.loads(payload_json)
            direct_assignments = [
                assignment
                for assignment in payload.get("assignments", [])
                if assignment.get("kind") == "direct"
            ]
            delayed = any(
                assignment.get("kind") in {"delayed", "unassigned"}
                for assignment in payload.get("assignments", [])
            )
            authorial = not payload.get("synthetic_syntax", True)
            live = authorial and bool(direct_assignments) and not delayed

            if live:
                live_count += 1
                status = "complete"
            elif delayed:
                partial_count += 1
                status = "partial"
            else:
                dead_count += 1
                status = "dead"

            step_id = f"step:{decl_id}:{payload.get('record_index', payload['ordinal'])}"
            step_row = self.connection.execute(
                "SELECT payload_json FROM step WHERE id = ?", (step_id,)
            ).fetchone()
            if step_row:
                step_payload = json.loads(step_row[0])
                step_payload["status"] = status
                step_payload["live"] = live
                step_payload["origin"] = "lean_infotree"
                self.connection.execute(
                    "UPDATE step SET payload_json = ?, origin = 'lean_infotree' WHERE id = ?",
                    (json.dumps(step_payload, sort_keys=True), step_id),
                )

            for assignment in direct_assignments:
                assignment_tokens = self._tokens(assignment.get("expr_pretty", ""))
                evidence_tokens.update(
                    token
                    for token in assignment_tokens
                    if not self._is_infrastructure(token)
                )

        for _, _, value_pretty in declarations:
            if value_pretty:
                final_tokens.update(
                    token
                    for token in self._tokens(value_pretty)
                    if not self._is_infrastructure(token)
                )

        if final_tokens:
            covered = evidence_tokens & final_tokens
            coverage = len(covered) / len(final_tokens)
            mismatches = sorted(final_tokens - evidence_tokens)
        else:
            coverage = 1.0

        self.connection.commit()
        return TraceResult(
            live_count=live_count,
            dead_count=dead_count,
            partial_count=partial_count,
            coverage=coverage,
            mismatches=mismatches[:200],
        )
