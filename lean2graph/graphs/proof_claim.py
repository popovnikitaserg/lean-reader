from __future__ import annotations

import json
import re
from importlib.resources import files
from pathlib import Path

import networkx as nx
import yaml


_TACTIC_ROLES = yaml.safe_load(
    files("lean2graph").joinpath("config", "tactic_roles.yaml").read_text(encoding="utf-8")
)


def _nearest_comment(comments: list, line: int) -> str | None:
    if not comments:
        return None
    nearest = min(comments, key=lambda c: abs(c.start_line - line))
    if nearest.start_line <= line <= nearest.end_line or abs(nearest.start_line - line) <= 1:
        return nearest.text
    return None


def _clean_statement(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _normalize_range(value: dict | None) -> dict | None:
    if not isinstance(value, dict):
        return None
    start = value.get("start")
    end = value.get("end")
    if not isinstance(start, dict):
        return None
    result = {"start": {"line": int(start.get("line", 0)), "column": int(start.get("column", 0))}}
    if isinstance(end, dict):
        result["end"] = {"line": int(end.get("line", 0)), "column": int(end.get("column", 0))}
    else:
        result["end"] = {"line": int(start.get("line", 0)), "column": int(start.get("column", 0))}
    if result["end"]["line"] <= 0:
        return None
    return result


def _rewrite_entries(tactic_text: str) -> list[dict[str, str]]:
    match = re.search(r"\b(?:rw|rwa|rewrite)\s*\[", tactic_text)
    if not match:
        return []
    start = match.end()
    nesting = 1
    end = start
    for index in range(start, len(tactic_text)):
        if tactic_text[index] == "[":
            nesting += 1
        elif tactic_text[index] == "]":
            nesting -= 1
            if nesting == 0:
                end = index
                break
    if nesting != 0:
        return []
    entries: list[str] = []
    entry_start = start
    nesting = 0
    for index in range(start, end):
        char = tactic_text[index]
        if char in "([{":
            nesting += 1
        elif char in ")]}":
            nesting -= 1
        elif char == "," and nesting == 0:
            entries.append(tactic_text[entry_start:index].strip())
            entry_start = index + 1
    entries.append(tactic_text[entry_start:end].strip())
    parsed: list[dict[str, str]] = []
    for entry in entries:
        direction = "forward"
        if entry.startswith(("←", "<-")):
            direction = "backward"
            entry = entry[1:].lstrip() if entry.startswith("←") else entry[2:].lstrip()
        name_match = re.match(r"[^\W\d]\w*(?:\.[^\W\d]\w*)*", entry, re.UNICODE)
        if name_match:
            parsed.append({"lemma": name_match.group(0), "direction": direction})
    return parsed


class ProofClaimGraph:
    def __init__(self, project_id: str, decl_name: str) -> None:
        self.project_id = project_id
        self.decl_name = decl_name
        self.graph = nx.DiGraph()
        self.graph.graph.update(
            project_id=project_id,
            decl_name=decl_name,
            edge_convention="claim -> inference -> claim",
            schema_version=2,
        )

    def classify_tactic(self, text: str, syntax_kind: str) -> tuple[str, str]:
        kind = syntax_kind or ""
        for tactic, syntax_name in _TACTIC_ROLES.get("automation", {}).items():
            if kind == syntax_name or kind.endswith(f".{tactic}"):
                return f"automation:{tactic}", "closed"
        for role, syntax_kinds in _TACTIC_ROLES.items():
            if role == "automation":
                continue
            if any(kind == name or kind.endswith(name.removeprefix("Lean.Parser.Tactic"))
                   for name in syntax_kinds):
                return role, "closed"
        if kind.startswith("Lean.Parser.Tactic."):
            return "other", "open"
        lower = (text or "").strip().lower()
        if lower and not lower.startswith(("·", "|")):
            return "other", "open"
        return "other", "open"

    def used_consts(
        self,
        payload: dict,
        known_declarations: dict[str, dict],
    ) -> list[dict]:
        raw = payload.get("used_consts")
        names: set[str] = set()
        if isinstance(raw, list):
            for item in raw:
                name = item.get("name") if isinstance(item, dict) else str(item)
                if name:
                    names.add(name)
        pending = list(names)
        expanded: set[str] = set()
        while pending:
            name = pending.pop()
            if name in expanded:
                continue
            expanded.add(name)
            metadata = known_declarations.get(name, {})
            if "_proof_" in name:
                pending.extend(
                    ref["const_name"]
                    for ref in metadata.get("const_refs", [])
                    if ref.get("origin") == "proof"
                )
        names = {
            name for name in expanded
            if "_proof_" not in name and not name.endswith(".eq_1")
        }
        result = []
        for name in sorted(names):
            metadata = known_declarations.get(name, {})
            target_role = metadata.get("target_role")
            if target_role in {"notation_infra", "logic_infra", "automation_internal"}:
                continue
            kind = metadata.get("kind", "theorem")
            role = {
                "def": "definition",
                "instance": "instance",
                "projection": "projection",
                "constructor": "constructor",
                "inductive": "type_former",
                "structure": "type_former",
                "class": "type_former",
                "recursor": "recursor",
                "axiom": "axiom",
                "opaque": "definition",
                "quot": "type_former",
            }.get(kind, "lemma")
            target_role = target_role or role
            result.append({
                "name": name,
                "role": role,
                "target_role": target_role,
                "origin": "lean_infotree",
                "kind": kind,
                "module": metadata.get("module"),
                "project": bool(metadata.get("project", name in known_declarations)),
                "is_instance": bool(metadata.get("is_instance", False)),
                "is_class": bool(metadata.get("is_class", False)),
                "is_projection": bool(metadata.get("is_projection", False)),
                "is_auto_generated": bool(metadata.get("is_auto_generated", False)),
                "statement_pretty": metadata.get("statement_pretty")
                or metadata.get("type_pretty", ""),
                "docstring": metadata.get("docstring"),
            })
        return result

    def _add_claim(
        self,
        claim_id: str,
        *,
        role: str,
        user_name: str,
        statement: str,
        range_value: dict | None,
        introduced_by: str,
        origin: str,
        scope_id: str = "root",
        inaccessible_name: bool = False,
        type_expr_id: str | None = None,
    ) -> None:
        statement = _clean_statement(statement)
        self.graph.add_node(
            claim_id,
            kind="claim",
            role=role,
            user_name=user_name,
            statement_pretty=statement,
            formal=statement,
            pretty=statement,
            type_expr_id=type_expr_id or f"expr:{self.project_id}:{claim_id}",
            scope_id=scope_id,
            introduced_by=introduced_by,
            range=_normalize_range(range_value),
            range_origin="lean" if range_value else "none",
            origin=origin,
            inaccessible_name=inaccessible_name,
            branch_tag=(
                scope_id.rsplit("/", 1)[-1]
                if scope_id != "root"
                else None
            ),
            is_trivial=False,
            is_final=role == "final_goal",
            fan_out=0,
            importance=0.0,
        )

    def add_declaration(
        self,
        record: dict,
        tactic_rows: list[tuple[str, str]],
        comments: list,
        known_declarations: dict[str, dict] | None = None,
        term_records: list[dict] | None = None,
        source_text: str = "",
    ) -> None:
        final_range = record.get("range")
        decl_id = f"claim:{self.project_id}:{self.decl_name}:final"
        type_pretty = _clean_statement(record.get("type_pretty", ""))
        statement_context = record.get("statement_context") or {}
        context_variables = statement_context.get("variables", [])
        context_assumptions = statement_context.get("assumptions", [])
        final_statement = _clean_statement(
            statement_context.get("goal_pretty") or type_pretty
        )
        fallback_variables: list[tuple[str, str]] = []
        fallback_assumptions: list[str] = []
        if not context_variables and not context_assumptions and type_pretty.startswith("∀"):
            match = re.match(r"^∀\s*(.+?),\s*(.+)$", type_pretty)
            if match:
                binders, rest = match.groups()
                for chunk in re.findall(r"\{([^}]*)\}", binders):
                    names_type = chunk.split(":", 1)
                    names = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", names_type[0])
                    fallback_variables.extend(
                        (name, names_type[1].strip() if len(names_type) > 1 else "")
                        for name in names
                    )
                arrow_parts = [p.strip() for p in re.split(r"\s*→\s*", rest)]
                final_statement = arrow_parts[-1] if arrow_parts else rest
                fallback_assumptions = arrow_parts[:-1]

        fvar_claim_ids: dict[str, str] = {}
        claim_names: dict[str, str] = {}
        initial_names: set[str] = set()
        anon_index = 0

        def display_name(item: dict) -> tuple[str, bool]:
            nonlocal anon_index
            raw_name = str(item.get("name", item.get("user_name", "")))
            inaccessible = bool(item.get("inaccessible_name", False))
            if not raw_name or raw_name == "_" or inaccessible:
                anon_index += 1
                return f"h_anon_{anon_index}", True
            return raw_name, False

        for index, item in enumerate(context_variables):
            name, inaccessible = display_name(item)
            claim_id = f"claim:{self.project_id}:{self.decl_name}:variable:{index}"
            type_pretty = _clean_statement(item.get("type_pretty", ""))
            self._add_claim(
                claim_id,
                role="variable",
                user_name=name,
                statement=f"{name} : {type_pretty}",
                range_value=final_range,
                introduced_by="statement",
                origin="lean_env",
                inaccessible_name=inaccessible,
                type_expr_id=item.get("type_expr_id"),
            )
            initial_names.add(str(item.get("name", "")))
            if item.get("fvar_id"):
                fvar_claim_ids[item["fvar_id"]] = claim_id
            claim_names[name] = claim_id

        for index, item in enumerate(context_assumptions, start=1):
            name, inaccessible = display_name(item)
            claim_id = f"claim:{self.project_id}:{self.decl_name}:assumption:{index}"
            statement = _clean_statement(item.get("type_pretty", ""))
            self._add_claim(
                claim_id,
                role="assumption",
                user_name=name,
                statement=statement,
                range_value=final_range,
                introduced_by="statement",
                origin="lean_env",
                inaccessible_name=inaccessible,
                type_expr_id=item.get("type_expr_id"),
            )
            initial_names.add(str(item.get("name", "")))
            if item.get("fvar_id"):
                fvar_claim_ids[item["fvar_id"]] = claim_id
            claim_names[name] = claim_id

        for index, (name, type_name) in enumerate(fallback_variables):
            claim_id = f"claim:{self.project_id}:{self.decl_name}:variable:{index}"
            self._add_claim(
                claim_id,
                role="variable",
                user_name=name,
                statement=f"{name} : {type_name or 'ℕ'}",
                range_value=final_range,
                introduced_by="statement",
                origin="lean_env",
            )
            initial_names.add(name)
            claim_names[name] = claim_id

        assumption_types = [
            item.get("type_pretty", "") for item in context_assumptions
        ] or fallback_assumptions
        for index, assumption in enumerate(assumption_types, start=1):
            if context_assumptions:
                continue
            name = f"h{index}"
            claim_id = f"claim:{self.project_id}:{self.decl_name}:assumption:{index}"
            self._add_claim(
                claim_id,
                role="assumption",
                user_name=name,
                statement=assumption,
                range_value=final_range,
                introduced_by="statement",
                origin="lean_env",
            )
            initial_names.add(name)
            claim_names[name] = claim_id

        final_type_expr_id = statement_context.get("goal_expr_id")
        self._add_claim(
            decl_id,
            role="final_goal",
            user_name="",
            statement=final_statement,
            range_value=final_range,
            introduced_by="statement",
            origin="lean_env",
            type_expr_id=final_type_expr_id,
        )
        claim_names["goal"] = decl_id

        known_declarations = known_declarations or {}
        term_records = term_records or []
        source_lines = source_text.splitlines()

        def claim_visible(claim_id: str, scope_id: str) -> bool:
            claim_scope = str(self.graph.nodes[claim_id].get("scope_id", "root"))
            return claim_scope == "root" or claim_scope == scope_id or scope_id.startswith(
                claim_scope + "/"
            )

        def map_local_fvar(
            local: dict,
            *,
            allow_new: bool,
            inference_id: str,
            scope_id: str,
            range_value: dict | None,
            claim_role: str = "intermediate",
        ) -> str | None:
            nonlocal anon_index
            fvar_id = str(local.get("fvar_id", ""))
            if fvar_id and fvar_id in fvar_claim_ids:
                return fvar_claim_ids[fvar_id]
            raw_name = str(local.get("user_name", local.get("name", "")))
            inaccessible = bool(local.get("inaccessible_name", False))
            if (
                scope_id == "root"
                and raw_name in initial_names
                and raw_name in claim_names
            ):
                claim_id = claim_names[raw_name]
                if fvar_id:
                    fvar_claim_ids[fvar_id] = claim_id
                return claim_id
            if not allow_new:
                claim_id = claim_names.get(raw_name)
                return claim_id if claim_id and claim_visible(claim_id, scope_id) else None
            anon_index += 1
            user_name = (
                f"h_anon_{anon_index}"
                if not raw_name or raw_name == "_" or inaccessible
                else raw_name
            )
            statement = _clean_statement(str(local.get("type_pretty", "")))
            if not statement:
                return None
            new_claim_id = (
                f"claim:{self.project_id}:{self.decl_name}:intermediate:"
                f"{inference_id.rsplit(':', 1)[-1]}:{len(fvar_claim_ids)}"
            )
            self._add_claim(
                new_claim_id,
                role=claim_role,
                user_name=user_name,
                statement=statement,
                range_value=range_value,
                introduced_by=inference_id,
                origin="lean_infotree",
                scope_id=scope_id,
                inaccessible_name=(not raw_name or raw_name == "_" or inaccessible),
                type_expr_id=local.get("type_expr_id"),
            )
            if fvar_id:
                fvar_claim_ids[fvar_id] = new_claim_id
            if raw_name:
                claim_names[raw_name] = new_claim_id
            claim_names[user_name] = new_claim_id
            return new_claim_id

        def add_calc_substeps(
            inference_id: str,
            payload: dict,
            *,
            inference_count: int,
            scope_id: str,
            range_value: dict | None,
        ) -> tuple[list[str], bool]:
            if not range_value or not source_lines:
                return [], False
            tactic_lines = str(payload.get("tactic_text", "")).splitlines()
            if tactic_lines and tactic_lines[0].strip() == "calc":
                tactic_lines = tactic_lines[1:]
            row_lines = [
                (index, line)
                for index, line in enumerate(tactic_lines, start=1)
                if line.strip()
            ]
            if not row_lines:
                return [], False

            parent_start = range_value["start"]["line"]
            claim_ids: list[str] = []
            child_inference_ids: list[str] = []
            all_complete = True
            for step_index, (line_offset, _) in enumerate(row_lines, start=1):
                source_line_number = parent_start + line_offset
                if source_line_number < 1 or source_line_number > len(source_lines):
                    return claim_ids, False
                source_line = source_lines[source_line_number - 1]
                code = source_line.strip()
                left_side = code.split(":=", 1)[0] if ":=" in code else ""
                relation_match = re.search(
                    r"(?:<=|>=|≤|≥|<|>|=|≠|≈|∈|∉|⊆)",
                    left_side,
                )
                parsed = bool(left_side and relation_match and ":=" in code)
                if not parsed:
                    all_complete = False

                assignment_column = source_line.find(":=") + 2 if ":=" in source_line else 0
                candidates = []
                for term in term_records:
                    if term.get("module") != record.get("module"):
                        continue
                    term_range = _normalize_range(term.get("range"))
                    if not term_range or term_range["start"]["line"] != source_line_number:
                        continue
                    expected = str(term.get("expected_type_pretty") or "")
                    if (
                        not expected
                        or expected == "<none>"
                        or expected.startswith(("Sort ", "Type "))
                        or "?m." in expected
                    ):
                        continue
                    if term_range["start"]["column"] < assignment_column:
                        continue
                    span = (
                        term_range["end"]["column"] - term_range["start"]["column"]
                    )
                    candidates.append((span, term))
                term_record = min(candidates, key=lambda item: item[0])[1] if candidates else None
                if term_record is None:
                    all_complete = False
                    claim_statement = left_side.strip()
                    type_expr_id = f"expr:{self.project_id}:{self.decl_name}:calc:{inference_count}:{step_index}"
                else:
                    claim_statement = str(term_record["expected_type_pretty"])
                    type_expr_id = term_record.get("expected_type_expr_id")
                    if not type_expr_id:
                        all_complete = False
                        type_expr_id = (
                            f"expr:{self.project_id}:{self.decl_name}:"
                            f"calc:{inference_count}:{step_index}"
                        )

                child_id = (
                    f"inference:{self.project_id}:{self.decl_name}:"
                    f"{inference_count}:calc:{step_index}"
                )
                claim_id = (
                    f"claim:{self.project_id}:{self.decl_name}:"
                    f"calc:{inference_count}:{step_index}"
                )
                claim_range = {
                    "start": {
                        "line": source_line_number,
                        "column": len(source_line) - len(source_line.lstrip()),
                    },
                    "end": {
                        "line": source_line_number,
                        "column": len(source_line.rstrip()),
                    },
                }
                self._add_claim(
                    claim_id,
                    role="intermediate",
                    user_name=f"calc_{step_index}",
                    statement=claim_statement,
                    range_value=claim_range,
                    introduced_by=child_id,
                    origin="lean_infotree" if term_record else "heuristic",
                    scope_id=scope_id,
                    type_expr_id=type_expr_id,
                )
                claim_ids.append(claim_id)

                used_fvars_for_step: list[str] = []
                step_status = "complete" if parsed and term_record else "partial"
                partial_reason = None
                if step_status == "partial":
                    partial_reason = (
                        "calc_step_type_unavailable"
                        if parsed
                        else "calc_step_parse_failed"
                    )
                term_fvars = term_record.get("used_fvars", []) if term_record else []
                for local in term_fvars:
                    if not isinstance(local, dict):
                        continue
                    claim_for_fvar = map_local_fvar(
                        local,
                        allow_new=False,
                        inference_id=child_id,
                        scope_id=scope_id,
                        range_value=claim_range,
                    )
                    if claim_for_fvar:
                        if claim_visible(claim_for_fvar, scope_id):
                            used_fvars_for_step.append(claim_for_fvar)
                        else:
                            step_status = "partial"
                            partial_reason = "cross_scope_fvar"
                            all_complete = False
                    else:
                        step_status = "partial"
                        partial_reason = "unmapped_fvar"
                        all_complete = False
                step_consts = self.used_consts(
                    {"used_consts": term_record.get("used_consts", []) if term_record else []},
                    known_declarations,
                )
                self.graph.add_node(
                    child_id,
                    kind="inference",
                    justification_type="term_construction",
                    tactic_text=code,
                    syntax_kind="Lean.calcStep",
                    range=claim_range,
                    range_origin="lean",
                    parent_inference=inference_id,
                    depth=int(self.graph.nodes[inference_id].get("depth", 1)) + 1,
                    depth_origin="heuristic",
                    ordinal=step_index,
                    ordinal_origin="heuristic",
                    scope_id=scope_id,
                    scope_origin=self.graph.nodes[inference_id].get(
                        "scope_origin", "heuristic"
                    ),
                    branch_tag=(
                        scope_id.rsplit("/", 1)[-1]
                        if scope_id != "root"
                        else None
                    ),
                    hierarchy_origin="heuristic",
                    status=step_status,
                    partial_reason=partial_reason,
                    proof_term_pretty=(
                        term_record.get("expr_pretty")
                        if term_record and not any(
                            token in str(term_record.get("expr_pretty", ""))
                            for token in ("_fvar.", "?m.", "_uniq.")
                        )
                        else None
                    ),
                    expr_id=(
                        term_record.get("expr_id")
                        if term_record
                        else f"expr:{self.project_id}:{child_id}"
                    ),
                    used_fvars=sorted(set(used_fvars_for_step)),
                    used_consts=step_consts,
                    closed_by_automation=False,
                    origin="lean_infotree" if term_record else "heuristic",
                    comment=_nearest_comment(comments, source_line_number),
                    is_trivial=False,
                    subproof_step_count=1,
                    subproof_term_size=len(str(term_record.get("expr_pretty", "")))
                    if term_record
                    else 0,
                    fan_out=1,
                    importance=0.4,
                    role="side_claim",
                )
                self.graph.add_edge(inference_id, child_id, kind="contains")
                for premise in sorted(set(used_fvars_for_step)):
                    self.graph.add_edge(premise, child_id, kind="premise")
                self.graph.add_edge(child_id, claim_id, kind="conclusion")
                if child_inference_ids:
                    self.graph.add_edge(
                        child_inference_ids[-1],
                        child_id,
                        kind="next_step",
                    )
                child_inference_ids.append(child_id)
                for const in step_consts:
                    metadata = known_declarations.get(const["name"])
                    if metadata is None:
                        self.graph.nodes[child_id]["status"] = "partial"
                        self.graph.nodes[child_id]["partial_reason"] = "missing_const_metadata"
                        all_complete = False
                        continue
                    is_project = bool(metadata.get("project", False))
                    ref_id = (
                        f"decl:{self.project_id}:{const['name']}"
                        if is_project
                        else f"decl:external:{const['name']}"
                    )
                    if not self.graph.has_node(ref_id):
                        self.graph.add_node(
                            ref_id,
                            kind="decl",
                            name=const["name"],
                            target_role=const["target_role"],
                            declaration_kind=metadata.get("kind", "unknown"),
                            module=metadata.get("module"),
                            statement_pretty=metadata.get("statement_pretty")
                            or metadata.get("type_pretty")
                            or "",
                            docstring=metadata.get("docstring"),
                            origin="lean_env",
                            range=None,
                            range_origin="none",
                            project=is_project,
                            external=not is_project,
                        )
                    self.graph.add_edge(child_id, ref_id, kind="refs")

            return claim_ids, all_complete


        selected_steps = []
        for row_id, payload_json in tactic_rows:
            payload = json.loads(payload_json)
            if payload.get("status") != "dead" and payload.get("synthetic_syntax") is not True:
                selected_steps.append((row_id, payload))
        step_ranges = [
            _normalize_range(payload.get("range"))
            for _, payload in selected_steps
        ]
        parent_indices: dict[int, int] = {}
        step_depths: dict[int, int] = {}
        for index, range_value in enumerate(step_ranges):
            if not range_value:
                step_depths[index] = 1
                continue
            start = range_value["start"]
            end = range_value["end"]
            enclosing = []
            for candidate, outer in enumerate(step_ranges):
                if candidate == index or not outer:
                    continue
                outer_start = outer["start"]
                outer_end = outer["end"]
                if (
                    (outer_start["line"], outer_start["column"]) <= (start["line"], start["column"])
                    and (outer_end["line"], outer_end["column"]) >= (end["line"], end["column"])
                    and (outer_end["line"], outer_end["column"]) > (end["line"], end["column"])
                ):
                    span = (
                        (outer_end["line"] - outer_start["line"]) * 1_000_000
                        + outer_end["column"] - outer_start["column"]
                    )
                    enclosing.append((span, candidate))
            if enclosing:
                parent_indices[index] = min(enclosing)[1]
            else:
                step_depths[index] = 1

        def resolve_depth(index: int, visiting: set[int] | None = None) -> int:
            if index in step_depths:
                return step_depths[index]
            if visiting is None:
                visiting = set()
            if index in visiting:
                raise ValueError("Tactic source ranges form a containment cycle")
            visiting.add(index)
            parent = parent_indices.get(index)
            depth = resolve_depth(parent, visiting) + 1 if parent is not None else 1
            step_depths[index] = depth
            visiting.remove(index)
            return depth

        for index in range(len(selected_steps)):
            resolve_depth(index)

        def branch_scope(line: int, column: int) -> str:
            branch_stack: list[tuple[int, str]] = []
            declaration_start_line = (
                _normalize_range(final_range)["start"]["line"]
                if _normalize_range(final_range)
                else 1
            )
            for line_number, source_line in enumerate(
                source_lines[declaration_start_line - 1:line],
                start=declaration_start_line,
            ):
                if any(comment.start_line <= line_number <= comment.end_line for comment in comments):
                    continue
                indent = len(source_line) - len(source_line.lstrip())
                if line_number == line and indent >= column:
                    continue
                match = re.match(
                    r"^\s*(?:case\s+([A-Za-z_][\w'.]*)\s*=>|\|\s*([A-Za-z_][\w'.]*)(?:\s+.*?)?\s*=>|·\s*)",
                    source_line,
                )
                if match:
                    label = match.group(1) or match.group(2)
                    while branch_stack and branch_stack[-1][0] >= indent:
                        branch_stack.pop()
                    branch_stack.append(
                        (indent, f"case:{label}" if label else f"bullet:{line_number}")
                    )
            if not branch_stack:
                return "root"
            return "root/" + "/".join(label for _, label in branch_stack)

        inference_count = 0
        previous_by_scope: dict[str, str] = {}
        ordinals_by_scope: dict[str, int] = {}
        inference_ids = {
            index: f"inference:{self.project_id}:{self.decl_name}:{index + 1}"
            for index in range(len(selected_steps))
        }
        for step_index, (_step_id, payload) in enumerate(selected_steps):
            inference_count += 1
            inference_id = f"inference:{self.project_id}:{self.decl_name}:{inference_count}"
            tactic_text = (payload.get("tactic_text") or "").strip()
            syntax_kind = payload.get("syntax_kind")
            if not syntax_kind:
                syntax_kind = "Lean.Parser.Tactic.unknown"
            justification, closed = self.classify_tactic(tactic_text, syntax_kind)
            range_value = _normalize_range(payload.get("range"))
            line = (range_value or {}).get("start", {}).get("line", 1)
            assignments = payload.get("assignments", [])
            assignment_text = "\n".join(
                str(a.get("expr_pretty")) for a in assignments
                if a.get("expr_pretty")
            )

            status = payload.get("status", "complete")
            if status not in {"complete", "partial"}:
                status = "complete"
            partial_reason = payload.get("partial_reason")
            if not tactic_text:
                status = "partial"
                partial_reason = "missing_tactic_text"
            if not syntax_kind or syntax_kind.endswith(".unknown"):
                status = "partial"
                partial_reason = partial_reason or "missing_syntax_kind"

            range_start = (range_value or {}).get("start", {})
            inferred_scope = branch_scope(
                int(range_start.get("line", 1)),
                int(range_start.get("column", 0)),
            )
            scope_id = payload.get("scope_id") or inferred_scope
            parent_index = parent_indices.get(step_index)
            parent_inference = (
                inference_ids[parent_index]
                if parent_index is not None
                else payload.get("parent_inference")
            )
            depth = step_depths.get(step_index, 1)
            sibling_key = f"{scope_id}|{parent_inference or 'root'}"
            ordinals_by_scope[sibling_key] = ordinals_by_scope.get(sibling_key, 0) + 1
            sibling_ordinal = ordinals_by_scope[sibling_key]
            before_fvars: set[str] = set()
            new_claim_ids: list[str] = []
            for goal in payload.get("goals_before", []) or []:
                for local in goal.get("locals", []) or []:
                    local_id = str(local.get("fvar_id", ""))
                    if local_id:
                        before_fvars.add(local_id)
                    map_local_fvar(
                        local,
                        allow_new=scope_id != "root",
                        inference_id=inference_id,
                        scope_id=scope_id,
                        range_value=range_value,
                        claim_role="case_branch",
                    )

            for goal in payload.get("goals_after", []) or []:
                for local in goal.get("locals", []) or []:
                    local_id = str(local.get("fvar_id", ""))
                    if local_id and local_id not in before_fvars and local_id not in fvar_claim_ids:
                        claim_id = map_local_fvar(
                            local,
                            allow_new=True,
                            inference_id=inference_id,
                            scope_id=scope_id,
                            range_value=range_value,
                        )
                        if claim_id:
                            new_claim_ids.append(claim_id)
                    else:
                        map_local_fvar(
                            local,
                            allow_new=False,
                            inference_id=inference_id,
                            scope_id=scope_id,
                            range_value=range_value,
                        )

            # Accept older raw fixtures while all newly exported facts use FVarId objects.
            if not new_claim_ids:
                for index, local in enumerate(payload.get("introduced_claims", []) or []):
                    name = str(local.get("user_name", ""))
                    claim_id = (
                        f"claim:{self.project_id}:{self.decl_name}:intermediate:"
                        f"{inference_count}:{index}"
                    )
                    self._add_claim(
                        claim_id,
                        role="intermediate",
                        user_name=name or f"h_anon_{index + 1}",
                        statement=str(local.get("type_pretty", "")),
                        range_value=local.get("range") or range_value,
                        introduced_by=inference_id,
                        origin="lean_infotree",
                        scope_id=local.get("scope_id", scope_id),
                        inaccessible_name=not bool(name),
                        type_expr_id=local.get("type_expr_id"),
                    )
                    new_claim_ids.append(claim_id)
                    if name:
                        claim_names[name] = claim_id

            used_fvars: list[str] = []
            unmapped = False
            raw_used_fvars = payload.get("used_fvars", []) or []
            if not raw_used_fvars:
                raw_used_fvars = [
                    fvar
                    for assignment in assignments
                    for fvar in assignment.get("used_fvars", []) or []
                ]
            for raw_fvar in raw_used_fvars:
                if isinstance(raw_fvar, dict):
                    fvar_id = str(raw_fvar.get("fvar_id", ""))
                    user_name = str(raw_fvar.get("user_name", ""))
                    claim_id = fvar_claim_ids.get(fvar_id) or claim_names.get(user_name)
                    if claim_id and claim_visible(claim_id, scope_id):
                        used_fvars.append(claim_id)
                    elif claim_id:
                        unmapped = True
                    elif fvar_id:
                        unmapped = True
                else:
                    name = str(raw_fvar).removeprefix("_fvar.")
                    claim_id = claim_names.get(name)
                    if claim_id and claim_visible(claim_id, scope_id):
                        used_fvars.append(claim_id)
                    elif claim_id:
                        unmapped = True
                    elif name:
                        unmapped = True

            if unmapped:
                status = "partial"
                partial_reason = "unmapped_fvar"
            if status == "partial" and not partial_reason:
                partial_reason = "incomplete_assignment"

            used_consts = self.used_consts(payload, known_declarations)
            safe_proof_term = assignment_text
            if any(token in safe_proof_term for token in ("_fvar.", "?m.", "_uniq.")):
                safe_proof_term = ""
            if len(safe_proof_term) > 1000:
                safe_proof_term = safe_proof_term[:997] + "..."
            direct_expr_ids = [
                assignment.get("expr_id")
                for assignment in assignments
                if assignment.get("kind") == "direct" and assignment.get("expr_id")
            ]

            self.graph.add_node(
                inference_id,
                kind="inference",
                justification_type=justification,
                tactic_text=tactic_text,
                syntax_kind=syntax_kind,
                range=range_value,
                range_origin="lean" if range_value else "none",
                used_consts=used_consts,
                used_fvars=sorted(set(used_fvars)),
                closed_by_automation=justification.startswith("automation:"),
                status=status,
                partial_reason=partial_reason,
                proof_term_pretty=safe_proof_term or None,
                expr_id=direct_expr_ids[0] if direct_expr_ids else f"expr:{self.project_id}:{inference_id}",
                origin="lean_infotree",
                comment=_nearest_comment(comments, line),
                is_trivial=bool(
                    tactic_text in {"trivial", "rfl", "assumption"} or
                    re.match(r"^exact\s+[A-Za-z_][A-Za-z0-9_]*$", tactic_text)
                ),
                is_trivial_origin="heuristic",
                rewrites=(
                    _rewrite_entries(tactic_text)
                    if justification == "rewrite"
                    else []
                ),
                subproof_step_count=1,
                subproof_term_size=len(assignment_text),
                fan_out=0,
                depth=depth,
                depth_origin=(
                    "lean_infotree" if payload.get("depth") is not None else "heuristic"
                ),
                ordinal=sibling_ordinal,
                ordinal_origin="heuristic",
                scope_id=scope_id,
                scope_origin=(
                    "lean_infotree" if payload.get("scope_id") is not None else "heuristic"
                ),
                branch_tag=(
                    scope_id.rsplit("/", 1)[-1]
                    if scope_id != "root"
                    else None
                ),
                parent_inference=parent_inference,
                hierarchy_origin=(
                    "lean_infotree"
                    if payload.get("parent_inference") is not None
                    else "heuristic"
                ),
                role="main_line",
                importance=0.5,
            )

            if justification == "calc":
                calc_claims, calc_complete = add_calc_substeps(
                    inference_id,
                    payload,
                    inference_count=inference_count,
                    scope_id=scope_id,
                    range_value=range_value,
                )
                if calc_claims:
                    used_fvars = []
                    used_consts = []
                    self.graph.nodes[inference_id]["used_fvars"] = []
                    self.graph.nodes[inference_id]["used_consts"] = []
                    self.graph.nodes[inference_id]["proof_term_pretty"] = None
                    for claim_id in calc_claims:
                        self.graph.add_edge(claim_id, inference_id, kind="premise")
                    if not calc_complete:
                        self.graph.nodes[inference_id]["status"] = "partial"
                        self.graph.nodes[inference_id]["partial_reason"] = "incomplete_calc_step"
                else:
                    self.graph.nodes[inference_id]["status"] = "partial"
                    self.graph.nodes[inference_id]["partial_reason"] = "calc_steps_unavailable"

            if used_fvars:
                for claim_id in set(used_fvars):
                    if claim_id != decl_id:
                        self.graph.add_edge(claim_id, inference_id, kind="premise")
            for claim_id in sorted(set(new_claim_ids)):
                self.graph.add_edge(inference_id, claim_id, kind="conclusion")
            if payload.get("goals_after") == [] and not new_claim_ids:
                self.graph.add_edge(inference_id, decl_id, kind="conclusion")

            for const in used_consts:
                name = const["name"]
                metadata = known_declarations.get(name)
                if metadata is None:
                    status = "partial"
                    self.graph.nodes[inference_id]["status"] = status
                    self.graph.nodes[inference_id]["partial_reason"] = "missing_const_metadata"
                    continue
                is_project = bool(metadata.get("project", False))
                ref_id = (
                    f"decl:{self.project_id}:{name}"
                    if is_project
                    else f"decl:external:{name}"
                )
                if not self.graph.has_node(ref_id):
                    self.graph.add_node(
                        ref_id,
                        kind="decl",
                        name=name,
                        target_role=const["target_role"],
                        declaration_kind=metadata.get("kind", const.get("kind", "unknown")),
                        module=metadata.get("module", const.get("module")),
                        statement_pretty=metadata.get("statement_pretty")
                        or metadata.get("type_pretty")
                        or const.get("statement_pretty", ""),
                        docstring=metadata.get("docstring", const.get("docstring")),
                        origin="lean_env",
                        range=None,
                        range_origin="none",
                        project=is_project,
                        external=not is_project,
                    )
                self.graph.add_edge(inference_id, ref_id, kind="refs")

            if parent_inference and self.graph.has_node(parent_inference):
                self.graph.add_edge(parent_inference, inference_id, kind="contains")
            previous_inference = previous_by_scope.get(sibling_key)
            if previous_inference:
                self.graph.add_edge(previous_inference, inference_id, kind="next_step")
            previous_by_scope[sibling_key] = inference_id

        logical_graph = nx.DiGraph()
        logical_graph.add_nodes_from(
            node for node, data in self.graph.nodes(data=True)
            if data.get("kind") in {"claim", "inference"}
        )
        logical_graph.add_edges_from(
            (source, target)
            for source, target, edge in self.graph.edges(data=True)
            if edge.get("kind") in {"premise", "conclusion"}
            and source in logical_graph
            and target in logical_graph
        )
        critical_nodes = (
            nx.ancestors(logical_graph, decl_id) | {decl_id}
            if decl_id in logical_graph
            else set()
        )
        contains_graph = nx.DiGraph()
        contains_graph.add_nodes_from(
            node for node, data in self.graph.nodes(data=True)
            if data.get("kind") == "inference"
        )
        contains_graph.add_edges_from(
            (source, target)
            for source, target, edge in self.graph.edges(data=True)
            if edge.get("kind") == "contains"
        )

        for claim_id, data in list(self.graph.nodes(data=True)):
            if data.get("kind") != "claim":
                continue
            fan_out = len({
                target
                for _source, target, edge in self.graph.out_edges(claim_id, data=True)
                if edge.get("kind") == "premise"
            })
            data["fan_out"] = fan_out
            role = (
                "technical"
                if data.get("role") in {"variable", "assumption"}
                else "case_branch"
                if data.get("scope_id") != "root"
                else "main_line"
                if claim_id in critical_nodes
                else "side_claim"
            )
            data["proof_role"] = role
            data["role_origin"] = "heuristic"
            data["importance"] = min(
                1.0,
                (0.45 if claim_id in critical_nodes else 0.0)
                + 0.25 * min(fan_out / 3, 1)
                + 0.2 * (1 if role == "main_line" else 0)
                + 0.1 / (1 + int(data.get("depth", 0))),
            )
            data["importance_origin"] = "heuristic"

        for inference_id, data in list(self.graph.nodes(data=True)):
            if data.get("kind") != "inference":
                continue
            fan_out = len({
                target
                for _source, target, edge in self.graph.out_edges(inference_id, data=True)
                if edge.get("kind") == "conclusion"
                and self.graph.nodes[target].get("kind") == "claim"
            })
            data["fan_out"] = fan_out
            subproof_size = sum(
                1
                for child in nx.descendants(contains_graph, inference_id)
                if not str(self.graph.nodes[child].get("justification_type", "")).startswith(
                    "automation:"
                )
            )
            if not str(data.get("justification_type", "")).startswith("automation:"):
                subproof_size += 1
            role = (
                "case_branch"
                if data.get("scope_id") != "root"
                else "main_line"
                if inference_id in critical_nodes
                else "side_claim"
            )
            data["role"] = role
            data["role_origin"] = "heuristic"
            data["importance"] = min(
                1.0,
                (0.45 if inference_id in critical_nodes else 0.0)
                + 0.25 * min(fan_out / 3, 1)
                + 0.2 * min(subproof_size / 5, 1)
                + 0.1 / (1 + int(data.get("depth", 1))),
            )
            data["importance_origin"] = "heuristic"
            data["subproof_step_count"] = subproof_size
            data["is_trivial_origin"] = "heuristic"

    def write(self, directory: Path) -> tuple[Path, Path]:
        directory.mkdir(parents=True, exist_ok=True)
        json_path = directory / f"{self.decl_name.replace('.', '_')}.json"
        graphml_path = directory / f"{self.decl_name.replace('.', '_')}.graphml"
        data = {
            "directed": True,
            "project_id": self.project_id,
            "decl_name": self.decl_name,
            "schema_version": 2,
            "edge_convention": "claim -> inference -> claim",
            "nodes": [{"id": node, **dict(attrs)} for node, attrs in self.graph.nodes(data=True)],
            "edges": [
                {"source": source, "target": target, **dict(attrs)}
                for source, target, attrs in self.graph.edges(data=True)
            ],
        }
        json_path.write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        graphml_graph = nx.DiGraph()
        graphml_graph.graph.update(self.graph.graph)
        for node, attrs in self.graph.nodes(data=True):
            graphml_graph.add_node(
                node,
                **{
                    key: json.dumps(value) if isinstance(value, (dict, list)) else ("" if value is None else value)
                    for key, value in attrs.items()
                },
            )
        for source, target, attrs in self.graph.edges(data=True):
            graphml_graph.add_edge(source, target, **attrs)
        nx.write_graphml(graphml_graph, graphml_path)
        return json_path, graphml_path
