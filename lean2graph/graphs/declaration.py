from __future__ import annotations

import json
from importlib.resources import files
from pathlib import Path

import networkx as nx
import re
import yaml


_ROLE_PREFIXES = yaml.safe_load(
    files("lean2graph").joinpath("config", "target_roles.yaml").read_text(encoding="utf-8")
)


def _target_role(
    name: str,
    kind: str,
    *,
    is_instance: bool = False,
    is_class: bool = False,
    is_projection: bool = False,
) -> str:
    for role in ("notation_infra", "logic_infra", "automation_internal"):
        if any(name == prefix or name.startswith(prefix) for prefix in _ROLE_PREFIXES[role]):
            return role
    if is_instance:
        return "instance"
    if is_class:
        return "type_former"
    if is_projection:
        return "projection"
    role = {
        "thm": "lemma",
        "theorem": "lemma",
        "instance": "instance",
        "defn": "definition",
        "def": "definition",
        "opaque": "definition",
        "axiom": "axiom",
        "ctor": "constructor",
        "constructor": "constructor",
        "induct": "type_former",
        "inductive": "type_former",
        "quot": "type_former",
        "rec": "recursor",
        "recursor": "recursor",
        "structure": "type_former",
        "class": "type_former",
    }.get(kind)
    if role is None:
        raise ValueError(f"Cannot assign a declaration target_role for kind {kind!r}: {name}")
    return role


_AUXILIARY_SUFFIXES = (
    re.compile(r"(?:^|[._])_?proof_[0-9]+$"),
    re.compile(r"(?:^|[._])match_[0-9]+$"),
    re.compile(r"\.eq_(?:[0-9]+|def)$"),
    re.compile(r"\._?sparseCasesOn_[0-9]+$"),
    re.compile(r"(?:^|[._])_?(?:unfold|sunfold|lambda|closed|spec|aux)(?:_[A-Za-z0-9]+)*$"),
    re.compile(r"(?:^|[._])_?cstage[A-Za-z0-9_]*$"),
)


class DeclarationDAG:
    def __init__(self, project_id: str, scope: str = "project", keep_aux: bool = False) -> None:
        self.project_id = project_id
        self.scope = scope
        self.keep_aux = keep_aux
        self.graph = nx.MultiDiGraph()
        self.graph.graph["project_id"] = project_id
        self.graph.graph["edge_convention"] = "dependent -> dependency"
        self.graph.graph["schema_version"] = 2
        self.folded_into: dict[str, str] = {}
        self.aux_claims: dict[str, list[dict]] = {}

    @staticmethod
    def _is_auxiliary_name(name: str) -> bool:
        return name.startswith("_private.") or name.startswith("_root_._private.") or any(
            pattern.search(name) for pattern in _AUXILIARY_SUFFIXES
        )

    @staticmethod
    def _aux_parent(
        name: str,
        project_names: set[str],
        *,
        is_auxiliary: bool = False,
        is_matcher: bool = False,
        is_private: bool = False,
    ) -> str | None:
        if not (
            is_auxiliary
            or is_matcher
            or is_private
            or DeclarationDAG._is_auxiliary_name(name)
        ):
            return None

        candidates: list[str] = []
        if name.startswith("_private.") or name.startswith("_root_._private."):
            private_name = name.removeprefix("_root_._private.").removeprefix("_private.")
            parts = private_name.split(".")
            if len(parts) >= 3 and parts[1].isdigit():
                private_name = ".".join([parts[0], *parts[2:]])
                candidates.append(private_name)
            suffix = parts[-1]
            matching_names = sorted(
                candidate for candidate in project_names
                if candidate.rsplit(".", 1)[-1] == suffix
            )
            if len(matching_names) == 1:
                candidates.append(matching_names[0])
        for marker in (
            r"\._proof_[0-9]+$",
            r"\.proof_[0-9]+$",
            r"\.match_[0-9]+$",
            r"\.eq_[0-9]+$",
            r"\.eq_def$",
            r"\._?sparseCasesOn_[0-9]+$",
            r"\._?(?:unfold|sunfold|lambda|closed|spec|aux)(?:_[A-Za-z0-9]+)*$",
            r"\._?cstage[A-Za-z0-9_]*$",
        ):
            stripped = re.sub(marker, "", name)
            if stripped != name:
                candidates.append(stripped)
        if "_proof_" in name and not name.startswith("_private."):
            candidates.append(re.sub(r"_proof_[0-9]+$", "", name).rstrip("._"))
        if name.startswith("_proof_"):
            candidates.extend(sorted(
                candidate for candidate in project_names
                if name.startswith(candidate + "_proof_")
            ))
        for candidate in candidates:
            if candidate in project_names:
                return candidate
        return None

    def add_project_declarations(
        self,
        declarations: list[dict],
        *,
        source_files: dict[str, str],
        tactic_records: list[dict] | None = None,
    ) -> None:
        project_records = {record["name"]: record for record in declarations}
        project_names = set(project_records)
        auxiliary_parents: dict[str, str] = {}
        for record in declarations:
            name = record["name"]
            parent = self._aux_parent(
                name,
                project_names - {name},
                is_auxiliary=bool(record.get("is_auxiliary", False)),
                is_matcher=bool(record.get("is_matcher", False)),
                is_private=bool(record.get("is_private", False)),
            )
            if parent:
                auxiliary_parents[name] = parent
        for auxiliary in sorted(auxiliary_parents):
            parent = auxiliary_parents[auxiliary]
            visited = {auxiliary}
            while parent in auxiliary_parents and parent not in visited:
                visited.add(parent)
                parent = auxiliary_parents[parent]
            auxiliary_parents[auxiliary] = parent
        folded = {} if self.keep_aux else auxiliary_parents
        self.folded_into = auxiliary_parents
        project_names.difference_update(folded)
        self.aux_claims = {name: [] for name in project_names}
        for auxiliary, parent in sorted(auxiliary_parents.items()):
            if re.search(r"(?:^|[._])_proof_[0-9]+$", auxiliary):
                record = project_records[auxiliary]
                self.aux_claims[parent].append(
                    {
                        "name": auxiliary,
                        "statement_pretty": record.get("statement_pretty")
                        or record.get("type_pretty", ""),
                        "type_expr_id": record.get("type_expr_id"),
                        "origin": "lean_env",
                    }
                )

        for record in declarations:
            name = record["name"]
            if not self.keep_aux and name in folded:
                continue
            decl_id = f"decl:{self.project_id}:{name}"
            range_record = (
                project_records[auxiliary_parents[name]]
                if self.keep_aux and name in auxiliary_parents
                else record
            )
            range_value = range_record.get("range")
            if isinstance(range_value, str):
                try:
                    range_value = json.loads(range_value)
                except json.JSONDecodeError:
                    range_value = None
            self.graph.add_node(
                decl_id,
                name=name,
                kind=record["kind"],
                type_pretty=record.get("type_pretty", ""),
                statement_pretty=record.get("statement_pretty") or record.get("type_pretty", ""),
                pretty=record.get("statement_pretty") or record.get("type_pretty", ""),
                type_expr_id=record.get("type_expr_id", ""),
                docstring=record.get("docstring"),
                module=record["module"],
                origin="lean_env",
                range=range_value if isinstance(range_value, dict) else None,
                name_range=range_record.get("name_range"),
                range_origin=range_record.get(
                    "range_origin",
                    "lean" if isinstance(range_value, dict) else "none",
                ),
                synthetic=range_value is None,
                project=True,
                is_instance=bool(record.get("is_instance", False)),
                is_class=bool(record.get("is_class", False)),
                is_projection=bool(record.get("is_projection", False)),
                is_auto_generated=bool(record.get("is_auto_generated", False)),
                folded_into=None,
                aux_claims=self.aux_claims.get(name, []),
                automation_summary=self._automation_summary(record, tactic_records or []),
                target_role=_target_role(
                    name,
                    record["kind"],
                    is_instance=bool(record.get("is_instance", False)),
                    is_class=bool(record.get("is_class", False)),
                    is_projection=bool(record.get("is_projection", False)),
                ),
            )

        pending_edges: dict[tuple[str, str, str, str, str, str], int] = {}
        pending_metadata: dict[str, dict] = {}
        for record in declarations:
            source_name = folded.get(record["name"], record["name"])
            if source_name not in project_names:
                continue
            source_id = f"decl:{self.project_id}:{source_name}"
            refs = record.get("const_refs", [])
            ref_metadata = {item["const_name"]: item for item in refs}
            for ref in refs:
                const_name = ref["const_name"]
                target_name = folded.get(const_name, const_name)
                if target_name == source_name:
                    continue
                target_record = project_records.get(target_name)
                target_data = target_record or ref_metadata.get(const_name, {})
                if target_name in project_names:
                    target_id = f"decl:{self.project_id}:{target_name}"
                else:
                    target_id = f"decl:external:{target_name}"
                    pending_metadata.setdefault(target_id, target_data)

                origin = str(ref.get("origin", ""))
                if origin == "type":
                    edge_type = "type_uses"
                    usage_kind = "type_level"
                elif origin == "body":
                    edge_type = "body_uses"
                    usage_kind = ref.get("usage_kind", "argument")
                elif origin == "proof":
                    edge_type = "proof_uses"
                    usage_kind = ref.get("usage_kind", "argument")
                elif origin == "value":
                    if record["kind"] in {"def", "defn", "instance", "opaque"}:
                        edge_type = "body_uses"
                    else:
                        edge_type = "proof_uses"
                    usage_kind = ref.get("usage_kind", "applied_head")
                else:
                    raise ValueError(
                        f"Unsupported constant-reference origin {origin!r} "
                        f"on declaration {record['name']}"
                    )
                if usage_kind not in {"applied_head", "argument", "type_level"}:
                    raise ValueError(
                        f"Unsupported usage_kind {usage_kind!r} on {record['name']} -> {const_name}"
                    )
                if edge_type == "type_uses":
                    usage_kind = "type_level"
                target_role = _target_role(
                    target_name,
                    target_data.get("kind", "unknown"),
                    is_instance=bool(target_data.get("is_instance", False)),
                    is_class=bool(target_data.get("is_class", False)),
                    is_projection=bool(target_data.get("is_projection", False)),
                )
                aux_origin = folded.get(record["name"]) == source_name
                if aux_origin:
                    evidence = f"via_aux:{record['name']}"
                elif const_name in folded:
                    evidence = f"via_aux:{const_name}"
                else:
                    evidence = f"{origin}:Expr.getUsedConstants"
                key = (
                    source_id,
                    target_id,
                    edge_type,
                    usage_kind,
                    evidence,
                    target_role,
                )
                pending_edges[key] = pending_edges.get(key, 0) + int(ref.get("count", 1))

        for external_id, ref_data in sorted(pending_metadata.items()):
            self.graph.add_node(
                external_id,
                name=external_id.removeprefix("decl:external:"),
                kind=ref_data.get("kind", "unknown"),
                target_role=_target_role(
                    external_id.removeprefix("decl:external:"),
                    ref_data.get("kind", "unknown"),
                    is_instance=bool(ref_data.get("is_instance", False)),
                    is_class=bool(ref_data.get("is_class", False)),
                    is_projection=bool(ref_data.get("is_projection", False)),
                ),
                statement_pretty=ref_data.get("statement_pretty") or "",
                type_pretty=ref_data.get("statement_pretty") or "",
                type_expr_id=ref_data.get("type_expr_id") or "",
                docstring=ref_data.get("docstring"),
                module=ref_data.get("module"),
                origin="lean_env",
                range=None,
                name_range=None,
                range_origin="none",
                synthetic=True,
                project=False,
                is_instance=bool(ref_data.get("is_instance", False)),
                is_class=bool(ref_data.get("is_class", False)),
                is_projection=bool(ref_data.get("is_projection", False)),
                is_auto_generated=bool(ref_data.get("is_auto_generated", False)),
            )

        for key, count in sorted(pending_edges.items()):
            source, target, edge_type, usage_kind, evidence, target_role = key
            self.graph.add_edge(
                source,
                target,
                key=f"{edge_type}:{usage_kind}:{evidence}",
                type=edge_type,
                usage_kind=usage_kind,
                count=count,
                origin="lean_env",
                evidence=evidence,
                target_role=target_role,
            )

    @staticmethod
    def _automation_summary(record: dict, tactic_records: list[dict]) -> dict[str, bool]:
        tactic_names = {
            "omega",
            "ring",
            "linarith",
            "nlinarith",
            "norm_num",
            "positivity",
            "simp",
            "decide",
            "aesop",
        }
        name_by_syntax = {
            "normnum": "norm_num",
            "omega": "omega",
            "ring": "ring",
            "linarith": "linarith",
            "nlinarith": "nlinarith",
            "positivity": "positivity",
            "simp": "simp",
            "decide": "decide",
            "aesop": "aesop",
        }
        result: set[str] = set()
        declaration_range = record.get("range")
        if isinstance(declaration_range, str):
            try:
                declaration_range = json.loads(declaration_range)
            except json.JSONDecodeError:
                declaration_range = None
        start = (declaration_range or {}).get("start", {}).get("line")
        end = (declaration_range or {}).get("end", {}).get("line")
        for tactic in tactic_records:
            if tactic.get("module") != record.get("module"):
                continue
            line = tactic.get("range", {}).get("start", {}).get("line")
            if (
                start is not None
                and end is not None
                and line is not None
                and not start <= line <= end
            ):
                continue
            syntax_tail = str(tactic.get("syntax_kind", "")).rsplit(".", 1)[-1].lower()
            name = name_by_syntax.get(syntax_tail)
            if name:
                result.add(name)
        if not result:
            for ref in record.get("const_refs", []):
                name = str(ref.get("const_name", ""))
                if name.startswith(("Lean.Omega.", "Mathlib.Tactic.Omega.")):
                    result.add("omega")
                elif name.startswith("Mathlib.Tactic.Ring"):
                    result.add("ring")
                elif name.startswith("Mathlib.Tactic.Linarith"):
                    result.add("linarith")
                elif name.startswith("Mathlib.Tactic.NormNum"):
                    result.add("norm_num")
        return {name: True for name in sorted(result & tactic_names)}

    def write(self, directory: Path) -> tuple[Path, Path]:
        directory.mkdir(parents=True, exist_ok=True)
        json_path = directory / "declaration_dag.json"
        full_json_path = directory / "declaration_dag.full.json"
        graphml_path = directory / "declaration_dag.graphml"
        full_nodes = [
            {"id": node, **dict(data)}
            for node, data in sorted(
                self.graph.nodes(data=True),
                key=lambda item: item[0],
            )
        ]
        full_edges = [
            {"source": source, "target": target, "key": key, **dict(data)}
            for source, target, key, data in sorted(
                self.graph.edges(data=True, keys=True),
                key=lambda item: (item[0], item[1], str(item[2])),
            )
        ]
        full_data = {
            "directed": True,
            "project_id": self.project_id,
            "edge_convention": "dependent -> dependency",
            "schema_version": 2,
            "profile": "full",
            "nodes": full_nodes,
            "edges": full_edges,
        }
        full_json = json.dumps(
            full_data,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        ) + "\n"
        json_path.write_text(full_json, encoding="utf-8")
        full_json_path.write_text(full_json, encoding="utf-8")

        graphml_graph = nx.MultiDiGraph()
        graphml_graph.graph.update(self.graph.graph)
        for node, data in self.graph.nodes(data=True):
            graphml_graph.add_node(
                node,
                **{
                    key: json.dumps(value) if isinstance(value, (dict, list)) else ("" if value is None else value)
                    for key, value in data.items()
                },
            )
        for source, target, key, data in self.graph.edges(data=True, keys=True):
            graphml_graph.add_edge(
                source,
                target,
                key=key,
                **{
                    key: json.dumps(value) if isinstance(value, (dict, list)) else ("" if value is None else value)
                    for key, value in data.items()
                },
            )
        nx.write_graphml(graphml_graph, graphml_path)

        narrative = nx.MultiDiGraph()
        narrative.graph.update(self.graph.graph)
        for node, data in self.graph.nodes(data=True):
            if data.get("project"):
                narrative.add_node(node, **data)
        for source, target, key, data in self.graph.edges(data=True, keys=True):
            target_data = self.graph.nodes[target]
            if target_data.get("project") or target_data.get("target_role") in {"lemma", "definition"}:
                if target not in narrative:
                    narrative.add_node(target, **target_data)
                narrative.add_edge(source, target, key=key, **data)
        narrative_path = directory / "declaration_dag.narrative.json"
        narrative_path.write_text(
            json.dumps(
                {
                    "directed": True,
                    "project_id": self.project_id,
                    "edge_convention": "dependent -> dependency",
                    "schema_version": 2,
                    "profile": "narrative",
                    "nodes": [
                        {"id": node, **dict(attrs)}
                        for node, attrs in sorted(
                            narrative.nodes(data=True),
                            key=lambda item: item[0],
                        )
                    ],
                    "edges": [
                        {"source": source, "target": target, "key": key, **dict(attrs)}
                        for source, target, key, attrs in sorted(
                            narrative.edges(data=True, keys=True),
                            key=lambda item: (item[0], item[1], str(item[2])),
                        )
                    ],
                },
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            ) + "\n",
            encoding="utf-8",
        )
        return json_path, graphml_path


def write_import_graph(root: Path, project_id: str, directory: Path) -> tuple[Path, Path]:
    graph = nx.DiGraph()
    graph.graph["project_id"] = project_id
    graph.graph["edge_convention"] = "module -> imported module"
    for source in sorted(p for p in root.rglob("*.lean") if ".lake" not in p.parts):
        rel = source.relative_to(root)
        module = ".".join(rel.with_suffix("").parts)
        graph.add_node(module, origin="lean_env", synthetic=False)
        text = source.read_text(encoding="utf-8", errors="replace")
        for match in re.finditer(r"(?m)^import\s+([A-Za-z0-9_.]+)", text):
            imported = match.group(1)
            graph.add_node(imported, origin="lean_env", synthetic=True)
            graph.add_edge(module, imported, origin="source_text")
    directory.mkdir(parents=True, exist_ok=True)
    json_path = directory / "import_graph.json"
    graphml_path = directory / "import_graph.graphml"
    json_path.write_text(
        json.dumps(
            {
                "directed": True,
                "project_id": project_id,
                "schema_version": 2,
                "nodes": [{"id": node, **dict(data)} for node, data in graph.nodes(data=True)],
                "edges": [
                    {"source": source, "target": target, **dict(data)}
                    for source, target, data in graph.edges(data=True)
                ],
            },
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    nx.write_graphml(graph, graphml_path)
    return json_path, graphml_path
