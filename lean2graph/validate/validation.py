from __future__ import annotations

import json
import hashlib
import sqlite3
import re
from pathlib import Path
from importlib.resources import files

import networkx as nx
from jsonschema import Draft202012Validator
from lean2graph.source.comments import tokenize_comments


def _read_schema(name: str) -> dict:
    return json.loads(
        files("lean2graph").joinpath("schemas", name).read_text(encoding="utf-8")
    )


def _schema_errors(data: object, schema_name: str) -> list[str]:
    schema = _read_schema(schema_name)
    return sorted(
        error.message
        for error in Draft202012Validator(schema).iter_errors(data)
    )


def validate_graph_outputs(graphs_dir: Path) -> list[str]:
    expected = [
        (graphs_dir / "declaration_dag.json", "declaration_dag.v2.json"),
        (graphs_dir / "declaration_dag.full.json", "declaration_dag.v2.json"),
        (graphs_dir / "declaration_dag.narrative.json", "declaration_dag.v2.json"),
        (graphs_dir / "import_graph.json", "import_graph.v2.json"),
    ]
    expected.extend(
        (path, "proof_claim.v2.json")
        for path in sorted((graphs_dir / "proofs").glob("*.json"))
    )
    failures: list[str] = []
    for path, schema_name in expected:
        if not path.is_file():
            if path.name in {
                "declaration_dag.json",
                "declaration_dag.full.json",
                "declaration_dag.narrative.json",
                "import_graph.json",
            }:
                failures.append(f"{path.name}: missing graph output")
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            failures.append(f"{path.name}: {exc}")
            continue
        if not isinstance(data, dict) or type(data.get("schema_version")) is not int:
            failures.append(
                f"{path.name}: schema_version must be an integer; "
                "schema v1 is not supported, run analyze to rebuild schema v2"
            )
            continue
        if data["schema_version"] != 2:
            failures.append(
                f"{path.name}: schema v{data['schema_version']} is not supported; "
                "run analyze to rebuild schema v2"
            )
            continue
        failures.extend(
            f"{path.name}: {message}"
            for message in _schema_errors(data, schema_name)
        )
    return failures


def validate_report_file(path: Path) -> list[str]:
    if not path.is_file():
        return [f"{path.name}: missing validation report"]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{path.name}: {exc}"]
    if not isinstance(data, dict) or type(data.get("schema_version")) is not int:
        return [f"{path.name}: schema_version must be an integer"]
    return [
        f"{path.name}: {message}"
        for message in _schema_errors(data, "validation_report.v2.json")
    ]


class ValidationReport:
    def __init__(self, project_id: str) -> None:
        self.project_id = project_id
        self.checks: list[dict] = []

    def add(
        self,
        check_id: str,
        severity: str,
        metric: str,
        value,
        offenders: list[str],
        passed: bool,
    ) -> None:
        self.checks.append(
            {
                "id": check_id,
                "severity": severity,
                "metric": metric,
                "value": value,
                "offenders": offenders,
                "status": "passed" if passed else "failed",
            }
        )

    def validate_m2(
        self,
        *,
        build_status: str,
        matched_toolchain: bool,
        declarations: list[dict],
        dag: nx.DiGraph,
        dag_json_path: Path,
        graphml_path: Path,
    ) -> None:
        self.add(
            "V1",
            "blocking",
            "build_success",
            build_status == "built",
            [] if build_status == "built" else ["project"],
            build_status == "built",
        )
        self.add(
            "V1",
            "blocking",
            "toolchain_match",
            matched_toolchain,
            [] if matched_toolchain else ["project"],
            matched_toolchain,
        )
        project_names = {record["name"] for record in declarations}
        unresolved: list[str] = []
        resolved = 0
        total = 0
        for record in declarations:
            for ref in record.get("const_refs", []):
                total += 1
                if ref["const_name"] in project_names:
                    resolved += 1
                elif ref["const_name"].startswith(("Nat.", "Lean.", "And.", "Eq.", "Bool.", "List.", "Option.", "Classical.", "Decidable.", "Prop", "Type", "Nat", "And", "Eq", "Bool", "List", "Option")):
                    resolved += 1
                else:
                    unresolved.append(ref["const_name"])
        resolution = resolved / total if total else 1.0
        self.add(
            "V3",
            "warning",
            "const_resolution_ratio",
            resolution,
            sorted(set(unresolved)),
            not unresolved,
        )

        cycles = list(nx.strongly_connected_components(dag))
        multi_cycles = [sorted(component) for component in cycles if len(component) > 1]
        self.add(
            "V4",
            "blocking",
            "dag_cycle_scc",
            len(multi_cycles),
            [node for component in multi_cycles for node in component],
            not multi_cycles,
        )
        duplicate_names = sorted(
            name
            for name in project_names
            if sum(record["name"] == name for record in declarations) > 1
        )
        self.add(
            "V4",
            "blocking",
            "duplicate_declarations",
            len(duplicate_names),
            duplicate_names,
            not duplicate_names,
        )

        missing: list[str] = []
        for node, data in dag.nodes(data=True):
            if not data.get("origin"):
                missing.append(str(node))
            if data.get("project") is not True and data.get("synthetic") is not True:
                missing.append(str(node))
        for source, target, data in dag.edges(data=True):
            if not data.get("origin"):
                missing.append(f"{source}->{target}")
        self.add(
            "V5",
            "blocking",
            "node_edge_provenance",
            len(missing),
            sorted(set(missing)),
            not missing,
        )

        data = json.loads(dag_json_path.read_text(encoding="utf-8"))
        schema_errors = _schema_errors(data, "declaration_dag.v2.json")
        self.add(
            "V11",
            "blocking",
            "dag_json_schema",
            len(schema_errors),
            schema_errors,
            not schema_errors,
        )
        try:
            loaded = nx.read_graphml(graphml_path)
            graphml_ok = loaded.number_of_nodes() == dag.number_of_nodes()
            graphml_offenders = [] if graphml_ok else ["declaration_dag.graphml"]
        except Exception as exc:
            graphml_ok = False
            graphml_offenders = [str(exc)]
        self.add(
            "V11",
            "blocking",
            "graphml_roundtrip",
            graphml_ok,
            graphml_offenders,
            graphml_ok,
        )

    def validate_dag_metadata(
        self,
        *,
        declarations: list[dict],
        dag: nx.MultiDiGraph,
        project_root: Path,
    ) -> None:
        range_failures: list[str] = []
        declaration_ranges: dict[str, list[tuple[tuple[int, int], tuple[int, int], str]]] = {}
        source_cache: dict[str, tuple[list[str], int]] = {}
        for declaration in declarations:
            name = declaration.get("name", "<unnamed>")
            module = declaration.get("module", "")
            source_path = project_root / f"{module.replace('.', '/')}.lean"
            if not source_path.is_file():
                source_path = project_root / "Main.lean"
            if source_path.is_file():
                cache_key = str(source_path)
                if cache_key not in source_cache:
                    source_text = source_path.read_text(encoding="utf-8", errors="replace")
                    source_cache[cache_key] = (
                        source_text.splitlines(),
                        source_text.count("\n") + 1,
                    )
                source_lines, line_count = source_cache[cache_key]
            else:
                source_lines, line_count = [], 0

            range_value = declaration.get("range")
            if isinstance(range_value, str):
                try:
                    range_value = json.loads(range_value)
                except json.JSONDecodeError:
                    range_value = None
            if not isinstance(range_value, dict):
                range_failures.append(f"{name}:missing_range")
                continue
            start = range_value.get("start")
            end = range_value.get("end")
            if not isinstance(start, dict) or not isinstance(end, dict):
                range_failures.append(f"{name}:invalid_range_shape")
                continue
            try:
                start_pos = (int(start["line"]), int(start["column"]))
                end_pos = (int(end["line"]), int(end["column"]))
            except (KeyError, TypeError, ValueError):
                range_failures.append(f"{name}:invalid_range_position")
                continue
            if (
                min(*start_pos, *end_pos) < 0
                or start_pos[0] == 0
                or end_pos[0] == 0
                or max(start_pos[0], end_pos[0]) >= 1_000_000_000
                or start_pos > end_pos
            ):
                range_failures.append(f"{name}:invalid_or_sentinel_range")
                continue
            if line_count and max(start_pos[0], end_pos[0]) > line_count:
                range_failures.append(f"{name}:range_outside_source")
                continue
            name_range = declaration.get("name_range")
            if name_range is not None:
                try:
                    name_start = name_range["start"]
                    name_end = name_range["end"]
                    selection = (
                        int(name_start["line"]),
                        int(name_start["column"]),
                    ), (
                        int(name_end["line"]),
                        int(name_end["column"]),
                    )
                    if selection[0] < start_pos or selection[1] > end_pos:
                        range_failures.append(f"{name}:name_range_outside_declaration")
                except (KeyError, TypeError, ValueError):
                    range_failures.append(f"{name}:invalid_name_range")

            auxiliary = any(
                declaration.get(flag)
                for flag in ("is_auxiliary", "is_matcher", "is_private", "is_auto_generated")
            )
            if not auxiliary:
                declaration_ranges.setdefault(module, []).append(
                    (start_pos, end_pos, name)
                )

        for module, ranges in declaration_ranges.items():
            ranges.sort()
            for previous, current in zip(ranges, ranges[1:]):
                if previous[1] > current[0]:
                    range_failures.append(
                        f"{previous[2]} overlaps {current[2]} in {module}"
                    )
        self.add(
            "V20",
            "blocking",
            "declaration_source_ranges",
            len(range_failures),
            sorted(set(range_failures)),
            not range_failures,
        )

        external_failures: list[str] = []
        referenced_external = {
            target
            for _source, target in dag.edges()
            if not dag.nodes[target].get("project", False)
        }
        for node in sorted(referenced_external):
            data = dag.nodes[node]
            for field in (
                "kind",
                "module",
                "statement_pretty",
                "type_expr_id",
                "is_instance",
                "is_class",
                "is_projection",
                "is_auto_generated",
            ):
                if field not in data or data[field] is None or data[field] == "":
                    external_failures.append(f"{node}:{field}")
        self.add(
            "V21",
            "blocking",
            "external_declaration_metadata",
            len(external_failures),
            sorted(set(external_failures)),
            not external_failures,
        )

    def validate_m4(self, trace) -> None:
        self.add(
            "V6",
            "blocking",
            "live_steps",
            trace.live_count,
            [],
            True,
        )
        self.add(
            "V6",
            "warning",
            "dead_steps",
            trace.dead_count,
            [f"{trace.dead_count} dead tactic records"],
            trace.dead_count == 0,
        )
        self.add(
            "V6",
            "warning",
            "partial_steps",
            trace.partial_count,
            [f"{trace.partial_count} partial tactic records"],
            trace.partial_count == 0,
        )
        self.add(
            "V7",
            "warning",
            "proof_term_coverage",
            trace.coverage,
            trace.mismatches,
            trace.coverage >= 0.5,
        )

    def validate_m6(
        self,
        *,
        strict: bool,
        declarations: list[dict],
        build_log: str,
        store_path: Path,
        manifest_path: Path,
        project_root: Path,
        proof_dir: Path,
        graphs_dir: Path,
    ) -> dict:
        forbidden: list[str] = []
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for declaration in declarations:
            name = declaration["name"]
            value_pretty = declaration.get("value_pretty") or ""
            if "sorryAx" in declaration.get("axioms", []) or "sorryAx" in value_pretty:
                forbidden.append(f"{name}:sorryAx")
            if declaration.get("is_unsafe"):
                forbidden.append(f"{name}:unsafe")
            if declaration.get("kind") == "axiom":
                forbidden.append(f"{name}:own_axiom")
            for axiom in declaration.get("axioms", []):
                if axiom not in allowed:
                    forbidden.append(f"{name}:{axiom}")
        for marker in ("Lean.ofReduceBool", "native_decide", "declaration uses 'sorry'"):
            if marker in build_log:
                forbidden.append(marker)
        forbidden = sorted(set(forbidden))
        axioms_passed = not forbidden or not strict
        self.add(
            "V2",
            "blocking" if strict else "warning",
            "unsafe_axioms",
            len(forbidden),
            forbidden,
            axioms_passed,
        )

        proof_files = sorted(proof_dir.glob("*.json"))
        proof_failures: list[str] = []
        schema_failures: list[str] = []
        proof_graphs: list[nx.DiGraph] = []
        for proof_file in proof_files:
            try:
                data = json.loads(proof_file.read_text(encoding="utf-8"))
                required = {"directed", "project_id", "decl_name", "schema_version", "nodes", "edges"}
                missing_fields = sorted(required - data.keys())
                if missing_fields:
                    schema_failures.append(
                        f"{proof_file.name}:missing={','.join(missing_fields)}"
                    )
                if data.get("schema_version") != 2:
                    schema_failures.append(
                        f"{proof_file.name}:schema v1; needed schema v2 rebuild"
                    )
                graph = nx.DiGraph()
                for node in data["nodes"]:
                    graph.add_node(node["id"], **node)
                for edge in data["edges"]:
                    graph.add_edge(edge["source"], edge["target"], **edge)
                proof_graphs.append(graph)
                finals = [
                    node for node in graph.nodes
                    if graph.nodes[node].get("role") == "final_goal"
                ]
                if len(finals) != 1:
                    proof_failures.append(f"{proof_file.name}:final_goal={len(finals)}")
                if not nx.is_directed_acyclic_graph(graph):
                    proof_failures.append(f"{proof_file.name}:cycle")
                claims = [
                    node for node in graph.nodes
                    if graph.nodes[node].get("kind") == "claim"
                ]
                for claim in claims:
                    role = graph.nodes[claim].get("role")
                    if role in {"variable", "assumption"}:
                        continue
                    if not any(
                        graph.nodes[parent].get("kind") == "inference"
                        and graph.edges[parent, claim].get("kind") == "conclusion"
                        for parent in graph.predecessors(claim)
                    ):
                        proof_failures.append(f"{proof_file.name}:claim_no_conclusion:{claim}")
                if finals:
                    logical_graph = nx.DiGraph()
                    logical_graph.add_nodes_from(
                        node for node in graph.nodes
                        if graph.nodes[node].get("kind") in {"claim", "inference"}
                    )
                    logical_graph.add_edges_from(
                        (edge["source"], edge["target"])
                        for edge in data["edges"]
                        if edge.get("kind") in {"premise", "conclusion"}
                        and edge["source"] in logical_graph
                        and edge["target"] in logical_graph
                    )
                    relevant_nodes = {
                        node for node in logical_graph
                        if graph.nodes[node].get("kind") == "inference"
                        or graph.nodes[node].get("role")
                        not in {"variable", "assumption"}
                    }
                    unreachable = [
                        node for node in relevant_nodes
                        if node not in nx.ancestors(logical_graph, finals[0])
                        and node != finals[0]
                    ]
                    if unreachable:
                        proof_failures.append(
                            f"{proof_file.name}:unreachable={','.join(sorted(unreachable)[:5])}"
                        )
            except Exception as exc:
                proof_failures.append(f"{proof_file.name}:{exc}")
        self.add(
            "V8",
            "blocking",
            "proof_claim_structure",
            len(proof_graphs),
            sorted(set(proof_failures)),
            not proof_failures,
        )
        self.add(
            "V11",
            "blocking",
            "proof_json_schema",
            len(proof_files),
            sorted(set(schema_failures)),
            not schema_failures,
        )
        graph_schema_failures = validate_graph_outputs(graphs_dir)
        self.add(
            "V16",
            "blocking",
            "all_graph_outputs_json_schema",
            len(graph_schema_failures),
            graph_schema_failures,
            not graph_schema_failures,
        )

        scope_failures: list[str] = []
        for graph in proof_graphs:
            for node, data in graph.nodes(data=True):
                if data.get("kind") == "inference":
                    for used_fvar in data.get("used_fvars", []):
                        claim = graph.nodes.get(used_fvar)
                        inference_scope = str(data.get("scope_id", "root"))
                        claim_scope = (
                            str(claim.get("scope_id", "root"))
                            if claim is not None
                            else "<missing>"
                        )
                        if claim is None or not (
                            claim_scope == "root"
                            or claim_scope == inference_scope
                            or inference_scope.startswith(claim_scope + "/")
                        ):
                            scope_failures.append(f"{node}:{used_fvar}")
        self.add(
            "V9",
            "blocking",
            "claim_scope_consistency",
            len(proof_graphs),
            sorted(set(scope_failures)),
            not scope_failures,
        )

        env_info_failures: list[str] = []
        try:
            with sqlite3.connect(store_path) as connection:
                env_names = {
                    row[0] for row in connection.execute("SELECT name FROM declaration")
                }
                tactic_count = connection.execute(
                    "SELECT COUNT(*) FROM tactic_node"
                ).fetchone()[0]
                term_count = connection.execute(
                    "SELECT COUNT(*) FROM expr_node"
                ).fetchone()[0]
            if not env_names:
                env_info_failures.append("no_environment_declarations")
            if tactic_count + term_count == 0:
                env_info_failures.append("no_infotree_records")
        except Exception as exc:
            env_info_failures.append(str(exc))
        self.add(
            "V10",
            "blocking",
            "environment_infotree_consistency",
            len(env_names) if "env_names" in locals() else 0,
            sorted(set(env_info_failures)),
            not env_info_failures,
        )

        integrity_failures: list[str] = []
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        for rel_path, expected in manifest.get("source_files", {}).items():
            actual_path = project_root / rel_path
            if not actual_path.is_file():
                integrity_failures.append(f"{rel_path}:missing")
                continue
            actual = hashlib.sha256(actual_path.read_bytes()).hexdigest()
            if actual != expected:
                integrity_failures.append(f"{rel_path}:hash_mismatch")
        self.add(
            "V13",
            "blocking",
            "source_integrity",
            len(manifest.get("source_files", {})),
            sorted(set(integrity_failures)),
            not integrity_failures,
        )

        leak_failures: list[str] = []
        claim_failures: list[str] = []
        step_failures: list[str] = []
        reference_failures: list[str] = []
        semantic_failures: list[str] = []
        automation_failures: list[str] = []
        flow_failures: list[str] = []
        dag_path = graphs_dir / "declaration_dag.full.json"
        try:
            declaration_dag = json.loads(dag_path.read_text(encoding="utf-8"))
            declaration_ids = {node["id"] for node in declaration_dag.get("nodes", [])}
        except (OSError, json.JSONDecodeError, KeyError, TypeError):
            declaration_ids = set()
            reference_failures.append("declaration_dag.full.json:missing_or_invalid")

        output_root = graphs_dir.parent
        output_json_files = set(graphs_dir.rglob("*.json"))
        manifest_json = output_root / "run_manifest.json"
        if manifest_json.is_file():
            output_json_files.add(manifest_json)
        reports_dir = output_root / "reports"
        if reports_dir.is_dir():
            output_json_files.update(reports_dir.glob("*.json"))
        for output_file in sorted(output_json_files):
            try:
                output_data = json.loads(output_file.read_text(encoding="utf-8"))
                output_text = json.dumps(output_data, ensure_ascii=False)
                if re.search(
                    r"(?:_fvar\.[A-Za-z0-9_]+|\?m\.\d+|\bm\.\d+|_uniq\.[A-Za-z0-9_]+)",
                    output_text,
                ):
                    leak_failures.append(
                        f"{output_file.relative_to(output_root)}:internal_identifier"
                    )

                def has_string_range(value: object) -> bool:
                    if isinstance(value, dict):
                        return any(
                            (key == "range" and isinstance(child, str))
                            or has_string_range(child)
                            for key, child in value.items()
                        )
                    if isinstance(value, list):
                        return any(has_string_range(child) for child in value)
                    return False

                if has_string_range(output_data):
                    leak_failures.append(
                        f"{output_file.relative_to(output_root)}:range-string"
                    )
            except (OSError, json.JSONDecodeError):
                leak_failures.append(
                    f"{output_file.relative_to(output_root)}:invalid-json"
                )

        for proof_file in proof_files:
            try:
                data = json.loads(proof_file.read_text(encoding="utf-8"))
                nodes_by_id = {node["id"]: node for node in data["nodes"]}
                ids = set(nodes_by_id)
                refs_by_inference: dict[str, set[str]] = {}
                used_consts_by_inference: dict[str, set[str]] = {}
                used_fvars_by_inference: dict[str, set[str]] = {}
                for node in data["nodes"]:
                    if node.get("kind") == "inference":
                        if not node.get("tactic_text") or node.get("syntax_kind") in {None, ""}:
                            step_failures.append(f"{proof_file.name}:empty-step:{node['id']}")
                        if node.get("status") == "partial" and not node.get("partial_reason"):
                            step_failures.append(f"{proof_file.name}:partial-reason:{node['id']}")
                        if node.get("status") not in {"complete", "partial"}:
                            step_failures.append(f"{proof_file.name}:invalid-status:{node['id']}")
                        justification = str(node.get("justification_type", ""))
                        syntax_kind = str(node.get("syntax_kind", ""))
                        is_automation = justification.startswith("automation:")
                        if is_automation:
                            tactic = justification.partition(":")[2]
                            if not syntax_kind.lower().endswith(f".{tactic.replace('_', '')}"):
                                automation_failures.append(
                                    f"{proof_file.name}:{node['id']}:automation_mismatch"
                                )
                        if node.get("closed_by_automation") != is_automation:
                            automation_failures.append(
                                f"{proof_file.name}:{node['id']}:closed_by_automation_mismatch"
                            )
                        used_fvars_by_inference[node["id"]] = {
                            str(value) for value in node.get("used_fvars", [])
                        }
                        used_consts_by_inference[node["id"]] = {
                            str(value.get("name"))
                            for value in node.get("used_consts", [])
                            if isinstance(value, dict) and value.get("name")
                        }
                    if node.get("kind") == "claim":
                        if not node.get("statement_pretty") or not node.get("type_expr_id"):
                            claim_failures.append(f"{proof_file.name}:claim-type:{node['id']}")
                        statement = str(node.get("statement_pretty", "")).strip()
                        if (
                            ":=" in statement
                            or re.match(r"^(?:have|fun)\b", statement)
                            or "?m." in statement
                        ):
                            claim_failures.append(
                                f"{proof_file.name}:proof-term-in-claim:{node['id']}"
                            )
                for edge in data["edges"]:
                    source = nodes_by_id.get(edge.get("source"), {})
                    target = nodes_by_id.get(edge.get("target"), {})
                    if edge.get("kind") == "refs":
                        if edge.get("target") not in ids:
                            reference_failures.append(f"{proof_file.name}:{edge['target']}")
                        elif edge.get("target") not in declaration_ids:
                            reference_failures.append(
                                f"{proof_file.name}:{edge['target']}:not_in_declaration_dag"
                            )
                        if source.get("kind") == "inference":
                            refs_by_inference.setdefault(edge["source"], set()).add(
                                str(target.get("name", ""))
                            )
                    if edge.get("kind") == "premise":
                        if source.get("kind") != "claim" or target.get("kind") != "inference":
                            semantic_failures.append(f"{proof_file.name}:invalid-premise-endpoints")
                        if source.get("role") == "final_goal":
                            semantic_failures.append(f"{proof_file.name}:final-as-premise")
                    elif edge.get("kind") == "conclusion":
                        if source.get("kind") != "inference" or target.get("kind") != "claim":
                            semantic_failures.append(f"{proof_file.name}:invalid-conclusion-endpoints")
                    elif edge.get("kind") == "contains":
                        if source.get("kind") != "inference" or target.get("kind") != "inference":
                            semantic_failures.append(f"{proof_file.name}:invalid-contains-endpoints")
                    elif edge.get("kind") == "next_step":
                        if source.get("kind") != "inference" or target.get("kind") != "inference":
                            semantic_failures.append(f"{proof_file.name}:invalid-next-step-endpoints")
                    elif edge.get("kind") == "refs":
                        if source.get("kind") != "inference" or target.get("kind") != "decl":
                            semantic_failures.append(f"{proof_file.name}:invalid-ref-endpoints")

                for inference_id, expected_fvars in used_fvars_by_inference.items():
                    if nodes_by_id[inference_id].get("justification_type") == "calc":
                        continue
                    actual_fvars = {
                        edge["source"]
                        for edge in data["edges"]
                        if edge.get("kind") == "premise" and edge.get("target") == inference_id
                        and nodes_by_id.get(edge.get("source"), {}).get("kind") == "claim"
                    }
                    if expected_fvars != actual_fvars:
                        flow_failures.append(
                            f"{proof_file.name}:{inference_id}:fvar-premise-mismatch"
                        )
                    if any(
                        fvar not in ids or nodes_by_id.get(fvar, {}).get("kind") != "claim"
                        for fvar in expected_fvars
                    ):
                        flow_failures.append(f"{proof_file.name}:{inference_id}:unmapped-fvar")
                    if used_consts_by_inference.get(inference_id, set()) != refs_by_inference.get(
                        inference_id, set()
                    ):
                        flow_failures.append(
                            f"{proof_file.name}:{inference_id}:constant-ref-mismatch"
                        )

                logical_graph = nx.DiGraph()
                logical_graph.add_nodes_from(
                    node_id for node_id, node in nodes_by_id.items()
                    if node.get("kind") in {"claim", "inference"}
                )
                logical_graph.add_edges_from(
                    (edge["source"], edge["target"])
                    for edge in data["edges"]
                    if edge.get("kind") in {"premise", "conclusion"}
                    and edge.get("source") in logical_graph
                    and edge.get("target") in logical_graph
                )
                if not nx.is_directed_acyclic_graph(logical_graph):
                    semantic_failures.append(f"{proof_file.name}:logical_cycle")
            except Exception as exc:
                semantic_failures.append(f"{proof_file.name}:{exc}")
        self.add(
            "V14",
            "blocking",
            "internal_identifier_leaks",
            len(leak_failures),
            sorted(set(leak_failures)),
            not leak_failures,
        )
        self.add(
            "V15",
            "blocking",
            "proof_reference_integrity",
            len(reference_failures),
            sorted(set(reference_failures)),
            not reference_failures,
        )
        self.add(
            "V17",
            "blocking",
            "claim_completeness",
            len(claim_failures),
            sorted(set(claim_failures)),
            not claim_failures,
        )
        self.add(
            "V18",
            "blocking",
            "step_quality",
            len(step_failures),
            sorted(set(step_failures)),
            not step_failures,
        )
        self.add(
            "V19",
            "blocking",
            "proof_edge_semantics",
            len(semantic_failures),
            sorted(set(semantic_failures)),
            not semantic_failures,
        )
        self.add(
            "V22",
            "blocking",
            "automation_attribution",
            len(automation_failures),
            sorted(set(automation_failures)),
            not automation_failures,
        )
        self.add(
            "V23",
            "blocking",
            "proof_dataflow_coverage",
            len(flow_failures),
            sorted(set(flow_failures)),
            not flow_failures,
        )

        canonical_hashes: list[str] = []
        for graph_file in sorted(proof_dir.glob("*")):
            if graph_file.is_file():
                if graph_file.suffix == ".json":
                    data = json.loads(graph_file.read_text(encoding="utf-8"))
                    canonical_hashes.append(
                        hashlib.sha256(
                            json.dumps(data, sort_keys=True, ensure_ascii=False).encode()
                        ).hexdigest()
                    )
                elif graph_file.suffix in {".graphml", ".json"}:
                    canonical_hashes.append(
                        hashlib.sha256(graph_file.read_bytes()).hexdigest()
                    )
        combined = hashlib.sha256(
            "\n".join(canonical_hashes).encode("utf-8")
        ).hexdigest()
        self.add(
            "V12",
            "blocking",
            "deterministic_graph_hash",
            combined,
            [],
            bool(combined),
        )

        total_nodes = sum(graph.number_of_nodes() for graph in proof_graphs)
        complete_inferences = sum(
            1
            for graph in proof_graphs
            for _, data in graph.nodes(data=True)
            if data.get("kind") == "inference"
            and data.get("status") == "complete"
        )
        inference_count = sum(
            1
            for graph in proof_graphs
            for _, data in graph.nodes(data=True)
            if data.get("kind") == "inference"
        )
        automation_count = sum(
            1
            for graph in proof_graphs
            for _, data in graph.nodes(data=True)
            if data.get("kind") == "inference"
            and data.get("closed_by_automation")
        )
        proof_by_decl = {}
        for path in proof_files:
            proof_data = json.loads(path.read_text(encoding="utf-8"))
            proof_by_decl[proof_data.get("decl_name")] = proof_data
        comments_in_proof_range = 0
        comments_attached = 0
        for declaration in declarations:
            proof_data = proof_by_decl.get(declaration.get("name"))
            if proof_data is None:
                continue
            module = declaration.get("module", "")
            source_path = project_root / f"{module.replace('.', '/')}.lean"
            if not source_path.is_file():
                source_path = project_root / "Main.lean"
            if not source_path.is_file():
                continue
            source_text = source_path.read_text(encoding="utf-8", errors="replace")
            range_value = declaration.get("range")
            if isinstance(range_value, str):
                try:
                    range_value = json.loads(range_value)
                except json.JSONDecodeError:
                    range_value = None
            if not isinstance(range_value, dict):
                continue
            start_line = range_value.get("start", {}).get("line")
            end_line = range_value.get("end", {}).get("line")
            if not isinstance(start_line, int) or not isinstance(end_line, int):
                continue
            comments = [
                comment
                for comment in tokenize_comments(source_text)
                if start_line <= comment.start_line <= end_line
            ]
            attached_steps = [
                node
                for node in proof_data.get("nodes", [])
                if node.get("kind") == "inference" and node.get("comment")
            ]
            comments_in_proof_range += len(comments)
            for comment in comments:
                attached = any(
                    node.get("comment") == comment.text
                    and isinstance(node.get("range"), dict)
                    and (
                        node["range"].get("start", {}).get("line", 0)
                        <= comment.start_line
                        <= node["range"].get("end", {}).get("line", 0)
                        or abs(
                            node["range"].get("start", {}).get("line", 0)
                            - comment.start_line
                        )
                        <= 1
                    )
                    for node in attached_steps
                )
                comments_attached += int(attached)
        self.metrics = {
            "proof_nodes": total_nodes,
            "trace_complete_ratio": (
                complete_inferences / inference_count if inference_count else 1.0
            ),
            "automation_ratio": (
                automation_count / inference_count if inference_count else 0.0
            ),
            "proof_graph_count": len(proof_graphs),
            "comments_attached": comments_attached,
            "comments_in_proof_range": comments_in_proof_range,
            "comments_attached_ratio": (
                comments_attached / comments_in_proof_range
                if comments_in_proof_range
                else 1.0
            ),
        }
        return self.metrics

    def write(self, directory: Path) -> tuple[Path, Path]:
        directory.mkdir(parents=True, exist_ok=True)
        json_path = directory / "validation.json"
        md_path = directory / "validation.md"
        payload = {
            "project_id": self.project_id,
            "schema_version": 2,
            "metrics": getattr(self, "metrics", {}),
            "blocking_failures": sum(
                check["severity"] == "blocking" and check["status"] == "failed"
                for check in self.checks
            ),
            "checks": self.checks,
        }
        report_schema_errors = _schema_errors(
            payload,
            "validation_report.v2.json",
        )
        if report_schema_errors:
            raise ValueError(
                "Generated validation report does not match schema v2: "
                + "; ".join(report_schema_errors)
            )
        json_path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        lines = [
            f"# Validation report: {self.project_id}",
            "",
            f"Blocking failures: {payload['blocking_failures']}",
            "",
            "| ID | Severity | Metric | Status | Value | Offenders |",
            "|---|---|---|---|---|---|",
        ]
        for check in self.checks:
            offenders = ", ".join(check["offenders"]) or "-"
            lines.append(
                f"| {check['id']} | {check['severity']} | {check['metric']} | "
                f"{check['status']} | {check['value']} | {offenders} |"
            )
        md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return json_path, md_path
