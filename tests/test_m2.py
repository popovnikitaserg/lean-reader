from pathlib import Path
import json
import shutil
import sqlite3

import pytest
import networkx as nx
from jsonschema import Draft202012Validator

from lean2graph.store.sqlite_store import RawStore
from lean2graph.graphs.declaration import DeclarationDAG


def test_versioned_schemas_are_valid_and_packaged() -> None:
    schema_dir = Path(__file__).parents[1] / "docs" / "schemas"
    package_schema_dir = Path(__file__).parents[1] / "lean2graph" / "schemas"
    for name in (
        "declaration_dag.v2.json",
        "proof_claim.v2.json",
        "import_graph.v2.json",
        "validation_report.v2.json",
    ):
        documented = json.loads((schema_dir / name).read_text(encoding="utf-8"))
        packaged = json.loads((package_schema_dir / name).read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(documented)
        assert packaged == documented


def test_raw_store_declarations_and_refs(tmp_path: Path) -> None:
    store_path = tmp_path / "raw" / "facts.sqlite"
    with RawStore(store_path) as store:
        store.put_project("project-test", "built", {"project_id": "project-test"})
        decl_id = store.put_declaration(
            "project-test",
            "Main",
            {
                "name": "Main.example",
                "kind": "thm",
                "type_pretty": "True",
                "value_pretty": "True.intro",
                "range": None,
                "axioms": ["sorryAx"],
                "const_refs": [
                    {
                        "const_name": "True.intro",
                        "origin": "value",
                        "usage_kind": "applied_head",
                        "count": 1,
                    }
                ],
            },
        )
    assert decl_id == "decl:project-test:Main.example"
    connection = sqlite3.connect(store_path)
    assert connection.execute("select name, kind from declaration").fetchone() == (
        "Main.example",
        "thm",
    )
    assert connection.execute(
        "select axiom_name from decl_axiom"
    ).fetchone() == ("sorryAx",)
    connection.close()


def test_raw_store_preserves_folded_auxiliary_and_expression(tmp_path: Path) -> None:
    store_path = tmp_path / "raw" / "facts.sqlite"
    with RawStore(store_path) as store:
        store.put_declaration(
            "project-test",
            "Main",
            {
                "name": "Main.parent",
                "kind": "thm",
                "type_pretty": "True",
                "type_expr_id": "expr:project-test:Main.parent:type",
                "type_expr_raw": "Expr.const True []",
                "range": None,
            },
        )
        store.put_declaration(
            "project-test",
            "Main",
            {
                "name": "Main.parent._proof_1",
                "kind": "thm",
                "type_pretty": "True",
                "type_expr_id": "expr:project-test:Main.parent._proof_1:type",
                "type_expr_raw": "Expr.const True []",
                "range": None,
            },
        )
        claims = [
            {
                "name": "Main.parent._proof_1",
                "statement_pretty": "True",
                "type_expr_id": "expr:project-test:Main.parent._proof_1:type",
                "origin": "lean_env",
            }
        ]
        store.update_declaration_projection(
            "project-test",
            {"Main.parent._proof_1": "Main.parent"},
            {"Main.parent": claims},
        )

    with sqlite3.connect(store_path) as connection:
        auxiliary = connection.execute(
            "SELECT folded_into FROM declaration WHERE name = ?",
            ("Main.parent._proof_1",),
        ).fetchone()
        parent_claims = connection.execute(
            "SELECT aux_claims_json FROM declaration WHERE name = ?",
            ("Main.parent",),
        ).fetchone()
        expression = connection.execute(
            "SELECT payload_json FROM expr_node WHERE id = ?",
            ("expr:project-test:Main.parent:type",),
        ).fetchone()

    assert auxiliary == ("Main.parent",)
    assert json.loads(parent_claims[0]) == claims
    assert json.loads(expression[0])["raw_expression"] == "Expr.const True []"


def test_declaration_dag_write_and_graphml_roundtrip(tmp_path: Path) -> None:
    dag = DeclarationDAG("project-test")
    dag.add_project_declarations(
        [
            {
                "name": "Main.a",
                "kind": "thm",
                "module": "Main",
                "type_pretty": "Nat",
                "docstring": None,
                "range": None,
                "const_refs": [
                    {
                        "const_name": "Nat",
                        "origin": "type",
                        "usage_kind": "applied_head",
                        "kind": "inductive",
                        "module": "Init.Prelude",
                        "statement_pretty": "Type",
                        "type_expr_id": "expr:external:Nat:type",
                        "count": 1,
                    }
                ],
            }
        ],
        source_files={},
    )
    json_path, graphml_path = dag.write(tmp_path)
    data = json.loads(json_path.read_text(encoding="utf-8"))
    assert data["edge_convention"] == "dependent -> dependency"
    assert len(data["nodes"]) == 2
    loaded = nx.read_graphml(graphml_path)
    assert loaded.number_of_nodes() == 2


def test_narrative_dag_keeps_only_project_lemmas_and_definitions(tmp_path: Path) -> None:
    dag = DeclarationDAG("project-test")
    dag.add_project_declarations(
        [
            {
                "name": "Main.source",
                "kind": "thm",
                "module": "Main",
                "type_pretty": "True",
                "const_refs": [
                    {"const_name": "Main.helper", "origin": "value", "usage_kind": "applied_head"},
                    {"const_name": "Nat.log_pow", "origin": "value", "usage_kind": "applied_head", "kind": "thm"},
                    {"const_name": "Nat.pow", "origin": "value", "usage_kind": "applied_head", "kind": "defn"},
                    {"const_name": "HAdd.hAdd", "origin": "value", "usage_kind": "applied_head", "kind": "defn"},
                    {"const_name": "Lean.Omega.foo", "origin": "value", "usage_kind": "applied_head", "kind": "thm"},
                    {"const_name": "Nat", "origin": "type", "usage_kind": "applied_head", "kind": "induct"},
                ],
            },
            {
                "name": "Main.helper",
                "kind": "thm",
                "module": "Main",
                "type_pretty": "True",
                "const_refs": [],
            },
        ],
        source_files={},
    )

    full_path, _ = dag.write(tmp_path)
    full = json.loads(full_path.read_text(encoding="utf-8"))
    narrative = json.loads(
        (tmp_path / "declaration_dag.narrative.json").read_text(encoding="utf-8")
    )
    full_targets = {edge["target"] for edge in full["edges"]}
    narrative_targets = {edge["target"] for edge in narrative["edges"]}

    assert len(narrative["edges"]) < len(full["edges"])
    assert "decl:project-test:Main.helper" in narrative_targets
    assert "decl:external:Nat.log_pow" in narrative_targets
    assert "decl:external:Nat.pow" in narrative_targets
    assert "decl:external:HAdd.hAdd" not in narrative_targets
    assert "decl:external:Lean.Omega.foo" not in narrative_targets
    assert "decl:external:Nat" not in narrative_targets
    assert full_targets > narrative_targets


def test_dag_folds_auxiliaries_and_classifies_definition_and_type_edges(
    tmp_path: Path,
) -> None:
    declarations = [
        {
            "name": "Main.fiber",
            "kind": "defn",
            "module": "Main",
            "type_pretty": "Nat → Set Nat",
            "range": None,
            "const_refs": [],
        },
        {
            "name": "Main.g",
            "kind": "defn",
            "module": "Main",
            "type_pretty": "Nat → Nat",
            "range": None,
            "const_refs": [
                {
                    "const_name": "Main.fiber",
                    "origin": "body",
                    "usage_kind": "applied_head",
                    "count": 1,
                }
            ],
        },
        {
            "name": "Main.recursiveCount",
            "kind": "defn",
            "module": "Main",
            "type_pretty": "Nat → Nat",
            "range": None,
            "const_refs": [],
        },
        {
            "name": "Main.recursiveCount.eq_1",
            "kind": "thm",
            "module": "Main",
            "type_pretty": "Main.recursiveCount 0 = 0",
            "is_auxiliary": True,
            "range": None,
            "const_refs": [
                {
                    "const_name": "Nat.zero",
                    "kind": "ctor",
                    "module": "Init.Prelude",
                    "statement_pretty": "Nat",
                    "type_expr_id": "expr:Nat.zero:type",
                    "docstring": None,
                    "origin": "proof",
                    "usage_kind": "argument",
                    "count": 1,
                }
            ],
        },
        {
            "name": "Main.theorem",
            "kind": "thm",
            "module": "Main",
            "type_pretty": "Main.g n ≤ n",
            "range": None,
            "const_refs": [
                {
                    "const_name": "Main.g",
                    "kind": "defn",
                    "module": "Main",
                    "statement_pretty": "Nat → Nat",
                    "type_expr_id": "expr:Main.g:type",
                    "docstring": None,
                    "origin": "type",
                    "usage_kind": "type_level",
                    "count": 1,
                }
            ],
        },
        {
            "name": "Main.theorem._proof_1",
            "kind": "thm",
            "module": "Main",
            "type_pretty": "Main.theorem",
            "is_auxiliary": True,
            "range": None,
            "const_refs": [
                {
                    "const_name": "Nat.succ",
                    "kind": "ctor",
                    "module": "Init.Prelude",
                    "statement_pretty": "Nat → Nat",
                    "type_expr_id": "expr:Nat.succ:type",
                    "docstring": None,
                    "origin": "proof",
                    "usage_kind": "applied_head",
                    "count": 1,
                }
            ],
        },
    ]

    dag = DeclarationDAG("project-test")
    dag.add_project_declarations(
        declarations,
        source_files={},
        tactic_records=[
            {
                "module": "Main",
                "range": {"start": {"line": 2, "column": 2}},
                "syntax_kind": "Lean.Parser.Tactic.omega",
            },
            {
                "module": "Other",
                "range": {"start": {"line": 2, "column": 2}},
                "syntax_kind": "Lean.Parser.Tactic.ring",
            },
        ],
    )
    full_path, _ = dag.write(tmp_path)
    full = json.loads(full_path.read_text(encoding="utf-8"))
    nodes = {node["id"]: node for node in full["nodes"]}
    edges = full["edges"]
    edge_types = {
        (edge["source"], edge["target"]): edge
        for edge in edges
    }

    assert full["profile"] == "full"
    assert (tmp_path / "declaration_dag.full.json").read_text(encoding="utf-8") == full_path.read_text(encoding="utf-8")
    assert "decl:project-test:Main.recursiveCount.eq_1" not in nodes
    assert "decl:project-test:Main.theorem._proof_1" not in nodes
    assert nodes["decl:project-test:Main.theorem"]["aux_claims"]
    assert nodes["decl:project-test:Main.theorem"]["automation_summary"] == {"omega": True}
    assert edge_types[
        ("decl:project-test:Main.g", "decl:project-test:Main.fiber")
    ]["type"] == "body_uses"
    assert edge_types[
        ("decl:project-test:Main.theorem", "decl:project-test:Main.g")
    ]["type"] == "type_uses"
    assert edge_types[
        ("decl:project-test:Main.theorem", "decl:external:Nat.succ")
    ]["evidence"] == "via_aux:Main.theorem._proof_1"
    assert edge_types[
        ("decl:project-test:Main.recursiveCount", "decl:external:Nat.zero")
    ]["evidence"] == "via_aux:Main.recursiveCount.eq_1"
    assert nodes["decl:external:Nat.zero"]["kind"] == "ctor"
    assert nodes["decl:external:Nat.zero"]["module"] == "Init.Prelude"
    assert nodes["decl:external:Nat.zero"]["statement_pretty"] == "Nat"
    assert nodes["decl:external:Nat.zero"]["type_expr_id"] == "expr:Nat.zero:type"

    keep_aux = DeclarationDAG("project-test", keep_aux=True)
    keep_aux.add_project_declarations(declarations, source_files={})
    keep_path, _ = keep_aux.write(tmp_path / "keep-aux")
    keep = json.loads(keep_path.read_text(encoding="utf-8"))
    keep_nodes = {node["id"]: node for node in keep["nodes"]}
    assert "decl:project-test:Main.theorem._proof_1" in keep_nodes
    assert keep_nodes["decl:project-test:Main.theorem"]["aux_claims"]
    assert "decl:project-test:Main.theorem._proof_1" in {
        node["id"] for node in keep["nodes"]
    }


@pytest.mark.skipif(shutil.which("lean") is None or shutil.which("lake") is None,
                    reason="Lean toolchain is not available")
def test_pass_a_exporter_fixture(tmp_path: Path) -> None:
    fixture = Path(__file__).parent / "fixtures" / "m0_have_exact"
    from lean2graph.extract.pass_a import PassAExtractor
    store_path = tmp_path / "facts.sqlite"
    exporter = Path(__file__).parents[1] / "lean2graph" / "lean_exporter" / "PassA.lean"
    with RawStore(store_path) as store:
        records = PassAExtractor(exporter).run(
            root=fixture,
            project_id="project-spike",
            store=store,
            timeout_seconds=300,
        )
    names = {record["name"] for record in records}
    assert "have_exact" in names
    theorem = next(record for record in records if record["name"] == "have_exact")
    assert theorem["range"] is not None
    assert theorem["range_origin"] == "lean"
    assert theorem["name_range"] is not None
    assert theorem["range"]["start"]["line"] <= theorem["name_range"]["start"]["line"]
    assert theorem["type_expr_id"]
    assert theorem["const_refs"]
    assert [item["name"] for item in theorem["statement_context"]["variables"]] == ["p", "q"]
    assert [item["name"] for item in theorem["statement_context"]["assumptions"]] == ["hp", "hq"]
    assert theorem["statement_context"]["goal_pretty"] == "p ∧ q"
    assert all(ref["kind"] and ref["statement_pretty"] for ref in theorem["const_refs"])
    assert all(
        ref["type_expr_id"]
        and ref["type_expr_raw"]
        and "is_class" in ref
        and "is_projection" in ref
        and "is_auto_generated" in ref
        for ref in theorem["const_refs"]
    )
    with sqlite3.connect(store_path) as connection:
        type_payload = connection.execute(
            "SELECT payload_json FROM expr_node WHERE id = ?",
            (theorem["type_expr_id"],),
        ).fetchone()
    assert type_payload is not None
    assert json.loads(type_payload[0])["raw_expression"]
    with sqlite3.connect(store_path) as connection:
        context_json = connection.execute(
            "SELECT statement_context_json FROM declaration WHERE name = ?",
            ("have_exact",),
        ).fetchone()[0]
    assert json.loads(context_json)["goal_pretty"] == "p ∧ q"
