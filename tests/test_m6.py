from pathlib import Path
import json
import sqlite3

import networkx as nx

from lean2graph.store.sqlite_store import RawStore
from lean2graph.validate.validation import ValidationReport


def test_m6_validation_source_integrity_axioms_and_metrics(tmp_path: Path) -> None:
    root = tmp_path / "project"
    root.mkdir()
    source = root / "Main.lean"
    source.write_text("theorem t : True := True.intro\n", encoding="utf-8")
    manifest_path = tmp_path / "run_manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "source_files": {
                    "Main.lean": __import__("hashlib").sha256(source.read_bytes()).hexdigest()
                }
            }
        ),
        encoding="utf-8",
    )

    store_path = tmp_path / "facts.sqlite"
    with RawStore(store_path) as store:
        store.put_declaration(
            "project-test",
            "Main",
            {
                "name": "t",
                "kind": "thm",
                "type_pretty": "True",
                "value_pretty": "True.intro",
                "range": None,
            },
        )

    proof_dir = tmp_path / "proofs"
    proof_dir.mkdir()
    proof = {
        "directed": True,
        "project_id": "project-test",
        "decl_name": "t",
        "schema_version": "1",
        "nodes": [
            {"id": "claim:t:final", "kind": "claim", "role": "final_goal", "scope_id": "root"},
            {"id": "claim:t:hyp", "kind": "claim", "role": "hypothesis", "scope_id": "root"},
            {
                "id": "inference:t:1",
                "kind": "inference",
                "status": "complete",
                "scope_id": "root",
                "used_fvars": [],
                "closed_by_automation": False,
            },
        ],
        "edges": [
            {"source": "claim:t:hyp", "target": "inference:t:1", "kind": "premise"},
            {"source": "inference:t:1", "target": "claim:t:final", "kind": "conclusion"},
        ],
    }
    (proof_dir / "t.json").write_text(json.dumps(proof), encoding="utf-8")

    report = ValidationReport("project-test")
    metrics = report.validate_m6(
        strict=True,
        declarations=[
            {
                "name": "t",
                "kind": "thm",
                "axioms": [],
                "is_unsafe": False,
                "value_pretty": "True.intro",
            }
        ],
        build_log="",
        store_path=store_path,
        manifest_path=manifest_path,
        project_root=root,
        proof_dir=proof_dir,
        graphs_dir=tmp_path / "graphs",
    )
    assert metrics["proof_graph_count"] == 1
    assert not any(
        check["id"] == "V2" and check["status"] == "failed"
        for check in report.checks
    )
    assert any(
        check["id"] == "V16" and check["status"] == "failed"
        for check in report.checks
    )


def test_dag_range_and_external_metadata_validation(tmp_path: Path) -> None:
    source = tmp_path / "Main.lean"
    source.write_text("def first := 1\ndef second := first\n", encoding="utf-8")
    dag = nx.MultiDiGraph()
    dag.add_node("decl:project:first", project=True)
    dag.add_node("decl:external:Nat", project=False)
    dag.add_edge("decl:project:first", "decl:external:Nat")
    report = ValidationReport("project-test")

    report.validate_dag_metadata(
        declarations=[
            {
                "name": "first",
                "module": "Main",
                "kind": "def",
                "range": {
                    "start": {"line": 1, "column": 0},
                    "end": {"line": 2, "column": 4},
                },
                "name_range": {
                    "start": {"line": 1, "column": 4},
                    "end": {"line": 1, "column": 9},
                },
            },
            {
                "name": "second",
                "module": "Main",
                "kind": "def",
                "range": {
                    "start": {"line": 2, "column": 0},
                    "end": {"line": 2, "column": 22},
                },
                "name_range": None,
            },
        ],
        dag=dag,
        project_root=tmp_path,
    )

    by_id = {check["id"]: check for check in report.checks}
    assert by_id["V20"]["status"] == "failed"
    assert any("overlaps" in offender for offender in by_id["V20"]["offenders"])
    assert by_id["V21"]["status"] == "failed"
    assert "decl:external:Nat:statement_pretty" in by_id["V21"]["offenders"]
