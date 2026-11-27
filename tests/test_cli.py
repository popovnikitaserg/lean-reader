from pathlib import Path
import json
import shutil
import sqlite3

import pytest
from typer.testing import CliRunner

from lean2graph.cli import _cache_workspace, _legacy_workspace, _write_manifest
from lean2graph.cli import app
from lean2graph.build.build import BuildResult
from lean2graph.loader.loader import LoadedInput
from lean2graph.store.sqlite_store import RawStore


def test_write_manifest(tmp_path: Path) -> None:
    project = tmp_path / "project"
    project.mkdir()
    (project / "Main.lean").write_text("theorem t : True := True.intro\n", encoding="utf-8")
    loaded = LoadedInput(project, "directory", str(project))
    result = BuildResult(
        "build_failed",
        "leanprover/lean4:v4.36.0",
        [],
        "exit_code=1",
        True,
        False,
    )
    manifest = _write_manifest(
        tmp_path / "out",
        loaded,
        result,
        "project-test",
        {"scope": "project", "jobs": 1},
    )
    data = json.loads(manifest.read_text(encoding="utf-8"))
    assert data["project_id"] == "project-test"
    assert data["status"] == "build_failed"
    assert data["source_files"]["Main.lean"]
    assert (manifest.parent / "reports" / "build.log").is_file()


def test_cache_workspace_preserves_lake_downloads(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "Main.lean").write_text("import Mathlib\n", encoding="utf-8")
    cache_dir = tmp_path / "cache"

    workspace = _cache_workspace(source, cache_dir, "project-test")
    lakefile = workspace / ".lake" / "packages" / "mathlib" / "download.marker"
    lakefile.parent.mkdir(parents=True)
    lakefile.write_text("cached", encoding="utf-8")

    second_workspace = _cache_workspace(source, cache_dir, "project-test")

    assert second_workspace == workspace
    assert lakefile.read_text(encoding="utf-8") == "cached"


def test_legacy_workspace_can_be_reused_after_changing_output_dir(tmp_path: Path) -> None:
    old_out = tmp_path / "out" / "old"
    new_out = tmp_path / "out" / "new"
    old_workspace = old_out / ".lean-projects" / "project-test"
    old_workspace.mkdir(parents=True)

    assert _legacy_workspace(new_out, "project-test") == old_workspace


def test_legacy_workspace_skips_inaccessible_siblings(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    out = tmp_path / "out"
    inaccessible = tmp_path / "aaa-inaccessible" / ".lean-projects" / "project-test"
    inaccessible.mkdir(parents=True)
    old_workspace = tmp_path / "old-out" / ".lean-projects" / "project-test"
    old_workspace.mkdir(parents=True)
    original_is_dir = Path.is_dir

    def is_dir(path: Path) -> bool:
        if path == inaccessible:
            raise PermissionError("test-only inaccessible directory")
        return original_is_dir(path)

    monkeypatch.setattr(Path, "is_dir", is_dir)

    assert _legacy_workspace(out, "project-test") == old_workspace


def test_validate_reports_v1_graph_needs_rebuild(tmp_path: Path) -> None:
    project_dir = tmp_path / "project-test"
    graphs_dir = project_dir / "graphs"
    reports_dir = project_dir / "reports"
    graphs_dir.mkdir(parents=True)
    reports_dir.mkdir()
    (project_dir / "run_manifest.json").write_text(
        json.dumps({"project_id": "project-test", "status": "built"}),
        encoding="utf-8",
    )
    (graphs_dir / "declaration_dag.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "directed": True,
                "project_id": "project-test",
                "edge_convention": "dependent -> dependency",
                "nodes": [],
                "edges": [],
            }
        ),
        encoding="utf-8",
    )
    (reports_dir / "validation.json").write_text(
        json.dumps(
            {
                "project_id": "project-test",
                "schema_version": 2,
                "metrics": {},
                "blocking_failures": 0,
                "checks": [],
            }
        ),
        encoding="utf-8",
    )

    result = CliRunner().invoke(app, ["validate", str(tmp_path)])

    assert result.exit_code == 1
    assert "schema v1 is not supported" in result.output
    assert "run analyze to rebuild schema v2" in result.output


def test_inspect_renders_nested_outline_and_source(tmp_path: Path) -> None:
    project_dir = tmp_path / "project"
    proof_dir = project_dir / "graphs" / "proofs"
    source_dir = project_dir / "source"
    proof_dir.mkdir(parents=True)
    source_dir.mkdir()
    (source_dir / "Main.lean").write_text(
        "theorem t (h : True) : True := by\n"
        "  have h1 : True := by\n"
        "    trivial\n"
        "  exact h1\n",
        encoding="utf-8",
    )
    with RawStore(project_dir / "raw" / "facts.sqlite") as store:
        store.put_declaration(
            "project-test",
            "Main",
            {"name": "t", "kind": "thm", "type_pretty": "True", "range": None},
        )
    proof = {
        "directed": True,
        "project_id": "project-test",
        "decl_name": "t",
        "schema_version": 2,
        "nodes": [
            {
                "id": "final",
                "kind": "claim",
                "role": "final_goal",
                "user_name": "",
                "statement_pretty": "True",
                "type_expr_id": "expr:final",
            },
            {
                "id": "h1",
                "kind": "claim",
                "role": "intermediate",
                "user_name": "h1",
                "statement_pretty": "True",
                "type_expr_id": "expr:h1",
            },
            {
                "id": "have",
                "kind": "inference",
                "tactic_text": "have h1 : True := by trivial",
                "justification_type": "claim_introduction",
                "range": {
                    "start": {"line": 2, "column": 2},
                    "end": {"line": 3, "column": 12},
                },
                "ordinal": 1,
                "depth": 1,
                "used_consts": [],
            },
            {
                "id": "trivial",
                "kind": "inference",
                "tactic_text": "trivial",
                "justification_type": "other",
                "parent_inference": "have",
                "range": {
                    "start": {"line": 3, "column": 4},
                    "end": {"line": 3, "column": 12},
                },
                "ordinal": 1,
                "depth": 2,
                "used_consts": [],
            },
            {
                "id": "exact",
                "kind": "inference",
                "tactic_text": "exact h1",
                "justification_type": "lemma_application",
                "range": {
                    "start": {"line": 4, "column": 2},
                    "end": {"line": 4, "column": 10},
                },
                "ordinal": 2,
                "depth": 1,
                "used_consts": [],
            },
        ],
        "edges": [
            {"source": "have", "target": "h1", "kind": "conclusion"},
            {"source": "have", "target": "trivial", "kind": "contains"},
            {"source": "h1", "target": "exact", "kind": "premise"},
            {"source": "exact", "target": "final", "kind": "conclusion"},
        ],
    }
    (proof_dir / "t.json").write_text(json.dumps(proof), encoding="utf-8")

    result = CliRunner().invoke(app, ["inspect", str(project_dir), "t"])

    assert result.exit_code == 0, result.output
    assert "theorem t" in result.output
    assert "[claim h1: True]" in result.output
    assert "have h1 : True := by" in result.output
    assert "trivial" in result.output
    assert "exact h1" in result.output
    assert result.output.index("trivial") < result.output.index("exact h1")


@pytest.mark.skipif(
    shutil.which("lake") is None or shutil.which("lean") is None,
    reason="Lean and Lake are required",
)
def test_core_fixture_v2_regressions(tmp_path: Path) -> None:
    fixture = Path(__file__).parent / "fixtures" / "m0_have_exact"
    result = CliRunner().invoke(
        app,
        [
            "analyze",
            str(fixture),
            "--out",
            str(tmp_path / "out"),
            "--required-free-gb",
            "0",
            "--only-module",
            "Main",
        ],
    )
    assert result.exit_code == 0, result.output
    project_dir = next((tmp_path / "out").glob("project-*"))
    graphs_dir = project_dir / "graphs"
    dag = json.loads((graphs_dir / "declaration_dag.full.json").read_text(encoding="utf-8"))
    dag_edges = dag["edges"]
    assert any(
        edge["source"].endswith(":shifted_type_uses_example")
        and edge["target"].endswith(":shifted")
        and edge["type"] == "type_uses"
        for edge in dag_edges
    )
    with sqlite3.connect(project_dir / "raw" / "facts.sqlite") as connection:
        folded = connection.execute(
            "SELECT folded_into FROM declaration WHERE name = 'shifted.eq_1'"
        ).fetchone()
    assert folded and folded[0] == "shifted"
    assert not any(node["name"].endswith(".eq_1") for node in dag["nodes"])

    def graph_for(name: str) -> dict:
        path = graphs_dir / "proofs" / f"{name}.json"
        return json.loads(path.read_text(encoding="utf-8"))

    rewrite = graph_for("rw_chain_example")
    rewrite_steps = [node for node in rewrite["nodes"] if node.get("kind") == "inference"]
    rewrite_nodes = [node for node in rewrite_steps if node.get("justification_type") == "rewrite"]
    assert len(rewrite_nodes) == 1
    assert rewrite_nodes[0]["rewrites"] == [
        {"lemma": "h", "direction": "forward"},
        {"lemma": "Nat.zero_add", "direction": "forward"},
    ]

    calc = graph_for("calc_mixed_example")
    calc_steps = [
        node for node in calc["nodes"]
        if node.get("kind") == "inference" and node.get("syntax_kind") == "Lean.calcStep"
    ]
    assert len(calc_steps) == 3

    nested = graph_for("nested_have_example")
    assert any(edge.get("kind") == "contains" for edge in nested["edges"])
    cases = graph_for("cases_example")
    branch_scopes = {
        node.get("scope_id")
        for node in cases["nodes"]
        if node.get("kind") == "inference"
    }
    assert "root/case:inl" in branch_scopes
    assert "root/case:inr" in branch_scopes

    comments = graph_for("comment_example")
    assert any(node.get("comment") for node in comments["nodes"])
    anonymous = graph_for("anonymous_intro_example")
    assert any(node.get("inaccessible_name") for node in anonymous["nodes"])
    validation = json.loads(
        (project_dir / "reports" / "validation.json").read_text(encoding="utf-8")
    )
    assert validation["blocking_failures"] == 0


@pytest.mark.skipif(
    shutil.which("lake") is None or shutil.which("lean") is None,
    reason="Lean and Lake are required",
)
def test_analyze_single_file_with_relative_output_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = tmp_path / "Main.lean"
    source.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    result = CliRunner().invoke(
        app,
        [
            "analyze",
            str(source),
            "--out",
            "out",
            "--required-free-gb",
            "0",
        ],
    )

    assert result.exit_code == 0, result.output
    project_dir = next(Path("out").glob("project-*"))
    errors = (project_dir / "reports" / "errors.jsonl").read_text(encoding="utf-8")
    declarations = json.loads(
        (project_dir / "graphs" / "declaration_dag.json").read_text(encoding="utf-8")
    )
    proof_graphs = list((project_dir / "graphs" / "proofs").glob("*.json"))
    assert "no such file or directory" not in errors
    assert declarations["nodes"]
    assert proof_graphs
