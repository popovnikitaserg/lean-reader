from pathlib import Path
import shutil
import sqlite3

import pytest

from lean2graph.store.sqlite_store import RawStore
from lean2graph.extract.pass_b import PassBExtractor


def test_store_raw_tactic_and_partial_assignment(tmp_path: Path) -> None:
    path = tmp_path / "facts.sqlite"
    with RawStore(path) as store:
        store.put_tactic(
            "project-test",
            "Main",
            {
                "ordinal": 3,
                "syntax_kind": "Lean.Parser.Tactic.simp",
                "tactic_text": "simp [h]",
                "range": {"start": {"line": 1, "column": 0}},
                "synthetic_syntax": False,
                "goals_before": [
                    {
                        "mvar_id": "_uniq.1",
                        "target_pretty": "p",
                        "target_expr_id": "expr:test:goal",
                        "target_expr_raw": "raw goal",
                        "locals": [],
                    }
                ],
                "goals_after": [],
                "assignments": [
                    {
                        "mvar_id": "_uniq.1",
                        "kind": "direct",
                        "expr_pretty": "h",
                        "expr_id": "expr:test:proof",
                        "expr_raw": "raw proof",
                    }
                ],
            },
        )
    connection = sqlite3.connect(path)
    assert connection.execute("select count(*) from tactic_node").fetchone()[0] == 1
    assert connection.execute("select count(*) from mvar_assignment").fetchone()[0] == 1
    assert connection.execute("select count(*) from step").fetchone()[0] == 1
    assert connection.execute("select count(*) from expr_node").fetchone()[0] == 2
    connection.close()


@pytest.mark.skipif(
    shutil.which("lean") is None or shutil.which("lake") is None,
    reason="Lean toolchain is not available",
)
def test_pass_b_fixture(tmp_path: Path) -> None:
    root = Path(__file__).parent / "fixtures" / "m0_have_exact"
    exporter = Path(__file__).parents[1] / "lean2graph" / "lean_exporter" / "PassB.lean"
    with RawStore(tmp_path / "facts.sqlite") as store:
        counts = PassBExtractor(exporter).run(
            root=root,
            project_id="project-spike",
            store=store,
            timeout_seconds=300,
        )
    assert counts["tactic"] > 0
    assert counts["term"] > 0
    assert counts["macro"] > 0
