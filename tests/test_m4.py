import json
import sqlite3
from pathlib import Path

from lean2graph.normalize.trace import TraceMatcher
from lean2graph.store.sqlite_store import RawStore
from lean2graph.validate.validation import ValidationReport


def test_live_dead_and_coverage(tmp_path: Path) -> None:
    store_path = tmp_path / "facts.sqlite"
    with RawStore(store_path) as store:
        store.put_declaration(
            "project-test",
            "Main",
            {
                "name": "Main.result",
                "kind": "thm",
                "type_pretty": "True",
                "value_pretty": "And.intro h h",
                "range": None,
            },
        )
        store.put_tactic(
            "project-test",
            "Main",
            {
                "ordinal": 1,
                "synthetic_syntax": False,
                "goals_before": ["_uniq.1"],
                "goals_after": [],
                "assignments": [
                    {
                        "mvar_id": "_uniq.1",
                        "kind": "direct",
                        "expr_pretty": "And.intro h h",
                    }
                ],
            },
        )
        store.put_tactic(
            "project-test",
            "Main",
            {
                "ordinal": 2,
                "synthetic_syntax": True,
                "goals_before": ["_uniq.2"],
                "goals_after": [],
                "assignments": [
                    {
                        "mvar_id": "_uniq.2",
                        "kind": "direct",
                        "expr_pretty": "h",
                    }
                ],
            },
        )
        store.put_tactic(
            "project-test",
            "Main",
            {
                "ordinal": 3,
                "synthetic_syntax": False,
                "goals_before": ["_uniq.3"],
                "goals_after": ["_uniq.4"],
                "assignments": [
                    {
                        "mvar_id": "_uniq.3",
                        "kind": "delayed",
                        "expr_pretty": None,
                    }
                ],
            },
        )

    with TraceMatcher(store_path) as matcher:
        result = matcher.match_all()

    assert result.live_count == 1
    assert result.dead_count == 1
    assert result.partial_count == 1
    assert result.coverage == 1.0

    connection = sqlite3.connect(store_path)
    step_payload = json.loads(
        connection.execute(
            "SELECT payload_json FROM step WHERE id LIKE '%:1'"
        ).fetchone()[0]
    )
    assert step_payload["status"] == "complete"
    assert step_payload["live"] is True
    connection.close()


def test_validation_m4(tmp_path: Path) -> None:
    report = ValidationReport("project-test")
    report.validate_m4(
        type(
            "Trace",
            (),
            {
                "live_count": 2,
                "dead_count": 1,
                "partial_count": 0,
                "coverage": 0.75,
                "mismatches": ["missingConst"],
            },
        )()
    )
    assert any(check["id"] == "V6" for check in report.checks)
    assert any(check["id"] == "V7" for check in report.checks)
