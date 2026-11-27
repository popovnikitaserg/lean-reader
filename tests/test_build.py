from pathlib import Path
import json

from lean2graph.build.build import ProjectBuilder
from lean2graph.models import ProjectRun


def test_read_toolchain_and_lake_manifest(tmp_path: Path) -> None:
    (tmp_path / "lean-toolchain").write_text(
        "leanprover/lean4:v4.36.0\n",
        encoding="utf-8",
    )
    (tmp_path / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packages": [
                    {
                        "name": "mathlib",
                        "rev": "abc123",
                        "source": {"type": "git", "url": "https://example.invalid/mathlib"},
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    builder = ProjectBuilder(sandbox="none")
    assert builder.read_toolchain(tmp_path) == "leanprover/lean4:v4.36.0"
    dependencies = builder.read_dependencies(tmp_path)
    assert dependencies == [
        {
            "name": "mathlib",
            "source": "git",
            "url": "https://example.invalid/mathlib",
            "rev": "abc123",
        }
    ]


def test_successful_empty_lake_build_is_not_built(
    tmp_path: Path,
    monkeypatch,
) -> None:
    builder = ProjectBuilder(sandbox="none")
    monkeypatch.setattr(builder, "ensure_toolchain", lambda _toolchain: (True, "Lean 4"))
    monkeypatch.setattr(
        builder,
        "_run",
        lambda _root, _command: (
            "warning: no targets specified and no default targets configured\n"
            "Nothing to build.\nexit_code=0"
        ),
    )

    result = builder.build(
        tmp_path,
        synthetic=True,
        project_id="project-empty",
    )

    assert result.status == "build_failed"


def test_project_run_model() -> None:
    run = ProjectRun(
        project_id="project-test",
        input_kind="directory",
        source="/tmp/project",
        root=Path("/tmp/project"),
        synthetic=False,
        toolchain="leanprover/lean4:v4.36.0",
        dependencies=[],
        status="pending",
    )
    assert run.project_id == "project-test"
