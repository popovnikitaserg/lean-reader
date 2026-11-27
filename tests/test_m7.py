from pathlib import Path
import json

from lean2graph.cache.cache import ModuleCache


def test_module_cache_key_changes_with_source(tmp_path: Path) -> None:
    source = tmp_path / "Main.lean"
    exporter = tmp_path / "PassA.lean"
    source.write_text("theorem a : True := True.intro\n", encoding="utf-8")
    exporter.write_text("-- exporter\n", encoding="utf-8")
    with ModuleCache(tmp_path / "cache.sqlite") as cache:
        first = cache.key(
            source=source,
            toolchain="leanprover/lean4:v4.36.0",
            exporter=exporter,
            pass_name="pass_a",
        )
        cache.put(first, "pass_a", [{"record": "declaration", "name": "a"}])
        assert cache.get(first) == [{"record": "declaration", "name": "a"}]
        source.write_text("theorem b : True := True.intro\n", encoding="utf-8")
        second = cache.key(
            source=source,
            toolchain="leanprover/lean4:v4.36.0",
            exporter=exporter,
            pass_name="pass_a",
        )
        assert second != first
        assert cache.get(second) is None


def test_resume_manifest_shape(tmp_path: Path) -> None:
    manifest = tmp_path / "run_manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "project_id": "project-test",
                "status": "built",
                "parameters": {"resume": False},
            }
        ),
        encoding="utf-8",
    )
    data = json.loads(manifest.read_text(encoding="utf-8"))
    data["parameters"]["resume"] = True
    data["resume_hit"] = True
    manifest.write_text(json.dumps(data), encoding="utf-8")
    resumed = json.loads(manifest.read_text(encoding="utf-8"))
    assert resumed["resume_hit"] is True
