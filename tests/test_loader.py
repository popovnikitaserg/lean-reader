from pathlib import Path
import io
import shutil
import subprocess
import tarfile
import zipfile

import pytest

from lean2graph.loader.loader import LoaderError, ProjectLoader


def test_single_lean_file_loads_as_synthetic_project(tmp_path: Path) -> None:
    source = tmp_path / "Main.lean"
    source.write_text("theorem t : True := True.intro\n", encoding="utf-8")

    loaded = ProjectLoader().load(str(source))
    try:
        assert loaded.input_kind == "lean_file"
        assert (loaded.root / "Main.lean").is_file()
        loader = ProjectLoader()
        assert loader.create_synthetic_project(loaded.root)
        lakefile = (loaded.root / "lakefile.lean").read_text(encoding="utf-8")
        assert "@[default_target]" in lakefile
        assert "roots := #[`Main]" in lakefile
    finally:
        loaded.close()


def test_legacy_synthetic_project_regenerates_default_target(
    tmp_path: Path,
) -> None:
    (tmp_path / "finite_fiber.lean").write_text(
        "import Mathlib\n\ntheorem t : True := True.intro\n",
        encoding="utf-8",
    )
    (tmp_path / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\n\npackage synthetic\n\nlean_lib Synthetic\n'
        '\nrequire mathlib from git\n  "https://github.com/leanprover-community/mathlib4.git"\n',
        encoding="utf-8",
    )

    assert ProjectLoader().create_synthetic_project(tmp_path)

    lakefile = (tmp_path / "lakefile.lean").read_text(encoding="utf-8")
    assert "@[default_target]" in lakefile
    assert "roots := #[`finite_fiber]" in lakefile
    assert "require mathlib from git" in lakefile


@pytest.mark.skipif(
    shutil.which("lake") is None or shutil.which("lean") is None,
    reason="Lean and Lake are required",
)
def test_synthetic_project_builds_its_source_module(tmp_path: Path) -> None:
    source = tmp_path / "finite_fiber.lean"
    source.write_text("theorem t : True := True.intro\n", encoding="utf-8")
    loader = ProjectLoader()
    assert loader.create_synthetic_project(tmp_path)

    result = subprocess.run(
        ["lake", "build"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "Built finite_fiber" in result.stdout + result.stderr


def test_directory_project_root_and_synthetic(tmp_path: Path) -> None:
    source = tmp_path / "Nested" / "Src"
    source.mkdir(parents=True)
    (source / "Main.lean").write_text(
        "import Mathlib\n\ntheorem trivial (p : Prop) (h : p) : p := h\n",
        encoding="utf-8",
    )

    loader = ProjectLoader()
    root = loader.find_project_root(tmp_path)
    assert root == source
    assert loader.create_synthetic_project(root)
    assert (root / "lakefile.lean").is_file()
    assert "mathlib4" in (root / "lakefile.lean").read_text(encoding="utf-8")
    assert loader.project_id(root).startswith("project-")


def test_zip_slip_rejected(tmp_path: Path) -> None:
    archive = tmp_path / "bad.zip"
    with zipfile.ZipFile(archive, "w") as zf:
        zf.writestr("../../escape.lean", "theorem bad : True := True.intro\n")

    with pytest.raises(LoaderError, match="path traversal"):
        ProjectLoader().load(str(archive))


def test_zip_symlink_rejected(tmp_path: Path) -> None:
    archive = tmp_path / "link.zip"
    info = zipfile.ZipInfo("outside.lean")
    info.create_system = 3
    info.external_attr = (0o120777 & 0xFFFF) << 16
    with zipfile.ZipFile(archive, "w") as zf:
        zf.writestr(info, "/tmp/secret")

    with pytest.raises(LoaderError, match="Symbolic links"):
        ProjectLoader().load(str(archive))


def test_archive_file_limit(tmp_path: Path) -> None:
    archive = tmp_path / "many.tar"
    with tarfile.open(archive, "w") as tf:
        for index in range(3):
            data = b"theorem x : True := True.intro\n"
            member = tarfile.TarInfo(f"file_{index}.lean")
            member.size = len(data)
            tf.addfile(member, io.BytesIO(data))

    with pytest.raises(LoaderError, match="more than 2"):
        ProjectLoader(max_files=2).load(str(archive))
