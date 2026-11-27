from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sqlite3
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Annotated

import typer

from lean2graph.build.build import ProjectBuilder
from lean2graph.loader.loader import LoaderError, ProjectLoader
from lean2graph.store.sqlite_store import RawStore
from lean2graph.extract.pass_a import PassAExtractor
from lean2graph.extract.pass_b import PassBExtractor
from lean2graph.normalize.trace import TraceMatcher
from lean2graph.graphs.proof_claim import ProofClaimGraph
from lean2graph.source.comments import tokenize_comments
from lean2graph.graphs.declaration import DeclarationDAG, _target_role, write_import_graph
from lean2graph.validate.validation import (
    ValidationReport,
    validate_graph_outputs,
    validate_report_file,
)
from lean2graph.cache.cache import ModuleCache
from lean2graph.logging_utils import configure_logging, log_event


app = typer.Typer(add_completion=False, no_args_is_help=True)


def _default_cache_dir() -> Path:
    configured = os.environ.get("LEAN2GRAPH_CACHE_DIR")
    if configured:
        return Path(configured).expanduser()
    xdg_cache = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return xdg_cache / "lean2graph"


def _cache_workspace(source: Path, cache_dir: Path, project_id: str) -> Path:
    workspace = cache_dir / "workspaces" / project_id
    workspace.mkdir(parents=True, exist_ok=True)
    shutil.copytree(
        source,
        workspace,
        dirs_exist_ok=True,
        ignore=shutil.ignore_patterns(".git", ".lake", "__pycache__"),
    )
    return workspace


def _legacy_workspace(out: Path, project_id: str) -> Path | None:
    candidates = [out / ".lean-projects" / project_id]
    try:
        candidates.extend(
            sibling / ".lean-projects" / project_id
            for sibling in sorted(out.parent.iterdir())
            if sibling != out and sibling.is_dir()
        )
    except OSError:
        return None
    for candidate in candidates:
        try:
            if candidate.is_dir():
                return candidate
        except OSError:
            continue
    return None


def _write_manifest(out: Path, loaded, result, project_id: str, params: dict) -> Path:
    project_dir = out / project_id
    project_dir.mkdir(parents=True, exist_ok=True)
    source_files: dict[str, str] = {}
    for path in sorted(p for p in loaded.root.rglob("*") if p.is_file()):
        if any(part in {".lake", ".git", "__pycache__"} for part in path.parts):
            continue
        try:
            source_files[path.relative_to(loaded.root).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
        except OSError:
            continue
    manifest = {
        "schema_version": 2,
        "project_id": project_id,
        "input_kind": loaded.input_kind,
        "source": loaded.source,
        "root": str(loaded.root),
        "synthetic": result.synthetic,
        "toolchain": result.toolchain,
        "matched_toolchain": result.matched_toolchain,
        "dependencies": result.dependencies,
        "status": result.status,
        "parameters": params,
        "source_files": source_files,
    }
    manifest_path = project_dir / "run_manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (project_dir / "reports").mkdir(parents=True, exist_ok=True)
    (project_dir / "reports" / "build.log").write_text(result.log, encoding="utf-8")
    (project_dir / "reports" / "errors.jsonl").touch(exist_ok=True)
    return manifest_path


def _analyze_one(
    input_value: str,
    out: Path,
    scope: str,
    jobs: int,
    timeout_module: int,
    timeout_decl: int,
    strict: bool,
    sandbox: str | None,
    resume: bool,
    only_module: str | None,
    only_decl: str | None,
    rev: str | None = None,
    max_archive_bytes: int = 2 * 1024**3,
    max_files: int = 100_000,
    verbose: bool = False,
    log_file: str | None = None,
    required_free_gb: float = 10.0,
    mathlib_cache: str = "none",
    cache_dir: Path | None = None,
    keep_aux: bool = False,
) -> Path:
    cache_root = (cache_dir or _default_cache_dir()).expanduser().resolve()
    cache_root.mkdir(parents=True, exist_ok=True)
    configure_logging(
        log_file=Path(log_file) if log_file else None,
        verbose=verbose,
    )
    log_event("analyze_start", input=input_value, out=str(out), scope=scope)
    loader = ProjectLoader(
        max_archive_bytes=max_archive_bytes,
        max_files=max_files,
    )
    loaded = loader.load(input_value, rev)
    log_event(
        "input_loaded",
        input_kind=loaded.input_kind,
        source=loaded.source,
        root=str(loaded.root),
    )
    try:
        out.mkdir(parents=True, exist_ok=True)
        disk = shutil.disk_usage(str(out))
        available_gb = disk.free / (1024**3)
        log_event(
            "disk_preflight",
            available_gb=round(available_gb, 2),
            required_gb=required_free_gb,
        )
        if available_gb < required_free_gb:
            raise LoaderError(
                f"Insufficient free disk space: {available_gb:.1f} GB available, "
                f"{required_free_gb:.1f} GB required"
            )
        if loaded.input_kind == "lean_file":
            source_path = Path(loaded.source)
            source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()[:16]
            project_id = f"project-{source_hash}"
            workspace = (cache_root / "workspaces" / project_id).resolve()
            workspace.mkdir(parents=True, exist_ok=True)
            legacy_workspace = _legacy_workspace(out, project_id)
            if not any(workspace.iterdir()) and legacy_workspace:
                shutil.copytree(legacy_workspace, workspace, dirs_exist_ok=True)
            target = workspace / source_path.name
            shutil.copy2(source_path, target)
            loaded.root = workspace
            log_event(
                "lean_file_workspace_reused",
                project_id=project_id,
                workspace=str(workspace),
            )
        synthetic = loader.create_synthetic_project(loaded.root)
        log_event("project_root_ready", root=str(loaded.root), synthetic=synthetic)
        if synthetic:
            lean_sources = "\n".join(
                path.read_text(encoding="utf-8", errors="replace")
                for path in loaded.root.rglob("*.lean")
                if ".lake" not in path.parts
            )
            if "import Mathlib" in lean_sources:
                log_event(
                    "synthetic_mathlib_dependency",
                    detail="Lake must fetch and materialize Mathlib; this can take a long time",
                )
        if loaded.input_kind != "lean_file":
            project_id = loader.project_id(loaded.root)
            if loaded.cleanup:
                loaded.root = _cache_workspace(loaded.root, cache_root, project_id)
        log_event("project_id", project_id=project_id)
        effective_sandbox = sandbox
        if effective_sandbox is None:
            effective_sandbox = "docker" if loaded.input_kind in {"archive", "git"} else "none"
        project_dir = out / project_id
        project_dir.mkdir(parents=True, exist_ok=True)
        (project_dir / "reports").mkdir(parents=True, exist_ok=True)
        configure_logging(
            log_file=project_dir / "reports" / "execution.log",
            extra_log_file=Path(log_file) if log_file else None,
            verbose=verbose,
        )
        log_event("project_directory_ready", project_id=project_id, path=str(project_dir))
        builder = ProjectBuilder(
            sandbox=effective_sandbox,
            timeout_seconds=timeout_module,
        )
        log_event("build_start", sandbox=effective_sandbox)
        result = builder.build(
            loaded.root,
            synthetic=synthetic,
            project_id=project_id,
            mathlib_cache=mathlib_cache,
        )
        log_event(
            "build_complete",
            status=result.status,
            toolchain=result.toolchain,
            matched_toolchain=result.matched_toolchain,
        )
        manifest = _write_manifest(
            out,
            loaded,
            result,
            project_id,
            {
                "scope": scope,
                "jobs": jobs,
                "timeout_module": timeout_module,
                "timeout_decl": timeout_decl,
                "strict": strict,
                "sandbox": effective_sandbox,
                "resume": resume,
                "only_module": only_module,
                "only_decl": only_decl,
                "schema_version": 2,
                "cache_dir": str(cache_root),
                "keep_aux": keep_aux,
            },
        )
        existing_manifest = project_dir / "run_manifest.json"
        if resume and existing_manifest.is_file():
            try:
                existing = json.loads(existing_manifest.read_text(encoding="utf-8"))
                if existing.get("status") == "built" and not only_module and not only_decl:
                    existing["parameters"]["resume"] = True
                    existing["resume_hit"] = True
                    existing_manifest.write_text(
                        json.dumps(existing, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8",
                    )
                    typer.echo(f"{project_id}\tresume-hit\t{existing_manifest}")
                    return existing_manifest
            except json.JSONDecodeError:
                pass
        if result.status == "built":
            cache_hits: list[str] = []
            with RawStore(project_dir / "raw" / "facts.sqlite") as store:
                store.put_project(project_id, result.status, json.loads(manifest.read_text()))
                exporter = Path(__file__).resolve().parent / "lean_exporter" / "PassA.lean"
                cache_store = ModuleCache(cache_root / "module-cache.sqlite")
                try:
                    declarations = PassAExtractor(exporter).run(
                        root=loaded.root,
                        project_id=project_id,
                        store=store,
                        timeout_seconds=timeout_module,
                        cache=cache_store,
                        toolchain=result.toolchain,
                        resume=resume,
                        cache_hits=cache_hits,
                        only_module=only_module,
                        only_decl=only_decl,
                    )
                finally:
                    cache_store.close()
                pass_b_exporter = Path(__file__).resolve().parent / "lean_exporter" / "PassB.lean"
                cache_store = ModuleCache(cache_root / "module-cache.sqlite")
                try:
                    PassBExtractor(pass_b_exporter).run(
                        root=loaded.root,
                        project_id=project_id,
                        store=store,
                        timeout_seconds=timeout_module,
                        cache=cache_store,
                        toolchain=result.toolchain,
                        resume=resume,
                        cache_hits=cache_hits,
                        only_module=only_module,
                        only_decl=only_decl,
                    )
                finally:
                    cache_store.close()
                with TraceMatcher(project_dir / "raw" / "facts.sqlite") as trace_matcher:
                    trace = trace_matcher.match_all()
                proofs_dir = project_dir / "graphs" / "proofs"
                proofs_dir.mkdir(parents=True, exist_ok=True)
                log_event("proof_graph_build_start", project_id=project_id)
                with sqlite3.connect(project_dir / "raw" / "facts.sqlite") as raw_connection:
                    raw_connection.row_factory = sqlite3.Row
                    tactic_records = [
                        json.loads(row["payload_json"])
                        for row in raw_connection.execute(
                            "SELECT payload_json FROM tactic_node ORDER BY rowid"
                        )
                    ]
                    term_records = [
                        json.loads(row["payload_json"])
                        for row in raw_connection.execute(
                            "SELECT payload_json FROM expr_node WHERE kind = 'term' ORDER BY rowid"
                        )
                    ]
                    known_declarations: dict[str, dict] = {}
                    for item in declarations:
                        metadata = {**item, "project": True}
                        metadata["statement_pretty"] = item.get("type_pretty", "")
                        metadata["target_role"] = _target_role(
                            item["name"],
                            item["kind"],
                            is_instance=bool(item.get("is_instance", False)),
                            is_class=bool(item.get("is_class", False)),
                            is_projection=bool(item.get("is_projection", False)),
                        )
                        known_declarations[item["name"]] = metadata
                    for item in declarations:
                        for ref in item.get("const_refs", []):
                            name = ref["const_name"]
                            if name in known_declarations:
                                continue
                            metadata = {**ref, "project": False}
                            try:
                                metadata["target_role"] = _target_role(
                                    name,
                                    ref.get("kind", "unknown"),
                                    is_instance=bool(ref.get("is_instance", False)),
                                    is_class=bool(ref.get("is_class", False)),
                                    is_projection=bool(ref.get("is_projection", False)),
                                )
                            except ValueError:
                                continue
                            known_declarations[name] = metadata
                    for declaration in declarations:
                        if declaration["kind"] not in {"thm", "theorem"}:
                            continue
                        if "._proof_" in declaration["name"] or "._sparseCases" in declaration["name"]:
                            continue
                        source_path = loaded.root / f"{declaration['module'].replace('.', '/')}.lean"
                        if not source_path.is_file():
                            source_path = loaded.root / "Main.lean"
                        source_text = (
                            source_path.read_text(encoding="utf-8", errors="replace")
                            if source_path.is_file()
                            else ""
                        )
                        comments = tokenize_comments(source_text)
                        declaration_range = declaration.get("range")
                        if isinstance(declaration_range, dict):
                            matching_start = declaration_range["start"]["line"]
                            next_start = declaration_range["end"]["line"] + 1
                        else:
                            log_event(
                                "proof_source_range_missing",
                                project_id=project_id,
                                declaration=declaration["name"],
                            )
                            matching_start = 1
                            next_start = len(source_text.splitlines()) + 1
                        tactic_rows: list[tuple[str, str]] = []
                        wrapper_kinds = {
                            "focus",
                            "Lean.Parser.Tactic.focus",
                            "Lean.Parser.Tactic.refine",
                            "Lean.Parser.Tactic.tacticRefine_lift_",
                            "Lean.Parser.Tactic.tacticSeq",
                            "Lean.Parser.Tactic.tacticSeq1Indented",
                            "Lean.Parser.Tactic.rotateRight",
                            "Lean.Parser.Tactic.paren",
                            "Lean.Parser.Tactic.tacticSeqBracketed",
                            "Lean.Parser.Tactic.tacticSeq1Indented",
                            "Lean.Parser.Tactic.tacticSeq",
                            "Lean.Parser.Tactic.«;»",
                            "«;»",
                            "Lean.calcSteps",
                            "by",
                            "Lean.Parser.Term.byTactic",
                        }
                        candidate_rows: list[tuple[str, dict]] = []
                        for row in raw_connection.execute(
                            "SELECT id, payload_json FROM tactic_node ORDER BY rowid"
                        ):
                            payload = json.loads(row["payload_json"])
                            if payload.get("module") != declaration["module"]:
                                continue
                            tactic_line = payload.get("range", {}).get("start", {}).get("line", 1)
                            if tactic_line < matching_start or tactic_line >= next_start:
                                continue
                            syntax_kind = payload.get("syntax_kind")
                            if (
                                not isinstance(syntax_kind, str)
                                or not (
                                    syntax_kind.startswith("Lean.Parser.Tactic.")
                                    or syntax_kind == "Lean.calcTactic"
                                )
                            ):
                                continue
                            if syntax_kind in wrapper_kinds:
                                continue
                            elif payload.get("synthetic_syntax", True):
                                continue
                            else:
                                candidate_rows.append((row["id"], payload))

                        selected_rows = candidate_rows
                        selected_rows.sort(
                            key=lambda item: (
                                item[1].get("range", {}).get("start", {}).get("line", 0),
                                item[1].get("range", {}).get("start", {}).get("column", 0),
                                item[1].get("record_index", 0),
                            )
                        )
                        for graph_ordinal, (row_id, payload) in enumerate(selected_rows, start=1):
                            payload["graph_ordinal"] = graph_ordinal
                            text = (payload.get("tactic_text") or "").strip()
                            range_value = payload.get("range")
                            if not text or not isinstance(range_value, dict):
                                continue
                            start = range_value.get("start", {})
                            end = range_value.get("end", {})
                            if (
                                not isinstance(start, dict)
                                or not isinstance(end, dict)
                                or (end.get("line", 0), end.get("column", 0))
                                <= (start.get("line", 0), start.get("column", 0))
                            ):
                                continue
                            direct = any(
                                assignment.get("kind") == "direct"
                                for assignment in payload.get("assignments", [])
                            )
                            delayed = any(
                                assignment.get("kind") in {"delayed", "unassigned"}
                                for assignment in payload.get("assignments", [])
                            )
                            if direct and not delayed and not payload.get("synthetic_syntax", True):
                                payload["status"] = "complete"
                            elif delayed:
                                payload["status"] = "partial"
                                payload["partial_reason"] = "unassigned_goal"
                            else:
                                payload["status"] = "dead"
                            if payload["status"] != "dead":
                                tactic_rows.append((row_id, json.dumps(payload)))
                        proof_graph = ProofClaimGraph(project_id, declaration["name"])
                        proof_graph.add_declaration(
                            declaration,
                            tactic_rows,
                            comments,
                            known_declarations=known_declarations,
                            term_records=term_records,
                            source_text=source_text,
                        )
                        proof_graph.write(proofs_dir)
                        log_event(
                            "proof_graph_written",
                            project_id=project_id,
                            declaration=declaration["name"],
                        )
            graphs_dir = project_dir / "graphs"
            graphs_dir.mkdir(parents=True, exist_ok=True)
            dag = DeclarationDAG(project_id, scope, keep_aux=keep_aux)
            dag.add_project_declarations(
                declarations,
                source_files={},
                tactic_records=tactic_records if result.status == "built" else [],
            )
            declaration_by_name = {item["name"]: item for item in declarations}
            for name, parent in dag.folded_into.items():
                parent_record = declaration_by_name.get(parent)
                record = declaration_by_name.get(name)
                if parent_record is None or record is None:
                    continue
                record["range"] = parent_record.get("range")
                record["name_range"] = parent_record.get("name_range")
                record["range_origin"] = parent_record.get("range_origin", "none")
            if result.status == "built":
                with RawStore(project_dir / "raw" / "facts.sqlite") as store:
                    store.update_declaration_projection(
                        project_id,
                        dag.folded_into,
                        dag.aux_claims,
                    )
            dag_json, graphml = dag.write(graphs_dir)
            write_import_graph(loaded.root, project_id, graphs_dir)

            report = ValidationReport(project_id)
            report.validate_m2(
                build_status=result.status,
                matched_toolchain=result.matched_toolchain,
                declarations=declarations,
                dag=dag.graph,
                dag_json_path=dag_json,
                graphml_path=graphml,
            )
            report.validate_dag_metadata(
                declarations=declarations,
                dag=dag.graph,
                project_root=loaded.root,
            )
            report.validate_m4(trace)
            report.validate_m6(
                strict=strict,
                declarations=declarations,
                build_log=result.log,
                store_path=project_dir / "raw" / "facts.sqlite",
                manifest_path=manifest,
                project_root=loaded.root,
                proof_dir=proofs_dir,
                graphs_dir=graphs_dir,
            )
            report.write(project_dir / "reports")
            log_event(
                "validation_complete",
                project_id=project_id,
                blocking_failures=sum(
                    check["severity"] == "blocking" and check["status"] == "failed"
                    for check in report.checks
                ),
            )
        try:
            manifest_data = json.loads(manifest.read_text(encoding="utf-8"))
            manifest_data["cache_hits"] = sorted(set(cache_hits))
            manifest.write_text(
                json.dumps(manifest_data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
        except (NameError, json.JSONDecodeError):
            pass
        log_event("analyze_complete", project_id=project_id, status=result.status)
        typer.echo(f"{project_id}\t{result.status}\t{manifest}")
        return manifest
    finally:
        loaded.close()


@app.command()
def analyze(
    input_value: Annotated[str, typer.Argument(help="Directory, archive, or git URL")],
    out: Annotated[Path, typer.Option("--out", help="Output directory")] = Path("out"),
    scope: Annotated[str, typer.Option(help="project or project+direct")] = "project",
    jobs: Annotated[int, typer.Option("--jobs")] = 1,
    timeout_module: Annotated[int, typer.Option("--timeout-module")] = 300,
    timeout_decl: Annotated[int, typer.Option("--timeout-decl")] = 60,
    strict: Annotated[bool, typer.Option("--strict")] = False,
    sandbox: Annotated[str | None, typer.Option("--sandbox")] = None,
    resume: Annotated[bool, typer.Option("--resume")] = False,
    only_module: Annotated[str | None, typer.Option("--only-module")] = None,
    only_decl: Annotated[str | None, typer.Option("--only-decl")] = None,
    rev: Annotated[str | None, typer.Option("--rev")] = None,
    max_archive_bytes: Annotated[int, typer.Option("--max-archive-bytes")] = 2 * 1024**3,
    max_files: Annotated[int, typer.Option("--max-files")] = 100_000,
    verbose: Annotated[bool, typer.Option("--verbose", "-v")] = False,
    log_file: Annotated[Path | None, typer.Option("--log-file")] = None,
    required_free_gb: Annotated[float, typer.Option("--required-free-gb")] = 10.0,
    mathlib_cache: Annotated[str, typer.Option("--mathlib-cache")] = "none",
    cache_dir: Annotated[Path | None, typer.Option("--cache-dir")] = None,
    keep_aux: Annotated[bool, typer.Option("--keep-aux")] = False,
) -> None:
    if scope not in {"project", "project+direct"}:
        raise typer.BadParameter("scope must be project or project+direct")
    if sandbox not in {None, "docker", "none"}:
        raise typer.BadParameter("sandbox must be docker or none")
    if jobs < 1:
        raise typer.BadParameter("--jobs must be at least 1")
    if mathlib_cache not in {"none", "full"}:
        raise typer.BadParameter("--mathlib-cache must be none or full")
    if required_free_gb < 0:
        raise typer.BadParameter("--required-free-gb must be non-negative")
    try:
        _analyze_one(
            input_value,
            out,
            scope,
            jobs,
            timeout_module,
            timeout_decl,
            strict,
            sandbox,
            resume,
            only_module,
            only_decl,
            rev,
            max_archive_bytes,
            max_files,
            verbose,
            str(log_file) if log_file else None,
            required_free_gb,
            mathlib_cache,
            cache_dir,
            keep_aux,
        )
    except LoaderError as exc:
        typer.echo(f"loader error: {exc}", err=True)
        raise typer.Exit(1) from exc


@app.command()
def batch(
    directory: Annotated[Path, typer.Argument(help="Directory with projects")],
    out: Annotated[Path, typer.Option("--out")] = Path("out"),
    scope: Annotated[str, typer.Option()] = "project",
    jobs: Annotated[int, typer.Option("--jobs")] = 1,
    timeout_module: Annotated[int, typer.Option("--timeout-module")] = 300,
    timeout_decl: Annotated[int, typer.Option("--timeout-decl")] = 60,
    strict: Annotated[bool, typer.Option("--strict")] = False,
    sandbox: Annotated[str | None, typer.Option("--sandbox")] = None,
    resume: Annotated[bool, typer.Option("--resume")] = False,
    verbose: Annotated[bool, typer.Option("--verbose", "-v")] = False,
    log_file: Annotated[Path | None, typer.Option("--log-file")] = None,
    required_free_gb: Annotated[float, typer.Option("--required-free-gb")] = 10.0,
    mathlib_cache: Annotated[str, typer.Option("--mathlib-cache")] = "none",
    cache_dir: Annotated[Path | None, typer.Option("--cache-dir")] = None,
    keep_aux: Annotated[bool, typer.Option("--keep-aux")] = False,
) -> None:
    if not directory.is_dir():
        raise typer.BadParameter("batch input must be a directory")
    children = [
        child
        for child in sorted(directory.iterdir())
        if child.is_dir() or child.name.lower().endswith(
            (".zip", ".tar.gz", ".tgz", ".tar")
        )
    ]
    def run_child(child: Path) -> str:
        try:
            _analyze_one(
                str(child),
                out,
                scope,
                jobs,
                timeout_module,
                timeout_decl,
                strict,
                sandbox,
                resume,
                None,
                None,
                None,
                2 * 1024**3,
                100_000,
                verbose,
                str(log_file) if log_file else None,
                required_free_gb,
                mathlib_cache,
                cache_dir,
                keep_aux,
            )
            return f"{child}: ok"
        except LoaderError as exc:
            return f"{child}: loader error: {exc}"

    with ThreadPoolExecutor(max_workers=max(1, jobs)) as executor:
        futures = [executor.submit(run_child, child) for child in children]
        for future in as_completed(futures):
            try:
                typer.echo(future.result())
            except Exception as exc:
                typer.echo(f"batch error: {exc}", err=True)


@app.command()
def validate(
    output_dir: Annotated[Path, typer.Argument(help="lean2graph output directory")],
) -> None:
    manifests = sorted(output_dir.rglob("run_manifest.json"))
    if not manifests:
        typer.echo("No run_manifest.json found", err=True)
        raise typer.Exit(1)
    failed = False
    for manifest in manifests:
        data = json.loads(manifest.read_text(encoding="utf-8"))
        validation_path = manifest.parent / "reports" / "validation.json"
        if validation_path.is_file():
            validation = json.loads(validation_path.read_text(encoding="utf-8"))
            blocking = validation.get("blocking_failures", 0)
        else:
            blocking = 1
        schema_failures = validate_graph_outputs(manifest.parent / "graphs")
        schema_failures.extend(validate_report_file(validation_path))
        if data.get("status") != "built" or blocking or schema_failures:
            typer.echo(f"{data.get('project_id')}: {data.get('status')}")
            for failure in schema_failures:
                typer.echo(f"  schema error: {failure}")
            failed = True
        else:
            typer.echo(f"{data.get('project_id')}: built")
    raise typer.Exit(1 if failed else 0)


@app.command()
def inspect(
    output_dir: Annotated[Path, typer.Argument(help="lean2graph output directory")],
    decl_name: Annotated[str, typer.Argument(help="Declaration name")] ,
) -> None:
    found: list[tuple[Path, dict]] = []
    for proof_path in sorted(output_dir.rglob("*.json")):
        if "proofs" not in proof_path.parts:
            continue
        try:
            data = json.loads(proof_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if data.get("decl_name") == decl_name:
            found.append((proof_path, data))
    if not found:
        typer.echo(f"No proof claim graph found for {decl_name}", err=True)
        raise typer.Exit(1)

    proof_path, data = found[0]
    project_dir = proof_path.parents[2]
    source_root = project_dir / "source"
    claims = [
        node for node in data["nodes"]
        if node.get("kind") == "claim"
    ]
    nodes = {node["id"]: node for node in data["nodes"]}
    variables = [claim for claim in claims if claim.get("role") == "variable"]
    assumptions = [claim for claim in claims if claim.get("role") == "assumption"]
    module = "Main"
    store_path = project_dir / "raw" / "facts.sqlite"
    if store_path.is_file():
        with sqlite3.connect(store_path) as connection:
            row = connection.execute(
                "SELECT module FROM declaration WHERE project_id = ? AND name = ? "
                "ORDER BY module LIMIT 1",
                (data["project_id"], decl_name),
            ).fetchone()
        if row:
            module = row[0]
    source_path = source_root / f"{module.replace('.', '/')}.lean"
    if not source_path.is_file():
        source_path = source_root / "Main.lean"
    source_lines = (
        source_path.read_text(encoding="utf-8", errors="replace").splitlines()
        if source_path.is_file()
        else []
    )

    inference_nodes = {
        node["id"]: node for node in data["nodes"]
        if node.get("kind") == "inference"
    }
    children: dict[str, list[str]] = {}
    for inference_id, inference in inference_nodes.items():
        parent = inference.get("parent_inference")
        if parent in inference_nodes:
            children.setdefault(parent, []).append(inference_id)
    for edge in data["edges"]:
        if edge.get("kind") == "contains" and edge.get("source") in inference_nodes:
            child = edge.get("target")
            if child in inference_nodes and child not in children.get(edge["source"], []):
                children.setdefault(edge["source"], []).append(child)

    def ordered_inferences(ids: list[str]) -> list[str]:
        return sorted(
            ids,
            key=lambda node_id: (
                inference_nodes[node_id].get("ordinal", 0),
                inference_nodes[node_id].get("range", {}).get("start", {}).get("line", 0),
            ),
        )

    def claims_for_edge(step_id: str, kind: str) -> list[dict]:
        result = []
        for edge in data["edges"]:
            if edge.get("kind") != kind:
                continue
            if kind == "premise" and edge.get("target") != step_id:
                continue
            if kind == "conclusion" and edge.get("source") != step_id:
                continue
            claim = nodes.get(edge["source"] if kind == "premise" else edge["target"], {})
            if claim.get("kind") == "claim":
                result.append(claim)
        return result

    def source_snippet(range_value: dict | None, indent: str) -> None:
        if not isinstance(range_value, dict) or not source_lines:
            return
        start = range_value.get("start", {}).get("line", 0)
        end = range_value.get("end", {}).get("line", start)
        if not isinstance(start, int) or not isinstance(end, int) or start < 1:
            return
        for line_number in range(start, min(end, start + 3) + 1):
            if line_number <= len(source_lines):
                typer.echo(f"{indent}  {line_number}: {source_lines[line_number - 1].strip()}")
        if end > start + 3:
            typer.echo(f"{indent}  …")

    def render_step(step_id: str, depth: int) -> None:
        inference = inference_nodes[step_id]
        indent = "  " * depth
        for claim in claims_for_edge(step_id, "conclusion"):
            if claim.get("role") == "final_goal":
                typer.echo(f"{indent}[final] {claim.get('statement_pretty', '')}")
            else:
                typer.echo(
                    f"{indent}[claim {claim.get('user_name') or 'anonymous'}: "
                    f"{claim.get('statement_pretty', '')}]"
                )
            source_snippet(claim.get("range"), indent)

        range_value = inference.get("range")
        location = ""
        if isinstance(range_value, dict):
            start = range_value.get("start", {})
            end = range_value.get("end", {})
            location = (
                f"{start.get('line', '?')}:{start.get('column', '?')}-"
                f"{end.get('line', '?')}:{end.get('column', '?')}"
            )
        premises = [
            claim.get("user_name")
            or claim.get("statement_pretty")
            or claim.get("role", "claim")
            for claim in claims_for_edge(step_id, "premise")
        ]
        suffix = f" ← {', '.join(premises)}" if premises else ""
        typer.echo(
            f"{indent}{location} {inference.get('justification_type', 'other')}: "
            f"{inference.get('tactic_text', '')}{suffix}"
        )
        source_snippet(range_value, indent)
        refs = sorted(
            const.get("name", "")
            for const in inference.get("used_consts", [])
            if isinstance(const, dict) and const.get("name")
        )
        if refs:
            typer.echo(f"{indent}  refs: {', '.join(refs)}")
        if inference.get("comment"):
            typer.echo(f"{indent}  comment: {inference['comment']}")
        for child_id in ordered_inferences(children.get(step_id, [])):
            render_step(child_id, depth + 1)

    typer.echo(f"theorem {decl_name}")
    typer.echo("")
    if variables:
        typer.echo("variables: " + ", ".join(
            f"{claim.get('user_name', '')}: {claim.get('statement_pretty', '')}"
            for claim in variables
        ))
    if assumptions:
        typer.echo("assumptions: " + ", ".join(
            f"{claim.get('user_name', '')}: {claim.get('statement_pretty', '')}"
            for claim in assumptions
        ))
    final_claim = next((claim for claim in claims if claim.get("role") == "final_goal"), None)
    if final_claim:
        typer.echo(f"goal: {final_claim.get('statement_pretty', '')}")
    child_ids = {
        child_id
        for values in children.values()
        for child_id in values
    }
    roots = ordered_inferences(
        [step_id for step_id in inference_nodes if step_id not in child_ids]
    )
    for step_id in roots:
        render_step(step_id, 0)
