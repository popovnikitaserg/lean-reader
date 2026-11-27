from __future__ import annotations

import json
import subprocess
import hashlib
from pathlib import Path

from lean2graph.store.sqlite_store import RawStore
from lean2graph.cache.cache import ModuleCache
from lean2graph.logging_utils import log_event


class PassAExtractor:
    def __init__(self, exporter: Path) -> None:
        self.exporter = exporter

    def module_name(self, root: Path, source: Path) -> str:
        rel = source.relative_to(root)
        if rel.suffix == ".lean":
            rel = rel.with_suffix("")
        return ".".join(rel.parts)

    def run(
        self,
        *,
        root: Path,
        project_id: str,
        store: RawStore,
        timeout_seconds: int = 300,
        cache: ModuleCache | None = None,
        toolchain: str | None = None,
        resume: bool = False,
        cache_hits: list[str] | None = None,
        only_module: str | None = None,
        only_decl: str | None = None,
    ) -> list[dict]:
        records: list[dict] = []
        sources = sorted(
            p
            for p in root.rglob("*.lean")
            if ".lake" not in p.parts and p.name != "lakefile.lean"
        )
        for source in sources:
            module = self.module_name(root, source)
            if only_module and module != only_module:
                continue
            log_event("pass_a_module_start", project_id=project_id, module=module)
            store.put_module(project_id, module, str(source.relative_to(root)))
            content = source.read_text(encoding="utf-8", errors="replace")
            import hashlib

            store.put_source(
                project_id,
                str(source.relative_to(root)),
                hashlib.sha256(source.read_bytes()).hexdigest(),
                content,
            )
            cache_key = (
                cache.key(
                    source=source,
                    toolchain=toolchain,
                    exporter=self.exporter,
                    pass_name="pass_a",
                )
                if cache is not None
                else None
            )
            cached_records = cache.get(cache_key) if cache is not None and cache_key else None
            if resume and cached_records is not None:
                log_event("pass_a_cache_hit", project_id=project_id, module=module)
                records.extend(cached_records)
                for record in cached_records:
                    if record.get("record") == "declaration":
                        if only_decl and record.get("name") != only_decl:
                            continue
                        if only_decl and record.get("name") != only_decl:
                            continue
                        store.put_declaration(project_id, module, record)
                if cache_hits is not None:
                    cache_hits.append(str(source.relative_to(root)))
                continue
            result_records: list[dict] = []
            try:
                result = subprocess.run(
                    [
                        "lake",
                        "env",
                        "lean",
                        "--run",
                        str(self.exporter),
                        project_id,
                        module,
                        str(source),
                    ],
                    cwd=root,
                    capture_output=True,
                    text=True,
                    timeout=timeout_seconds,
                )
            except subprocess.TimeoutExpired as exc:
                store.put_error(project_id, "module", module, "module timeout")
                log_event("pass_a_module_timeout", project_id=project_id, module=module)
                continue
            if result.returncode != 0:
                message = (result.stderr or result.stdout).strip()
                store.put_error(
                    project_id,
                    "module",
                    module,
                    message or f"Lean exporter exited with {result.returncode}",
                )
                continue
            for line in result.stdout.splitlines():
                if not line.startswith("{"):
                    continue
                try:
                    record = json.loads(line)
                except json.JSONDecodeError as exc:
                    store.put_error(project_id, "jsonl", module, str(exc))
                    continue
                if record.get("record") == "declaration":
                    record["axioms"] = record.get("axioms", [])
                    record["const_refs"] = record.get("const_refs", [])
                    store.put_declaration(project_id, module, record)
                    records.append(record)
                    result_records.append(record)
                elif record.get("record") == "error":
                    store.put_error(project_id, "declaration", module, record["message"])
                    result_records.append(record)
            if cache is not None and cache_key:
                cache.put(cache_key, "pass_a", result_records)
            log_event(
                "pass_a_module_complete",
                project_id=project_id,
                module=module,
                declarations=len([r for r in result_records if r.get("record") == "declaration"]),
            )
        store.connection.commit()
        return records
