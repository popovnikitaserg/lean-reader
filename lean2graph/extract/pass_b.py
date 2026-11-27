from __future__ import annotations

import json
import subprocess
from pathlib import Path
from lean2graph.cache.cache import ModuleCache
from lean2graph.logging_utils import log_event

from lean2graph.store.sqlite_store import RawStore


class PassBExtractor:
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
    ) -> dict[str, int]:
        counts = {"tactic": 0, "term": 0, "macro": 0, "error": 0}
        sources = sorted(
            p
            for p in root.rglob("*.lean")
            if ".lake" not in p.parts and p.name != "lakefile.lean"
        )
        for source in sources:
            module = self.module_name(root, source)
            if only_module and module != only_module:
                continue
            log_event("pass_b_module_start", project_id=project_id, module=module)
            store.clear_infotree_module(project_id, module)
            cache_key = (
                cache.key(
                    source=source,
                    toolchain=toolchain,
                    exporter=self.exporter,
                    pass_name="pass_b",
                )
                if cache is not None
                else None
            )
            cached_records = cache.get(cache_key) if cache is not None and cache_key else None
            result_records: list[dict] = []
            if resume and cached_records is not None:
                log_event("pass_b_cache_hit", project_id=project_id, module=module)
                for record in cached_records:
                    kind = record.get("record")
                    if kind == "tactic":
                        store.put_tactic(project_id, module, record)
                        counts["tactic"] += 1
                        result_records.append(record)
                    elif kind in {"term", "macro"}:
                        store.put_infotree_record(project_id, module, record)
                        counts[kind] += 1
                        result_records.append(record)
                    elif kind == "error":
                        store.put_error(project_id, "declaration", module, record["message"])
                        counts["error"] += 1
                        result_records.append(record)
                if cache_hits is not None:
                    cache_hits.append(str(source.relative_to(root)))
                continue
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
            except subprocess.TimeoutExpired:
                store.put_error(project_id, "module", module, "Pass B module timeout")
                counts["error"] += 1
                log_event("pass_b_module_timeout", project_id=project_id, module=module)
                continue
            if result.returncode != 0:
                message = (result.stderr or result.stdout).strip()
                store.put_error(
                    project_id,
                    "module",
                    module,
                    message or f"Pass B exporter exited with {result.returncode}",
                )
                counts["error"] += 1
                continue
            for line in result.stdout.splitlines():
                if not line.startswith("{"):
                    continue
                try:
                    record = json.loads(line)
                except json.JSONDecodeError as exc:
                    store.put_error(project_id, "jsonl", module, str(exc))
                    counts["error"] += 1
                    continue
                kind = record.get("record")
                if kind == "tactic":
                    store.put_tactic(project_id, module, record)
                    counts["tactic"] += 1
                    result_records.append(record)
                elif kind in {"term", "macro"}:
                    store.put_infotree_record(project_id, module, record)
                    counts[kind] += 1
                    result_records.append(record)
                elif kind == "error":
                    store.put_error(project_id, "declaration", module, record["message"])
                    counts["error"] += 1
                    result_records.append(record)
            if cache is not None and cache_key:
                cache.put(cache_key, "pass_b", result_records)
            log_event(
                "pass_b_module_complete",
                project_id=project_id,
                module=module,
                tactic_records=counts["tactic"],
                term_records=counts["term"],
                macro_records=counts["macro"],
            )
        store.connection.commit()
        return counts
