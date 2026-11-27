from __future__ import annotations

import hashlib
import json
import sqlite3
from pathlib import Path


class ModuleCache:
    SCHEMA_VERSION = "m7-1"

    def __init__(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.connection = sqlite3.connect(path)
        self.connection.execute(
            """
            CREATE TABLE IF NOT EXISTS module_cache (
                key TEXT PRIMARY KEY,
                pass_name TEXT NOT NULL,
                payload_json TEXT NOT NULL,
                created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        self.connection.commit()

    def close(self) -> None:
        self.connection.close()

    def __enter__(self) -> "ModuleCache":
        return self

    def __exit__(self, *args: object) -> None:
        self.close()

    def key(
        self,
        *,
        source: Path,
        toolchain: str | None,
        exporter: Path,
        pass_name: str,
    ) -> str:
        digest = hashlib.sha256()
        digest.update(source.read_bytes())
        digest.update((toolchain or "none").encode("utf-8"))
        digest.update(exporter.read_bytes())
        digest.update(self.SCHEMA_VERSION.encode("ascii"))
        digest.update(pass_name.encode("utf-8"))
        return digest.hexdigest()

    def get(self, key: str) -> list[dict] | None:
        row = self.connection.execute(
            "SELECT payload_json FROM module_cache WHERE key = ?",
            (key,),
        ).fetchone()
        if row is None:
            return None
        data = json.loads(row[0])
        return data if isinstance(data, list) else None

    def put(self, key: str, pass_name: str, payload: list[dict]) -> None:
        self.connection.execute(
            "INSERT OR REPLACE INTO module_cache(key, pass_name, payload_json) VALUES (?, ?, ?)",
            (key, pass_name, json.dumps(payload, ensure_ascii=False, sort_keys=True)),
        )
        self.connection.commit()
