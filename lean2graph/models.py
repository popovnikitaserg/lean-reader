from __future__ import annotations

from pathlib import Path
from pydantic import BaseModel, ConfigDict


class ProjectRun(BaseModel):
    model_config = ConfigDict(extra="forbid")

    project_id: str
    input_kind: str
    source: str
    root: Path
    synthetic: bool
    toolchain: str | None
    dependencies: list[dict[str, str]]
    status: str = "pending"
    build_log: str | None = None
