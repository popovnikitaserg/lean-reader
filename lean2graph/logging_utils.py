from __future__ import annotations

import json
import logging
import sys
from pathlib import Path
from typing import Any


logger = logging.getLogger("lean2graph")
logger.setLevel(logging.DEBUG)
logger.propagate = False


def configure_logging(
    *,
    log_file: Path | None = None,
    extra_log_file: Path | None = None,
    verbose: bool = False,
) -> Path | None:
    logger.handlers.clear()
    level = logging.DEBUG if verbose else logging.INFO
    logger.setLevel(level)

    console = logging.StreamHandler(sys.stderr)
    console.setLevel(level)
    console.setFormatter(
        logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%Y-%m-%dT%H:%M:%S")
    )
    logger.addHandler(console)

    if log_file is not None:
        log_file.parent.mkdir(parents=True, exist_ok=True)
        file_handler = logging.FileHandler(log_file, encoding="utf-8")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(
            logging.Formatter(
                "%(asctime)s %(levelname)s %(message)s",
                "%Y-%m-%dT%H:%M:%S",
            )
        )
        logger.addHandler(file_handler)
    if extra_log_file is not None:
        extra_log_file.parent.mkdir(parents=True, exist_ok=True)
        extra_handler = logging.FileHandler(extra_log_file, encoding="utf-8")
        extra_handler.setLevel(logging.DEBUG)
        extra_handler.setFormatter(
            logging.Formatter(
                "%(asctime)s %(levelname)s %(message)s",
                "%Y-%m-%dT%H:%M:%S",
            )
        )
        logger.addHandler(extra_handler)
    return log_file


def log_event(
    event: str,
    *,
    level: int = logging.INFO,
    **fields: Any,
) -> None:
    payload = {"event": event, **fields}
    message = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    logger.log(level, message)
