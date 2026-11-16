"""Content-addressed provenance for the active Python/Dask/Deal workflow.

This module replaces the earlier build-system-specific hashing helper.
Only Python standard-library SHA-256 and JSON serialization are used.
Both functions are annotated with explicit contracts and return no
probability-model or numerical-validity guarantees.
Author/requester: Anders Hellström. AI-assisted development.
"""
import hashlib
import json
from pathlib import Path

import deal


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.pre(lambda path: not path.is_dir())
@deal.pre(lambda path: path.stat().st_size < 2 ** 31)
@deal.post(lambda result: isinstance(result, str))
@deal.post(lambda result: len(result) == 64)
@deal.post(lambda result: set(result) <= set("0123456789abcdef"))
@deal.ensure(lambda path, result: len(result) == 64 and result.isascii())
@deal.raises(OSError, ValueError)
@deal.has("read")
def digest(path: Path) -> str:
    """SHA-256 of exactly the file bytes; no source-version claim is inferred."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


@deal.pre(lambda path, value: isinstance(path, Path))
@deal.pre(lambda path, value: path.suffix == ".json")
@deal.pre(lambda path, value: path.parent.is_dir())
@deal.pre(lambda path, value: isinstance(value, dict))
@deal.pre(lambda path, value: all(isinstance(key, str) and key for key in value))
@deal.post(lambda result: result is None)
@deal.ensure(lambda path, value, result: path.is_file() and path.stat().st_size > 2)
@deal.ensure(lambda path, value, result: path.read_text(encoding="utf-8").endswith("\n"))
@deal.ensure(lambda path, value, result: json.loads(path.read_text(encoding="utf-8")) == value)
@deal.raises(OSError, TypeError, ValueError)
@deal.has("read", "write")
def dump(path: Path, value: dict) -> None:
    """Write one UTF-8 JSON record; verification uses the parsed exact payload."""
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8")
