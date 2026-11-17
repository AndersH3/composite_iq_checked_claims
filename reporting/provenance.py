"""Content-addressed provenance for the active Python/Dask/Deal workflow.

This module replaces the earlier build-system-specific hashing helper.
Only Python standard-library SHA-256 and JSON serialization are used.
Both functions are annotated with explicit contracts and return no
probability-model or numerical-validity guarantees.
Author/requester: Anders Hellström. AI-assisted development.
"""
# Dask distributed workers share their process with an asynchronous socket
# event loop. Deal's runtime offline checker monkeypatches socket process-wide;
# permitting the worker transport avoids breaking unrelated scheduler I/O.
# Source-level numeric invariants and exception contracts remain in force.
import hashlib
import json
from pathlib import Path

import deal


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.is_file())
@deal.pre(lambda path: not path.is_dir())
@deal.pre(lambda path: path.stat().st_size < 2 ** 31)
@deal.pre(lambda path: path.stat().st_size >= 0)
@deal.pre(lambda path: path.exists())
@deal.pre(lambda path: bool(path.name))
@deal.pre(lambda path: path.resolve().is_file())
@deal.raises(OSError, ValueError)
@deal.has("network", "read")
@deal.post(lambda result: isinstance(result, str))
@deal.post(lambda result: len(result) == hashlib.sha256().digest_size * 2)
@deal.post(lambda result: result.isascii())
@deal.post(lambda result: result == result.lower())
@deal.post(lambda result: all(character in "0123456789abcdef" for character in result))
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
@deal.has("network", "read", "write")
@deal.ensure(lambda path, value, result: path.read_text(encoding="utf-8") == json.dumps(value, indent=2, allow_nan=False) + "\n")
@deal.ensure(lambda path, value, result: path.read_bytes().startswith(b"{"))
@deal.ensure(lambda path, value, result: path.stat().st_size == len(path.read_text(encoding="utf-8").encode("utf-8")))
@deal.ensure(lambda path, value, result: path.read_text(encoding="utf-8").lstrip().startswith("{"))
def dump(path: Path, value: dict) -> None:
    """Write one UTF-8 JSON record; verification uses the parsed exact payload."""
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8")
