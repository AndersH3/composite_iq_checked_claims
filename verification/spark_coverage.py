"""Read native GNATprove coverage without confusing trusted specs with bodies.

The schema here is the nested ``sloc`` form emitted by the installed GNATprove
13 toolchain. Source filtering affects entity counts only: assumptions and
suppressed messages from every retained raw file are always reported.
"""
import hashlib
import json
from json import JSONDecodeError
from pathlib import Path

import deal


@deal.pre(lambda condition, message: isinstance(condition, bool) and isinstance(message, str))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.reason(ValueError, lambda condition, message: not condition)
@deal.has()
def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@deal.pre(lambda pairs: isinstance(pairs, list))
@deal.pre(lambda pairs: all((isinstance(p, tuple) and len(p) == 2 and isinstance(p[0], str) for p in pairs)))
@deal.ensure(lambda pairs, result: isinstance(result, dict) and len(result) == len(pairs))
@deal.raises(ValueError)
@deal.has()
# JSON object decoding must not normalize keys, reorder fields, change
# references to nested values, or lose explicit null-valued mappings.
@deal.post(lambda result: all(isinstance(key, str) for key in result))
@deal.ensure(lambda pairs, result:
             list(result) == [key for key, _ in pairs])
@deal.ensure(lambda pairs, result:
             set(result) == {key for key, _ in pairs})
@deal.ensure(lambda pairs, result:
             all(result[key] is value for key, value in pairs))
@deal.ensure(lambda pairs, result:
             {key for key, value in result.items() if value is None} ==
             {key for key, value in pairs if value is None})
def unique_object(pairs: list) -> dict:
    """Reject ambiguous JSON objects rather than keeping the last duplicate key."""
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON object key: " + key)
        result[key] = value
    return result


@deal.post(lambda result: bool(result['file']) and type(result['line']) is int and (result['line'] > 0))
@deal.post(lambda result: isinstance(result['file'], str))
@deal.post(lambda result: isinstance(result, dict))
@deal.raises(ValueError)
@deal.has()
# Preserve the exact GNATprove source locator, its Ada extension and the
# normalized two-field schema; do not fabricate line numbers or file names.
@deal.post(lambda result: set(result) == {"file", "line"})
@deal.ensure(lambda value, result: result["file"] == value["file"])
@deal.ensure(lambda value, result: result["line"] == value["line"])
@deal.post(lambda result: Path(result["file"]).suffix in {".ads", ".adb"})
@deal.post(lambda result: bool(result["file"].strip()))
def location(value: object) -> dict:
    require(isinstance(value, dict), "Source location must be an object")
    require(isinstance(value.get("file"), str) and bool(value["file"].strip()),
            "Source location requires a nonempty file")
    require(type(value.get("line")) is int and value["line"] > 0,
            "Source location requires a positive integer line")
    require(Path(value["file"]).suffix in {".ads", ".adb"}, "Source location must name Ada source")
    return {"file": value["file"], "line": value["line"]}


@deal.post(lambda result: result['status'] in {'all', 'spec', 'no'} and bool(result['sloc']) and (result['file'] == result['sloc'][0]['file']) and (result['line'] == result['sloc'][0]['line']))
@deal.post(lambda result: bool(result['name']))
@deal.post(lambda result: isinstance(result, dict))
@deal.raises(ValueError)
@deal.has()
# Source/coverage normalization must not silently change an entity's
# identity, analysis status, number of locations or first source line.
@deal.post(lambda result:
           set(result) == {"name", "file", "line", "status", "sloc"})
@deal.ensure(lambda value, result: result["name"] == value["name"])
@deal.ensure(lambda value, result: result["status"] == value["spark"])
@deal.ensure(lambda value, result:
             len(result["sloc"]) == len(value["sloc"]))
@deal.ensure(lambda value, result:
             result["sloc"][0]["line"] == value["sloc"][0]["line"])
def normalize_entity(value: object) -> dict:
    require(isinstance(value, dict), "SPARK entity must be an object")
    require(isinstance(value.get("name"), str) and bool(value["name"].strip()),
            "SPARK entity requires a nonempty name")
    require(isinstance(value.get("spark"), str) and value["spark"] in {"all", "spec", "no"},
            "Unknown SPARK entity status")
    require(isinstance(value.get("sloc"), list) and bool(value["sloc"]),
            "SPARK entity requires a nonempty sloc array")
    sloc = [location(item) for item in value["sloc"]]
    return {"name": value["name"], "file": sloc[0]["file"], "line": sloc[0]["line"],
            "status": value["spark"], "sloc": sloc}


@deal.pre(lambda folder, source_names=None, analysis_mode='all': isinstance(folder, Path))
@deal.pre(lambda folder, source_names=None, analysis_mode='all': folder.is_dir() and isinstance(analysis_mode, str) and (source_names is None or (isinstance(source_names, set) and bool(source_names) and all((isinstance(name, str) and Path(name).name == name and (Path(name).suffix in {'.ads', '.adb'}) for name in source_names)))))
@deal.post(lambda result: isinstance(result, dict) and bool(result["raw_files"])
           and all(type(row["entity_count"]) is int and row["entity_count"] >= 0
                   and isinstance(row["sections_present"], list) for row in result["raw_files"])
           and result["total_entities"] > 0
           and result["total_entities"] == len(result["entities"])
           and sum(result["counts"].values()) == result["total_entities"]
           and set(result["counts"]) == {"all", "spec", "no"}
           and result["analysis_mode"] in {"all", "flow"}
           and isinstance(result["proof_metadata_complete"], bool)
           and result["no_assumptions_or_suppressions"]
               == (result["analysis_mode"] == "all" and result["proof_metadata_complete"]
                   and not result["pragma_assume"] and not result["suppressed"]))
@deal.raises(OSError, ValueError, JSONDecodeError)
@deal.has("read")
# The original archive-sensitive result dictionary must keep its
# exact schema. These additional independent receipt properties verify
# source-selection provenance, deterministic file order and uniqueness,
# and the canonical shape of every retained SHA-256 digest.
@deal.post(lambda result: set(result) == {
    "source_names", "analysis_mode", "proof_metadata_complete",
    "counts", "total_entities", "entities", "raw_files",
    "pragma_assume", "suppressed", "no_assumptions_or_suppressions"})
@deal.ensure(lambda folder, source_names=None, analysis_mode="all", *, result:
             result["source_names"] ==
             (sorted(source_names) if source_names is not None else None))
@deal.post(lambda result:
           [row["path"] for row in result["raw_files"]] ==
           sorted(row["path"] for row in result["raw_files"]))
@deal.post(lambda result:
           len({row["path"] for row in result["raw_files"]}) ==
           len(result["raw_files"]))
@deal.post(lambda result:
           all(len(row["sha256"]) == 64
               and all(char in "0123456789abcdef" for char in row["sha256"])
               for row in result["raw_files"]))
def read_coverage(folder: Path, source_names: set[str] | None = None,
                  analysis_mode: str = "all") -> dict:
    """Return coverage, raw-file hashes, and all explicit assumption/suppression flags.

    ``all`` means both specification and body are in SPARK, not that every
    verification condition was proved. ``spec`` explicitly identifies a trusted
    completion. An entity is selected when any native sloc frame belongs to
    ``source_names``; its complete native location chain remains visible.

    Full-proof mode requires proof and pragma-assume metadata in every raw
    file. Explicit ``flow`` mode accepts their omission, records whether both
    were present everywhere, and always leaves the completion flag false.
    Empty native entity arrays are retained in the raw inventory; they do not
    enumerate or quantify code excluded from analysis.
    """
    require(analysis_mode in {"all", "flow"}, "Unknown native coverage analysis mode")
    paths = sorted(folder.rglob("*.spark"))
    require(bool(paths), "No native .spark files were retained")
    entities = {}
    raw_files = []
    assumptions = []
    suppressed = []
    proof_metadata_complete = True
    for path in paths:
        require(path.is_file() and not path.is_symlink(), "Native .spark inventory must contain regular files")
        raw = path.read_bytes()
        relative = path.relative_to(folder).as_posix()
        record = json.JSONDecoder(object_pairs_hook=unique_object).decode(raw.decode("utf-8"))
        require(isinstance(record, dict), "Native .spark file must contain an object")
        for section in ("spark", "flow"):
            require(isinstance(record.get(section), list), "Native .spark section must be a list: " + section)
        for section in ("proof", "pragma_assume"):
            if section in record or analysis_mode == "all":
                require(isinstance(record.get(section), list), "Native .spark section must be a list: " + section)
            else:
                proof_metadata_complete = False
        raw_files.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                          "entity_count": len(record["spark"]), "sections_present": sorted(record)})
        for value in record["spark"]:
            row = normalize_entity(value)
            key = (row["file"], row["line"], row["name"])
            if key in entities:
                require(entities[key] == row, "Conflicting SPARK entity status or source location: " + row["name"])
            else:
                entities[key] = row
        for entry in record.get("pragma_assume", []):
            location(entry)
            require(type(entry.get("col")) is int and entry["col"] > 0,
                    "Pragma Assume requires a positive column")
            assumptions.append({"raw_file": relative, "entry": entry})
        for section in ("flow", "proof"):
            for entry in record.get(section, []):
                require(isinstance(entry, dict), "Native message must be an object")
                if "suppressed" in entry:
                    require(isinstance(entry["suppressed"], str), "Suppression justification must be a string")
                    location(entry)
                    suppressed.append({"raw_file": relative, "section": section, "entry": entry})
    selected = [row for row in entities.values() if source_names is None
                or any(Path(frame["file"]).name in source_names for frame in row["sloc"])]
    selected.sort(key=lambda row: (row["file"], row["line"], row["name"]))
    require(bool(selected), "No SPARK entities match the requested source inventory")
    counts = {status: sum(row["status"] == status for row in selected) for status in ("all", "spec", "no")}
    return {"source_names": sorted(source_names) if source_names is not None else None,
            "analysis_mode": analysis_mode, "proof_metadata_complete": proof_metadata_complete,
            "counts": counts, "total_entities": len(selected), "entities": selected,
            "raw_files": raw_files, "pragma_assume": assumptions, "suppressed": suppressed,
            "no_assumptions_or_suppressions": analysis_mode == "all" and proof_metadata_complete
                and not assumptions and not suppressed}
