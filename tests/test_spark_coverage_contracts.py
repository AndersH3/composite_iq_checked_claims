"""Native coverage cannot pass by omitting files or hiding trusted boundaries."""
from conftest import protected_history_intact, reference_inputs_intact
import hashlib
import json
from pathlib import Path

import deal
import pytest

from verification.spark_coverage import read_coverage, unique_object


@deal.ensure(lambda name, status='all', file='sample.ads', line=1, *, result: protected_history_intact())
@deal.pre(lambda name, status="all", file="sample.ads", line=1:
          isinstance(name, str) and bool(name) and isinstance(status, str)
          and isinstance(file, str) and type(line) is int)
@deal.post(lambda result: isinstance(result, dict) and bool(result["sloc"]))
@deal.raises()
@deal.has("read")
def entity(name: str, status: str = "all", file: str = "sample.ads", line: int = 1) -> dict:
    return {"name": name, "sloc": [{"file": file, "line": line}], "spark": status}


@deal.ensure(lambda path, entities, assume=None, flow=None, proof=None, *, result: protected_history_intact())
@deal.pre(lambda path, entities, assume=None, flow=None, proof=None:
          isinstance(path, Path) and path.suffix == ".spark" and isinstance(entities, list))
@deal.post(lambda result: isinstance(result, Path) and result.is_file())
@deal.raises(OSError, ValueError, TypeError)
@deal.has("write", "read")
def write_native(path: Path, entities: list, assume=None, flow=None, proof=None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"spark": entities, "flow": flow or [], "proof": proof or [],
                                "pragma_assume": assume or []}))
    return path


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_native_statuses_are_separate_and_raw_hashes_match(tmp_path):
    path = write_native(tmp_path.joinpath("nested/unit.spark"), [entity("Body"), entity("Boundary", "spec", line=2), entity("Outside", "no", line=3)])
    result = read_coverage(tmp_path)
    assert result["counts"] == {"all": 1, "spec": 1, "no": 1}
    assert result["total_entities"] == 3
    assert result["entities"][1]["name"] == "Boundary"
    assert result["raw_files"] == [{"path": "nested/unit.spark", "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                                      "entity_count": 3, "sections_present": ["flow", "pragma_assume", "proof", "spark"]}]
    assert result["no_assumptions_or_suppressions"]


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_duplicate_identical_entities_are_counted_once(tmp_path):
    row = entity("One")
    write_native(tmp_path.joinpath("a.spark"), [row, row])
    write_native(tmp_path.joinpath("b.spark"), [row])
    result = read_coverage(tmp_path)
    assert result["counts"] == {"all": 1, "spec": 0, "no": 0}
    assert len(result["raw_files"]) == 2
    assert [row["entity_count"] for row in result["raw_files"]] == [2, 1]
    assert all(row["sections_present"] == ["flow", "pragma_assume", "proof", "spark"]
               for row in result["raw_files"])


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_conflicting_duplicate_status_cannot_pass(tmp_path):
    write_native(tmp_path.joinpath("a.spark"), [entity("One")])
    write_native(tmp_path.joinpath("b.spark"), [entity("One", "spec")])
    with pytest.raises(ValueError, match="Conflicting"):
        read_coverage(tmp_path)


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_filter_uses_location_chain_and_preserves_external_assumption_flags(tmp_path):
    instance = entity("Generic.Instance", file="runtime.ads")
    instance["sloc"].append({"file": "sample.adb", "line": 10})
    assume = {"file": "external.adb", "line": 12, "col": 4, "entity": entity("Other", file="external.ads")}
    write_native(tmp_path.joinpath("unit.spark"), [instance, entity("Other", "no", file="external.ads")], assume=[assume])
    result = read_coverage(tmp_path, {"sample.adb"})
    assert result["total_entities"] == 1
    assert result["entities"][0]["sloc"] == instance["sloc"]
    assert result["pragma_assume"] == [{"raw_file": "unit.spark", "entry": assume}]
    assert not result["no_assumptions_or_suppressions"]


@pytest.mark.parametrize("section", ["flow", "proof"])
@deal.pre(lambda tmp_path, section: protected_history_intact())
@deal.ensure(lambda tmp_path, section, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, section, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_suppressed_messages_are_reported_even_with_empty_justification(tmp_path, section):
    message = {"file": "sample.adb", "line": 2, "col": 4, "suppressed": "", "rule": "VC_ASSERT"}
    arguments = {section: [message]}
    write_native(tmp_path.joinpath("unit.spark"), [entity("One")], **arguments)
    result = read_coverage(tmp_path)
    assert result["suppressed"] == [{"raw_file": "unit.spark", "section": section, "entry": message}]
    assert not result["no_assumptions_or_suppressions"]


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_missing_or_empty_native_inventory_cannot_pass(tmp_path):
    with pytest.raises(ValueError, match="No native"):
        read_coverage(tmp_path)
    write_native(tmp_path.joinpath("empty.spark"), [])
    with pytest.raises(ValueError, match="No SPARK entities"):
        read_coverage(tmp_path)


@pytest.mark.parametrize("row", [None, {}, {"name": "Bad", "spark": "all"},
    {"name": "Bad", "spark": "invalid", "sloc": [{"file": "sample.ads", "line": 1}]},
    {"name": "Bad", "spark": "all", "sloc": []},
    {"name": "Bad", "spark": "all", "sloc": [{"file": "sample.ads", "line": True}]},
    {"name": "Bad", "spark": "all", "sloc": [{"file": "sample.ads", "line": 0}]},
    {"name": "Bad", "spark": "all", "sloc": [{"file": "", "line": 1}]}])
@deal.pre(lambda tmp_path, row: protected_history_intact())
@deal.ensure(lambda tmp_path, row, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, row, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_malformed_entity_schema_is_rejected(tmp_path, row):
    write_native(tmp_path.joinpath("bad.spark"), [row])
    with pytest.raises(ValueError):
        read_coverage(tmp_path)


@pytest.mark.parametrize("text", ["{", "[]", '{"spark": []}',
    '{"spark": [], "spark": [], "flow": [], "proof": [], "pragma_assume": []}'])
@deal.pre(lambda tmp_path, text: protected_history_intact())
@deal.ensure(lambda tmp_path, text, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, text, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_invalid_json_or_missing_sections_cannot_pass(tmp_path, text):
    tmp_path.joinpath("bad.spark").write_text(text)
    with pytest.raises(ValueError):
        read_coverage(tmp_path)


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_source_filter_cannot_make_empty_coverage_successful(tmp_path):
    write_native(tmp_path.joinpath("unit.spark"), [entity("One")])
    with pytest.raises(ValueError, match="No SPARK entities"):
        read_coverage(tmp_path, {"missing.ads"})


@pytest.mark.parametrize("section,entries", [("pragma_assume", [None]),
    ("pragma_assume", [{"file": "sample.adb", "line": 2, "col": False}]),
    ("proof", [{"file": "sample.adb", "line": 2, "suppressed": False}]),
    ("flow", [None])])
@deal.pre(lambda tmp_path, section, entries: protected_history_intact())
@deal.ensure(lambda tmp_path, section, entries, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, section, entries, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_malformed_assumption_or_suppression_metadata_cannot_pass(tmp_path, section, entries):
    record = {"spark": [entity("One")], "flow": [], "proof": [], "pragma_assume": []}
    record[section] = entries
    tmp_path.joinpath("bad.spark").write_text(json.dumps(record))
    with pytest.raises(ValueError):
        read_coverage(tmp_path)


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_source_filter_cannot_hide_malformed_foreign_entities(tmp_path):
    write_native(tmp_path.joinpath("bad.spark"), [entity("One"), entity("Broken", "unknown", file="external.ads")])
    with pytest.raises(ValueError, match="Unknown SPARK"):
        read_coverage(tmp_path, {"sample.ads"})


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_explicit_flow_mode_retains_empty_units_without_claiming_proof_completeness(tmp_path):
    tmp_path.joinpath("body.spark").write_text(json.dumps({"spark": [entity("Body")], "flow": []}))
    tmp_path.joinpath("outside.spark").write_text(json.dumps({"spark": [], "flow": []}))
    result = read_coverage(tmp_path, analysis_mode="flow")
    assert result["analysis_mode"] == "flow"
    assert result["counts"] == {"all": 1, "spec": 0, "no": 0}
    assert len(result["raw_files"]) == 2
    assert [row["entity_count"] for row in result["raw_files"]] == [1, 0]
    assert all(row["sections_present"] == ["flow", "spark"] for row in result["raw_files"])
    assert not result["proof_metadata_complete"]
    assert not result["no_assumptions_or_suppressions"]
    with pytest.raises(ValueError, match="section must be a list"):
        read_coverage(tmp_path)


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_flow_mode_cannot_satisfy_completion_even_if_proof_arrays_are_present(tmp_path):
    write_native(tmp_path.joinpath("body.spark"), [entity("Body")])
    result = read_coverage(tmp_path, analysis_mode="flow")
    assert result["proof_metadata_complete"]
    assert not result["no_assumptions_or_suppressions"]
    assert read_coverage(tmp_path)["no_assumptions_or_suppressions"]


@pytest.mark.parametrize("section,value", [("proof", None), ("pragma_assume", {}), ("flow", None)])
@deal.pre(lambda tmp_path, section, value: protected_history_intact())
@deal.ensure(lambda tmp_path, section, value, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, section, value, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_flow_mode_validates_present_optional_sections(tmp_path, section, value):
    record = {"spark": [entity("Body")], "flow": []}
    record[section] = value
    tmp_path.joinpath("bad.spark").write_text(json.dumps(record))
    with pytest.raises(ValueError, match="section must be a list"):
        read_coverage(tmp_path, analysis_mode="flow")


@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_unknown_analysis_mode_is_explicitly_rejected(tmp_path):
    write_native(tmp_path.joinpath("body.spark"), [entity("Body")])
    with pytest.raises(ValueError, match="Unknown native coverage analysis mode"):
        read_coverage(tmp_path, analysis_mode="quiet")


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_native_unique_object_preserves_key_order_value_identity_and_nulls():
    """A duplicate-free JSON object retains order and original nested values."""
    nested = {"observations": [1, None, "value"]}
    pairs = [("unit", nested), ("missing", None), ("positive", 17)]
    mapping = unique_object(pairs)
    assert list(mapping) == ["unit", "missing", "positive"]
    assert mapping["unit"] is nested
    assert mapping["missing"] is None
    assert mapping["positive"] is pairs[2][1]
    with pytest.raises(ValueError, match="Duplicate"):
        unique_object([("unit", nested), ("unit", None)])
