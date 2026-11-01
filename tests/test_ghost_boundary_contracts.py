"""Ghost modeling coverage must expose every trusted boundary and real link."""
import copy
from copy import Error
import hashlib
from pathlib import Path

import deal
import pytest

from verification.ghost_boundaries import (
    GHOST_SCHEMA, GLOBAL_OBLIGATION_SCOPES, ada_code, contract_reference, coupling_reference, foreign_imports,
    pinned_ada_sources, validate_boundaries,
)


@pytest.fixture
@deal.pre(lambda tmp_path: isinstance(tmp_path, Path) and tmp_path.is_dir())
@deal.post(lambda result: isinstance(result, dict) and set(result) == {"register", "coverage", "sources", "root"})
@deal.raises(OSError, ValueError)
@deal.has("read", "write")
def ghost_fixture(tmp_path):
    texts = {
        "model.ads": "package Model with SPARK_Mode, Ghost is\n"
                     "function Valid (X : Float) return Boolean is (X >= 0.0);\nend Model;\n",
        "boundary.ads": "with Model; package Boundary with SPARK_Mode is\n"
                        "function Numeric (X : Float) return Float with Post => Model.Valid (Numeric'Result);\nend Boundary;\n",
        "boundary.adb": "package body Boundary with SPARK_Mode is\n"
                        "function C_Backend (X : Float; Y : Float) return Float with Import, Convention => C, SPARK_Mode => Off;\nend Boundary;\n",
    }
    sources = []
    for relative, text in texts.items():
        path = tmp_path.joinpath(relative)
        path.write_text(text)
        sources.append({"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    base = {"source": "boundary.ads", "model_file": "model.ads", "model_entities": ["Model.Valid"],
            "contract_file": "boundary.ads", "contract_refs": ["Model.Valid"],
            "obligations": ["Backend normal-return value must satisfy the checked range."],
            "implementation_proved": False, "model_adequacy_proved": False}
    numeric = dict(base, entity="Boundary.Numeric", kind="spec-only")
    backend = dict(base, entity="Boundary.C_Backend", kind="foreign-import", source="boundary.adb",
                   contract_entity="Boundary.Numeric")
    register = {"schema": GHOST_SCHEMA, "projects": {"hoeflin": [numeric, backend], "towers": []},
                "external_dependencies": {"hoeflin": {}, "towers": {}},
                "standard_library_models": {"hoeflin": [], "towers": []},
                "global_unproved_obligations": {scope: "This obligation is explicitly not established by a ghost model."
                                                 for scope in GLOBAL_OBLIGATION_SCOPES}}
    coverage = {"entities": [{"name": "Model.Valid", "status": "all", "file": "model.ads"},
                             {"name": "Boundary.Numeric", "status": "spec", "file": "boundary.ads"}]}
    return {"register": register, "coverage": coverage, "sources": sources, "root": tmp_path}


@deal.pre(lambda data: isinstance(data, dict))
@deal.post(lambda result: isinstance(result, dict) and result["coverage_complete"])
@deal.raises(OSError, FileNotFoundError, PermissionError, ValueError, UnicodeDecodeError)
@deal.has("read")
def audit_fixture(data):
    return validate_boundaries(data["register"], "hoeflin", data["coverage"], data["sources"], data["root"])


@deal.post(lambda result: result is None)
@deal.has("read")
def test_complete_register_has_explicit_unproved_adequacy_and_implementation(ghost_fixture):
    result = audit_fixture(ghost_fixture)
    assert result["boundary_count"] == 2
    assert result["native_spec_entities"] == ["boundary.numeric"]
    assert result["foreign_imports"] == ["boundary.c_backend"]
    assert result["implementation_proved"] is False
    assert result["model_adequacy_proved"] is False


@pytest.mark.parametrize("kind", ["spec-only", "foreign-import"])
@deal.post(lambda result: result is None)
@deal.has("read")
def test_omitted_spec_or_foreign_boundary_is_rejected(ghost_fixture, kind):
    data = copy.deepcopy(ghost_fixture)
    data["register"]["projects"]["hoeflin"] = [e for e in data["register"]["projects"]["hoeflin"] if e["kind"] != kind]
    with pytest.raises(ValueError, match="boundary inventory differs"):
        audit_fixture(data)


@pytest.mark.parametrize("field,value,message", [
    ("entity", "Boundary.Missing", "absent from native coverage"),
    ("kind", "unknown", "Unknown ghost boundary kind"),
    ("source", "missing.ads", "Boundary source is not pinned"),
    ("model_file", "missing.ads", "Ghost model source is not pinned"),
    ("contract_file", "missing.ads", "Ghost contract source is not pinned"),
    ("implementation_proved", True, "must not claim"),
    ("model_adequacy_proved", True, "must not claim"),
    ("obligations", [], "obligations are missing"),
    ("model_entities", [], "entity inventory is empty"),
    ("model_entities", ["Model.Valid", "model.valid"], "entity inventory is empty or duplicated"),
    ("model_entities", ["Model.Missing"], "Contract references must name registered"),
    ("contract_refs", [], "Contract references must name registered"),
    ("contract_refs", ["Model.Missing"], "Contract references must name registered"),
    ("excluded_helpers", [None], "helper inventory is malformed"),
])
@deal.post(lambda result: result is None)
@deal.has("read")
def test_invalid_mapping_cannot_pass(ghost_fixture, field, value, message):
    data = copy.deepcopy(ghost_fixture)
    data["register"]["projects"]["hoeflin"][0][field] = value
    with pytest.raises(ValueError, match=message):
        audit_fixture(data)


@pytest.mark.parametrize("status", ["spec", "no"])
@deal.post(lambda result: result is None)
@deal.has("read")
def test_model_without_analyzed_body_is_rejected(ghost_fixture, status):
    data = copy.deepcopy(ghost_fixture)
    data["coverage"]["entities"][0]["status"] = status
    with pytest.raises(ValueError):
        audit_fixture(data)


@deal.post(lambda result: result is None)
@deal.has("read")
def test_model_at_wrong_native_source_is_rejected(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    data["coverage"]["entities"][0]["file"] = "unrelated.ads"
    with pytest.raises(ValueError, match="not analyzed at its declared source"):
        audit_fixture(data)


@deal.post(lambda result: result is None)
@deal.has("read")
def test_duplicate_boundary_and_unknown_native_spec_are_rejected(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    data["register"]["projects"]["hoeflin"].append(data["register"]["projects"]["hoeflin"][0])
    with pytest.raises(ValueError, match="Duplicate ghost boundary"):
        audit_fixture(data)
    data = copy.deepcopy(ghost_fixture)
    data["coverage"]["entities"].append({"name": "Boundary.New", "status": "spec", "file": "boundary.ads"})
    with pytest.raises(ValueError, match="spec-only ghost boundary inventory differs"):
        audit_fixture(data)


@pytest.mark.parametrize("text", [
    "-- Post => Model.Valid (X);\nfunction Value return Boolean;",
    'function Value return String is ("Post => Model.Valid (X)");',
    "function Value return Boolean is begin return Model.Valid (X); end Value;",
    "function Value return Boolean with Post => Other.Valid (X);",
])
@deal.post(lambda result: result is None)
@deal.has()
def test_comment_string_body_or_other_predicate_is_not_a_contract_link(text):
    assert not contract_reference(text, "Model.Valid")
    return None


@deal.post(lambda result: result is None)
@deal.has()
def test_real_pre_post_reference_is_case_insensitive_and_qualified():
    assert contract_reference("procedure P with Pre => MODEL . Valid (X);", "Model.Valid")
    assert contract_reference("function P return Float with Post => Model.Valid (P'Result);", "Model.Valid")
    assert "Model.Valid" not in ada_code('X := "-- Model.Valid"; -- Model.Valid\n')
    return None


@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_changed_source_hash_and_non_ghost_model_are_rejected(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    path = data["root"].joinpath("model.ads")
    path.write_text(path.read_text().replace(", Ghost", ""))
    with pytest.raises(ValueError, match="source hash differs"):
        audit_fixture(data)
    for source in data["sources"]:
        if source["path"] == "model.ads":
            source["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    with pytest.raises(ValueError, match="declared Ghost package"):
        audit_fixture(data)


@deal.post(lambda result: result is None)
@deal.has("read")
def test_unsafe_duplicate_or_invalid_source_inventory_is_rejected(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    data["sources"][0]["path"] = "../outside.ads"
    with pytest.raises(ValueError, match="Unsafe ghost source path"):
        audit_fixture(data)
    data = copy.deepcopy(ghost_fixture)
    data["sources"].append(data["sources"][0])
    with pytest.raises(ValueError, match="Duplicate ghost source"):
        audit_fixture(data)
    with pytest.raises(ValueError, match="No pinned Ada sources"):
        pinned_ada_sources([], ghost_fixture["root"])


@deal.post(lambda result: result is None)
@deal.has()
def test_foreign_import_inventory_ignores_comments_strings_and_parameter_semicolons():
    text = 'package body P is\n-- function Fake with Import;\n'
    text += 'function F (X : Float; Y : Float) return Float with Import, External_Name => "F";\nend P;'
    assert foreign_imports({"p.adb": text}) == {"p.f": "p.adb"}
    return None


@deal.post(lambda result: result is None)
@deal.has()
def test_ghost_body_coupling_ignores_other_and_nested_operations():
    source = "with Model; use Model; package body P is\n"
    source += "procedure Other is begin Model.Observe (1.0); end Other;\n"
    source += "procedure Outer is procedure Nested is begin Model.Observe (1.0); end Nested; begin Nested; end Outer;\n"
    source += "procedure Actual is begin Observe (1.0); end Actual; end P;"
    assert coupling_reference(source, "Model.Observe", "P.Actual", "ghost-call")
    assert not coupling_reference(source, "Model.Observe", "P.Outer", "ghost-call")
    assert coupling_reference(source, "Model.Observe", "P.Outer.Nested", "ghost-call")
    with pytest.raises(ValueError, match="missing or ambiguous"):
        coupling_reference(source, "Model.Observe", "P.Missing", "ghost-call")
    return None


@deal.post(lambda result: result is None)
@deal.has("read")
def test_unregistered_library_or_global_obligation_is_rejected(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    del data["register"]["global_unproved_obligations"]["model-adequacy"]
    with pytest.raises(ValueError, match="Global unproved obligation inventory"):
        audit_fixture(data)
    data = copy.deepcopy(ghost_fixture)
    data["register"]["external_dependencies"]["hoeflin"] = {"ada.text_io": "IO remains unproved."}
    with pytest.raises(ValueError, match="External dependency obligation inventory"):
        audit_fixture(data)


@deal.pre(lambda data, relative, text: isinstance(data, dict) and isinstance(relative, str) and isinstance(text, str))
@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError)
@deal.has("read", "write")
def replace_source(data, relative, text):
    path = data["root"].joinpath(relative)
    path.write_text(text)
    for source in data["sources"]:
        if source["path"] == relative:
            source["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.fixture
@deal.post(lambda result: isinstance(result, dict) and "register" in result)
@deal.raises(OSError, ValueError, Error)
@deal.has("read", "write")
def standard_fixture(ghost_fixture):
    data = copy.deepcopy(ghost_fixture)
    text = data["root"].joinpath("model.ads").read_text().replace(
        "end Model;", "procedure Observe (X : Float) with Pre => Valid (X); end Model;")
    replace_source(data, "model.ads", text)
    text = data["root"].joinpath("boundary.adb").read_text().replace(
        "package body Boundary", "with Ada.Numerics.Long_Elementary_Functions; package body Boundary").replace(
        "end Boundary;", "package Math renames Ada.Numerics.Long_Elementary_Functions;\n"
        "procedure Pair is Cosine,Sine : Float; begin Cosine := Math.Cos (0.0); Model.Observe (Cosine);\n"
        "Sine := Math.Sin (0.0); Model.Observe (Sine); end Pair; end Boundary;")
    replace_source(data, "boundary.adb", text)
    data["coverage"]["entities"] += [{"name": "Model.Observe", "status": "all", "file": "model.ads"},
                                      {"name": "Boundary.Pair", "status": "all", "file": "boundary.adb"}]
    data["register"]["external_dependencies"]["hoeflin"] = {"ada.numerics.long_elementary_functions": "Installed specification is trusted; the implementation remains unproved."}
    data["register"]["standard_library_models"]["hoeflin"] = [{
        "entity": "Ada.Numerics.Long_Elementary_Functions." + callee,
        "model_file": "model.ads", "model_entities": ["Model.Valid", "Model.Observe"],
        "contract_refs": ["Model.Observe"], "contract_file": "boundary.adb", "contract_entity": "Boundary.Pair",
        "observed_argument": argument, "source_callee": "Math." + callee,
        "implementation_proved": False, "model_adequacy_proved": False,
        "obligations": ["Only a checked normal-return property is modeled; no trigonometric accuracy theorem is established."]}
        for callee, argument in [("Cos", "Cosine"), ("Sin", "Sine")]]
    return data


@deal.post(lambda result: result is None)
@deal.has("read")
def test_standard_models_link_both_actual_cached_results(standard_fixture):
    result = audit_fixture(standard_fixture)
    assert len(result["standard_library_models"]) == 2
    assert result["model_adequacy_proved"] is False


@pytest.mark.parametrize("change", ["omit", "wrong-result", "wrong-callee", "unproved-caller", "backend-proof"])
@deal.post(lambda result: result is None)
@deal.has("read")
def test_standard_model_omissions_and_false_links_are_rejected(standard_fixture, change):
    data = copy.deepcopy(standard_fixture)
    entries = data["register"]["standard_library_models"]["hoeflin"]
    if change == "omit":
        entries.pop()
    elif change == "wrong-result":
        entries[0]["observed_argument"] = "Other_Value"
    elif change == "wrong-callee":
        entries[0]["source_callee"] = "Math.Sin"
    elif change == "unproved-caller":
        data["coverage"]["entities"][-1]["status"] = "spec"
    else:
        entries[0]["implementation_proved"] = True
    with pytest.raises(ValueError):
        audit_fixture(data)


@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_standard_observation_before_actual_call_cannot_pass(standard_fixture):
    data = copy.deepcopy(standard_fixture)
    text = data["root"].joinpath("boundary.adb").read_text()
    text = text.replace("Cosine := Math.Cos (0.0); Model.Observe (Cosine);",
                        "Model.Observe (Cosine); Cosine := Math.Cos (0.0);")
    replace_source(data, "boundary.adb", text)
    with pytest.raises(ValueError, match="after its call"):
        audit_fixture(data)


@deal.post(lambda result: result is None)
@deal.has("read", "write")
def test_private_excluded_helper_must_have_its_own_ghost_link(standard_fixture):
    data = copy.deepcopy(standard_fixture)
    text = data["root"].joinpath("boundary.adb").read_text().replace("with SPARK_Mode is", "with SPARK_Mode => Off is")
    text = text.replace("end Boundary;", "procedure Format is begin Model.Observe (1.0); end Format; end Boundary;")
    replace_source(data, "boundary.adb", text)
    # Pair is now an inherited-off helper too: it must be mapped rather than hidden.
    boundary = data["register"]["projects"]["hoeflin"][0]
    boundary["model_entities"].append("Model.Observe")
    boundary["excluded_helpers"] = [{"entity": "Boundary." + name, "contract_file": "boundary.adb",
                                      "contract_refs": ["Model.Observe"], "link_kind": "ghost-call"}
                                     for name in ["Pair", "Format"]]
    assert len(audit_fixture(data)["private_helpers"]) == 2
    boundary["excluded_helpers"].pop()
    with pytest.raises(ValueError, match="Private excluded helper ghost inventory differs"):
        audit_fixture(data)
