"""The explicit Ada contract floor is structural and must fail closed."""
from conftest import ROOT, protected_history_intact, reference_inputs_intact

import deal
import pytest

from verification.spark_contracts import (
    clauses, contract_entries, current_sources, inventory, masked,
)

SPEC = """package P with SPARK_Mode is
function F (X : Integer) return Integer with
  Global => null,
  Depends => (F'Result => X),
  Pre => X >= 0,
  Post => F'Result >= 0 and then F'Result = X;
end P;
"""
BODY = """package body P with SPARK_Mode is
function F (X : Standard.Integer) return Standard.Integer is
begin
  return X;
end F;
end P;
"""


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_mask_preserves_locations_and_ignores_comments_strings_and_characters():
    source = '-- function Fake with Post => True;\nX := "procedure Hidden; ""quoted""";\nC := \'x\';\n'
    result = masked(source)
    assert len(result) == len(source)
    assert [i for i, char in enumerate(result) if char == "\n"] == [
        i for i, char in enumerate(source) if char == "\n"]
    assert "Fake" not in result and "Hidden" not in result and "quoted" not in result
    assert "X :=" in result and "C :=" in result


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_forward_declaration_pairs_with_body_and_qualified_parameter_types():
    result = inventory({"p.ads": SPEC, "p.adb": BODY})
    assert result["complete"] and result["minimum_observed"] == 5
    row, = result["entities"]
    assert row["identity"] == "p.f" and row["path"] == "p.ads"
    assert row["contract_count"] == 5


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_overloaded_names_are_rejected_instead_of_merged():
    overloaded = SPEC.replace("end P;", "function F (X : Float) return Float;\nend P;")
    with pytest.raises(ValueError, match="Overloaded"):
        inventory({"p.ads": overloaded})


@pytest.mark.parametrize("count,complete", [(4, False), (5, True)])
@deal.pre(lambda count, complete: protected_history_intact())
@deal.ensure(lambda count, complete, *, result: protected_history_intact())
@deal.ensure(lambda count, complete, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_four_clauses_fail_and_five_pass(count, complete):
    source = SPEC if count == 5 else SPEC.replace("  Pre => X >= 0,\n", "")
    result = inventory({"p.ads": source})
    assert result["minimum_observed"] == count
    assert result["complete"] is complete
    assert result["insufficient"] == ([] if complete else ["p.f"])


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_ghost_mode_ranges_and_body_assertions_do_not_count():
    source = """package P with SPARK_Mode is
subtype Small is Integer range 1 .. 5;
function F (X : Small) return Small with Ghost, SPARK_Mode => On;
end P;
"""
    body = """package body P with SPARK_Mode is
function F (X : Small) return Small is
begin pragma Assert (X > 0); return X; end F;
end P;
"""
    result = inventory({"p.ads": source, "p.adb": body})
    assert result["minimum_observed"] == 0 and not result["complete"]
    assert result["contracts"] == 0


@pytest.mark.parametrize("text,expected", [
    ("((A and then B))", ["A", "B"]),
    ("(A and then B) and then C", ["(A and then B)", "C"]),
    ("(if A then B and then C else D)", ["if A then B and then C else D"]),
    ("(for all X in Y => P (X) and then Q (X))", ["for all X in Y => P (X) and then Q (X)"]),
])
@deal.pre(lambda text, expected: protected_history_intact())
@deal.ensure(lambda text, expected, *, result: protected_history_intact())
@deal.ensure(lambda text, expected, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_top_level_conjunctions_and_atomic_conditionals(text, expected):
    assert clauses(text) == expected


@pytest.mark.parametrize("text", ["", "()", "   "])
@deal.pre(lambda text: protected_history_intact())
@deal.ensure(lambda text, *, result: protected_history_intact())
@deal.ensure(lambda text, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_empty_behavioral_clauses_are_rejected(text):
    with pytest.raises(ValueError, match="Empty"):
        clauses(text)


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_repeated_clauses_are_rejected_despite_case_and_whitespace():
    with pytest.raises(ValueError, match="Repeated explicit"):
        contract_entries({"pre": "X > 0 and then (x  >  0)"})


@pytest.mark.parametrize("literal", ["True", "False"])
@deal.pre(lambda literal: protected_history_intact())
@deal.ensure(lambda literal, *, result: protected_history_intact())
@deal.ensure(lambda literal, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_literal_boolean_padding_is_rejected(literal):
    with pytest.raises(ValueError, match="Literal Boolean padding"):
        contract_entries({"pre": literal})


@pytest.mark.parametrize("status", ["all", "spec"])
@deal.pre(lambda status: protected_history_intact())
@deal.ensure(lambda status, *, result: protected_history_intact())
@deal.ensure(lambda status, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_native_source_locations_match_both_specification_and_body(status):
    coverage = {"entities": [
        {"name": "P.F", "status": status, "file": "p.ads", "line": 2,
         "sloc": [{"file": "p.ads", "line": 2}, {"file": "p.adb", "line": 2}]},
    ]}
    result = inventory({"p.ads": SPEC, "p.adb": BODY}, coverage)
    assert result["native_cross_check"] and result["complete"]
    row, = result["entities"]
    assert row["native_statuses"] == [status]


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_missing_native_entity_cannot_establish_complete_coverage():
    result = inventory({"p.ads": SPEC}, {"entities": []})
    assert result["native_cross_check"] and not result["complete"]
    assert result["missing_native"] == ["p.f"]


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_native_non_spark_status_cannot_establish_complete_coverage():
    coverage = {"entities": [{"name": "P.F", "status": "no", "file": "p.ads", "line": 2,
                              "sloc": [{"file": "p.ads", "line": 2}]}]}
    result = inventory({"p.ads": SPEC}, coverage)
    assert not result["complete"] and result["invalid_native"] == ["p.f"]


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_unmatched_native_subprogram_cannot_disappear_from_the_floor():
    coverage = {"entities": [{"name": "P.F", "status": "all", "file": "p.ads", "line": 2,
                              "sloc": [{"file": "p.ads", "line": 2}]},
                             {"name": "P.Hidden", "status": "all", "file": "p.ads", "line": 3,
                              "sloc": [{"file": "p.ads", "line": 3}]}]}
    result = inventory({"p.ads": SPEC}, coverage)
    assert not result["complete"] and result["unmatched_native"] == ["P.Hidden"]


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_native_package_interface_is_explicitly_outside_the_subprogram_floor():
    coverage = {"entities": [{"name": "P.F", "status": "all", "file": "p.ads", "line": 2,
                              "sloc": [{"file": "p.ads", "line": 2}]},
                             {"name": "P", "status": "spec", "file": "p.ads", "line": 1,
                              "sloc": [{"file": "p.ads", "line": 1}]}]}
    result = inventory({"p.ads": SPEC}, coverage)
    assert result["complete"] and not result["unmatched_native"]


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_unsupported_mode_pragmas_fail_closed():
    with pytest.raises(ValueError, match="Pragma SPARK_Mode"):
        inventory({"p.ads": SPEC.replace("function F", "pragma SPARK_Mode (Off);\nfunction F")})


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_off_completion_keeps_the_explicit_interface_in_the_inventory():
    body = BODY.replace("package body P with SPARK_Mode is", "package body P with SPARK_Mode => Off is")
    result = inventory({"p.ads": SPEC, "p.adb": body})
    assert result["complete"] and len(result["entities"]) == 1
    row, = result["excluded_completions"]
    assert row["name"] == "F" and row["path"] == "p.adb"


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_contract_case_alternatives_count_as_distinct_behavioral_clauses():
    result = contract_entries({"global": "null", "depends": "(F'Result => X)",
                               "pre": "X >= 0", "contract_cases": "(X = 0 => F'Result = 0, X > 0 => F'Result > 0)"})
    assert len(result) == 5
    assert [row["aspect"] for row in result].count("contract_cases") == 2


@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_all_current_ada_interfaces_meet_the_explicit_contract_floor():
    result = inventory(current_sources(ROOT))
    assert result["complete"], result["insufficient"]
    assert result["minimum_observed"] >= 5
    assert result["functions"] > 0 and result["procedures"] > 0


@pytest.mark.parametrize("position", ["before_key", "within_clause", "duplicate_padding"])
@deal.pre(lambda position: protected_history_intact())
@deal.ensure(lambda position, *, result: protected_history_intact())
@deal.ensure(lambda position, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_aspect_comments_neither_hide_nor_pad_contracts(position):
    if position == "duplicate_padding":
        with pytest.raises(ValueError, match="Repeated"):
            contract_entries({"post": "X >= 0 and then X >= 0 -- extra words\n"})
    else:
        source = SPEC.replace("Pre =>", "-- Post => True is a comment\n Pre =>") if position == "before_key" else SPEC.replace("and then", "-- Post => True is a comment\n and then")
        result = inventory({"p.ads": source, "p.adb": BODY})
        assert result["complete"]
        assert result["entities"][0]["contract_count"] == 5
    return None
