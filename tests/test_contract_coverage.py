"""Audit decorators as syntax, rather than trusting mentions in text."""
import ast
from conftest import protected_history_intact, reference_inputs_intact
import deal
import pytest

from conftest import ROOT


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_finds_a_missing_function_contract(coverage_checker, tmp_path):
    path = tmp_path / "missing.py"
    path.write_text("import deal\n\ndef unchecked(value):\n    return value\n")
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is True
    assert report["function_count"] == 1 and report["contract_count"] == 0
    assert [row["name"] for row in report["missing"]] == ["unchecked"]


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_comments_and_strings_are_not_counted_as_contracts(coverage_checker, tmp_path):
    path = tmp_path / "mentions.py"
    path.write_text('''"""import deal
@deal.post(lambda result: result > 0)
"""
# @deal.pre(lambda value: value > 0)
def unchecked(value):
    return value
''')
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is False and report["contract_count"] == 0
    assert [row["name"] for row in report["missing"]] == ["unchecked"]


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_accepts_a_real_deal_import_alias(coverage_checker, tmp_path):
    path = tmp_path / "aliased.py"
    path.write_text("import deal as contracts\n\n@contracts.post(lambda result: isinstance(result, int))\n"
                    "@contracts.post(lambda result: result > 0)\n"
                    "@contracts.post(lambda result: result <= 1)\n"
                    "@contracts.raises()\n@contracts.has()\n"
                    "def checked():\n    return 1\n")
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is True
    assert report["function_count"] == 1 and report["contract_count"] == 5
    assert report["missing"] == []
    assert report["insufficient"] == []
    # Check the exact AST classification boundaries, not just aggregated
    # counts: only direct imported Deal attribute calls qualify.
    is_deal = coverage_checker.is_contract
    assert is_deal(ast.parse("contracts.post(lambda result: True)", mode="eval").body,
                   {"contracts"})
    assert not is_deal(ast.parse("not_deal.post(lambda result: True)", mode="eval").body,
                       {"contracts"})
    assert not is_deal(ast.parse("post(lambda result: True)", mode="eval").body,
                       {"contracts"})
    assert not is_deal(ast.parse("contracts.wrapped.post(lambda x: True)", mode="eval").body,
                       {"contracts"})
    assert not is_deal(ast.parse("'@contracts.post'", mode="eval").body,
                       {"contracts"})


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_checks_nested_functions(coverage_checker, tmp_path):
    path = tmp_path / "nested.py"
    path.write_text("import deal\n\n@deal.post(lambda result: callable(result))\n"
                    "@deal.post(lambda result: result.__name__ == 'unchecked_inner')\n"
                    "@deal.post(lambda result: result() == 1)\n"
                    "@deal.raises()\n@deal.has()\n"
                    "def checked_outer():\n    def unchecked_inner():\n        return 1\n"
                    "    return unchecked_inner\n")
    report = coverage_checker.audit_file(path)
    assert report["function_count"] == 2 and report["contract_count"] == 5
    assert [row["name"] for row in report["missing"]] == ["unchecked_inner"]


@deal.pre(lambda coverage_checker: protected_history_intact())
@deal.ensure(lambda coverage_checker, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "time", "stdout", "stderr", "import")
def test_every_repository_python_function_has_a_real_contract(coverage_checker):
    files = coverage_checker.python_files(ROOT)
    assert files
    # Preserve strengthened, mathematically motivated contracts in historic
    # independent reference calculations and Ada result validators. The
    # deliberately false negative-control and pinned symbolic theorem inputs
    # are intentionally not forced into the optional ten-contract target.
    targeted = {
        "analyses/hoeflin-ferguson/scripts/verify_calculations.py":
            {"_finite", "variance_factor", "mean_threshold", "_positive_ratio", "_valid_rows",
             "thresholds", "write_csv"},
        "analyses/hoeflin-ferguson/ada/scripts/validate_results.py":
            {"_positive_ratio", "wilson", "csv_rows",
             "validate_calculations", "validate_simulation"},
        "analyses/towers-multiple-test-admissions/scripts/verify_calculations.py":
            {"_finite", "probability_union", "conditional_probability",
             "_valid_fields_rows", "_valid_admissions", "_valid_grid",
             "admission_rows", "basic_grid"},
        "analyses/towers-multiple-test-admissions/ada/validate_results.py":
            {"_open_unit_ratio", "read"},
        "verification/check_contract_coverage.py":
            {"audit_file", "is_contract", "python_files"},
        "verification/spark_coverage.py":
            {"location", "normalize_entity", "unique_object", "read_coverage"},
        "verification/proof_gate.py":
            {"totals_balanced", "successful_checks"},
        "verification/spark_contracts.py":
            {"masked", "split_top", "unparenthesized", "contract_entries",
             "inventory", "ten_contract_summary", "current_sources", "declarations"},
    }
    for path in files:
        report = coverage_checker.audit_file(path)
        assert report["imports_deal"], path
        assert not report["missing"], (path, report["missing"])
        assert not report["insufficient"], (path, report["insufficient"])
        assert not report["duplicated"], (path, report["duplicated"])
        assert report["contract_count"] > 0, path
        target_names = targeted.get(path.relative_to(ROOT).as_posix(), set())
        counts = {entry["name"]: entry["distinct_contract_count"]
                  for entry in report["function_contracts"]}
        assert target_names <= counts.keys(), path
        assert all(counts[name] >= 10 for name in target_names), (path, counts)


@pytest.mark.parametrize("count", range(9))
@deal.pre(lambda coverage_checker, tmp_path, count: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, count, *, result: protected_history_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
@deal.ensure(lambda coverage_checker, tmp_path, count, *, result: reference_inputs_intact())
def test_contract_floor_accepts_five_or_more_distinct_decorators(coverage_checker, tmp_path, count):
    path = tmp_path / "floor.py"
    declarations = ["@deal.has()", "@deal.raises()",
                    "@deal.pre(lambda value: type(value) is int)",
                    "@deal.pre(lambda value: 0 <= value <= 4)",
                    "@deal.ensure(lambda value, result: result == value + 1)",
                    "@deal.post(lambda result: type(result) is int)",
                    "@deal.post(lambda result: 1 <= result <= 5)",
                    "@deal.ensure(lambda value, result: result > value)"]
    path.write_text("import deal\n" + "\n".join(declarations[:count])
                    + "\ndef checked(value):\n    return value + 1\n")
    report = coverage_checker.audit_file(path)
    assert bool(report["insufficient"]) is (count < 5)
    assert report["contract_count"] == count
    assert report["function_contracts"][0]["distinct_contract_count"] == count


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
def test_duplicate_aliases_and_whitespace_do_not_meet_the_floor(coverage_checker, tmp_path):
    path = tmp_path / "duplicates.py"
    path.write_text("import deal\nimport deal as contracts\n"
                    "@deal.post(lambda result: result > 0)\n"
                    "@contracts.post(lambda result: result  >  0)\n"
                    "@deal.post(lambda result: isinstance(result, int))\n"
                    "@deal.raises()\n@deal.has()\n"
                    "def checked():\n    return 1\n")
    report = coverage_checker.audit_file(path)
    assert report["contract_count"] == 5
    row, = report["function_contracts"]
    assert row["distinct_contract_count"] == 4
    assert row["duplicate_contract_count"] == 1
    assert report["insufficient"] == [row]
    assert report["duplicated"] == [row]


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "time", "stdout", "stderr", "import")
def test_empty_python_inventory_cannot_establish_coverage(coverage_checker, tmp_path):
    with pytest.raises(ValueError):
        coverage_checker.python_files(tmp_path)


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result:
             protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result:
             reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall")
def test_python_source_enumeration_rejects_ignored_and_outside_files(
        coverage_checker, tmp_path):
    """A local fallback scan retains only deterministic regular Python sources."""
    first = tmp_path / "first.py"
    nested = tmp_path / "nested" / "second.py"
    ignored = tmp_path / "__pycache__" / "ignored.py"
    for path in (first, nested, ignored):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("pass\n", encoding="utf-8")
    report = coverage_checker.python_files(tmp_path)
    assert report == [first, nested]
    assert all(path.is_file() and path.is_relative_to(tmp_path)
               and not path.is_symlink() for path in report)
