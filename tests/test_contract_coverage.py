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
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_coverage_finds_a_missing_function_contract(coverage_checker, tmp_path):
    """Reject a source function that has no actual Deal decorators.
    
    Create an isolated bad module and check the auditor identifies its name and line.
    The check must use parsed syntax, not incidental mentions of a contract.
    """
    path = tmp_path / "missing.py"
    path.write_text("import deal\n\ndef unchecked(value):\n    return value\n")
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is True
    assert report["function_count"] == 1 and report["contract_count"] == 0
    assert [row["name"] for row in report["missing"]] == ["unchecked"]
    assert not report["module_documented"]
    assert [row["name"] for row in report["undocumented"]] == ["unchecked"]


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_comments_and_strings_are_not_counted_as_contracts(coverage_checker, tmp_path):
    """Ensure comments and quoted text cannot spoof a Deal decorator.
    
    The fixture contains decorator-looking prose but no real Deal import.
    A parser-based audit must therefore report zero applicable contracts.
    """
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
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_import_alias_is_recognized_but_five_decorators_are_insufficient(coverage_checker, tmp_path):
    """Check aliased Deal imports without weakening the fifteen-contract floor.
    
    The checker must recognize valid alias syntax and still reject insufficient coverage.
    This prevents implementation-specific import spelling from bypassing the gate.
    """
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
    assert len(report["insufficient"]) == 1
    assert report["insufficient"][0]["distinct_contract_count"] == 5
    assert report["insufficient_file"] is True
    assert report["file_distinct_contract_count"] == 5
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
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_coverage_checks_nested_functions(coverage_checker, tmp_path):
    """Require coverage for named nested functions, not only module-level APIs.
    
    A local function remains an executable Python boundary even when enclosed in another.
    The AST traversal must report its missing or insufficient decorators.
    """
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
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_every_repository_python_function_has_a_real_contract(coverage_checker):
    """Audit every tracked Python source against the canonical Deal requirements.
    
    Require at least fifteen distinct decorator contracts per applicable function.
    Exclude neither production Dask tasks nor maintained tests from the inventory.
    """
    files = coverage_checker.python_files(ROOT)
    assert files
    # Preserve strengthened contracts in maintained Python numerical,
    # Dask and core validation interfaces; retired sources are excluded.
    targeted = {
        "analyses/hoeflin-ferguson/scripts/verify_calculations.py":
            {"variance_factor", "mean_threshold", "_positive_ratio", "_valid_rows",
             "thresholds", "write_csv"},
        "analyses/towers-multiple-test-admissions/scripts/verify_calculations.py":
            {"probability_union", "conditional_probability",
             "_valid_fields_rows", "_valid_admissions", "_valid_grid",
             "admission_rows", "basic_grid", "write_csv"},
        "library/python/numeric.py": {"finite_real"},
        "verification/check_contract_coverage.py":
            {"audit_file", "is_contract", "python_files"},
        "reporting/provenance.py": {"digest", "dump"},
        "reporting/simulate.py": {"reference_data"},
        "reporting/assets.py": {"write_assets"},
    }
    import_only = {"library/__init__.py", "library/python/__init__.py",
                   "reporting/statistics.py"}
    for path in files:
        report = coverage_checker.audit_file(path)
        relpath = path.relative_to(ROOT).as_posix()
        assert report["module_documented"], (path, "missing file-purpose docstring")
        assert not report["undocumented"], (path, report["undocumented"])
        # A module with no named function has no Deal contracts to attach.
        # Reject any other source that silently becomes import-only:
        # every new exception requires an explicit source-ownership review.
        if not report["function_count"]:
            assert relpath in import_only, relpath
            assert report["contract_count"] == 0
            continue
        assert report["imports_deal"], path
        assert not report["missing"], (path, report["missing"])
        assert not report["insufficient"], (path, report["insufficient"])
        assert not report["duplicated"], (path, report["duplicated"])
        assert not report["insufficient_file"], (path, report["file_distinct_contract_count"])
        assert report["file_distinct_contract_count"] >= 15, path
        assert report["minimum_file_contracts"] == 15
        assert report["minimum_contracts"] == 15
        counts = {entry["name"]: entry["distinct_contract_count"]
                  for entry in report["function_contracts"]}
        assert all(count >= 15 for count in counts.values()), (path, counts)
        assert report["contract_count"] > 0, path
        target_names = targeted.get(path.relative_to(ROOT).as_posix(), set())
        assert target_names <= counts.keys(), path
        assert all(counts[name] >= 15 for name in target_names), (path, counts)


@pytest.mark.parametrize("count", (0, 1, 5, 10, 14, 15, 16, 17))
@deal.pre(lambda coverage_checker, tmp_path, count: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, count, *, result: protected_history_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
@deal.ensure(lambda coverage_checker, tmp_path, count, *, result: reference_inputs_intact())
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_contract_floor_accepts_fifteen_or_more_distinct_decorators(coverage_checker, tmp_path, count):
    """Accept fifteen or more distinct decorators without requiring an exact count.

    Construct several small, fully parsed source files around the mandatory
    boundary and reject counts below fifteen while allowing larger numbers.
    The rule is a lower bound, never a quota or an upper limit.
    """
    path = tmp_path / "floor.py"
    declarations = ["@deal.has()", "@deal.raises()",
                    "@deal.pre(lambda value: type(value) is int)",
                    "@deal.pre(lambda value: 0 <= value <= 4)",
                    "@deal.ensure(lambda value, result: result == value + 1)",
                    "@deal.post(lambda result: type(result) is int)",
                    "@deal.post(lambda result: 1 <= result <= 5)",
                    "@deal.ensure(lambda value, result: result > value)"]
    declarations.extend(f"@deal.ensure(lambda value, result, bound={i}: result >= bound)"
                        for i in range(10))
    path.write_text("import deal\n" + "\n".join(declarations[:count])
                    + "\ndef checked(value):\n    return value + 1\n")
    report = coverage_checker.audit_file(path)
    assert bool(report["insufficient"]) is (count < 15)
    assert report["minimum_contracts"] == 15
    assert report["insufficient_file"] is (count < 15)
    assert report["contract_count"] == count
    assert report["function_contracts"][0]["distinct_contract_count"] == count


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_aggregate_contracts_never_mask_below_minimum_functions(
        coverage_checker, tmp_path):
    """A 15-contract aggregate cannot mask two below-15 callables."""
    path = tmp_path / "aggregate.py"
    decorators = [
        "@deal.raises()", "@deal.has()",
        "@deal.post(lambda result: isinstance(result, int))",
        "@deal.post(lambda result: result == 1)",
        "@deal.post(lambda result: result >= 0)",
        "@deal.post(lambda result: result <= 1)",
        "@deal.post(lambda result: result != 0)",
        "@deal.post(lambda result: result in (1,))",
    ]
    for last in (7, 8):
        parts = ["import deal", ""]
        for name, count in (("first", 7), ("second", last)):
            parts.extend(decorators[:count])
            parts.extend([f"def {name}():", "    return 1", ""])
        path.write_text("\n".join(parts), encoding="utf-8")
        report = coverage_checker.audit_file(path)
        assert report["function_count"] == 2
        assert len(report["insufficient"]) == 2
        assert not report["duplicated"]
        assert report["file_distinct_contract_count"] == 7 + last
        assert report["insufficient_file"] is (last == 7)


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_duplicate_aliases_and_whitespace_do_not_meet_the_floor(coverage_checker, tmp_path):
    """Reject duplicate AST-equivalent Deal contracts despite formatting differences.
    
    Repeated equivalent predicates or import aliases do not increase coverage.
    Only distinct proof obligations can satisfy the mandatory lower bound.
    """
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
    assert report["insufficient_file"] is True
    assert report["duplicated"] == [row]

    # A closed predicate must not evade duplicate detection by changing only
    # its unused lambda signature or by accepting arbitrary keyword arguments.
    closed = tmp_path / "closed_lambda_duplicates.py"
    closed.write_text(
        "import deal\n"
        "@deal.pre(lambda: 1 == 1)\n"
        "@deal.pre(lambda *args, **kwargs: 1 == 1)\n"
        "@deal.post(lambda result: result is True)\n"
        "def checked():\n    return True\n"
    )
    closed_report = coverage_checker.audit_file(closed)
    closed_row, = closed_report["function_contracts"]
    assert closed_row["duplicate_contract_count"] == 1
    assert closed_row["distinct_contract_count"] == 2
    assert closed_report["duplicated"] == [closed_row]


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "time", "stdout", "stderr", "import")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
def test_empty_python_inventory_cannot_establish_coverage(coverage_checker, tmp_path):
    """Ensure the repository-wide audit cannot pass vacuously on no files.
    
    An empty or inaccessible source inventory must raise a validation error.
    This protects the verification result from incomplete repository enumeration.
    """
    with pytest.raises(ValueError):
        coverage_checker.python_files(tmp_path)


@deal.pre(lambda coverage_checker, tmp_path: protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result:
             protected_history_intact())
@deal.ensure(lambda coverage_checker, tmp_path, *, result:
             reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","contract_negative_control.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","fixtures","nonzero_division_lint_probe.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","test_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("tests","conftest.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath(".github","workflows","python-contracts.yml").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("requirements-dev.txt").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","numeric.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("library","python","statistics.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","provenance.py").is_file())
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
