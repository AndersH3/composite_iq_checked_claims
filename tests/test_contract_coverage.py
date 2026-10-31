"""Audit decorators as syntax, rather than trusting mentions in text."""
import deal
import pytest

from conftest import ROOT


@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_finds_a_missing_function_contract(coverage_checker, tmp_path):
    path = tmp_path / "missing.py"
    path.write_text("import deal\n\ndef unchecked(value):\n    return value\n")
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is True
    assert report["function_count"] == 1 and report["contract_count"] == 0
    assert [row["name"] for row in report["missing"]] == ["unchecked"]


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


@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_accepts_a_real_deal_import_alias(coverage_checker, tmp_path):
    path = tmp_path / "aliased.py"
    path.write_text("import deal as contracts\n\n@contracts.post(lambda result: result > 0)\n"
                    "def checked():\n    return 1\n")
    report = coverage_checker.audit_file(path)
    assert report["imports_deal"] is True
    assert report["function_count"] == report["contract_count"] == 1
    assert report["missing"] == []


@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "import")
def test_coverage_checks_nested_functions(coverage_checker, tmp_path):
    path = tmp_path / "nested.py"
    path.write_text("import deal\n\n@deal.post(lambda result: callable(result))\n"
                    "def checked_outer():\n    def unchecked_inner():\n        return 1\n"
                    "    return unchecked_inner\n")
    report = coverage_checker.audit_file(path)
    assert report["function_count"] == 2 and report["contract_count"] == 1
    assert [row["name"] for row in report["missing"]] == ["unchecked_inner"]


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "time", "stdout", "stderr", "import")
def test_every_repository_python_function_has_a_real_contract(coverage_checker):
    files = coverage_checker.python_files(ROOT)
    assert files
    for path in files:
        report = coverage_checker.audit_file(path)
        assert report["imports_deal"], path
        assert not report["missing"], (path, report["missing"])
        assert report["contract_count"] > 0, path


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "time", "stdout", "stderr", "import")
def test_empty_python_inventory_cannot_establish_coverage(coverage_checker, tmp_path):
    with pytest.raises(ValueError):
        coverage_checker.python_files(tmp_path)
