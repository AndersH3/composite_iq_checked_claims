"""Exercise the actual lint process and its fail-closed acceptance boundary."""
from conftest import protected_history_intact, reference_inputs_intact
from copy import deepcopy
from types import ModuleType
import sys

import deal
import pytest

from conftest import ROOT, load_script


@pytest.fixture(scope="module")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, ModuleType)
           and callable(result.lint_paths) and callable(result.accepted))
@deal.has("read", "write", "import", "global")
def lint_checker():
    return load_script("checked_static_lint", "verification/check_static_lint.py")


@pytest.fixture(scope="module")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, ModuleType) and callable(result.safe_half))
@deal.has("read", "write", "import", "global")
def division_probe():
    return load_script("checked_lint_positive", "tests/fixtures/nonzero_division_lint_probe.py")


@pytest.fixture(scope="module")
@deal.pre(lambda lint_checker: protected_history_intact())
@deal.ensure(lambda lint_checker, *, result: protected_history_intact())
@deal.ensure(lambda lint_checker, *, result: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, tuple) and len(result) == 2)
@deal.has("read", "syscall")
def control_reports(lint_checker):
    positive = lint_checker.lint_paths(ROOT, [ROOT.joinpath("tests/fixtures/nonzero_division_lint_probe.py")])
    negative = lint_checker.lint_paths(ROOT, [ROOT.joinpath(lint_checker.NEGATIVE_CONTROL)])
    return positive, negative


@deal.pre(lambda lint_checker, control_reports: protected_history_intact())
@deal.ensure(lambda lint_checker, control_reports, *, result: protected_history_intact())
@deal.ensure(lambda lint_checker, control_reports, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "syscall")
def test_real_positive_and_negative_lint_controls_are_accepted(lint_checker, control_reports):
    positive, negative = control_reports
    assert positive["returncode"] == 0 and positive["diagnostics"] == []
    assert negative["returncode"] == 1
    assert lint_checker.accepted(positive, negative)


@pytest.mark.parametrize("field,value", [("returncode", 0), ("diagnostics", []),
                                         ("stderr", "linter crashed")])
@deal.pre(lambda lint_checker, control_reports, field, value: protected_history_intact())
@deal.ensure(lambda lint_checker, control_reports, field, value, *, result: protected_history_intact())
@deal.ensure(lambda lint_checker, control_reports, field, value, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("io")
def test_missing_or_broken_negative_diagnostic_cannot_pass(lint_checker, control_reports, field, value):
    positive, negative = deepcopy(control_reports)
    negative[field] = value
    assert not lint_checker.accepted(positive, negative)


@deal.pre(lambda lint_checker, tmp_path, control_reports: protected_history_intact())
@deal.ensure(lambda lint_checker, tmp_path, control_reports, *, result: protected_history_intact())
@deal.ensure(lambda lint_checker, tmp_path, control_reports, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall")
def test_new_unsafe_implementation_is_reported_by_the_real_linter(lint_checker, tmp_path, control_reports):
    broken = tmp_path.joinpath("broken.py")
    broken.write_text("import deal\n\n@deal.raises()\n@deal.has()\n"
                      "def reciprocal():\n    return 1.0 / 0.0\n")
    positive = lint_checker.lint_paths(tmp_path, [broken])
    assert positive["returncode"] != 0
    assert any(row["code"] == "DEL021" and row["value"] == "ZeroDivisionError"
               for row in positive["diagnostics"])
    assert not lint_checker.accepted(positive, control_reports[1])


@deal.pre(lambda lint_checker, tmp_path, monkeypatch: protected_history_intact())
@deal.ensure(lambda lint_checker, tmp_path, monkeypatch, *, result: protected_history_intact())
@deal.ensure(lambda lint_checker, tmp_path, monkeypatch, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "global")
def test_missing_negative_control_cannot_pass(lint_checker, tmp_path, monkeypatch):
    tmp_path.joinpath("only.py").write_text("import deal\n\n@deal.has()\ndef okay():\n    return None\n")
    monkeypatch.setattr(sys, "argv", ["check_static_lint.py", "--root", str(tmp_path)])
    with pytest.raises(ValueError, match="negative control is missing"):
        lint_checker.main()


@deal.pre(lambda division_probe: protected_history_intact())
@deal.ensure(lambda division_probe, *, result: protected_history_intact())
@deal.ensure(lambda division_probe, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("io")
def test_division_control_checks_its_domain_without_changing_arithmetic(division_probe):
    assert division_probe.safe_half() == 0.5
    assert division_probe.positive_ratio(1.0, 1.5) == 1.0 / 1.5
    with pytest.raises(deal.PreContractError):
        division_probe.positive_ratio(1.0, 0.0)
