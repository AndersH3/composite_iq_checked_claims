"""The symbolic negative control must fail mathematically, never by skipping type checks."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import Mock

import deal
import pytest
from deal_solver import UnsupportedError
from deal_solver._context import Context
from deal_solver._funcs import FUNCTIONS
from deal_solver._funcs._builtins import builtins_int, builtins_float
from deal_solver._proxies import FuncSort, UntypedListSort

from conftest import ROOT, protected_history_intact, reference_inputs_intact
from verification import check_symbolic as symbolic

@pytest.fixture(scope="module")
@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, dict) and result["complete"])
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def good_report() -> dict:
    return symbolic.run(ROOT)


@pytest.fixture
@deal.pre(lambda tmp_path: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, Path) and result.is_dir())
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def copied_root(tmp_path) -> Path:
    for relative in symbolic.EXPECTED:
        target = tmp_path.joinpath(relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(ROOT.joinpath(relative).read_bytes())
    return tmp_path


@deal.pre(lambda good_report: protected_history_intact())
@deal.ensure(lambda good_report, *, result: protected_history_intact())
@deal.ensure(lambda good_report, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_real_fixture_has_a_negative_counterexample_and_all_other_posts_prove(good_report) -> None:
    assert good_report["complete"] and symbolic.accepted(good_report)
    # The ten-contract proof gates each contribute their original equality
    # postcondition and five independently checked safety implications.
    positive = good_report["files"][0]["theorems"]
    assert {row["name"] for row in positive} == {
        "totals_balanced", "successful_checks"}
    assert all(len(row["obligations"]) == 6 for row in positive)
    assert all(obligation["outcome"] == "proved"
               for row in positive for obligation in row["obligations"])
    negative = good_report["files"][1]["theorems"][1]
    assert negative["name"] == "negative_probability"
    assert negative["conclusion"] == "FAIL"
    assert negative["counterexample"] == {} and negative["counterexample"] is not None
    assert [row["outcome"] for row in negative["obligations"]] == ["counterexample", "proved", "proved"]
    # The archived report was emitted by the pinned one-postcondition version.
    # Accept its actual source-bound obligations, but never tolerate removing
    # clauses from a current report or corrupting an archived obligation.
    historical_path = (ROOT / "verification/evidence"
                       / "symbolic-fixture-computer10-20261105/symbolic/result.json")
    historical = json.loads(historical_path.read_text())
    assert symbolic.accepted(historical)
    assert all(len(row["obligations"]) == 1 for row in historical["files"][0]["theorems"])
    corrupted = deepcopy(historical)
    corrupted["files"][0]["theorems"][0]["obligations"][0]["outcome"] = "unsupported"
    assert not symbolic.accepted(corrupted)
    unpinned = deepcopy(historical)
    unpinned["files"][0]["sha256"] = "0" * 64
    unpinned["sources"][0]["sha256"] = "0" * 64
    assert not symbolic.accepted(unpinned)


@deal.pre(lambda good_report: protected_history_intact())
@deal.ensure(lambda good_report, *, result: protected_history_intact())
@deal.ensure(lambda good_report, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_all_inputs_and_contracts_are_source_pinned(good_report) -> None:
    for row in good_report["sources"]:
        raw = ROOT.joinpath(row["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]
    fixture = ROOT.joinpath("tests/fixtures/contract_negative_control.py").read_text()
    assert "@deal.post(lambda result: isinstance(result, int))" in fixture


@pytest.mark.parametrize("value,expected", [
    ("0", ["proved", "proved", "proved"]), ("1", ["proved", "proved", "proved"]),
    ("False", ["proved", "proved", "proved"]), ("True", ["proved", "proved", "proved"]),
    ("-1", ["counterexample", "proved", "proved"]), ("2", ["proved", "proved", "counterexample"]),
    ("0.0", ["proved", "counterexample", "proved"]), ("1.0", ["proved", "counterexample", "proved"]),
])
@deal.pre(lambda copied_root, value, expected: protected_history_intact())
@deal.ensure(lambda copied_root, value, expected, *, result: protected_history_intact())
@deal.ensure(lambda copied_root, value, expected, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_result_mutations_preserve_integer_type_and_both_range_checks(copied_root, value, expected) -> None:
    path = copied_root.joinpath("tests/fixtures/contract_negative_control.py")
    path.write_text(path.read_text().replace("return -1", "return " + value))
    report = symbolic.run(copied_root)
    negative = report["files"][1]["theorems"][1]
    assert [row["outcome"] for row in negative["obligations"]] == expected
    assert report["complete"] is (value == "-1")


@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_registry_is_restored_after_success() -> None:
    before = dict(FUNCTIONS)
    assert symbolic.run(ROOT)["complete"]
    assert FUNCTIONS == before


@deal.pre(lambda monkeypatch: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_registry_is_restored_after_solver_exception(monkeypatch) -> None:
    before = dict(FUNCTIONS)
    monkeypatch.setattr(symbolic, "prove_text", Mock(side_effect=RuntimeError("injected solver failure")))
    with pytest.raises(RuntimeError, match="injected solver failure"):
        symbolic.run(ROOT)
    assert FUNCTIONS == before


@deal.pre(lambda monkeypatch: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_existing_handler_is_not_overwritten(monkeypatch) -> None:
    handler = object()
    monkeypatch.setitem(FUNCTIONS, "builtins.isinstance", handler)
    with pytest.raises(ValueError, match="existing isinstance"):
        symbolic.run(ROOT)
    assert FUNCTIONS["builtins.isinstance"] is handler


@deal.pre(lambda monkeypatch: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_version_mismatch_fails_closed(monkeypatch) -> None:
    monkeypatch.setattr(symbolic.deal_solver, "__version__", "future-version")
    with pytest.raises(ValueError, match="pinned"):
        symbolic.run(ROOT)
    assert "builtins.isinstance" not in FUNCTIONS


@pytest.mark.parametrize("prefix", ["int = float", "isinstance = bool", "from other import int", "import other as isinstance", "def helper(int): return int", "def int(): return 1", "class Custom: pass"])
@deal.pre(lambda prefix: protected_history_intact())
@deal.ensure(lambda prefix, *, result: protected_history_intact())
@deal.ensure(lambda prefix, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_shadowed_builtin_names_are_rejected(prefix) -> None:
    assert not symbolic.source_is_supported(prefix + "\nimport deal\n@deal.post(lambda result: isinstance(result, int))\ndef f():\n return 0\n")


@pytest.mark.parametrize("which", ["classinfo", "sort"])
@deal.pre(lambda which: protected_history_intact())
@deal.ensure(lambda which, *, result: protected_history_intact())
@deal.ensure(lambda which, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_unmodeled_classinfo_and_sorts_fail_closed(which) -> None:
    ctx = Context.make_empty(get_contracts=symbolic.DealTheorem.get_contracts)
    value = UntypedListSort()
    classinfo = FuncSort(builtins_float if which == "classinfo" else builtins_int)
    with pytest.raises(UnsupportedError):
        symbolic.symbolic_isinstance_int(value, classinfo, ctx=ctx)


@pytest.mark.parametrize("change", ["complete", "schema", "adapter", "version", "missing_file", "source_hash", "missing_theorem", "extra_theorem", "missing_model", "exception", "partial", "wrong_kind", "skip_type", "omit_type", "malformed_path", "malformed_name"])
@deal.pre(lambda good_report, change: protected_history_intact())
@deal.ensure(lambda good_report, change, *, result: protected_history_intact())
@deal.ensure(lambda good_report, change, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_report_validator_rejects_changed_or_missing_theorem_evidence(good_report, change) -> None:
    report = deepcopy(good_report)
    negative = report["files"][1]["theorems"][1]
    if change == "complete": report["complete"] = False
    elif change == "schema": report["schema"] = "unknown"
    elif change == "adapter": report["adapter"] = "untrusted"
    elif change == "version": report["toolchain"]["deal_solver"] = "unknown"
    elif change == "missing_file": report["files"].pop()
    elif change == "source_hash": report["sources"][0]["sha256"] = "0" * 64
    elif change == "missing_theorem": report["files"][0]["theorems"].pop()
    elif change == "extra_theorem": report["files"][0]["theorems"].append(deepcopy(negative))
    elif change == "missing_model": negative["counterexample"] = None
    elif change == "exception": negative["error"] = "UnsupportedError"
    elif change == "partial": negative["conclusion"] = "PARTIAL"
    elif change == "wrong_kind": negative["obligations"][0]["kind"] = "assertion"
    elif change == "skip_type": negative["obligations"][1]["outcome"] = "unsupported"
    elif change == "omit_type": negative["obligations"].pop(1)
    elif change == "malformed_path": report["files"][0]["path"] = None
    else: negative["name"] = None
    assert not symbolic.accepted(report)


@deal.pre(lambda copied_root: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_valid_integer_mutation_cannot_pass_as_a_negative_control(copied_root) -> None:
    path = copied_root.joinpath("tests/fixtures/contract_negative_control.py")
    path.write_text(path.read_text().replace("return -1", "return 0"))
    report = symbolic.run(copied_root)
    assert report["files"][1]["theorems"][1]["conclusion"] == "OK"
    assert not report["complete"]


@deal.pre(lambda copied_root: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_unexpected_theorem_cannot_pass(copied_root) -> None:
    path = copied_root.joinpath("verification/proof_gate.py")
    path.write_text(path.read_text() + "\ndef unexpected(value: int) -> int:\n return value\n")
    assert not symbolic.run(copied_root)["complete"]


@deal.pre(lambda copied_root: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: protected_history_intact())
@deal.ensure(lambda copied_root, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_missing_input_is_not_a_success(copied_root) -> None:
    copied_root.joinpath("tests/fixtures/contract_negative_control.py").unlink()
    with pytest.raises(FileNotFoundError):
        symbolic.run(copied_root)
    assert "builtins.isinstance" not in FUNCTIONS


@pytest.mark.parametrize("mode", ["normal", "optimized"])
@deal.pre(lambda mode: protected_history_intact())
@deal.ensure(lambda mode, *, result: protected_history_intact())
@deal.ensure(lambda mode, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import", "syscall", "stdout", "stderr")
def test_symbolic_cli_keeps_contracts_enabled_under_optimization(mode) -> None:
    argv = [sys.executable] + (["-O"] if mode == "optimized" else []) + [str(ROOT / "verification/check_symbolic.py")]
    process = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert process.returncode == 0, process.stderr
    assert symbolic.accepted(json.loads(process.stdout))



@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import")
def test_chained_upper_bound_is_checked_not_silently_discarded() -> None:
    source = "import deal\n@deal.post(lambda result: 0 <= result <= 1)\ndef upper_bound() -> int:\n return 2\n"
    rows = symbolic.prove_text(source)
    assert rows[0]["conclusion"] == "FAIL"
    assert rows[0]["obligations"][0]["outcome"] == "counterexample"
    assert symbolic.normalized_source(source).count("result <= 1") == 1


@pytest.mark.parametrize("middle", ["get_value()", "obj.value", "values[0]"])
@deal.pre(lambda middle: protected_history_intact())
@deal.ensure(lambda middle, *, result: protected_history_intact())
@deal.ensure(lambda middle, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "global", "import")
def test_chains_with_operands_unsafe_to_repeat_are_rejected(middle) -> None:
    source = "import deal\n@deal.post(lambda result: 0 <= " + middle + " <= 1)\ndef f() -> int:\n return 0\n"
    with pytest.raises(UnsupportedError, match="unsafe to repeat"):
        symbolic.normalized_source(source)


@deal.pre(lambda monkeypatch: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: protected_history_intact())
@deal.ensure(lambda monkeypatch, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import")
def test_native_failure_cannot_hide_skipped_statements(monkeypatch) -> None:
    source = "import deal\n@deal.post(lambda result: result >= 0)\ndef f() -> int:\n return -1\n"
    theorem = Mock(spec=symbolic.DealTheorem)
    theorem.prove.return_value = symbolic.Proof(symbolic.Conclusion.FAIL, "post-condition")
    theorem._context = Mock(skips=[UnsupportedError("injected unsupported statement")])
    monkeypatch.setattr(symbolic.DealTheorem, "from_text", Mock(return_value=iter([theorem])))
    with pytest.raises(UnsupportedError, match="skipped source"):
        symbolic.prove_text(source)


@deal.pre(protected_history_intact)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import")
def test_module_executable_code_is_not_silently_ignored() -> None:
    assert not symbolic.source_is_supported("raise RuntimeError('module effect')\n")
    assert not symbolic.source_is_supported("from external import *\n")
    assert not symbolic.source_is_supported("import external\n")


@pytest.mark.parametrize("source", [
    "@deal.post(lambda result: result == 0)\ndef f() -> int:\n return 0\n",
    "import deal\n@print('effect')\n@deal.post(lambda result: result == 0)\ndef f() -> int:\n return 0\n",
    "import deal\n@deal.post(lambda result: result == 0)\ndef f(value: int = print('effect')) -> int:\n return 0\n",
    "import deal\ndef deal(value: int) -> int:\n return value\n",
    "import deal\n@deal.post(check_value)\ndef f() -> int:\n return 0\n",
    "import deal\ndef f() -> int:\n import builtins\n builtins.int = float\n return 0\n",
    "import deal\ndef f(value: custom_type()) -> int:\n return 0\n",
    "import deal\ndef f(value: object) -> int:\n return 0\n",
    "import deal\ndef f(value: int) -> int:\n return print(value)\n",
    "import deal\n@deal.post(lambda result: isinstance(result, float))\ndef f() -> int:\n return 0\n",
    "import deal\n@deal.post(lambda result: result >= 0)\ndef f() -> int:\n return -1\n yield 0\n",
])
@deal.pre(lambda source: protected_history_intact())
@deal.ensure(lambda source, *, result: protected_history_intact())
@deal.ensure(lambda source, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import")
def test_native_extractor_ignored_or_effectful_forms_fail_closed(source) -> None:
    assert not symbolic.source_is_supported(source)
    with pytest.raises(ValueError, match="Unsupported or shadowed"):
        symbolic.prove_text(source)


