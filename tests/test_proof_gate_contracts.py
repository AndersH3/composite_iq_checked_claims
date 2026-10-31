"""A balanced report must not be mistaken for a completed proof campaign."""
import deal
from hypothesis import given, settings, strategies as st
import pytest

from conftest import ROOT


@pytest.mark.parametrize("returncode,total,unproved,justified,expected", [
    (0, 1, 0, 0, True),
    (0, 0, 0, 0, False),
    (1, 1, 0, 0, False),
    (-9, 1, 0, 0, False),
    (124, 1, 0, 0, False),
    (0, 3, 1, 0, False),
    (0, 3, 0, 1, False),
])
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr')
def test_success_gate_rejects_empty_failed_or_unfinished_runs(
    proof_runner, returncode, total, unproved, justified, expected,
):
    assert proof_runner.successful_checks(returncode, total, unproved, justified) is expected


@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr')
def test_count_gates_reject_negative_counts(proof_runner):
    for index in range(5):
        counts = [0] * 5
        counts[index] = -1
        with pytest.raises(deal.PreContractError):
            proof_runner.totals_balanced(*counts)
    for arguments in ((0, -1, 0, 0), (0, 1, -1, 0), (0, 1, 0, -1)):
        with pytest.raises(deal.PreContractError):
            proof_runner.successful_checks(*arguments)


@settings(max_examples=40, derandomize=True, deadline=None)
@given(flow=st.integers(0, 10_000), proved=st.integers(1, 10_000))
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr')
def test_moving_a_check_to_unproved_preserves_balance_but_rejects_success(proof_runner, flow, proved):
    total = flow + proved
    assert proof_runner.totals_balanced(total, flow, proved, 0, 0)
    assert proof_runner.successful_checks(0, total, 0, 0)
    assert proof_runner.totals_balanced(total, flow, proved-1, 0, 1)
    assert not proof_runner.successful_checks(0, total, 1, 0)
    assert not proof_runner.totals_balanced(total+1, flow, proved, 0, 0)


@pytest.mark.parametrize("project,total", [("hoeflin", 47), ("towers", 31)])
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read')
def test_native_report_parser_accepts_retained_portfolios(proof_runner, project, total):
    path = ROOT / "verification/evidence/computer10-20261031" / project / "portfolio/gnatprove.out"
    report = proof_runner.report_summary(path)
    assert report["categories"]["Total"]["total"] == total
    assert report["categories"]["Total"]["unproved"] == 0
    assert report["categories"]["Total"]["justified"] == 0
    assert report["contains_not_proved"] is False


@pytest.mark.parametrize("text", [
    "Summary without a totals row\n",
    "Total  0  .  .  .  .\n",
    "Total  5  1  1  .  1\n",
    "Total  3  malformed  1  .  1\n",
])
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write')
def test_native_report_parser_rejects_missing_zero_or_inconsistent_totals(proof_runner, tmp_path, text):
    path = tmp_path / "gnatprove.out"
    path.write_text(text)
    with pytest.raises(ValueError):
        proof_runner.report_summary(path)
