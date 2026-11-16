"""Check native/Dask report comparisons and rejection of damaged observations."""
import csv
import json

import dask
import deal
import pytest

from conftest import protected_history_intact, reference_inputs_intact
from reporting import native_audit


@pytest.mark.parametrize("project,expected", list(zip(native_audit.PROJECTS, native_audit.COUNTS, strict=True)))
@deal.pre(lambda project, expected: project in native_audit.PROJECTS)
@deal.pre(lambda project, expected: expected in (8, 4, 46))
@deal.pre(lambda project, expected: protected_history_intact() and reference_inputs_intact())
@deal.ensure(lambda project, expected, result: protected_history_intact())
@deal.ensure(lambda project, expected, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "import", "random", "global", "syscall")
def test_native_case_inventory_and_comparison_denominators(project, expected):
    """Every native row survives; missing Dask cases are explicitly absent."""
    result = dask.compute(dask.delayed(native_audit.audit_project)(project), scheduler="single-threaded")[0]
    assert len(result["rows"]) == expected
    assert result["random_draws_generated"] == 0
    assert result["native_execution_performed"] is False
    if project == native_audit.PROJECTS[2]:
        assert {row["n_samples"] for row in result["rows"]} == {200000}
        assert sum(row["dask_sample_mean"] is not None for row in result["rows"]) == 24
        assert sum(row["dask_sample_mean"] is None for row in result["rows"]) == 22
        deterministic = [row for row in result["rows"] if row["theory_variance"] == 0]
        assert deterministic
        assert all(row["sample_variance"] == 0 for row in deterministic)
        assert all(abs(row["sample_mean"] - row["theory_mean"]) < 1e-8 for row in deterministic)
    elif project == native_audit.PROJECTS[1]:
        assert {row["n_samples"] for row in result["rows"]} == {1000000}
        assert [row["both"] for row in result["rows"]] == [6239, 167, 4, 640]
        assert result["rows"][2]["conditional_b_given_a"] == 4 / 32
        assert result["rows"][2]["conditional_a_given_b"] == 4 / 36
    else:
        assert {row["n_samples"] for row in result["rows"]} == {1000000}
        assert [row["n"] for row in result["rows"]] == [1, 2, 3, 4, 5, 10, 100, 1000]
        assert [row["count_rare"] for row in result["rows"]] == [1, 0, 1, 1, 1, 1, 1, 1]


@pytest.mark.parametrize("damage", ["historical-record", "union", "conditional", "interval"])
@deal.pre(lambda tmp_path, monkeypatch, damage: damage in {"historical-record", "union", "conditional", "interval"})
@deal.pre(lambda tmp_path, monkeypatch, damage: tmp_path.is_dir())
@deal.pre(lambda tmp_path, monkeypatch, damage: protected_history_intact() and reference_inputs_intact())
@deal.ensure(lambda tmp_path, monkeypatch, damage, result: protected_history_intact())
@deal.ensure(lambda tmp_path, monkeypatch, damage, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import", "random", "global", "syscall")
def test_native_audit_rejects_changed_history_and_derived_projections(tmp_path, monkeypatch, damage):
    """A matching copied history cannot conceal a false event projection."""
    source_root = native_audit.ROOT
    source = source_root.joinpath(native_audit.SOURCES[1])
    with source.open(encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    summary_path = source_root.joinpath("analyses", native_audit.PROJECTS[1], "simulation-data", "summary.json")
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    # Three controls modify both copies so raw-record equality passes and
    # the independent projection/interval calculation must detect the fault.
    field = {"historical-record": "both", "union": "union", "conditional": "conditional_b_given_a", "interval": "joint_wilson_lower"}[damage]
    rows[0][field] = str(float(rows[0][field]) + 1)
    if damage != "historical-record":
        summary["historical"] = rows
    target = tmp_path.joinpath(native_audit.SOURCES[1])
    target.parent.mkdir(parents=True)
    with target.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    target_summary = tmp_path.joinpath(summary_path.relative_to(source_root))
    target_summary.parent.mkdir(parents=True)
    target_summary.write_text(json.dumps(summary), encoding="utf-8")
    monkeypatch.setattr(native_audit, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="Native records differ|projection/interval mismatch"):
        dask.compute(dask.delayed(native_audit.audit_project)(native_audit.PROJECTS[1]), scheduler="single-threaded")
