"""Independent checks of Dask report moments, event rates and artifact boundaries.

The fixtures use deliberately different replicate centres and denominators so
incorrect averaging or conditional-rate bookkeeping cannot pass by symmetry.
All files written by these tests are disposable scratch artifacts.  Published
reports and historical scientific evidence remain protected by explicit frames.
"""
import copy
import csv
from pathlib import Path

import dask
import dask.array as da
import deal
import pytest
from scipy.stats import binomtest

from conftest import ROOT, protected_history_intact, reference_inputs_intact
from reporting import assets, statistics


HOEFLIN = "hoeflin-ferguson"
TOWERS = "towers-multiple-test-admissions"
SEQUENTIAL = "sequential-conditional-means"


@pytest.fixture
@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, dict) and result["project"] == HOEFLIN)
@deal.post(lambda result: result["n_samples"] == 3 and result["n"] == 2)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def moment_meta():
    """Supply standardized-composite metadata independently of the simulator."""
    return {"project": HOEFLIN, "n_samples": 3, "replicate": 0, "seed": 11,
            "n": 2, "theory_mean": 0.0, "theory_variance": 1.0,
            "theory_sd": 0.8 ** 0.5, "theory_mse": 0.25}


@pytest.fixture
@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, dict) and result["project"] == TOWERS)
@deal.post(lambda result: result["n_samples"] == 1000 and result["p_a"] != result["p_b"])
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def event_meta():
    """Use unequal marginal probabilities to reveal denominator substitutions."""
    return {"project": TOWERS, "n_samples": 1000, "replicate": 0, "seed": 13,
            "case_index": 0, "label": "synthetic_asymmetric",
            "p_a": 0.2, "p_b": 0.3, "theory_joint": 0.1,
            "cutoff_a": 0.0, "cutoff_b": 0.0}


@deal.pre(lambda moment_meta: protected_history_intact())
@deal.pre(lambda moment_meta: reference_inputs_intact())
@deal.pre(lambda moment_meta: isinstance(moment_meta, dict) and moment_meta["n_samples"] == 3)
@deal.ensure(lambda moment_meta, result: protected_history_intact())
@deal.ensure(lambda moment_meta, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "random", "global", "import", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_moment_pool_matches_combined_sample_not_average_of_variances(moment_meta):
    """Between-replicate displacement contributes to pooled unbiased variance."""
    first = statistics.moment_result(moment_meta, -1.0, 1.0, 0.2)
    second_meta = dict(moment_meta, n_samples=2, replicate=1, seed=17)
    second = statistics.moment_result(second_meta, 5.0, 8.0, 0.7)
    untouched = copy.deepcopy([first, second])
    pooled = statistics.pool_rows(HOEFLIN, [first, second])[0]
    # [-2,-1,0] and [3,7] have the moments supplied above. Dask's reduction
    # supplies an independent combined-array calculation with ddof=1.
    combined = da.from_array([-2.0, -1.0, 0.0, 3.0, 7.0], chunks=2)
    expected_mean, expected_variance = dask.compute(combined.mean(), combined.var(ddof=1), scheduler="single-threaded")
    assert pooled["n_samples"] == 5
    assert pooled["mean"] == pytest.approx(float(expected_mean))
    assert pooled["variance"] == pytest.approx(float(expected_variance))
    assert pooled["variance"] != pytest.approx((1.0 + 8.0) / 2)
    assert pooled["mse"] == pytest.approx((3 * 0.2 + 2 * 0.7) / 5)
    assert [first, second] == untouched


@pytest.mark.parametrize("damage", ["duplicate", "theory", "project"])
@deal.pre(lambda moment_meta, damage: protected_history_intact())
@deal.pre(lambda moment_meta, damage: reference_inputs_intact())
@deal.pre(lambda moment_meta, damage: damage in {"duplicate", "theory", "project"})
@deal.ensure(lambda moment_meta, damage, result: protected_history_intact())
@deal.ensure(lambda moment_meta, damage, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_pool_rejects_duplicate_or_incompatible_replicates(moment_meta, damage):
    """One stream cannot be counted twice, and incompatible targets cannot pool."""
    first = statistics.moment_result(moment_meta, 0.0, 1.0)
    second = copy.deepcopy(first)
    if damage == "theory":
        second.update(replicate=1, seed=17, theory_variance=2.0)
    elif damage == "project":
        second.update(replicate=1, seed=17, project=SEQUENTIAL)
    with pytest.raises((ValueError, deal.PreContractError)):
        statistics.pool_rows(HOEFLIN, [first, second])


@pytest.mark.parametrize("field,value", [("mean", float("nan")), ("variance", -0.1), ("mse", -0.1)])
@deal.pre(lambda moment_meta, field, value: protected_history_intact())
@deal.pre(lambda moment_meta, field, value: reference_inputs_intact())
@deal.pre(lambda moment_meta, field, value: field in {"mean", "variance", "mse"})
@deal.ensure(lambda moment_meta, field, value, result: protected_history_intact())
@deal.ensure(lambda moment_meta, field, value, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_invalid_moments_are_rejected(moment_meta, field, value):
    """Nonfinite observations and negative variances/MSEs are not report data."""
    arguments = {"mean": 0.0, "variance": 1.0, "mse": 0.1}
    arguments[field] = value
    with pytest.raises((ValueError, deal.PreContractError)):
        statistics.moment_result(moment_meta, **arguments)


@deal.pre(lambda event_meta: protected_history_intact())
@deal.pre(lambda event_meta: reference_inputs_intact())
@deal.pre(lambda event_meta: isinstance(event_meta, dict) and event_meta["n_samples"] == 1000)
@deal.ensure(lambda event_meta, result: protected_history_intact())
@deal.ensure(lambda event_meta, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "random", "global", "import", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_conditional_intervals_use_observed_marginal_denominators(event_meta):
    """Conditioning on A uses 200 successes of A, not all 1,000 trials."""
    row = statistics.event_result(event_meta, (600, 100, 200, 100))
    assert row["marginal_a"] == 200 and row["marginal_b"] == 300
    assert row["union_count"] == 400
    assert row["joint"] == pytest.approx(0.1)
    assert row["union"] == pytest.approx(0.4)
    assert row["conditional_b_given_a"] == pytest.approx(0.5)
    assert row["conditional_a_given_b"] == pytest.approx(1 / 3)
    reference = dask.delayed(binomtest)(100, 200).proportion_ci(confidence_level=0.95, method="wilson")
    interval = dask.compute(reference, scheduler="single-threaded")[0]
    assert row["conditional_b_given_a_low"] == pytest.approx(interval.low)
    assert row["conditional_b_given_a_high"] == pytest.approx(interval.high)
    assert row["conditional_b_given_a_low"] < 0.5 < row["conditional_b_given_a_high"]


@pytest.mark.parametrize("counts", [(600, 100, 200, 99), (600, 100, 200, 101), (600, -1, 301, 100), (600, 100, 200, True)])
@deal.pre(lambda event_meta, counts: protected_history_intact())
@deal.pre(lambda event_meta, counts: reference_inputs_intact())
@deal.pre(lambda event_meta, counts: isinstance(counts, tuple) and len(counts) == 4)
@deal.ensure(lambda event_meta, counts, result: protected_history_intact())
@deal.ensure(lambda event_meta, counts, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_event_partition_corruption_is_rejected(event_meta, counts):
    """Cells must be integer nonnegative counts partitioning the sample exactly."""
    with pytest.raises((ValueError, deal.PreContractError)):
        statistics.event_result(event_meta, counts)


@deal.pre(lambda event_meta: protected_history_intact())
@deal.pre(lambda event_meta: reference_inputs_intact())
@deal.pre(lambda event_meta: isinstance(event_meta, dict) and event_meta["n_samples"] >= 2)
@deal.ensure(lambda event_meta, result: protected_history_intact())
@deal.ensure(lambda event_meta, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_zero_events_retain_upper_uncertainty_and_undefined_conditionals(event_meta):
    """No observed joint event does not imply zero theoretical probability."""
    row = statistics.event_result(event_meta, (1000, 0, 0, 0))
    assert row["joint"] == 0.0
    assert row["joint_high"] > 0.0
    assert row["exact_joint_low"] == 0.0 < row["exact_joint_high"]
    assert row["conditional_b_given_a"] is None
    assert row["conditional_a_given_b"] is None
    assert row["phi"] is None


@deal.pre(lambda moment_meta: protected_history_intact())
@deal.pre(lambda moment_meta: reference_inputs_intact())
@deal.pre(lambda moment_meta: isinstance(moment_meta, dict) and moment_meta["n_samples"] == 3)
@deal.ensure(lambda moment_meta, result: protected_history_intact())
@deal.ensure(lambda moment_meta, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_nested_hoeflin_tail_counts_and_observation_domains_are_enforced(moment_meta):
    """A more extreme threshold cannot have more exceedances than a lower one."""
    for counts in ((1, 2, 0), (2, 1, 2), (4, 0, 0)):
        with pytest.raises((ValueError, deal.PreContractError)):
            statistics.moment_result(moment_meta, 0.0, 1.0, counts=counts)
    with pytest.raises((ValueError, deal.PreContractError)):
        statistics.moment_result(dict(moment_meta, n_samples=1), 0.0, 1.0)


@pytest.mark.parametrize("value", [float("nan"), float("inf"), -float("inf")])
@deal.pre(lambda value: protected_history_intact())
@deal.pre(lambda value: reference_inputs_intact())
@deal.pre(lambda value: isinstance(value, float))
@deal.ensure(lambda value, result: protected_history_intact())
@deal.ensure(lambda value, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_nonfinite_numbers_cannot_be_formatted_as_report_evidence(value):
    """Formatting must fail rather than conceal NaN or infinity in a table."""
    with pytest.raises((ValueError, deal.PreContractError)):
        assets.format_number(value)


@pytest.mark.parametrize("invalid_key", [1, None, ("column",)])
@deal.pre(lambda tmp_path, invalid_key: protected_history_intact())
@deal.pre(lambda tmp_path, invalid_key: reference_inputs_intact())
@deal.pre(lambda tmp_path, invalid_key: isinstance(tmp_path, Path) and tmp_path.is_dir())
@deal.ensure(lambda tmp_path, invalid_key, result: protected_history_intact())
@deal.ensure(lambda tmp_path, invalid_key, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "write")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_csv_writer_preserves_numeric_rows_and_rejects_heterogeneous_schema(tmp_path, invalid_key):
    """Preserve scalar CSV records and reject invalid keys or differing schemas."""
    destination = tmp_path.joinpath("numeric.csv")
    rows = [{"count": 0, "rate": 0.0}, {"count": 3, "rate": 0.125}]
    untouched = copy.deepcopy(rows)
    # The CSV projection must not mutate full JSON records or drop zero,
    # False, None, or the empty string merely because they are falsey.
    source = [
        {"count": 0, "_meta": {"seed": 42}, "rate": 0.0,
         "flag": False, "missing": None, "label": "", "nested": [1, 2]},
        {"label": "next", "count": 3},
    ]
    original = copy.deepcopy(source)
    projected = assets.public_scalar_rows(source)
    assert projected == [
        {"count": 0, "rate": 0.0, "flag": False, "missing": None, "label": ""},
        {"label": "next", "count": 3},
    ]
    assert list(projected[0]) == ["count", "rate", "flag", "missing", "label"]
    assert projected is not source and projected[0] is not source[0]
    assert source == original
    assert assets.public_scalar_rows([]) == []
    assert assets.public_scalar_rows([{"_hidden": 1}]) == [{}]
    # Parameterized negative cases exercise the runtime precondition, just
    # as the numeric domain tests do, without a statically invalid literal
    # call in the positive Deal lint inventory.
    with pytest.raises(deal.PreContractError):
        assets.public_scalar_rows([{invalid_key: "not a CSV column name"}])
    assets.write_csv(destination, rows)
    with destination.open(newline="", encoding="utf-8") as stream:
        observed = list(csv.DictReader(stream))
    assert len(observed) == 2
    assert int(observed[1]["count"]) == 3
    assert float(observed[1]["rate"]) == pytest.approx(0.125)
    assert rows == untouched
    with pytest.raises((ValueError, deal.PreContractError)):
        assets.write_csv(tmp_path.joinpath("bad.csv"), [{"count": 1}, {"rate": 0.1}])


@pytest.fixture
@deal.pre(lambda: protected_history_intact())
@deal.pre(lambda: reference_inputs_intact())
@deal.post(lambda result: isinstance(result, dict) and result["trials"] == 2000)
@deal.post(lambda result: result["chunk"] == 500 and len(result["seeds"]) == 1)
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def small_config():
    """Retain multiple blocks while making the numerical smoke tests cheap."""
    return {"trials": 2000, "chunk": 500, "seeds": [20261114]}


@pytest.mark.parametrize("project", [HOEFLIN, SEQUENTIAL])
@deal.pre(lambda small_config, project: protected_history_intact())
@deal.pre(lambda small_config, project: reference_inputs_intact())
@deal.pre(lambda small_config, project: project in {HOEFLIN, SEQUENTIAL})
@deal.ensure(lambda small_config, project, result: protected_history_intact())
@deal.ensure(lambda small_config, project, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "write", "random", "global", "import", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_small_dask_moment_graph_is_lazy_reproducible_and_on_correct_scale(small_config, project):
    """Fixed seeds/chunks reproduce rows; whole-vector SDs use the stated scale."""
    from reporting import simulate
    from dask.delayed import Delayed
    builder = simulate.graph_hoeflin if project == HOEFLIN else simulate.graph_sequential
    first_graph = builder(small_config)
    assert first_graph and all(isinstance(row, Delayed) for row in first_graph)
    first = dask.compute(*first_graph, scheduler="single-threaded")
    second = dask.compute(*builder(small_config), scheduler="single-threaded")
    assert first == second
    assert len(first) == (8 if project == HOEFLIN else 24)
    for row in first:
        assert row["n_samples"] == small_config["trials"]
        assert abs(row["mean_error_se"]) < 8
        # These broad fixed-seed smoke bounds detect missing square roots,
        # variance scaling mistakes and forgotten conditioned starting terms.
        assert 0.65 < row["variance"] / row["theory_variance"] < 1.35
    if project == SEQUENTIAL:
        specific = next(row for row in first if (row["r"], row["k"], row["mode"]) == (2, 10, "conditional"))
        assert specific["theory_mean_iq"] == pytest.approx(1675 / 12)
        assert specific["theory_sd_iq"] ** 2 == pytest.approx(475 / 16)
        populations = [row for row in first if row["mode"].startswith("population")]
        assert all(row["theory_mean_iq"] == 100.0 for row in populations)


@deal.pre(lambda small_config: protected_history_intact())
@deal.pre(lambda small_config: reference_inputs_intact())
@deal.pre(lambda small_config: isinstance(small_config, dict) and small_config["trials"] == 2000)
@deal.ensure(lambda small_config, result: protected_history_intact())
@deal.ensure(lambda small_config, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "write", "random", "global", "import", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_small_towers_graph_counts_every_pair_once_in_all_five_cases(small_config):
    """All reference cutoffs stay lazy and classification preserves partitions."""
    from reporting import simulate
    reference = dask.delayed(simulate.reference_data)(TOWERS)
    graph = simulate.graph_towers(small_config, reference)
    rows = dask.compute(*graph, scheduler="single-threaded")
    assert {row["case_index"] for row in rows} == {1, 2, 3, 4, 5}
    assert len(rows) == 5
    for row in rows:
        assert row["neither"] + row["a_only"] + row["b_only"] + row["both"] == 2000
        assert row["marginal_a"] == row["a_only"] + row["both"]
        assert row["marginal_b"] == row["b_only"] + row["both"]
        assert row["union_count"] == 2000 - row["neither"]
        assert row["joint_low"] <= row["joint"] <= row["joint_high"]
    calibrated = next(row for row in rows if row["case_index"] == 5)
    assert calibrated["theory_union"] == pytest.approx(0.02, abs=1e-12)


@pytest.mark.parametrize("change", [{"trials": 1}, {"chunk": 0}, {"seeds": [1, 1]}])
@deal.pre(lambda small_config, change: protected_history_intact())
@deal.pre(lambda small_config, change: reference_inputs_intact())
@deal.pre(lambda small_config, change: isinstance(change, dict) and len(change) == 1)
@deal.ensure(lambda small_config, change, result: protected_history_intact())
@deal.ensure(lambda small_config, change, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read", "write", "random", "global", "import", "syscall")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_invalid_dask_simulation_domains_are_rejected(small_config, change):
    """A replicate needs two observations, valid chunks and distinct seeds."""
    from reporting import simulate
    damaged = dict(small_config, **change)
    with pytest.raises((ValueError, deal.PreContractError)):
        simulate.graph_hoeflin(damaged)


@pytest.mark.parametrize("project", [HOEFLIN, TOWERS])
@deal.pre(lambda moment_meta, event_meta, project: protected_history_intact())
@deal.pre(lambda moment_meta, event_meta, project: reference_inputs_intact())
@deal.pre(lambda moment_meta, event_meta, project: project in {HOEFLIN, TOWERS})
@deal.ensure(lambda moment_meta, event_meta, project, result: protected_history_intact())
@deal.ensure(lambda moment_meta, event_meta, project, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("network", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: len({HOEFLIN,TOWERS,SEQUENTIAL}) == 3)
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","block_simulations.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","simulate.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","assets.py").is_file())
@deal.pre(lambda *args, **kwargs: callable(statistics.moment_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.event_result))
@deal.pre(lambda *args, **kwargs: callable(statistics.pool_rows))
@deal.pre(lambda *args, **kwargs: callable(assets.write_assets))
def test_pool_rejects_individual_corruption_even_if_aggregate_counts_cancel(moment_meta, event_meta, project):
    """Valid-looking totals must not conceal impossible individual replicates."""
    if project == TOWERS:
        first = statistics.event_result(event_meta, (600, 100, 200, 100))
        second = statistics.event_result(dict(event_meta, replicate=1, seed=17), (600, 100, 200, 100))
        # The two damaged cell totals still sum to the pooled sample size.
        first["neither"] -= 1
        second["neither"] += 1
    else:
        first = statistics.moment_result(moment_meta, 0.0, 1.0)
        second = statistics.moment_result(dict(moment_meta, replicate=1, seed=17), 0.0, 1.0)
        # The pooled counts satisfy count2 >= count3, but the first row does not.
        first["count3"] = 1
        second["count2"] = 1
    with pytest.raises(ValueError):
        statistics.pool_rows(project, [first, second])
