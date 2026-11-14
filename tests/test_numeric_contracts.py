"""Check domain rejection and independent mathematical properties."""
from conftest import protected_history_intact, reference_inputs_intact
import math
import csv

import deal
from hypothesis import given, settings, strategies as st
import pytest
from scipy.stats import norm

PROPERTY = settings(max_examples=40, derandomize=True, deadline=None)
UNIT = st.floats(min_value=0, max_value=1, allow_nan=False, allow_infinity=False)


@pytest.mark.parametrize("n,rho", [
    (0, .6), (-1, .6), (1_000_001, .6), (True, .6), (1.5, .6),
    (3, -.1), (3, 1.1), (3, math.nan), (3, math.inf), (3, True),
])
@deal.pre(lambda hoeflin, n, rho: protected_history_intact())
@deal.ensure(lambda hoeflin, n, rho, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, n, rho, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_variance_rejects_invalid_domain(hoeflin, n, rho):
    with pytest.raises(deal.PreContractError):
        hoeflin.variance_factor(n, rho)


@pytest.mark.parametrize("quantile", [-1.0, 10.1, math.nan, math.inf, True])
@deal.pre(lambda hoeflin, quantile: protected_history_intact())
@deal.ensure(lambda hoeflin, quantile, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, quantile, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_threshold_rejects_invalid_quantile(hoeflin, quantile):
    with pytest.raises(deal.PreContractError):
        hoeflin.mean_threshold(3, .6, quantile)


@PROPERTY
@given(n=st.integers(1, 1_000_000), rho=UNIT)
@deal.pre(lambda hoeflin, n, rho: protected_history_intact())
@deal.ensure(lambda hoeflin, n, rho, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, n, rho, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_variance_between_independent_and_identical_limits(hoeflin, n, rho):
    factor = hoeflin.variance_factor(n, rho)
    assert 1/n - 2e-15 <= factor <= 1 + 2e-15
    assert rho - 2e-15 <= factor
    assert hoeflin.variance_factor(n, 0.0) == pytest.approx(1/n, abs=2e-15)
    assert hoeflin.variance_factor(n, 1.0) == pytest.approx(1.0, abs=2e-15)


@PROPERTY
@given(n=st.integers(1, 500_000), extra=st.integers(1, 500_000), rho=UNIT)
@deal.pre(lambda hoeflin, n, extra, rho: protected_history_intact())
@deal.ensure(lambda hoeflin, n, extra, rho, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, n, extra, rho, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_more_tests_reduce_required_mean_at_fixed_correlation(hoeflin, n, extra, rho):
    assert hoeflin.mean_threshold(n + extra, rho, 4.753424308822899) <= (
        hoeflin.mean_threshold(n, rho, 4.753424308822899) + 2e-14
    )


@PROPERTY
@given(rho=UNIT, quantile=st.floats(0, 10, allow_nan=False, allow_infinity=False))
@deal.pre(lambda hoeflin, rho, quantile: protected_history_intact())
@deal.ensure(lambda hoeflin, rho, quantile, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, rho, quantile, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_one_test_is_unaffected_by_intertest_correlation(hoeflin, rho, quantile):
    assert hoeflin.variance_factor(1, rho) == pytest.approx(1.0, abs=2e-15)
    assert hoeflin.mean_threshold(1, rho, quantile) == pytest.approx(quantile, abs=2e-14)


@deal.pre(lambda hoeflin: protected_history_intact())
@deal.ensure(lambda hoeflin, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read')
def test_corrected_hundred_test_threshold_and_stored_table(hoeflin):
    z = hoeflin.mean_threshold(100, .6, float(norm.isf(1e-6)))
    assert z == pytest.approx(3.69423953831691, abs=2e-13)
    assert not math.isclose(z, 3.71, abs_tol=.001)
    rows = hoeflin.thresholds()
    hoeflin.verify_csv(rows)
    hoeflin.verify_source_values(rows)
    hoeflin.verify_examples()


@pytest.mark.parametrize("p_a,p_b,joint", [
    (.2, .3, -.1), (.2, .3, .4), (.8, .8, .5), (math.nan, .2, 0),
    (.2, math.inf, 0), (True, .2, 0),
])
@deal.pre(lambda towers, p_a, p_b, joint: protected_history_intact())
@deal.ensure(lambda towers, p_a, p_b, joint, *, result: protected_history_intact())
@deal.ensure(lambda towers, p_a, p_b, joint, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_union_rejects_impossible_probabilities(towers, p_a, p_b, joint):
    with pytest.raises(deal.PreContractError):
        towers.probability_union(p_a, p_b, joint)


@pytest.mark.parametrize("joint,marginal", [
    (0, 0), (.3, .2), (-.1, .2), (math.nan, .2), (.1, math.inf), (False, .2),
])
@deal.pre(lambda towers, joint, marginal: protected_history_intact())
@deal.ensure(lambda towers, joint, marginal, *, result: protected_history_intact())
@deal.ensure(lambda towers, joint, marginal, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_conditional_rejects_invalid_domain(towers, joint, marginal):
    with pytest.raises(deal.PreContractError):
        towers.conditional_probability(joint, marginal)


@PROPERTY
@given(a=st.sets(st.integers(0, 15)), b=st.sets(st.integers(0, 15)))
@deal.pre(lambda towers, a, b: protected_history_intact())
@deal.ensure(lambda towers, a, b, *, result: protected_history_intact())
@deal.ensure(lambda towers, a, b, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_union_matches_independent_finite_set_counting(towers, a, b):
    # Dyadic probabilities avoid ambiguity at floating Frechet boundaries.
    value = towers.probability_union(len(a)/16, len(b)/16, len(a & b)/16)
    assert value == len(a | b)/16
    if a:
        assert towers.conditional_probability(len(a & b)/16, len(a)/16) == (
            len(a & b)/len(a)
        )


@pytest.mark.parametrize("a,b,rho", [
    (math.nan, 1, .7), (1, math.inf, .7), (9, 1, .7),
    (1, 1, 1.0), (1, 1, -.951), (True, 1, .7),
])
@deal.pre(lambda towers, a, b, rho: protected_history_intact())
@deal.ensure(lambda towers, a, b, rho, *, result: protected_history_intact())
@deal.ensure(lambda towers, a, b, rho, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_joint_tail_rejects_invalid_domain(towers, a, b, rho):
    with pytest.raises(deal.PreContractError):
        towers.joint_tail(a, b, rho)


@PROPERTY
@given(a=st.floats(0, 4, allow_nan=False, allow_infinity=False),
       b=st.floats(0, 4, allow_nan=False, allow_infinity=False))
@deal.pre(lambda towers, a, b: protected_history_intact())
@deal.ensure(lambda towers, a, b, *, result: protected_history_intact())
@deal.ensure(lambda towers, a, b, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_independent_gaussian_tail_factorizes(towers, a, b):
    assert towers.joint_tail(a, b, 0.0) == pytest.approx(norm.sf(a)*norm.sf(b), abs=1e-14)


@PROPERTY
@given(a=st.floats(0, 4, allow_nan=False, allow_infinity=False),
       b=st.floats(0, 4, allow_nan=False, allow_infinity=False),
       rho=st.floats(-.5, .8, allow_nan=False, allow_infinity=False))
@deal.pre(lambda towers, a, b, rho: protected_history_intact())
@deal.ensure(lambda towers, a, b, rho, *, result: protected_history_intact())
@deal.ensure(lambda towers, a, b, rho, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_joint_tail_is_symmetric_and_bounded(towers, a, b, rho):
    result = towers.joint_tail(a, b, rho)
    assert result == pytest.approx(towers.joint_tail(b, a, rho), abs=1e-14)
    assert 0 <= result <= min(norm.sf(a), norm.sf(b)) + 1e-14


@pytest.mark.parametrize("p_a,p_b,expected", [
    (.02, .02, .006276274020528095),
    (.02, .001, .0006585888039150674),
])
@deal.pre(lambda towers, p_a, p_b, expected: protected_history_intact())
@deal.ensure(lambda towers, p_a, p_b, expected, *, result: protected_history_intact())
@deal.ensure(lambda towers, p_a, p_b, expected, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_admission_reference_overlaps(towers, p_a, p_b, expected):
    result = towers.joint_tail(float(norm.isf(p_a)), float(norm.isf(p_b)), .7)
    assert result == pytest.approx(expected, abs=1e-14)


@deal.pre(lambda towers: protected_history_intact())
@deal.ensure(lambda towers, *, result: protected_history_intact())
@deal.ensure(lambda towers, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', "read")
def test_higher_correlation_increases_mixed_overlap(towers):
    a, b = float(norm.isf(.02)), float(norm.isf(.001))
    results = [towers.joint_tail(a, b, r) for r in (.3, .5, .7, .9)]
    assert all(left < right for left, right in zip(results, results[1:]))


@deal.pre(lambda towers: protected_history_intact())
@deal.ensure(lambda towers, *, result: protected_history_intact())
@deal.ensure(lambda towers, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read')
def test_towers_reference_csvs(towers):
    admissions, grid = towers.admission_rows(), towers.basic_grid()
    # Independent table-level provenance and arithmetic laws: these
    # guards fail even if a stale CSV happens to contain plausible totals.
    assert [row["case"] for row in admissions] == [
        label for label, _, _ in towers.CASES]
    assert all(row["rho"] == towers.RHO for row in admissions)
    assert all(row["union"] == row["p_a"] + row["p_b"] - row["joint"]
               for row in admissions)
    assert [row["cutoff_iq"] for row in grid] == [133, 150, 164]
    assert all(row["grid_minus_published"] ==
               row["grid_joint"] - row["published_joint"] for row in grid)
    assert all(row["grid_conditional"] ==
               row["grid_joint"] / row["grid_marginal"] for row in grid)
    towers.verify_csv(towers.ROOT / "data/admission_probabilities.csv", towers.ADMISSION_FIELDS, admissions)
    towers.verify_csv(towers.ROOT / "data/followup_grid.csv", towers.GRID_FIELDS, grid)
    towers.verify_known_results(admissions, grid)


@pytest.mark.parametrize("kernel", ["variance", "conditional"])
@deal.pre(lambda hoeflin, towers, kernel: protected_history_intact())
@deal.ensure(lambda hoeflin, towers, kernel, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, towers, kernel, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has('stdout', 'stderr', 'read', 'write', 'import', 'global', 'random', 'time')
def test_deal_generated_contract_cases(hoeflin, towers, kernel):
    # Exercise deal's own generator/introspection as well as direct Hypothesis.
    if kernel == "variance":
        function = hoeflin.variance_factor
        kwargs = {"n": st.integers(1, 1_000_000), "rho": UNIT}
    else:
        function = towers.conditional_probability
        kwargs = {"joint": UNIT, "marginal": st.floats(1e-5, 1, allow_nan=False, allow_infinity=False)}
    cases = list(deal.cases(function, count=25, kwargs=kwargs, seed=20261031,
                           settings=settings(max_examples=25, database=None, deadline=None)))
    assert cases
    for case in cases:
        result = case()
        assert math.isfinite(result) and 0 <= result <= 1

@pytest.mark.parametrize("value,expected", [
    (None, False), ("0.5", False), (False, False), (True, False),
    (complex(1, 2), False), (math.nan, False), (math.inf, False),
    (-math.inf, False), (0, True), (-11, True), (0.25, True),
    (10 ** 500, False),
])
@deal.pre(lambda hoeflin, towers, value, expected: protected_history_intact())
@deal.ensure(lambda hoeflin, towers, value, expected, *, result: protected_history_intact())
@deal.ensure(lambda hoeflin, towers, value, expected, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read")
def test_legacy_finite_number_guards_reject_invalid_types(hoeflin, towers, value, expected):
    """Both original model scripts must reject non-finite input categories."""
    assert hoeflin._finite(value) is expected
    assert towers._finite(value) is expected


@deal.pre(lambda hoeflin, tmp_path, monkeypatch: protected_history_intact())
@deal.ensure(lambda hoeflin, tmp_path, monkeypatch, *, result:
             protected_history_intact())
@deal.ensure(lambda hoeflin, tmp_path, monkeypatch, *, result:
             reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "global", "import")
def test_legacy_hoeflin_csv_writer_retains_exact_twelve_digit_rows(
        hoeflin, tmp_path, monkeypatch):
    """Write only into a temporary path and independently parse every field."""
    destination = tmp_path / "thresholds.csv"
    monkeypatch.setattr(hoeflin, "CSV_PATH", destination)
    rows = hoeflin.thresholds()
    hoeflin.write_csv(rows)
    with destination.open(newline="", encoding="utf-8") as stream:
        stored = list(csv.reader(stream))
    assert stored[0] == list(hoeflin.FIELDS)
    assert stored[1:] == [[name, f"{z:.12f}", f"{score:.12f}"]
                          for name, z, score in rows]
    assert len(stored) == len(rows) + 1


@deal.pre(lambda towers, tmp_path: protected_history_intact())
@deal.ensure(lambda towers, tmp_path, *, result: protected_history_intact())
@deal.ensure(lambda towers, tmp_path, *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("read", "write", "import")
def test_legacy_towers_csv_writer_preserves_quoted_rows_and_field_order(
        towers, tmp_path):
    """Exercise csv.DictWriter with a real embedded delimiter/newline."""
    path = tmp_path / "quoted-original-model.csv"
    fields = ("case", "rho", "source notes")
    records = [
        {"case": "first,case", "rho": 0.25, "source notes": "two\nlines"},
        {"case": "second", "rho": 0.5, "source notes": "has,comma"},
    ]
    towers.write_csv(path, fields, records)
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        assert reader.fieldnames == list(fields)
        assert list(reader) == [
            {column: str(row[column]) for column in fields}
            for row in records
        ]
