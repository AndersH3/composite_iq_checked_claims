"""Regression tests for the general n initial observations equal to a.

These exact rational certificates supplement, rather than replace, the
Gaussian conditional-regression proofs and the existing Dask grid.
Researcher/requester: Anders Hellström.
AI disclosure: OpenAI assisted the design and implementation of these tests.
"""

from fractions import Fraction as F

import deal
import numpy as np
from numpy.linalg import LinAlgError
import pytest

from conftest import protected_history_intact, reference_inputs_intact
from library.python.sequential import equal_initial_scores


@pytest.mark.parametrize(
    "n,k,a,c,expected",
    [
        (1, 10, F(10, 3), F(3, 5), (F(2), F(70, 33), F(7, 11), F(28, 121))),
        (2, 10, F(10, 3), F(3, 5), (F(5, 2), F(95, 36), F(19, 30), F(19, 144))),
        (3, 10, F(10, 3), F(3, 5), (F(30, 11), F(410, 143), F(41, 65), F(164, 1859))),
        (5, 10, F(10, 3), F(3, 5), (F(50, 17), F(470, 153), F(47, 75), F(188, 3825))),
        (5, 10, F(10, 3), F(0), (F(0), F(10, 9), F(1, 15), F(2, 45))),
        (5, 10, F(10, 3), F(1), (F(10, 3), F(10, 3), F(1), F(0))),
        (5, 10, F(10, 3), F(-1, 14), (F(-5, 3), F(0), F(0), F(0))),
        (1, 1, F(7, 3), F(-1), (F(-7, 3), F(0), F(0), F(0))),
    ],
)
@deal.pre(lambda n, k, a, c, expected: type(n) is int and n >= 1)
@deal.pre(lambda n, k, a, c, expected: type(k) is int and k >= 1)
@deal.pre(lambda n, k, a, c, expected: type(a) is F)
@deal.pre(lambda n, k, a, c, expected: type(c) is F)
@deal.pre(lambda n, k, a, c, expected: -F(1, n + k - 1) <= c <= 1)
@deal.pre(lambda n, k, a, c, expected: isinstance(expected, tuple) and len(expected) == 4)
@deal.pre(lambda n, k, a, c, expected: all(type(value) is F for value in expected))
@deal.pre(lambda n, k, a, c, expected: expected[2] >= 0 and expected[3] >= 0)
@deal.pre(lambda n, k, a, c, expected: expected[3] <= expected[2])
@deal.pre(lambda n, k, a, c, expected: protected_history_intact())
@deal.pre(lambda n, k, a, c, expected: reference_inputs_intact())
@deal.ensure(lambda n, k, a, c, expected, result: result is None)
@deal.ensure(lambda n, k, a, c, expected, result: protected_history_intact())
@deal.ensure(lambda n, k, a, c, expected, result: reference_inputs_intact())
@deal.raises(AssertionError, LinAlgError)
@deal.has("read", "import")
def test_general_n_exact_values_and_gaussian_schur_complement(n, k, a, c, expected):
    """Check eight exact cases and an independent finite-matrix calculation."""
    observed = equal_initial_scores(n, k, a, c)
    assert observed["initial_count"] == n
    assert observed["future_count"] == k
    assert observed["total_count"] == n + k
    assert tuple(observed[key] for key in (
        "next_prediction", "inclusive_mean", "population_variance",
        "conditional_variance",
    )) == expected

    # For c<1 the observed block is positive definite, including when
    # the *full* covariance is singular at its negative lower endpoint.
    # At c=1 the observed block is rank one and must be treated on its
    # diagonal support, not inverted as if it were nonsingular.
    if c < 1:
        count = n + k
        correlation = float(c)
        covariance = (1 - correlation) * np.eye(count) + correlation * np.ones((count, count))
        weights = np.full(count, 1.0 / count)
        observed_covariance = covariance[:n, :n]
        cross_covariance = covariance[:n, :] @ weights
        start_scores = np.full(n, float(a))
        regression = np.linalg.solve(observed_covariance, cross_covariance)
        numerical_mean = float(np.dot(start_scores, regression))
        numerical_conditional_variance = float(
            weights @ covariance @ weights - cross_covariance @ regression
        )
        assert numerical_mean == pytest.approx(float(observed["inclusive_mean"]), abs=2e-12)
        assert numerical_conditional_variance == pytest.approx(
            float(observed["conditional_variance"]), abs=2e-12,
        )
    else:
        assert observed["next_prediction"] == a
        assert observed["inclusive_mean"] == a
        assert observed["conditional_variance"] == 0

    # Test rejection of count, value, type and covariance-domain violations.
    # n=5 is deliberately beyond the recorded n=1,2,3 Dask grid.
    if n == 5 and c == F(3, 5):
        bad_inputs = (
            (0, k, a, c), (n, 0, a, c), (True, k, a, c),
            (n, False, a, c), (n, k, float(a), c),
            (n, k, a, float(c)), (n, k, a, F(11, 10)),
            (n, k, a, -F(1, n + k - 1) - F(1, 100)),
            (1_000_000, k, a, c),
        )
        for args in bad_inputs:
            with pytest.raises(deal.PreContractError):
                equal_initial_scores(*args)
