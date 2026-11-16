"""Exact finite-battery formulas for any number of equal initial results.

Mathematical assumptions:
* n >= 1 initial distinct standardized Gaussian scores have observed value a.
* k >= 1 subsequent scores have the same zero population mean, unit variance,
  and pairwise correlation c as the initial scores.
* The full (n+k)-score equicorrelation covariance is positive semidefinite.
* Conditioning at a precise continuous history uses the canonical Gaussian
  regression version; at c=1 the history must lie on its diagonal support.

The returned predictions and conditional moments are algebraic consequences
of these assumptions, not statements about observed populations. Fractions
prevent silently approximating the exact IQ-150 examples. The population and
conditional variances describe different experiments, whereas the recursively
filled inclusive mean has variance zero once a, n, k and c are fixed.

Researcher/requester: Anders Hellström.
AI disclosure: OpenAI assisted the formal derivation, implementation and tests.
"""

from fractions import Fraction

import deal


@deal.pre(lambda n, k, a, c: type(n) is int and n >= 1)
@deal.pre(lambda n, k, a, c: type(k) is int and k >= 1)
@deal.pre(lambda n, k, a, c: type(n) is int and type(k) is int and n + k <= 1_000_000)
@deal.pre(lambda n, k, a, c: type(a) in (Fraction, int))
@deal.pre(lambda n, k, a, c: type(c) in (Fraction, int))
@deal.pre(lambda n, k, a, c: type(n) is int and type(k) is int and n >= 1 and k >= 1 and type(c) in (Fraction, int) and -Fraction(1, n + k - 1) <= c <= 1)
@deal.ensure(lambda n, k, a, c, result: set(result) == {"initial_count", "future_count", "total_count", "next_prediction", "inclusive_mean", "population_variance", "conditional_variance"})
@deal.ensure(lambda n, k, a, c, result: result["initial_count"] == n and result["future_count"] == k and result["total_count"] == n + k)
@deal.ensure(lambda n, k, a, c, result: all(type(result[key]) is Fraction for key in ("next_prediction", "inclusive_mean", "population_variance", "conditional_variance")))
@deal.ensure(lambda n, k, a, c, result: result["next_prediction"] * (1 + (n - 1) * c) == n * c * a)
@deal.ensure(lambda n, k, a, c, result: result["inclusive_mean"] * (n + k) == n * a + k * result["next_prediction"])
@deal.ensure(lambda n, k, a, c, result: result["inclusive_mean"] * (n + k) * (1 + (n - 1) * c) == n * (1 + (n + k - 1) * c) * a)
@deal.ensure(lambda n, k, a, c, result: result["population_variance"] * (n + k) == 1 + (n + k - 1) * c)
@deal.ensure(lambda n, k, a, c, result: result["conditional_variance"] * (n + k) ** 2 * (1 + (n - 1) * c) == k * (1 - c) * (1 + (n + k - 1) * c))
@deal.ensure(lambda n, k, a, c, result: 0 <= result["conditional_variance"] <= result["population_variance"])
@deal.ensure(lambda n, k, a, c, result: c != 1 or result["conditional_variance"] == 0)
@deal.ensure(lambda n, k, a, c, result: c != 0 or result["next_prediction"] == 0)
@deal.ensure(lambda n, k, a, c, result: result["inclusive_mean"] - a == Fraction(k, n + k) * (result["next_prediction"] - a))
@deal.raises()
@deal.has()
def equal_initial_scores(n: int, k: int, a: Fraction | int, c: Fraction | int) -> dict[str, Fraction | int]:
    """Return exact predictions and variances for arbitrary initial count n.

    The k future recursive conditional predictions are all equal to the
    returned next_prediction. The average includes all n observed results
    and all k predictions. The population variance refers to a fresh full
    battery; conditional variance refers to its actual mean with the first n
    values observed as a. The predicted average itself is nonrandom.
    All divisions have nonzero denominators in the contracted model domain.
    """
    initial_denominator = 1 + (n - 1) * c
    total = n + k
    total_denominator = 1 + (total - 1) * c
    next_prediction = Fraction(n * c * a, initial_denominator)
    inclusive_mean = Fraction(n * a + k * next_prediction, total)
    population_variance = Fraction(total_denominator, total)
    conditional_variance = Fraction(k * (1 - c) * total_denominator, total * total * initial_denominator)
    return {
        "initial_count": n,
        "future_count": k,
        "total_count": total,
        "next_prediction": next_prediction,
        "inclusive_mean": inclusive_mean,
        "population_variance": population_variance,
        "conditional_variance": conditional_variance,
    }
