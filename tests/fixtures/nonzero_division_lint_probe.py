"""Positive control: contracted division retains the exact original operation."""
import deal


@deal.pre(lambda numerator, denominator: isinstance(numerator, float)
          and isinstance(denominator, float) and 0.0 <= numerator <= 1.0
          and 1.0 <= denominator <= 2.0)
@deal.post(lambda result: isinstance(result, float) and 0.0 <= result <= 1.0)
@deal.ensure(lambda numerator, denominator, result: result <= numerator)
@deal.raises()
@deal.has()
def positive_ratio(numerator: float, denominator: float) -> float:
    return numerator / denominator


@deal.post(lambda result: result == 0.5)
@deal.post(lambda result: isinstance(result, float))
@deal.post(lambda result: 0.0 < result < 1.0)
@deal.raises()
@deal.has()
def safe_half() -> float:
    return positive_ratio(1.0, 2.0)
