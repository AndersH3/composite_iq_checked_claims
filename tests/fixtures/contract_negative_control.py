"""Intentionally wrong fixture, excluded from production contract checks."""
import deal


@deal.pre(lambda value: 0.0 <= value <= 1.0)
@deal.post(lambda result: 0.0 <= result <= 1.0)
@deal.ensure(lambda value, result: result == value)
@deal.has()
@deal.raises()
def probability_identity(value: float) -> float:
    return value


@deal.post(lambda result: result >= 0)
@deal.post(lambda result: isinstance(result, int))
@deal.post(lambda result: result <= 1)
@deal.has()
@deal.raises()
def negative_probability() -> int:
    return -1
