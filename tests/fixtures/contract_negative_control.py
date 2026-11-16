"""Intentionally wrong fixture, excluded from production contract checks."""
import deal


@deal.pre(lambda value: 0.0 <= value <= 1.0)
@deal.post(lambda result: 0.0 <= result <= 1.0)
@deal.ensure(lambda value, result: result == value)
@deal.has()
@deal.raises()
# These are genuine identity/probability properties of the positive
# fixture. Keep the deliberately failing negative_probability untouched:
# the static-lint gate requires exactly one DEL012 diagnostic from it.
@deal.pre(lambda value: type(value) in (int, float))
@deal.post(lambda result: isinstance(result, (int, float)))
@deal.ensure(lambda value, result: (value == 0) == (result == 0))
@deal.ensure(lambda value, result: (value == 1) == (result == 1))
@deal.ensure(lambda value, result: (value < 0.5) == (result < 0.5))
def probability_identity(value: float) -> float:
    return value


@deal.post(lambda result: result >= 0)
@deal.post(lambda result: isinstance(result, int))
@deal.post(lambda result: result <= 1)
@deal.has()
@deal.raises()
def negative_probability() -> int:
    return -1
