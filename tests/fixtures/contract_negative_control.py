"""Deliberate negative Deal-lint control, still subject to >=15-contract coverage."""
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
# Deliberate control semantics and numerical boundary properties.
@deal.ensure(lambda value, result: result >= 0)
@deal.ensure(lambda value, result: result <= 1)
@deal.ensure(lambda value, result: result == result)
@deal.ensure(lambda value, result: result - value == 0)
@deal.ensure(lambda value, result: (value <= 0.5) == (result <= 0.5))
def probability_identity(value: float) -> float:
    """Provide a positive identity baseline for real Deal static lint.
    
    The annotated input and output remain the same probability value.
    This function ensures the negative fixture tests an actual violation elsewhere.
    """
    return value


@deal.post(lambda result: result >= 0)
@deal.post(lambda result: isinstance(result, int))
@deal.post(lambda result: result <= 1)
@deal.has()
@deal.raises()
# Deliberate control semantics and numerical boundary properties.
@deal.post(lambda result: result == -1)
@deal.post(lambda result: result < 0)
@deal.post(lambda result: result != 0)
@deal.post(lambda result: result <= -1)
@deal.post(lambda result: result >= -1)
@deal.post(lambda result: result + 1 == 0)
@deal.post(lambda result: -result == 1)
@deal.post(lambda result: result in (-1,))
@deal.post(lambda result: abs(result) == 1)
@deal.post(lambda result: result % 2 == 1)
def negative_probability() -> int:
    """Deliberately return a negative mass to test fail-closed Deal lint.
    
    Its declared nonnegative postcondition must be rejected by the real linter.
    Do not repair the violation: the workflow requires this negative control to fail.
    """
    return -1
