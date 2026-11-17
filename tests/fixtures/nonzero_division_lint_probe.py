"""Positive control: contracted division retains the exact original operation."""
import deal


@deal.pre(lambda numerator, denominator: isinstance(numerator, float)
          and isinstance(denominator, float) and 0.0 <= numerator <= 1.0
          and 1.0 <= denominator <= 2.0)
@deal.post(lambda result: isinstance(result, float) and 0.0 <= result <= 1.0)
@deal.ensure(lambda numerator, denominator, result: result <= numerator)
@deal.raises()
@deal.has()
# Independently check zero propagation, positivity, the identity divisor,
# strictly shrinking a positive numerator for a larger divisor, and NaNs.
# Do not introduce any unchecked division inside the contracts themselves.
@deal.ensure(lambda numerator, denominator, result:
             numerator != 0.0 or result == 0.0)
@deal.ensure(lambda numerator, denominator, result:
             numerator <= 0.0 or result > 0.0)
@deal.ensure(lambda numerator, denominator, result:
             denominator != 1.0 or result == numerator)
@deal.ensure(lambda numerator, denominator, result:
             denominator <= 1.0 or numerator <= 0.0 or result < numerator)
@deal.post(lambda result: result == result)
# Deliberate control semantics and numerical boundary properties.
@deal.ensure(lambda numerator, denominator, result: math.isclose(result * denominator, numerator, rel_tol=1e-12, abs_tol=1e-15))
@deal.ensure(lambda numerator, denominator, result: result >= 0)
@deal.ensure(lambda numerator, denominator, result: result == numerator / denominator)
@deal.ensure(lambda numerator, denominator, result: (numerator == denominator) == (result == 1))
@deal.ensure(lambda numerator, denominator, result: numerator != 1 or result >= 0.5)
def positive_ratio(numerator: float, denominator: float) -> float:
    return numerator / denominator


@deal.post(lambda result: result == 0.5)
@deal.post(lambda result: isinstance(result, float))
@deal.post(lambda result: 0.0 < result < 1.0)
@deal.raises()
@deal.has()
# Deliberate control semantics and numerical boundary properties.
@deal.post(lambda result: result + 0.25 == 0.75)
@deal.post(lambda result: result > 0)
@deal.post(lambda result: result < 1)
@deal.post(lambda result: result * 2 == 1)
@deal.post(lambda result: 1 / result == 2)
@deal.post(lambda result: result.as_integer_ratio() == (1, 2))
@deal.post(lambda result: result.hex() == '0x1.0000000000000p-1')
@deal.post(lambda result: 0 < result <= 0.5)
@deal.post(lambda result: float.fromhex(result.hex()) == result)
@deal.post(lambda result: result == positive_ratio(1.0, 2.0))
def safe_half() -> float:
    return positive_ratio(1.0, 2.0)
