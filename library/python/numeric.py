"""Shared finite-real validation used by all three report validators.

This canonical predicate deliberately rejects booleans (Python subclasses
bool from int), nonnumeric objects, NaN, infinities, and unrepresentably
large integers. It never coerces a string to a real number. The contract
conditions document the precise rejection boundary; source ownership is
central so specialized scripts cannot silently diverge.
"""
# A Dask worker's async communication thread shares this process; explicit
# transport permission avoids Deal's process-wide socket monkeypatch.
import math

import deal


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda value, result: not result or isinstance(value, (int, float)) and not isinstance(value, bool))
@deal.ensure(lambda value, result: not result or -math.inf < value < math.inf)
# Explicitly guard each non-finite input category, including the Boolean
# subclass of int, without strengthening finite numeric input preconditions.
@deal.ensure(lambda value, result: not isinstance(value, bool) or result is False)
@deal.ensure(lambda value, result: isinstance(value, (int, float)) or result is False)
@deal.ensure(lambda value, result:
             not isinstance(value, float) or not math.isnan(value) or result is False)
@deal.ensure(lambda value, result:
             not isinstance(value, float) or value != math.inf or result is False)
@deal.ensure(lambda value, result:
             not isinstance(value, float) or value != -math.inf or result is False)
# A finite float is accepted exactly; numeric integer boundaries are
# independently specified so Python's float-conversion overflow cannot
# silently turn a large integer into a valid report observation.
@deal.ensure(lambda value, result:
             not isinstance(value, float) or result is math.isfinite(value))
@deal.ensure(lambda value, result:
             not (isinstance(value, int) and not isinstance(value, bool)
                  and value.bit_length() <= 1023) or result is True)
@deal.ensure(lambda value, result:
             not (isinstance(value, int) and not isinstance(value, bool)
                  and value.bit_length() >= 1026) or result is False)
# Distinct unsupported input families must never be coerced into a real.
@deal.ensure(lambda value, result:
             not isinstance(value, complex) or result is False)
@deal.ensure(lambda value, result:
             not isinstance(value, (str, bytes, bytearray)) or result is False)
def finite_real(value) -> bool:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False
