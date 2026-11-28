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
from collections.abc import Collection

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
    """Recognize only finite Python real numbers within the numerical working range.
    
    Reject booleans despite their integer subclass, strings, NaN, and both infinities.
    Handle integer-to-float overflow without coercing untrusted values into valid evidence.
    """
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


# A seed may be shifted by a model-specific substream offset before it
# crosses the worker's unsigned 32-bit input boundary. Keep the predicate
# independent of Dask, so graph construction and worker validation can
# share the same numeric rule without importing scheduler machinery.
@deal.pre(lambda seeds, offset=0: isinstance(seeds, Collection))
@deal.pre(lambda seeds, offset=0: type(offset) is int)
@deal.pre(lambda seeds, offset=0: 0 <= offset < 2**32)
@deal.post(lambda result: type(result) is bool)
@deal.raises()
@deal.has()
# Acceptance and rejection domains are checked independently; empty
# collections are vacuously valid here (replicate count is a graph rule).
@deal.ensure(lambda seeds, offset=0, result=None: len(seeds) != 0 or result is True)
@deal.ensure(lambda seeds, offset=0, result=None:
             len(seeds) == 0 or not all(type(seed) is int and 0 <= seed < 2**32 - offset
                                  for seed in seeds) or result is True)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(type(seed) is bool for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(isinstance(seed, float) for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(isinstance(seed, int) and type(seed) not in (int, bool)
                     for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(isinstance(seed, (str, bytes, bytearray))
                     for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(not isinstance(seed, (int, float, str, bytes, bytearray))
                     for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(type(seed) is int and seed < 0 for seed in seeds) or result is False)
@deal.ensure(lambda seeds, offset=0, result=None:
             not any(type(seed) is int and seed >= 2**32 - offset
                     for seed in seeds) or result is False)
def valid_seed_values(seeds, offset=0) -> bool:
    """Check whether all base and shifted seeds fit the worker's uint32 domain.

    Require a sized, reiterable collection and a nonnegative integer offset.
    Only exact Python integers are accepted as seeds; bool and noninteger
    values are rejected without coercion. The largest admissible base seed
    is 2**32 - 1 - offset. No random draws or I/O are performed.
    Empty collections are accepted here; uniqueness and replicate count
    remain separate graph-level preconditions.
    """
    return all(type(seed) is int and 0 <= seed < 2**32 - offset
               for seed in seeds)
