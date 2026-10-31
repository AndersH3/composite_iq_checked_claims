"""Minimal positive runtime control for Deal 4.24.6's division-lint limitation."""
import deal


@deal.post(lambda result: result == 0.5)
@deal.raises()
@deal.has()
def safe_half() -> float:
    return 1.0 / 2.0
