"""Pure, contract-checked decisions used to accept or reject native proof totals."""
import deal


@deal.pre(lambda total, flow, proved, justified, unproved: total >= 0)
@deal.pre(lambda total, flow, proved, justified, unproved: flow >= 0 and proved >= 0 and (justified >= 0) and (unproved >= 0))
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             result == (total == flow + proved + justified + unproved))
# Independent componentwise and partial-sum bounds on an accepted total.
# These preserve the existing domain and make each proof-count constraint visible.
@deal.ensure(lambda total, flow, proved, justified, unproved, result: not result or flow <= total)
@deal.ensure(lambda total, flow, proved, justified, unproved, result: not result or proved <= total)
@deal.ensure(lambda total, flow, proved, justified, unproved, result: not result or justified <= total)
@deal.ensure(lambda total, flow, proved, justified, unproved, result: not result or unproved <= total)
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             not result or flow + proved + justified <= total)
@deal.raises()
@deal.has()
def totals_balanced(total: int, flow: int, proved: int, justified: int, unproved: int) -> bool:
    return total == flow + proved + justified + unproved


@deal.pre(lambda returncode, total, unproved, justified: total >= 0)
@deal.pre(lambda returncode, total, unproved, justified: unproved >= 0 and justified >= 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             result == (returncode == 0 and total > 0 and unproved == 0 and justified == 0))
# Acceptance separately certifies status, positive inventory and clean goals.
# A process failure is unconditionally rejected, even with zero goal counts.
@deal.ensure(lambda returncode, total, unproved, justified, result: not result or returncode == 0)
@deal.ensure(lambda returncode, total, unproved, justified, result: not result or total >= 1)
@deal.ensure(lambda returncode, total, unproved, justified, result: not result or unproved == 0)
@deal.ensure(lambda returncode, total, unproved, justified, result: not result or justified == 0)
@deal.ensure(lambda returncode, total, unproved, justified, result: returncode == 0 or result is False)
@deal.raises()
@deal.has()
def successful_checks(returncode: int, total: int, unproved: int, justified: int) -> bool:
    return returncode == 0 and total > 0 and unproved == 0 and justified == 0


