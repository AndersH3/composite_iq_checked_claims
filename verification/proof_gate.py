"""Pure, contract-checked decisions used to accept or reject native proof totals."""
import deal


@deal.pre(lambda total, flow, proved, justified, unproved: total >= 0)
@deal.pre(lambda total, flow, proved, justified, unproved: flow >= 0 and proved >= 0 and (justified >= 0) and (unproved >= 0))
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             result == (total == flow + proved + justified + unproved))
@deal.raises()
@deal.has()
def totals_balanced(total: int, flow: int, proved: int, justified: int, unproved: int) -> bool:
    return total == flow + proved + justified + unproved


@deal.pre(lambda returncode, total, unproved, justified: total >= 0)
@deal.pre(lambda returncode, total, unproved, justified: unproved >= 0 and justified >= 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             result == (returncode == 0 and total > 0 and unproved == 0 and justified == 0))
@deal.raises()
@deal.has()
def successful_checks(returncode: int, total: int, unproved: int, justified: int) -> bool:
    return returncode == 0 and total > 0 and unproved == 0 and justified == 0


