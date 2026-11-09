"""Pure, contract-checked decisions used to accept or reject native proof totals."""
import deal


@deal.pre(lambda total, flow, proved, justified, unproved: total >= 0)
@deal.pre(lambda total, flow, proved, justified, unproved: flow >= 0 and proved >= 0 and (justified >= 0) and (unproved >= 0))
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             result == (total == flow + proved + justified + unproved))
@deal.raises()
@deal.has()
# Additional conservation checks distinguish partial category tallies and
# explicitly verify the arithmetic residuals used in proof acceptance.
@deal.post(lambda result: type(result) is bool)
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             not result or total >= flow + proved)
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             not result or total >= justified + unproved)
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             not result or total - flow - proved == justified + unproved)
@deal.ensure(lambda total, flow, proved, justified, unproved, result:
             not result or total - justified - unproved == flow + proved)
def totals_balanced(total: int, flow: int, proved: int, justified: int, unproved: int) -> bool:
    return total == flow + proved + justified + unproved


@deal.pre(lambda returncode, total, unproved, justified: total >= 0)
@deal.pre(lambda returncode, total, unproved, justified: unproved >= 0 and justified >= 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             result == (returncode == 0 and total > 0 and unproved == 0 and justified == 0))
@deal.raises()
@deal.has()
# Each conjunct of native proof acceptance is checked separately so that
# a future refactor cannot silently admit failed, empty or unfinished runs.
@deal.post(lambda result: type(result) is bool)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             not result or returncode == 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             not result or total > 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             not result or unproved == 0)
@deal.ensure(lambda returncode, total, unproved, justified, result:
             not result or justified == 0)
def successful_checks(returncode: int, total: int, unproved: int, justified: int) -> bool:
    return returncode == 0 and total > 0 and unproved == 0 and justified == 0


