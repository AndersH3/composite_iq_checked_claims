#!/usr/bin/env python3
"""Recalculate the Towers letters under an expressly assumed normal model."""

import argparse
import csv
import math
from pathlib import Path

import sys

import deal
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.stats import norm


ROOT = Path(__file__).resolve().parents[1]
RHO = 0.7
CASES = (
    ("equal_top_2_percent", 0.02, 0.02),
    ("equal_top_0_1_percent", 0.001, 0.001),
    ("equal_top_1_in_33000", 1 / 33000, 1 / 33000),
    ("mixed_top_2_and_0_1_percent", 0.02, 0.001),
)
ADMISSION_FIELDS = (
    "case", "rho", "cutoff_a_z", "cutoff_b_z", "p_a", "p_b", "joint",
    "union", "conditional_b_given_a", "conditional_a_given_b", "phi",
)
GRID_FIELDS = (
    "cutoff_iq", "marginal_continuous", "joint_continuous",
    "conditional_continuous", "grid_joint", "grid_marginal",
    "grid_conditional", "published_rounded_denominator", "grid_div_rounded",
    "published_joint", "grid_minus_published",
)


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
def _finite(value) -> bool:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


@deal.pre(lambda p_a, p_b, joint: all(_finite(p) and 0 <= p <= 1 for p in (p_a, p_b, joint))
          and max(0, p_a + p_b - 1) <= joint <= min(p_a, p_b))
@deal.post(lambda result: _finite(result) and -5e-15 <= result <= 1 + 5e-15)
@deal.ensure(lambda p_a, p_b, joint, result:
             max(p_a, p_b) - 5e-15 <= result <= min(1, p_a + p_b) + 5e-15)
@deal.has()
@deal.raises()
# Inclusion-exclusion also constrains each marginal contribution,
# its upper sum bound, and the disjoint-events boundary exactly.
@deal.ensure(lambda p_a, p_b, joint, result: result == p_a + p_b - joint)
@deal.ensure(lambda p_a, p_b, joint, result: result + 5e-15 >= p_a)
@deal.ensure(lambda p_a, p_b, joint, result: result + 5e-15 >= p_b)
@deal.ensure(lambda p_a, p_b, joint, result: result <= p_a + p_b + 5e-15)
@deal.ensure(lambda p_a, p_b, joint, result: joint != 0 or math.isclose(
    result, p_a + p_b, rel_tol=0, abs_tol=5e-15))
def probability_union(p_a: float, p_b: float, joint: float) -> float:
    """Inclusion-exclusion for a feasible pair of event probabilities."""
    return p_a + p_b - joint


@deal.pre(lambda joint, marginal: _finite(joint))
@deal.pre(lambda joint, marginal: _finite(marginal) and 0 <= joint <= marginal <= 1 and (marginal > 0))
@deal.post(lambda result: _finite(result) and 0 <= result <= 1)
@deal.has()
@deal.raises()
# Recover the joint mass from its conditional, and check the
# empty-intersection, equal-event and certain-conditioning boundaries.
@deal.ensure(lambda joint, marginal, result: result == joint / marginal)
@deal.ensure(lambda joint, marginal, result: math.isclose(
    result * marginal, joint, rel_tol=8e-15, abs_tol=1e-15))
@deal.ensure(lambda joint, marginal, result: joint != 0 or result == 0)
@deal.ensure(lambda joint, marginal, result: joint != marginal or result == 1)
@deal.ensure(lambda joint, marginal, result: marginal != 1 or result == joint)
def conditional_probability(joint: float, marginal: float) -> float:
    """Conditional rate with its explicitly positive marginal denominator."""
    return joint / marginal


@deal.pre(lambda actual, expected, label, *, atol=5e-14, rtol=2e-12:
          _finite(actual) and _finite(expected) and isinstance(label, str)
          and _finite(atol) and atol >= 0 and _finite(rtol) and rtol >= 0)
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.reason(ValueError, lambda actual, expected, label, *, atol=5e-14, rtol=2e-12:
             not math.isclose(actual, expected, abs_tol=atol, rel_tol=rtol))
@deal.has()
def close(actual: float, expected: float, label: str, *, atol: float = 5e-14,
          rtol: float = 2e-12) -> None:
    if not math.isclose(actual, expected, abs_tol=atol, rel_tol=rtol):
        raise ValueError(f"{label}: got {actual!r}, expected {expected!r}")


@deal.pre(lambda a, b, rho=RHO: _finite(a) and _finite(b) and _finite(rho)
          and -8 <= a <= 8 and -8 <= b <= 8 and -.95 <= rho <= .95)
@deal.post(lambda result: _finite(result) and 0 <= result <= 1 + 5e-14)
@deal.ensure(lambda a, b, rho=RHO, *, result:
             max(0, float(norm.sf(a)) + float(norm.sf(b)) - 1) - 5e-14 <= result
             <= min(float(norm.sf(a)), float(norm.sf(b))) + 5e-14)
@deal.has("stderr")
@deal.raises(ValueError)
def joint_tail(a: float, b: float, rho: float = RHO) -> float:
    """Integrate over X and independently check with Plackett's rho integral."""
    scale = math.sqrt(1 - rho * rho)
    value, error = quad(
        lambda x: norm.pdf(x) * norm.sf((b - rho * x) / scale),
        a, math.inf, epsabs=1e-14, epsrel=2e-14, limit=200,
    )
    @deal.pre(lambda r: _finite(r))
    @deal.pre(lambda r: -0.95 <= r <= 0.95)
    @deal.post(lambda result: _finite(result) and result >= 0)
    @deal.has()
    @deal.raises()
    def density_at_cutoffs(r: float) -> float:
        s = 1 - r * r
        return math.exp(-(a*a - 2*r*a*b + b*b) / (2*s)) / (2*math.pi*math.sqrt(s))
    increment, rho_error = quad(
        density_at_cutoffs, 0, rho, epsabs=1e-14, epsrel=2e-14, limit=200,
    )
    alternate = norm.sf(a) * norm.sf(b) + increment
    # Both quadrature error estimates must also satisfy the requested budget.
    if error > 1e-14 or rho_error > 1e-14:
        raise ValueError(f"Quadrature error estimate too large: {error}, {rho_error}")
    close(value, alternate, "independent joint-tail integrations", atol=5e-15)
    return float(value)


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda fields, rows, result: not result or len(fields) == len(set(fields)) and all(isinstance(field, str) and field for field in fields))
@deal.ensure(lambda fields, rows, result: not result or all(isinstance(row, dict) and set(row) == set(fields) for row in rows))
# Successful CSV-schema validation guarantees usable sequence types,
# a nonempty header, safe typed values, and no absent field values.
@deal.ensure(lambda fields, rows, result: not result or isinstance(fields, (list, tuple)))
@deal.ensure(lambda fields, rows, result: not result or bool(fields))
@deal.ensure(lambda fields, rows, result: not result or isinstance(rows, (list, tuple)))
@deal.ensure(lambda fields, rows, result: not result or
             all(isinstance(value, str) or _finite(value)
                 for row in rows for value in row.values()))
@deal.ensure(lambda fields, rows, result: not result or
             all(value is not None for row in rows for value in row.values()))
def _valid_fields_rows(fields, rows) -> bool:
    if not isinstance(fields, (tuple, list)) or not fields:
        return False
    if not all(isinstance(field, str) and field for field in fields):
        return False
    if len(set(fields)) != len(fields):
        return False
    if not isinstance(rows, (list, tuple)):
        return False
    for row in rows:
        if not isinstance(row, dict) or set(row) != set(fields):
            return False
        if not all(isinstance(value, str) or _finite(value) for value in row.values()):
            return False
    return True


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda rows, result: not result or len(rows) == len(CASES))
@deal.ensure(lambda rows, result: not result or [(row["case"], row["p_a"], row["p_b"]) for row in rows] == list(CASES))
# The accepted admissions table preserves its declared complete schema,
# row label uniqueness, probability bounds, and correlation bounds.
@deal.ensure(lambda rows, result: not result or
             _valid_fields_rows(ADMISSION_FIELDS, rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["joint"]) and 0 <= row["joint"] <= 1 + 5e-14
                 and _finite(row["union"]) and 0 <= row["union"] <= 1 + 5e-14
                 for row in rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["conditional_b_given_a"])
                 and 0 <= row["conditional_b_given_a"] <= 1 + 5e-14
                 and _finite(row["conditional_a_given_b"])
                 and 0 <= row["conditional_a_given_b"] <= 1 + 5e-14
                 for row in rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["phi"]) and abs(row["phi"]) <= 1 + 5e-14
                 for row in rows))
@deal.ensure(lambda rows, result: not result or
             len({row["case"] for row in rows}) == len(CASES))
def _valid_admissions(rows) -> bool:
    if not _valid_fields_rows(ADMISSION_FIELDS, rows) or len(rows) != len(CASES):
        return False
    for row, (label, p_a, p_b) in zip(rows, CASES):
        if row["case"] != label or row["p_a"] != p_a or row["p_b"] != p_b:
            return False
        for field in ("joint", "union", "conditional_b_given_a", "conditional_a_given_b"):
            if not _finite(row[field]) or not 0 <= row[field] <= 1 + 5e-14:
                return False
        if not _finite(row["phi"]) or not -1 - 5e-14 <= row["phi"] <= 1 + 5e-14:
            return False
    return True


@deal.post(lambda result: isinstance(result, bool))
@deal.has()
@deal.raises()
@deal.ensure(lambda rows, result: not result or tuple(row["cutoff_iq"] for row in rows) == (133, 150, 164))
@deal.ensure(lambda rows, result: not result or all(_finite(row[field]) and 0 <= row[field] <= 1 for row in rows for field in ("marginal_continuous", "joint_continuous", "conditional_continuous", "grid_joint", "grid_marginal", "grid_conditional")))
# Preserve the exact grid size, complete numeric schema, and independent
# probability-domain checks for continuous and discretized outputs.
@deal.ensure(lambda rows, result: not result or len(rows) == 3)
@deal.ensure(lambda rows, result: not result or _valid_fields_rows(GRID_FIELDS, rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["joint_continuous"]) and
                 0 <= row["joint_continuous"] <= 1 for row in rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["grid_joint"]) and
                 0 <= row["grid_joint"] <= 1 for row in rows))
@deal.ensure(lambda rows, result: not result or
             all(_finite(row["conditional_continuous"]) and
                 0 <= row["conditional_continuous"] <= 1 for row in rows))
def _valid_grid(rows) -> bool:
    return (_valid_fields_rows(GRID_FIELDS, rows) and len(rows) == 3
            and tuple(row["cutoff_iq"] for row in rows) == (133, 150, 164)
            and all(_finite(row[field]) and 0 <= row[field] <= 1 for row in rows for field in (
                "marginal_continuous", "joint_continuous", "conditional_continuous",
                "grid_joint", "grid_marginal", "grid_conditional")))


@deal.post(_valid_admissions)
@deal.has("stderr")
@deal.raises(ValueError)
@deal.pre(lambda: _finite(RHO) and -.95 <= RHO <= .95)
@deal.pre(lambda: bool(CASES) and len({row[0] for row in CASES}) == len(CASES) and all(isinstance(label, str) and label and _finite(p_a) and _finite(p_b) and 0 < p_a < 1 and 0 < p_b < 1 for label, p_a, p_b in CASES))
# Each modeled row must retain its source-case identity and raw
# probabilities; the derived union must obey inclusion-exclusion
# exactly as calculated rather than trusting a rounded CSV fixture.
# The preexisting _valid_admissions postcondition rejects empty tables;
# the guarded length assertion also supports Deal's empty-return abstraction.
@deal.post(lambda result: not result or len(result) == len(CASES))
@deal.post(lambda result: [row["case"] for row in result] ==
           [label for label, _, _ in CASES])
@deal.post(lambda result: all(row["rho"] == RHO for row in result))
@deal.post(lambda result: all(row["p_a"] == p_a and row["p_b"] == p_b
                              for row, (_, p_a, p_b) in zip(result, CASES)))
@deal.post(lambda result: all(row["union"] ==
                              row["p_a"] + row["p_b"] - row["joint"]
                              for row in result))
def admission_rows() -> list[dict]:
    rows = []
    for label, p_a, p_b in CASES:
        a, b = float(norm.isf(p_a)), float(norm.isf(p_b))
        j = joint_tail(a, b)
        close(j, joint_tail(b, a), "joint-tail symmetry", atol=5e-15)
        union = probability_union(p_a, p_b, j)
        if not 0 <= j <= min(p_a, p_b):
            raise ValueError("Joint probability violates an event bound")
        if not max(p_a, p_b) <= union <= min(1, p_a + p_b):
            raise ValueError("Union probability violates an event bound")
        phi = (j - p_a*p_b) / math.sqrt(p_a*(1-p_a)*p_b*(1-p_b))
        rows.append(dict(zip(ADMISSION_FIELDS, (
            label, RHO, a, b, p_a, p_b, j, union,
            conditional_probability(j, p_a), conditional_probability(j, p_b), phi,
        ))))
    return rows


@deal.post(_valid_grid)
@deal.has("stderr")
@deal.raises(ValueError)
@deal.pre(lambda: _finite(RHO) and -.95 <= RHO <= .95)
@deal.pre(lambda: len(GRID_FIELDS) == 11 and len(set(GRID_FIELDS)) == len(GRID_FIELDS) and all(isinstance(field, str) and field for field in GRID_FIELDS))
# Preserve the exact three BASIC cutoffs and the algebraic dependence
# of each published comparison and conditional ratio on its recorded
# unrounded joint/marginal values. The existing _valid_grid
# postcondition rejects emptiness; a guarded length law avoids the
# static linter's intermediate empty-list abstraction.
@deal.post(lambda result: not result or len(result) == 3)
@deal.post(lambda result:
           tuple(row["cutoff_iq"] for row in result) == (133, 150, 164))
@deal.post(lambda result: all(row["grid_minus_published"] ==
                              row["grid_joint"] - row["published_joint"]
                              for row in result))
@deal.post(lambda result: all(row["grid_conditional"] ==
                              row["grid_joint"] / row["grid_marginal"]
                              for row in result))
@deal.post(lambda result: all(row["grid_div_rounded"] ==
                              row["grid_joint"] /
                              row["published_rounded_denominator"]
                              for row in result))
def basic_grid() -> list[dict]:
    """Reproduce Q..199 STEP .5 point sums in the published BASIC program.

    The omitted IQ-scale Jacobian and cell area are common to numerator and
    denominator, so they cancel in these ratios. This does not make the grid
    an exact continuous-tail integration.
    """
    iq = np.arange(1, 199.25, 0.5)
    z = (iq - 100) * 0.0625
    x, y = z[:, None], z[None, :]
    density = np.exp(np.divide(-(x*x - 2*RHO*x*y + y*y), 2*(1-RHO*RHO)))
    density /= 2*math.pi*math.sqrt(1-RHO*RHO)
    total = float(density.sum())
    if len(iq) != 397 or density.size != 157609:
        raise ValueError("BASIC grid dimensions do not match the specified loops")
    rows = []
    for cutoff, rounded_p, published in (
        (133, 0.02, 0.0064061692),
        (150, 0.001, 0.00014748463),
        (164, 0.000030303, 2.6393845e-6),
    ):
        passes = iq >= cutoff
        grid_joint = float(density[np.ix_(passes, passes)].sum() / total)
        grid_marginal = float(density[passes, :].sum() / total)
        a = (cutoff - 100) * 0.0625
        p = float(norm.sf(a))
        j = joint_tail(a, a)
        rows.append(dict(zip(GRID_FIELDS, (
            cutoff, p, j, conditional_probability(j, p), grid_joint, grid_marginal,
            conditional_probability(grid_joint, grid_marginal), rounded_p,
            conditional_probability(grid_joint, rounded_p),
            published, grid_joint-published,
        ))))
    return rows


@deal.pre(lambda path, fields, rows: isinstance(path, Path))
@deal.pre(lambda path, fields, rows: _valid_fields_rows(fields, rows))
@deal.post(lambda result: result is None)
@deal.has("write")
@deal.raises(OSError, csv.Error)
def write_csv(path: Path, fields: tuple[str, ...], rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


@deal.pre(lambda path, fields, expected: isinstance(path, Path))
@deal.pre(lambda path, fields, expected: _valid_fields_rows(fields, expected))
@deal.post(lambda result: result is None)
@deal.has("read")
@deal.raises(OSError, ValueError, csv.Error)
def verify_csv(path: Path, fields: tuple[str, ...], expected: list[dict]) -> None:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames or ()) != fields:
            raise ValueError(f"Unexpected CSV schema in {path.name}")
        actual = list(reader)
    if len(actual) != len(expected):
        raise ValueError(f"Unexpected row count in {path.name}")
    for stored, calculated in zip(actual, expected):
        for field in fields:
            value = calculated[field]
            if isinstance(value, str):
                if stored[field] != value:
                    raise ValueError(f"Mismatched row label in {path.name}")
            else:
                try:
                    number = float(stored[field])
                except (TypeError, KeyError) as error:
                    raise ValueError(f"Missing numeric CSV value: {field}") from error
                if not _finite(number):
                    raise ValueError(f"Non-finite CSV value: {field}")
                close(number, float(value), f"{path.name}: {field}")


@deal.pre(lambda admissions, grid: _valid_admissions(admissions))
@deal.pre(lambda admissions, grid: _valid_grid(grid))
@deal.post(lambda result: result is None)
@deal.has("stderr")
@deal.raises(ValueError)
def verify_known_results(admissions: list[dict], grid: list[dict]) -> None:
    expected_joint = (
        0.006276274020528095, 0.00015958919471554256,
        0.000002312497921350349, 0.0006585888039150674,
    )
    for row, expected in zip(admissions, expected_joint):
        close(row["joint"], expected, row["case"])
    close(admissions[0]["conditional_b_given_a"], 0.31381370102640477, "equal 2% conditional")
    close(admissions[3]["conditional_a_given_b"], 0.6585888039150675, "mixed high-group conditional")
    close(admissions[0]["phi"], 0.29980989900653543, "dichotomized phi correlation")
    close(admissions[0]["joint"] / admissions[0]["union"], 0.1861085582402296,
          "both-pass share of union-eligible population")
    if 0.0211 <= 0.02 + 0.001:
        raise ValueError("The original mixed union should violate the union bound")
    # Float64 reproduction is close to the printed legacy results, but does
    # not match all printed digits. Record the residual instead of hiding it.
    for row in grid:
        close(row["grid_joint"], row["published_joint"], "near-reproduction of published BASIC result",
              atol=0, rtol=3e-7)
    a = float(norm.isf(0.05))
    close(joint_tail(a, a), 0.01959930097779461, "equal top-5% cross-check")

    # Calibrate the complete two-test selection rule, rather than using a
    # 2% threshold on each component and assuming the union is also 2%.
    or_cutoff = brentq(lambda t: 2*norm.sf(t) - joint_tail(t, t) - 0.02,
                       1, 4, xtol=1e-12)
    and_cutoff = brentq(lambda t: joint_tail(t, t) - 0.02,
                        1, 4, xtol=1e-12)
    close(or_cutoff, 2.2700549290597922, "2%-overall OR cutoff", atol=2e-11)
    close(float(norm.sf(or_cutoff)), 0.0116021252451422,
          "OR-calibrated marginal pass probability")
    close(100+16*or_cutoff, 136.32087886495668, "OR-calibrated SD16 cutoff", atol=5e-10)
    close(and_cutoff, 1.63698581434, "2%-overall AND cutoff", atol=1e-10)


@deal.post(lambda result: result is None)
@deal.has("read", "write", "stdout", "stderr", "syscall")
@deal.raises(OSError, ValueError, csv.Error, SystemExit)
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate CSVs before checking")
    args = parser.parse_args()
    admissions = admission_rows()
    grid = basic_grid()
    files = (
        (ROOT.joinpath("data", "admission_probabilities.csv"), ADMISSION_FIELDS, admissions),
        (ROOT.joinpath("data", "followup_grid.csv"), GRID_FIELDS, grid),
    )
    for path, fields, rows in files:
        if args.write:
            write_csv(path, fields, rows)
        verify_csv(path, fields, rows)
    verify_known_results(admissions, grid)
    print("Verified 4 nominal-cutoff cases with independent integrations, 3 BASIC-grid cases, and OR/AND calibration.")
    print("Legacy printed grid results agree within 3e-7 relative tolerance; residuals are recorded in the CSV.")
    first = admissions[0]
    print(f"Equal top-2% tests: joint={first['joint']:.10f}, union={first['union']:.10f}, conditional={first['conditional_b_given_a']:.8f}")
    print("Mixed cutoffs: P(low pass | high pass)=%.8f" % admissions[3]["conditional_a_given_b"])


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
