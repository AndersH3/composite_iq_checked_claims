#!/usr/bin/env python3
"""Recalculate the Towers letters under an expressly assumed normal model."""

import argparse
import csv
import math
from pathlib import Path

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


def close(actual, expected, label, *, atol=5e-14, rtol=2e-12):
    if not math.isclose(actual, expected, abs_tol=atol, rel_tol=rtol):
        raise ValueError(f"{label}: got {actual!r}, expected {expected!r}")


def joint_tail(a, b, rho=RHO):
    """Integrate over X and independently check with Plackett's rho integral."""
    scale = math.sqrt(1 - rho * rho)
    value, error = quad(
        lambda x: norm.pdf(x) * norm.sf((b - rho * x) / scale),
        a, math.inf, epsabs=1e-14, epsrel=2e-12, limit=200,
    )
    def density_at_cutoffs(r):
        s = 1 - r * r
        return math.exp(-(a*a - 2*r*a*b + b*b) / (2*s)) / (2*math.pi*math.sqrt(s))
    increment, rho_error = quad(
        density_at_cutoffs, 0, rho, epsabs=1e-14, epsrel=2e-12, limit=200,
    )
    alternate = norm.sf(a) * norm.sf(b) + increment
    # Both quadrature error estimates must also satisfy the requested budget.
    if error > 1e-14 or rho_error > 1e-14:
        raise ValueError(f"Quadrature error estimate too large: {error}, {rho_error}")
    close(value, alternate, "independent joint-tail integrations", atol=5e-15)
    return float(value)


def admission_rows():
    rows = []
    for label, p_a, p_b in CASES:
        a, b = float(norm.isf(p_a)), float(norm.isf(p_b))
        j = joint_tail(a, b)
        close(j, joint_tail(b, a), "joint-tail symmetry", atol=5e-15)
        union = p_a + p_b - j
        if not 0 <= j <= min(p_a, p_b):
            raise ValueError("Joint probability violates an event bound")
        if not max(p_a, p_b) <= union <= min(1, p_a + p_b):
            raise ValueError("Union probability violates an event bound")
        phi = (j - p_a*p_b) / math.sqrt(p_a*(1-p_a)*p_b*(1-p_b))
        rows.append(dict(zip(ADMISSION_FIELDS, (
            label, RHO, a, b, p_a, p_b, j, union, j/p_a, j/p_b, phi,
        ))))
    return rows


def basic_grid():
    """Reproduce Q..199 STEP .5 point sums in the published BASIC program.

    The omitted IQ-scale Jacobian and cell area are common to numerator and
    denominator, so they cancel in these ratios. This does not make the grid
    an exact continuous-tail integration.
    """
    iq = np.arange(1, 199.25, 0.5)
    z = (iq - 100) / 16
    x, y = z[:, None], z[None, :]
    density = np.exp(-(x*x - 2*RHO*x*y + y*y) / (2*(1-RHO*RHO)))
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
        a = (cutoff - 100) / 16
        p = float(norm.sf(a))
        j = joint_tail(a, a)
        rows.append(dict(zip(GRID_FIELDS, (
            cutoff, p, j, j/p, grid_joint, grid_marginal,
            grid_joint/grid_marginal, rounded_p, grid_joint/rounded_p,
            published, grid_joint-published,
        ))))
    return rows


def write_csv(path, fields, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def verify_csv(path, fields, expected):
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
                close(float(stored[field]), float(value), f"{path.name}: {field}")


def verify_known_results(admissions, grid):
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate CSVs before checking")
    args = parser.parse_args()
    admissions = admission_rows()
    grid = basic_grid()
    files = (
        (ROOT / "data" / "admission_probabilities.csv", ADMISSION_FIELDS, admissions),
        (ROOT / "data" / "followup_grid.csv", GRID_FIELDS, grid),
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
    main()
