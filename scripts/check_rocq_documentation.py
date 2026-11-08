#!/usr/bin/env python3
"""Verify source-level documentation of every Rocq declaration.

This is a static documentation gate, not a substitute for kernel checking.
It checks that each module has an explanatory header, and each theorem,
lemma, definition, record, and other named declaration has an adjacent,
substantive declaration-specific Rocq doc comment. It does not parse or
interpret proof terms; GitHub Actions separately runs Rocq 9.2.
"""
from __future__ import annotations

import re
import sys

import deal
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOF_DIR = ROOT / "rocq"
MODULES = (
    "Hoeflin", "Admissions", "FiniteUnion", "FiniteMoments",
    "FiniteSum", "FiniteBridge", "FourCellBridge",
)
DECLARATION = re.compile(
    r"^[ \t]*(?:(?:Local|Global|Polymorphic|Program)\s+)?"
    r"(Theorem|Lemma|Example|Definition|Fixpoint|Record|Inductive|"
    r"Corollary|Proposition|Fact|Remark)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
REQUIRED_COMMENT_FIELDS = (
    "Mathematical meaning:",
    "Exact ",
    "Premises and side conditions:",
    "Proof/definition method:",
    "Library reuse:",
    "Boundary:",
)
REQUIRED_HEADER_FIELDS = (
    "Purpose:",
    "Mathematical representation:",
    "Explicit hypotheses:",
    "Library use:",
    "Limitations:",
    "Reproduction:",
)


# Repository-wide policy: named Python functions have at least five Deal
# contracts. These guard module selection, output shape, and count consistency.
@deal.pre(lambda module: isinstance(module, str))
@deal.pre(lambda module: module in MODULES)
@deal.pre(lambda module: bool(module))
@deal.post(lambda result: isinstance(result, tuple))
@deal.post(lambda result: len(result) == 3)
@deal.post(lambda result: 0 <= result[1] <= result[2])
def check_module(module: str) -> tuple[list[str], int, int]:
    path = PROOF_DIR / f"{module}.v"
    failures: list[str] = []
    source = path.read_text(encoding="utf-8")
    expected_prefix = f"(** Module: {module}.v"
    if not source.startswith(expected_prefix):
        failures.append(f"{path}: missing explanatory opening module comment")
    header_end = source.find("*)")
    header = source[: header_end + 2] if header_end >= 0 else ""
    if len(header) < 350:
        failures.append(f"{path}: header is too short to explain the module")
    for field in REQUIRED_HEADER_FIELDS:
        if field not in header:
            failures.append(f"{path}: header missing {field}")

    proof_count = 0
    declaration_count = 0
    for match in DECLARATION.finditer(source):
        declaration_count += 1
        kind, name = match.groups()
        if kind in {"Theorem", "Lemma", "Example", "Corollary",
                    "Proposition", "Fact", "Remark"}:
            proof_count += 1
        line = source.count("\n", 0, match.start()) + 1
        previous = source[: match.start()].rstrip()
        if not previous.endswith("*)"):
            failures.append(f"{path}:{line}: {kind} {name} lacks adjacent doc comment")
            continue
        doc_start = previous.rfind("(**")
        if doc_start < 0:
            failures.append(f"{path}:{line}: {kind} {name} lacks Rocq (** ... *) documentation")
            continue
        comment = previous[doc_start:]
        if len(comment) < 320 or f"[{name}]" not in comment:
            failures.append(f"{path}:{line}: {name} has incomplete or non-specific documentation")
        for field in REQUIRED_COMMENT_FIELDS:
            if field not in comment:
                failures.append(f"{path}:{line}: {name} documentation missing {field}")

    if not declaration_count:
        failures.append(f"{path}: no checked declarations located")
    return failures, proof_count, declaration_count


# The entrypoint is explicitly parameterized to give non-vacuous input
# preconditions rather than inventing tautological contracts for a no-arg main.
@deal.pre(lambda modules: len(modules) > 0)
@deal.pre(lambda modules: all(isinstance(module, str) for module in modules))
@deal.pre(lambda modules: len(set(modules)) == len(modules))
@deal.pre(lambda modules: all(module in MODULES for module in modules))
@deal.post(lambda result: result in (0, 1))
def main(modules: tuple[str, ...]) -> int:
    errors: list[str] = []
    proofs = 0
    declarations = 0
    for module in modules:
        issues, proof_count, declaration_count = check_module(module)
        errors.extend(issues)
        proofs += proof_count
        declarations += declaration_count
        print(f"{module}.v: {proof_count} proof declarations; "
              f"{declaration_count} named declarations checked")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Documented all {declarations} declarations "
          f"({proofs} theorem/lemma/example-like proofs) "
          f"across {len(modules)} Rocq modules.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(MODULES))
