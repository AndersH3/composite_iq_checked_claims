#!/usr/bin/env bash
# Verify Rocq module headers and theorem-level comments before kernel checking.
# The checker intentionally lives in a shell utility rather than an additional
# Python source module: the repository's Python contract inventory is pinned
# to historical, source-specific Deal/SPARK verification evidence.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 - <<'PY'
"""Documentation audit using only Python's standard library.

This examines source comments, not proof correctness. The separately pinned
Rocq 9.2 kernel compilation validates the mathematical statements.
"""
import re
import sys
from pathlib import Path

# Canonical source ownership manifest. The initial 18 modules remain unchanged;
# the new SequentialSensitivity module is owned by its report subproject.
# Generic mathematical files live only in library/rocq; specialized proofs
# are owned by their corresponding report project.
paths_by_module = {
    "FiniteSum": Path("library/rocq/FiniteSum.v"),
    "FiniteUnion": Path("library/rocq/FiniteUnion.v"),
    "FiniteMoments": Path("library/rocq/FiniteMoments.v"),
    "FiniteBridge": Path("library/rocq/FiniteBridge.v"),
    "EquicorrelationSpectral": Path("analyses/sequential-conditional-means/rocq/EquicorrelationSpectral.v"),
    "EquicorrelationVectors": Path("analyses/sequential-conditional-means/rocq/EquicorrelationVectors.v"),
    "EquicorrelationInverseVectors": Path("analyses/sequential-conditional-means/rocq/EquicorrelationInverseVectors.v"),
    "FiniteTwoCellProjection": Path("library/rocq/FiniteTwoCellProjection.v"),
    "FiniteNestedProjection": Path("library/rocq/FiniteNestedProjection.v"),
    "FiniteConditionalCovariance": Path("library/rocq/FiniteConditionalCovariance.v"),
    "FiniteConditionalResidual": Path("library/rocq/FiniteConditionalResidual.v"),
    "TwoObservationSchur": Path("library/rocq/TwoObservationSchur.v"),
    "Hoeflin": Path("analyses/hoeflin-ferguson/rocq/Hoeflin.v"),
    "Admissions": Path("analyses/towers-multiple-test-admissions/rocq/Admissions.v"),
    "FourCellBridge": Path("analyses/towers-multiple-test-admissions/rocq/FourCellBridge.v"),
    "ThreeTestAdmissions": Path("analyses/towers-multiple-test-admissions/rocq/ThreeTestAdmissions.v"),
    "ThreeTestPairBridge": Path("analyses/towers-multiple-test-admissions/rocq/ThreeTestPairBridge.v"),
    "ThreeTestConditionalStrata": Path("analyses/towers-multiple-test-admissions/rocq/ThreeTestConditionalStrata.v"),
    "TwoStratumAssociation": Path("library/rocq/TwoStratumAssociation.v"),
    "ThreeTestSelectionDecomposition": Path("analyses/towers-multiple-test-admissions/rocq/ThreeTestSelectionDecomposition.v"),
    "SequentialReport": Path("analyses/sequential-conditional-means/rocq/SequentialReport.v"),
    "SequentialSensitivity": Path("analyses/sequential-conditional-means/rocq/SequentialSensitivity.v"),
    "ReportRounding": Path("analyses/sequential-conditional-means/rocq/ReportRounding.v"),
    "ReportCounterexample": Path("analyses/sequential-conditional-means/rocq/ReportCounterexample.v"),
}
modules = tuple(paths_by_module)
canonical = set(paths_by_module.values())
present = set(Path("library/rocq").glob("*.v"))
for project in ("hoeflin-ferguson", "towers-multiple-test-admissions",
                "sequential-conditional-means"):
    present.update(Path("analyses", project, "rocq").glob("*.v"))
present.update(Path("rocq").glob("*.v"))
if present != canonical:
    missing = sorted(map(str, canonical - present))
    extra = sorted(map(str, present - canonical))
    raise SystemExit(f"Canonical Rocq source mismatch: missing={missing}; extra={extra}")

decl = re.compile(
    r"^[ \t]*(?:(?:Local|Global|Polymorphic|Program)\s+)?"
    r"(Theorem|Lemma|Example|Definition|Fixpoint|Record|Inductive|"
    r"Corollary|Proposition|Fact|Remark)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
comment_fields = (
    "Mathematical meaning:", "Exact ", "Premises and side conditions:",
    "Proof/definition method:", "Library reuse:", "Boundary:",
)
header_fields = (
    "Purpose:", "Mathematical representation:",
    "Explicit hypotheses:", "Library use:", "Limitations:", "Reproduction:",
)
issues = []
total = 0
theorems = 0
total_scripts = 0
refactor_register = Path("rocq/PROOF_REFACTOR_REGISTER.md").read_text(encoding="utf-8")
proof_decl = re.compile(
    r"^[ \t]*(?:(?:Local|Global)\s+)?"
    r"(?:Theorem|Lemma|Example|Definition|Fixpoint|Record)\s+"
    r"([A-Za-z_][\w']*)",
    re.MULTILINE,
)

for module in modules:
    path = paths_by_module[module]
    source = path.read_text(encoding="utf-8")
    if not source.startswith("(** Module: " + module + ".v"):
        issues.append(f"{path}: explanatory module header missing")
    header_end = source.find("*)")
    header = source[:header_end + 2] if header_end >= 0 else ""
    if len(header) < 350:
        issues.append(f"{path}: header lacks sufficient explanation")
    for field in header_fields:
        if field not in header:
            issues.append(f"{path}: header missing {field}")

    module_decls = 0
    module_proofs = 0
    for match in decl.finditer(source):
        kind, name = match.groups()
        module_decls += 1
        total += 1
        if kind in {"Theorem", "Lemma", "Example", "Corollary",
                    "Proposition", "Fact", "Remark"}:
            module_proofs += 1
            theorems += 1
        line = source.count("\n", 0, match.start()) + 1
        prefix = source[:match.start()].rstrip()
        if not prefix.endswith("*)"):
            issues.append(f"{path}:{line}: {kind} {name} lacks adjacent docs")
            continue
        start = prefix.rfind("(**")
        if start < 0:
            issues.append(f"{path}:{line}: {name} lacks Rocq doc comment")
            continue
        comment = prefix[start:]
        if len(comment) < 320 or f"[{name}]" not in comment:
            issues.append(f"{path}:{line}: {name} has incomplete docs")
        for field in comment_fields:
            if field not in comment:
                issues.append(f"{path}:{line}: {name} missing {field}")
    if not module_decls:
        issues.append(f"{path}: no declarations identified")

    # The review register must account for every proof block, including
    # the two four-cell record constructors using Proof/Defined.
    code = re.sub(r"\(\*[\s\S]*?\*\)", "", source)
    declarations = list(proof_decl.finditer(code))
    expected = []
    for block in re.finditer(r"\bProof\.", code):
        preceding = [item for item in declarations if item.start() < block.start()]
        if not preceding:
            issues.append(f"{path}: proof block without named declaration")
            continue
        expected.append(preceding[-1].group(1))

    section_match = re.search(
        r"^## " + re.escape(module) + r"\.v — [0-9]+ proof scripts$",
        refactor_register,
        re.MULTILINE,
    )
    if section_match is None:
        issues.append(f"{path}: missing proof-by-proof review section")
    else:
        section_tail = refactor_register[section_match.end():]
        next_heading = re.search(r"^## ", section_tail, re.MULTILINE)
        section = section_tail[:next_heading.start()] if next_heading else section_tail
        recorded = re.findall(r"^\| `([A-Za-z_][\w']*)` \(", section, re.MULTILINE)
        if recorded != expected:
            issues.append(
                f"{path}: proof-refactor register differs "
                f"({len(recorded)} recorded, {len(expected)} in source)"
            )
    total_scripts += len(expected)
    print(
        f"{path}: {module_decls} declarations; {module_proofs} theorem proofs; "
        f"{len(expected)} registered proof scripts"
    )

if issues:
    print("\n".join(issues), file=sys.stderr)
    sys.exit(1)
print(
    f"Documented all {total} declarations and {theorems} proofs "
    f"(including local helper lemmas), and audited all {total_scripts} "
    f"Proof./Qed. or Proof./Defined. scripts in {len(modules)} Rocq files."
)
PY
