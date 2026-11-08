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

modules = (
    "Hoeflin", "Admissions", "FiniteUnion", "FiniteMoments",
    "FiniteSum", "FiniteBridge", "FourCellBridge",
)
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

for module in modules:
    path = Path("rocq") / (module + ".v")
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
    print(f"{path}: {module_decls} declarations; {module_proofs} proofs")

if issues:
    print("\n".join(issues), file=sys.stderr)
    sys.exit(1)
print(
    f"Documented all {total} declarations and {theorems} proofs "
    "(including local helper lemmas) in seven Rocq files."
)
PY
