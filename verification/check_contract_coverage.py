#!/usr/bin/env python3
"""Require at least five real Deal decorators on every named Python function."""
import argparse
import ast
import json
from pathlib import Path
import subprocess
from subprocess import CalledProcessError

import sys

import deal

ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = {"pre", "post", "ensure", "raises", "reason", "has", "pure", "safe", "inv", "example", "chain"}
MINIMUM_CONTRACTS = 5
# Ten is a staged, nonredundant contract target; only five are compulsory
# until every production function has a defensible ten-contract specification.
TARGET_CONTRACTS = 10


@deal.pre(lambda node, aliases: isinstance(node, ast.expr))
@deal.pre(lambda node, aliases: isinstance(aliases, set))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
# Protect against distinct ways to spoof a Deal decorator in Python AST:
# bare names, constants, non-attribute call targets and nested attributes.
# The positive implication separately protects an explicitly imported
# direct Deal attribute from being overlooked by a later AST refactor.
@deal.ensure(lambda node, aliases, result:
             not isinstance(node, ast.Name) or result is False)
@deal.ensure(lambda node, aliases, result:
             not isinstance(node, ast.Constant) or result is False)
@deal.ensure(lambda node, aliases, result:
             not isinstance(node, ast.Call) or
             isinstance(node.func, ast.Attribute) or result is False)
@deal.ensure(lambda node, aliases, result:
             not isinstance(node, ast.Attribute) or
             isinstance(node.value, ast.Name) or result is False)
@deal.ensure(lambda node, aliases, result:
             not (isinstance(node, ast.Attribute) and
                  isinstance(node.value, ast.Name) and
                  node.value.id in aliases and node.attr in CONTRACTS)
             or result is True)
def is_contract(node: ast.expr, aliases: set) -> bool:
    expression = node.func if isinstance(node, ast.Call) else node
    return (isinstance(expression, ast.Attribute) and isinstance(expression.value, ast.Name)
            and expression.value.id in aliases and expression.attr in CONTRACTS)


@deal.pre(lambda path: isinstance(path, Path))
@deal.pre(lambda path: path.suffix == '.py')
@deal.post(lambda result: result["function_count"] >= 0 and isinstance(result["missing"], list)
           and isinstance(result["imports_deal"], bool) and result["contract_count"] >= 0)
@deal.raises(OSError, ValueError, SyntaxError, TypeError)
@deal.has("read", "import")
# These invariants protect the audit's quantitative claims rather than merely
# checking that its dictionary happens to have the expected field types.
@deal.post(lambda result: result["function_count"] == len(result["function_contracts"]))
@deal.post(lambda result: result["contract_count"] ==
           sum(row["contract_count"] for row in result["function_contracts"]))
@deal.post(lambda result: result["minimum_contracts"] == MINIMUM_CONTRACTS)
@deal.post(lambda result: len(result["missing"]) <= len(result["insufficient"]))
@deal.post(lambda result: len(result["duplicated"]) <= result["function_count"])
def audit_file(path: Path) -> dict:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    aliases = {alias.asname or "deal" for node in tree.body if isinstance(node, ast.Import)
               for alias in node.names if alias.name == "deal"}
    functions = [node for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]
    function_contracts = []
    for node in functions:
        decorators = [d for d in node.decorator_list if is_contract(d, aliases)]
        identities = []
        for decorator in decorators:
            expression = decorator.func if isinstance(decorator, ast.Call) else decorator
            # Normalize the imported Deal alias while retaining validator,
            # exception, marker and keyword syntax. Locations/whitespace are
            # not part of identity. This is a structural, not semantic, test.
            identity = (expression.attr,
                        tuple(ast.dump(arg, include_attributes=False) for arg in decorator.args)
                        if isinstance(decorator, ast.Call) else None,
                        tuple((keyword.arg, ast.dump(keyword.value, include_attributes=False))
                              for keyword in decorator.keywords)
                        if isinstance(decorator, ast.Call) else None)
            identities.append(identity)
        function_contracts.append({"name": node.name, "line": node.lineno,
                                   "contract_count": len(decorators),
                                   "distinct_contract_count": len(set(identities)),
                                   "duplicate_contract_count": len(identities) - len(set(identities))})
    missing = [{"name": row["name"], "line": row["line"]} for row in function_contracts
               if row["contract_count"] == 0]
    insufficient = [row for row in function_contracts if row["distinct_contract_count"] < MINIMUM_CONTRACTS]
    duplicated = [row for row in function_contracts if row["duplicate_contract_count"]]
    count = sum(row["contract_count"] for row in function_contracts)
    return {"path": str(path), "function_count": len(functions), "missing": missing,
            "imports_deal": bool(aliases), "contract_count": count,
            "minimum_contracts": MINIMUM_CONTRACTS, "function_contracts": function_contracts,
            "insufficient": insufficient, "duplicated": duplicated}


@deal.pre(lambda root: isinstance(root, Path))
@deal.pre(lambda root: root.is_dir())
@deal.post(lambda result: isinstance(result, list) and len(result) > 0
           and len(result) == len(set(result)) and all(p.suffix == ".py" for p in result))
@deal.raises(OSError, ValueError, subprocess.SubprocessError)
@deal.has("read", "syscall")
# Enumerated code must be repository-relative, regular, non-symlink
# Python source and deterministic. A malicious or stale Git index must
# not silently introduce outside paths or missing files into the audit.
@deal.post(lambda result: result == sorted(result))
@deal.ensure(lambda root, result: all(path.is_relative_to(root)
                                     for path in result))
@deal.post(lambda result: all(path.is_file() for path in result))
@deal.post(lambda result: all(not path.is_symlink() for path in result))
@deal.ensure(lambda root, result:
             all(".." not in path.relative_to(root).parts
                 for path in result))
def python_files(root: Path) -> list:
    try:
        output = subprocess.check_output(["git", "-C", str(root), "ls-files", "--cached", "--others",
                                          "--exclude-standard", "--", "*.py"], stderr=subprocess.PIPE,
                                         text=True, timeout=15)
    except CalledProcessError:
        # Support this computer10 workspace, which was authored through the
        # GitHub connector rather than a local checkout. CI uses Git's inventory.
        ignored = {".git", ".venv", ".venv-deal", "venv", "__pycache__", "obj", "obj-proof", "proof_obj", "bin"}
        paths = [p for p in root.rglob("*.py") if not ignored.intersection(p.relative_to(root).parts)]
    else:
        paths = [root.joinpath(relative) for relative in output.splitlines()]
    paths = sorted(set(paths))
    if not paths:
        raise ValueError("Empty Python inventory cannot establish coverage")
    return paths


@deal.raises(SystemExit, OSError, ValueError, SyntaxError, TypeError, subprocess.SubprocessError)
@deal.has("read", "stdout", "stderr", "syscall", "import")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
@deal.pre(lambda: ROOT.is_dir())
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    rows = [audit_file(path) for path in python_files(args.root)]
    problems = [r for r in rows if r["insufficient"] or r["duplicated"]
                or not r["imports_deal"] or r["contract_count"] == 0]
    report = {"python_files": len(rows), "named_functions": sum(r["function_count"] for r in rows),
              "deal_contracts": sum(r["contract_count"] for r in rows), "problems": problems,
              "minimum_contracts": MINIMUM_CONTRACTS,
              "minimum_observed": min(row["distinct_contract_count"] for r in rows for row in r["function_contracts"]),
              "complete": not problems}
    contract_counts = [function["distinct_contract_count"] for row in rows
                       for function in row["function_contracts"]]
    report["target_contracts"] = TARGET_CONTRACTS
    report["functions_at_target"] = sum(count >= TARGET_CONTRACTS
                                        for count in contract_counts)
    report["functions_below_target"] = sum(count < TARGET_CONTRACTS
                                           for count in contract_counts)
    print(json.dumps(report, indent=2))
    raise SystemExit(1 if problems else 0)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
