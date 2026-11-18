#!/usr/bin/env python3
"""Audit a minimum of fifteen distinct Deal contracts per named Python function."""
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
MINIMUM_CONTRACTS = 15
# The independent executable-file floor applies to all tracked Python
# modules containing a named function, including tests and lint fixtures.
# Import-only modules have no callable boundary on which to hang a contract.
MINIMUM_FILE_CONTRACTS = 15
# The reporting target equals the mandatory per-function floor; a greater
# number of meaningful contracts is always allowed, never rejected.
TARGET_CONTRACTS = MINIMUM_CONTRACTS


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
@deal.ensure(lambda node, aliases, result: not isinstance(node, ast.Subscript) or not result)
@deal.ensure(lambda node, aliases, result: not isinstance(node, ast.BinOp) or not result)
@deal.ensure(lambda node, aliases, result: not isinstance(node, ast.Compare) or not result)
@deal.ensure(lambda node, aliases, result: not isinstance(node, ast.Lambda) or not result)
@deal.ensure(lambda node, aliases, result: not isinstance(node, ast.Dict) or not result)
def is_contract(node: ast.expr, aliases: set) -> bool:
    """Identify only AST decorators actually imported from the Deal module.
    
    Normalize valid import aliases while rejecting unrelated names and syntax nodes.
    String literals, nested attributes, and comments cannot masquerade as contracts.
    """
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
@deal.post(lambda result:
           result["file_distinct_contract_count"] ==
           sum(row["distinct_contract_count"] for row in result["function_contracts"]))
@deal.post(lambda result:
           result["insufficient_file"] ==
           (result["function_count"] > 0 and
            result["file_distinct_contract_count"] < MINIMUM_FILE_CONTRACTS))
@deal.post(lambda result: all(row["line"] > 0 for row in result["function_contracts"]))
@deal.post(lambda result: all(row["contract_count"] >= row["distinct_contract_count"] >= 0 for row in result["function_contracts"]))
@deal.post(lambda result: len(result["insufficient"]) == sum(row["distinct_contract_count"] < MINIMUM_CONTRACTS for row in result["function_contracts"]))
def audit_file(path: Path) -> dict:
    """Audit every named function in a Python module using its parsed AST.
    
    Count distinct Deal preconditions, postconditions, effects, and other validators.
    Expose missing, duplicated, and below-floor contracts without executing source code.
    Also audit module and function descriptions without loading the module.
    """
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    # The first AST statement must be an explanatory module docstring.
    # This includes package facades and test files with no named functions.
    purpose = ast.get_docstring(tree)
    module_documented = bool(purpose and len(purpose.split()) >= 6)
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
            normalized_arguments = []
            if isinstance(decorator, ast.Call):
                for argument in decorator.args:
                    # An unused lambda parameter never affects the checked
                    # proposition. Normalize closed predicates even when one
                    # validator accepts spare *args/**kwargs.
                    # Keep used parameters and defaults unchanged.
                    if isinstance(argument, ast.Lambda):
                        formals = {
                            parameter.arg for parameter in (
                                argument.args.posonlyargs + argument.args.args
                                + argument.args.kwonlyargs
                            )
                        }
                        for parameter in (argument.args.vararg, argument.args.kwarg):
                            if parameter is not None:
                                formals.add(parameter.arg)
                        referenced = {
                            name.id for name in ast.walk(argument.body)
                            if isinstance(name, ast.Name)
                        }
                        if (not formals.intersection(referenced)
                                and not argument.args.defaults
                                and not any(default is not None for default in argument.args.kw_defaults)):
                            normalized_arguments.append((
                                "closed-lambda", ast.dump(argument.body, include_attributes=False)
                            ))
                        else:
                            normalized_arguments.append((
                                "lambda", ast.dump(argument, include_attributes=False)
                            ))
                    else:
                        normalized_arguments.append((
                            "expression", ast.dump(argument, include_attributes=False)
                        ))
            identity = (expression.attr,
                        tuple(normalized_arguments) if isinstance(decorator, ast.Call) else None,
                        tuple((keyword.arg, ast.dump(keyword.value, include_attributes=False))
                              for keyword in decorator.keywords)
                        if isinstance(decorator, ast.Call) else None)
            identities.append(identity)
        # Every nested or top-level function needs its own description.
        # The AST excludes decorator-looking text inside strings/comments.
        description = ast.get_docstring(node)
        documented = bool(description and len(description.split()) >= 6)
        function_contracts.append({"name": node.name, "line": node.lineno,
                                   "documented": documented,
                                   "contract_count": len(decorators),
                                   "distinct_contract_count": len(set(identities)),
                                   "duplicate_contract_count": len(identities) - len(set(identities))})
    missing = [{"name": row["name"], "line": row["line"]} for row in function_contracts
               if row["contract_count"] == 0]
    insufficient = [row for row in function_contracts if row["distinct_contract_count"] < MINIMUM_CONTRACTS]
    duplicated = [row for row in function_contracts if row["duplicate_contract_count"]]
    undocumented = [{"name": row["name"], "line": row["line"]}
                    for row in function_contracts if not row["documented"]]
    count = sum(row["contract_count"] for row in function_contracts)
    distinct = sum(row["distinct_contract_count"] for row in function_contracts)
    # Count only distinct AST contract expressions *within each function*.
    # Identical-looking contracts on different callable boundaries are
    # different checks, whereas repeating one decorator is not progress.
    file_below_floor = bool(functions) and distinct < MINIMUM_FILE_CONTRACTS
    return {"path": str(path), "function_count": len(functions), "missing": missing,
            "module_documented": module_documented, "undocumented": undocumented,
            "imports_deal": bool(aliases), "contract_count": count,
            "file_distinct_contract_count": distinct,
            "minimum_contracts": MINIMUM_CONTRACTS,
            "minimum_file_contracts": MINIMUM_FILE_CONTRACTS,
            "insufficient_file": file_below_floor,
            "function_contracts": function_contracts,
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
@deal.pre(lambda root: root.is_absolute())
@deal.post(lambda result: all(path.is_absolute() for path in result))
@deal.ensure(lambda root, result: all(path.resolve().is_relative_to(root.resolve()) for path in result))
@deal.post(lambda result: all(path.parent.is_dir() for path in result))
@deal.post(lambda result: all(path.resolve().is_file() for path in result))
def python_files(root: Path) -> list:
    """Enumerate every relevant tracked Python file within the repository root.
    
    Use the Git index when present and a constrained local fallback otherwise.
    Reject empty inventories, path escapes, symlinks, and duplicate entries.
    """
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
@deal.pre(lambda: isinstance(MINIMUM_CONTRACTS, int) and MINIMUM_CONTRACTS >= 15)
@deal.pre(lambda: isinstance(MINIMUM_FILE_CONTRACTS, int) and MINIMUM_FILE_CONTRACTS >= MINIMUM_CONTRACTS)
@deal.pre(lambda: isinstance(TARGET_CONTRACTS, int) and TARGET_CONTRACTS >= MINIMUM_CONTRACTS)
@deal.pre(lambda: {"pre", "post", "ensure", "raises", "has"} <= CONTRACTS)
@deal.pre(lambda: ROOT.is_absolute())
@deal.pre(lambda: ROOT.joinpath("verification", "check_contract_coverage.py").is_file())
@deal.pre(lambda: ROOT.joinpath("tests").is_dir())
@deal.pre(lambda: ROOT.joinpath("AGENTS.md").is_file())
@deal.pre(lambda: bool(sys.argv) and isinstance(sys.argv[0], str))
@deal.pre(lambda: CONTRACTS <= {"pre", "post", "ensure", "raises", "reason", "has", "pure", "safe", "inv", "example", "chain"})
def main() -> None:
    """Run the fail-closed repository-wide Deal contract compliance audit.
    
    Report per-file and per-function coverage alongside the minimum distinct floor.
    Return nonzero on missing imports, duplicate contracts, or any below-floor function.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    rows = [audit_file(path) for path in python_files(args.root)]
    # Import-only package entry points and compatibility facades contain
    # no subprograms and therefore have no Deal obligations to decorate.
    # A file with even one named function must still import Deal and
    # meet the full >=15 per-function contract floor; the negative fixture
    # tests this non-vacuous requirement.
    problems = [r for r in rows if r["insufficient"] or r["insufficient_file"]
                or r["duplicated"] or r["undocumented"] or not r["module_documented"]
                or (r["function_count"] > 0
                    and (not r["imports_deal"] or r["contract_count"] == 0))]
    report = {"python_files": len(rows), "named_functions": sum(r["function_count"] for r in rows),
              "deal_contracts": sum(r["contract_count"] for r in rows), "problems": problems,
              "minimum_contracts": MINIMUM_CONTRACTS,
              "minimum_file_contracts": MINIMUM_FILE_CONTRACTS,
              "files_below_minimum": sum(r["insufficient_file"] for r in rows),
              "files_without_purpose": sum(not r["module_documented"] for r in rows),
              "undocumented_functions": sum(len(r["undocumented"]) for r in rows),
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
