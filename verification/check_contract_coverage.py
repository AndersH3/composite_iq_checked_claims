#!/usr/bin/env python3
"""Require real Deal decorators on every named function in repository Python."""
import argparse
import ast
import json
from pathlib import Path
import subprocess

import deal

ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = {"pre", "post", "ensure", "raises", "reason", "has", "pure", "safe", "inv", "example", "chain"}


@deal.pre(lambda node, aliases: isinstance(node, ast.expr) and isinstance(aliases, set))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
def is_contract(node: ast.expr, aliases: set) -> bool:
    expression = node.func if isinstance(node, ast.Call) else node
    return (isinstance(expression, ast.Attribute) and isinstance(expression.value, ast.Name)
            and expression.value.id in aliases and expression.attr in CONTRACTS)


@deal.pre(lambda path: isinstance(path, Path) and path.suffix == ".py")
@deal.post(lambda result: result["function_count"] >= 0 and isinstance(result["missing"], list)
           and isinstance(result["imports_deal"], bool) and result["contract_count"] >= 0)
@deal.raises(OSError, ValueError, SyntaxError)
@deal.has("read", "import")
def audit_file(path: Path) -> dict:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    aliases = {alias.asname or "deal" for node in tree.body if isinstance(node, ast.Import)
               for alias in node.names if alias.name == "deal"}
    functions = [node for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]
    missing = [{"name": node.name, "line": node.lineno} for node in functions
               if not any(is_contract(d, aliases) for d in node.decorator_list)]
    count = sum(is_contract(d, aliases) for node in functions for d in node.decorator_list)
    return {"path": str(path), "function_count": len(functions), "missing": missing,
            "imports_deal": bool(aliases), "contract_count": count}


@deal.pre(lambda root: isinstance(root, Path) and root.is_dir())
@deal.post(lambda result: isinstance(result, list) and len(result) > 0
           and len(result) == len(set(result)) and all(p.suffix == ".py" for p in result))
@deal.raises(OSError, ValueError, subprocess.SubprocessError)
@deal.has("read", "syscall")
def python_files(root: Path) -> list:
    process = subprocess.run(["git", "-C", str(root), "ls-files", "--cached", "--others",
                              "--exclude-standard", "--", "*.py"], capture_output=True,
                             text=True, timeout=15)
    if process.returncode == 0:
        paths = [root.joinpath(relative) for relative in process.stdout.splitlines()]
    else:
        # Support this computer10 workspace, which was authored through the
        # GitHub connector rather than a local checkout. CI uses Git's inventory.
        ignored = {".git", ".venv", ".venv-deal", "venv", "__pycache__", "obj", "obj-proof", "proof_obj", "bin"}
        paths = [p for p in root.rglob("*.py") if not ignored.intersection(p.relative_to(root).parts)]
    paths = sorted(set(paths))
    if not paths:
        raise ValueError("Empty Python inventory cannot establish coverage")
    return paths


@deal.raises(SystemExit, OSError, ValueError, SyntaxError, subprocess.SubprocessError)
@deal.has("read", "stdout", "stderr", "syscall", "import")
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    rows = [audit_file(path) for path in python_files(args.root)]
    problems = [r for r in rows if r["missing"] or not r["imports_deal"] or r["contract_count"] == 0]
    report = {"python_files": len(rows), "named_functions": sum(r["function_count"] for r in rows),
              "deal_contracts": sum(r["contract_count"] for r in rows), "problems": problems,
              "complete": not problems}
    print(json.dumps(report, indent=2))
    raise SystemExit(1 if problems else 0)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
