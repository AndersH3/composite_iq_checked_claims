#!/usr/bin/env python3
"""Check exact positive/negative Deal theorems with a scoped integer-type model.

Deal Solver 0.1.2 does not model isinstance. This version-pinned extension
handles only isinstance(value, int) on known primitive solver sorts. It retains
Python's bool-is-an-int behavior and fails closed for every unsupported class
or sort. Runtime contracts and third-party package files are never changed.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import sys

import deal
import deal_solver
from deal._cli._prove import DealTheorem
from deal_solver import Conclusion, Proof, UnsupportedError
from deal_solver._funcs import FUNCTIONS
from deal_solver._funcs._builtins import builtins_int
from deal_solver._proxies import BoolSort, FloatSort, FuncSort, IntSort, ProxySort, StrSort
from deal_solver._context import Context
import z3

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "deal-symbolic-int-v1"
ADAPTER = "isinstance-int-v1"
NORMALIZATION = "pure-comparison-chains-v1"
EXPECTED = {
    "verification/proof_gate.py": {
        "totals_balanced": ["proved"] * 6,
        "successful_checks": ["proved"] * 6,
    },
    "tests/fixtures/contract_negative_control.py": {
        "probability_identity": ["proved", "proved"],
        "negative_probability": ["counterexample", "proved", "proved"],
    },
}
PROTECTED_NAMES = {"deal", "isinstance", "int", "bool", "float", "str"}


@deal.pre(lambda condition, message: isinstance(condition, bool))
@deal.pre(lambda condition, message: isinstance(message, str) and bool(message))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.has()
def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@deal.pre(lambda value, classinfo, ctx, **kwargs: isinstance(value, ProxySort))
@deal.pre(lambda value, classinfo, ctx, **kwargs: isinstance(classinfo, ProxySort) and isinstance(ctx, Context))
@deal.post(lambda result: isinstance(result, BoolSort))
@deal.raises(UnsupportedError)
@deal.has()
def symbolic_isinstance_int(value: ProxySort, classinfo: ProxySort, /, *, ctx: Context, **kwargs) -> BoolSort:
    """Exact nominal type test for supported builtin scalar proxy classes."""
    if kwargs or not isinstance(classinfo, FuncSort) or classinfo.impl is not builtins_int:
        raise UnsupportedError("only positional isinstance(value, int) is modeled")
    if type(value) not in {IntSort, BoolSort, StrSort} and not isinstance(value, FloatSort):
        raise UnsupportedError("unmodeled isinstance value sort")
    return BoolSort.val(isinstance(value, (IntSort, BoolSort)), ctx=ctx)


@deal.post(lambda result: result == {"deal": "4.24.6", "deal_solver": "0.1.2"})
@deal.post(lambda result: isinstance(result, dict))
@deal.raises(ValueError)
@deal.has()
@deal.ensure(lambda result: FUNCTIONS.get("builtins.int") is builtins_int)
def check_toolchain() -> dict:
    require(deal.__version__ == "4.24.6" and deal_solver.__version__ == "0.1.2",
            "The symbolic adapter requires the pinned Deal/Deal Solver versions")
    require(FUNCTIONS.get("builtins.int") is builtins_int, "Unexpected builtin int solver implementation")
    return {"deal": deal.__version__, "deal_solver": deal_solver.__version__}


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises(SyntaxError, ValueError, TypeError)
@deal.has("import")
@deal.ensure(lambda text, result: not result or bool(text.strip()))
def source_is_supported(text: str) -> bool:
    """Accept only the small, effect-free grammar used by the two checked inputs.

    Native extraction ignores decorators, defaults and module execution. Reject
    those effects here rather than misreport a theorem for different Python.
    """
    if not text.strip():
        return False
    tree = ast.parse(text)
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)]
    imports = [node for node in tree.body if isinstance(node, ast.Import)]
    if len(imports) != 1 or len(imports[0].names) != 1:
        return False
    decorator_calls = []
    decorator_attributes = []
    for node in tree.body:
        if isinstance(node, ast.Import):
            if any(alias.name != "deal" or alias.asname is not None for alias in node.names):
                return False
        elif not isinstance(node, ast.FunctionDef) and not (
                isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)):
            return False
    for function in functions:
        arguments = function.args
        if (arguments.posonlyargs or arguments.kwonlyargs or arguments.vararg is not None
                or arguments.kwarg is not None or arguments.defaults or arguments.kw_defaults):
            return False
        if any(not isinstance(argument.annotation, ast.Name)
               or argument.annotation.id not in {"int", "bool", "float", "str"}
               for argument in arguments.args):
            return False
        if (not isinstance(function.returns, ast.Name)
                or function.returns.id not in {"int", "bool", "float", "str"}):
            return False
        if len(function.body) != 1 or not isinstance(function.body[0], ast.Return):
            return False
        for decorator in function.decorator_list:
            if (not isinstance(decorator, ast.Call) or decorator.keywords
                    or not isinstance(decorator.func, ast.Attribute)
                    or not isinstance(decorator.func.value, ast.Name)
                    or decorator.func.value.id != "deal"
                    or decorator.func.attr not in {"pre", "post", "ensure", "raises", "has"}):
                return False
            if decorator.func.attr in {"pre", "post", "ensure"}:
                if len(decorator.args) != 1 or not isinstance(decorator.args[0], ast.Lambda):
                    return False
            elif decorator.args:
                return False
            decorator_calls.append(decorator)
            decorator_attributes.append(decorator.func)
    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.AsyncFunctionDef)):
            return False
        if isinstance(node, ast.FunctionDef) and node not in functions:
            return False
        if isinstance(node, (ast.Import, ast.ImportFrom)) and node not in imports:
            return False
        if isinstance(node, ast.Attribute) and node not in decorator_attributes:
            return False
        if isinstance(node, ast.Call) and node not in decorator_calls and (
                not isinstance(node.func, ast.Name) or node.func.id != "isinstance"
                or node.keywords or len(node.args) != 2
                or not isinstance(node.args[1], ast.Name) or node.args[1].id != "int"):
            return False
        if isinstance(node, ast.Lambda) and (
                node.args.defaults or node.args.kw_defaults or node.args.vararg is not None
                or node.args.kwarg is not None or node.args.posonlyargs or node.args.kwonlyargs):
            return False
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in PROTECTED_NAMES:
            return False
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in PROTECTED_NAMES:
            return False
        if isinstance(node, ast.arg) and node.arg in PROTECTED_NAMES:
            return False
        if isinstance(node, (ast.Global, ast.Nonlocal)) and PROTECTED_NAMES.intersection(node.names):
            return False
        if isinstance(node, ast.ExceptHandler) and node.name in PROTECTED_NAMES:
            return False
        if isinstance(node, (ast.MatchAs, ast.MatchStar)) and node.name in PROTECTED_NAMES:
            return False
    return True


class ComparisonChains(ast.NodeTransformer):
    """Expand only side-effect-free chained comparison operands."""

    @deal.pre(lambda self, node: isinstance(self, ast.NodeTransformer))
    @deal.pre(lambda self, node: isinstance(node, ast.Compare))
    @deal.post(lambda result: isinstance(result, (ast.Compare, ast.BoolOp)))
    @deal.raises(UnsupportedError, ValueError, TypeError, RecursionError)
    @deal.has()
    def visit_Compare(self, node: ast.Compare) -> ast.AST:
        self.generic_visit(node)
        if len(node.ops) <= 1:
            return node
        operands = [node.left, *node.comparators]
        if not all(isinstance(value, (ast.Name, ast.Constant)) for value in operands):
            raise UnsupportedError("chained comparison has operands unsafe to repeat")
        values = [ast.Compare(left=operands[index], ops=[operator],
                              comparators=[operands[index + 1]])
                  for index, operator in enumerate(node.ops)]
        return ast.copy_location(ast.BoolOp(op=ast.And(), values=values), node)


@deal.pre(lambda text: isinstance(text, str) and bool(text.strip()))
@deal.post(lambda result: isinstance(result, str))
@deal.ensure(lambda text, result: not any(isinstance(node, ast.Compare) and len(node.ops) > 1
                                       for node in ast.walk(ast.parse(result))))
@deal.raises(UnsupportedError, SyntaxError, ValueError, TypeError, RecursionError)
@deal.has("import")
def normalized_source(text: str) -> str:
    """Preserve every contract while repairing native first-comparison-only evaluation."""
    tree = ComparisonChains().visit(ast.parse(text))
    return ast.unparse(ast.fix_missing_locations(tree))


@deal.pre(lambda proof: isinstance(proof, Proof))
@deal.post(lambda result: isinstance(result, dict) and isinstance(result["conclusion"], str))
@deal.ensure(lambda proof, result: result["conclusion"] == proof.conclusion.name and result["description"] == proof.description)
@deal.raises(ValueError, TypeError, NameError, SyntaxError)
@deal.has()
def proof_record(proof: Proof) -> dict:
    return {"conclusion": proof.conclusion.name, "description": proof.description,
            "error": None if proof.error is None else str(proof.error),
            "counterexample": None if proof.example is None else dict(proof.example)}


@deal.pre(lambda theorem: isinstance(theorem, DealTheorem))
@deal.post(lambda result: isinstance(result, list))
@deal.post(lambda result: all(row["index"] == index for index, row in enumerate(result)))
@deal.raises(UnsupportedError, RuntimeError, ValueError, TypeError, z3.Z3Exception, NameError, SyntaxError, RecursionError)
@deal.has()
def prove_obligations(theorem: DealTheorem) -> list:
    """Use native Deal constraints and native Z3 outcome interpretation per clause."""
    rows = []
    for index, constraint in enumerate(theorem.constraints):
        solver = z3.Solver(ctx=theorem._z3_context)
        solver.set(timeout=5000)
        solver.add(constraint.condition.expr)
        proof = theorem._prove(solver=solver, descr=constraint.description)
        record = proof_record(proof)
        record.update(index=index, kind=constraint.description,
                      outcome="proved" if proof.conclusion == Conclusion.OK else
                              "counterexample" if proof.conclusion == Conclusion.FAIL else "unsupported")
        rows.append(record)
    return rows


@deal.pre(lambda text: isinstance(text, str) and bool(text.strip()))
@deal.post(lambda result: isinstance(result, list))
@deal.post(lambda result: all(isinstance(row["name"], str) for row in result))
@deal.raises(UnsupportedError, RuntimeError, ValueError, TypeError, z3.Z3Exception, NameError, SyntaxError, RecursionError)
@deal.has("import")
def prove_text(text: str) -> list:
    require(source_is_supported(text), "Unsupported or shadowed builtin names in symbolic source")
    text = normalized_source(text)
    rows = []
    for theorem in DealTheorem.from_text(text):
        native = theorem.prove()
        if theorem._context.skips:
            raise UnsupportedError("Deal Solver skipped source statements")
        row = proof_record(native)
        # A fresh theorem/context avoids adding duplicate assumptions/returns
        # while independently enumerating every native obligation.
        fresh = next(value for value in DealTheorem.from_text(text) if value.name == theorem.name)
        row.update(name=theorem.name, obligations=prove_obligations(fresh))
        if fresh._context.skips:
            raise UnsupportedError("Deal Solver skipped source statements during clause audit")
        rows.append(row)
    return rows


@deal.pre(lambda report: isinstance(report, dict))
@deal.post(lambda result: isinstance(result, bool))
@deal.ensure(lambda report, result: not result or report.get("schema") == SCHEMA)
@deal.raises()
@deal.has()
def accepted(report: dict) -> bool:
    """Validate every expected theorem, clause and counterexample; ignore no skips."""
    if (report.get("schema") != SCHEMA or report.get("adapter") != ADAPTER or report.get("normalization") != NORMALIZATION
            or report.get("toolchain") != {"deal": "4.24.6", "deal_solver": "0.1.2"}):
        return False
    if "complete" in report and report["complete"] is not True:
        return False
    files = report.get("files")
    sources = report.get("sources")
    if not isinstance(files, list) or not isinstance(sources, list) or len(files) != len(EXPECTED):
        return False
    if not all(isinstance(row, dict) for row in files + sources):
        return False
    if not all(isinstance(row.get("path"), str) for row in files):
        return False
    if sorted(row.get("path", "") for row in files) != sorted(EXPECTED):
        return False
    if sources != [{"path": row.get("path"), "sha256": row.get("sha256")} for row in files]:
        return False
    for file in files:
        digest = file.get("sha256")
        if not isinstance(digest, str) or len(digest) != 64 or set(digest) - set("0123456789abcdef"):
            return False
        normalized_digest = file.get("normalized_sha256")
        if not isinstance(normalized_digest, str) or len(normalized_digest) != 64 or set(normalized_digest) - set("0123456789abcdef"):
            return False
        rows = file.get("theorems")
        expected = EXPECTED[file["path"]]
        if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
            return False
        if not all(isinstance(row.get("name"), str) for row in rows):
            return False
        if sorted(row.get("name", "") for row in rows) != sorted(expected):
            return False
        for row in rows:
            outcomes = expected[row["name"]]
            negative = "counterexample" in outcomes
            if (row.get("conclusion") != ("FAIL" if negative else "OK") or row.get("error") is not None
                    or row.get("description") != ", ".join(["post-condition"] * (1 if negative else len(outcomes)))
                    or (not isinstance(row.get("counterexample"), dict) if negative else row.get("counterexample") is not None)):
                return False
            obligations = row.get("obligations")
            if not isinstance(obligations, list) or len(obligations) != len(outcomes):
                return False
            for index, (obligation, outcome) in enumerate(zip(obligations, outcomes)):
                if (not isinstance(obligation, dict) or obligation.get("index") != index
                        or obligation.get("kind") != "post-condition" or obligation.get("outcome") != outcome
                        or obligation.get("conclusion") != ("FAIL" if outcome == "counterexample" else "OK")
                        or obligation.get("description") != "post-condition" or obligation.get("error") is not None
                        or (not isinstance(obligation.get("counterexample"), dict) if outcome == "counterexample" else obligation.get("counterexample") is not None)):
                    return False
    return True


@deal.pre(lambda root=ROOT: isinstance(root, Path) and root.is_dir())
@deal.post(lambda result: isinstance(result, dict) and type(result["complete"]) is bool)
@deal.ensure(lambda root=ROOT, result=None: "builtins.isinstance" not in FUNCTIONS)
@deal.raises(OSError, ValueError, TypeError, SyntaxError, UnsupportedError, RuntimeError, z3.Z3Exception, NameError, RecursionError, FileNotFoundError, PermissionError, UnicodeDecodeError)
@deal.has("read", "import", "global")
def run(root: Path = ROOT) -> dict:
    tools = check_toolchain()
    require("builtins.isinstance" not in FUNCTIONS, "Unexpected existing isinstance solver handler")
    files = []
    FUNCTIONS["builtins.isinstance"] = symbolic_isinstance_int
    try:
        for relative in EXPECTED:
            path = root.joinpath(relative)
            raw = path.read_bytes()
            files.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                          "normalized_sha256": hashlib.sha256(normalized_source(raw.decode("utf-8")).encode("utf-8")).hexdigest(),
                          "theorems": prove_text(raw.decode("utf-8"))})
    finally:
        del FUNCTIONS["builtins.isinstance"]
    report = {"schema": SCHEMA, "adapter": ADAPTER, "normalization": NORMALIZATION, "toolchain": tools, "files": files,
              "sources": [{"path": row["path"], "sha256": row["sha256"]} for row in files]}
    report["complete"] = accepted(report)
    return report


@deal.raises(SystemExit, OSError, ValueError, TypeError, SyntaxError, UnsupportedError, RuntimeError, z3.Z3Exception, NameError, RecursionError, FileNotFoundError, PermissionError, UnicodeDecodeError)
@deal.has("read", "import", "global", "stdout", "stderr")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(value, str) for value in sys.argv))
@deal.pre(lambda: ROOT.is_dir())
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    report = run(args.root.resolve())
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["complete"] else 1)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
