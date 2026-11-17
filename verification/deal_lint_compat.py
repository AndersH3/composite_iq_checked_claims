"""Repair Deal 4.24.6 synthetic AST range metadata before full static lint.

The upstream Deal linter constructs a compilation AST that can retain an
end-column offset earlier than its start-column offset on Python 3.12/3.13.
Only invalid location metadata is repaired. The contract validator and the
linter's mathematical/effect checks are not weakened or bypassed.
Requesting researcher: Anders Hellström. AI-assisted implementation.
"""

import ast
from types import CodeType

import deal
from deal.linter._contract import Category, Contract


@deal.pre(lambda contract: isinstance(contract, Contract))
@deal.pre(lambda contract: isinstance(contract.category, Category))
@deal.pre(lambda contract: isinstance(contract.args, tuple))
@deal.pre(lambda contract: isinstance(contract.kwargs, tuple))
@deal.pre(lambda contract: isinstance(contract.context, dict))
@deal.pre(lambda contract: isinstance(contract.func_args, ast.arguments))
@deal.pre(lambda contract: isinstance(contract.line, int))
@deal.pre(lambda contract: contract.line >= 0)
@deal.pre(lambda contract: isinstance(contract.module, ast.Module))
@deal.pre(lambda contract: isinstance(contract.module.body, list))
@deal.pre(lambda contract: bool(contract.module.body))
@deal.post(lambda result: isinstance(result, CodeType))
@deal.post(lambda result: result.co_filename == "<ast>")
@deal.post(lambda result: result.co_name == "<module>")
@deal.post(lambda result: result.co_argcount == 0)
@deal.post(lambda result: result.co_posonlyargcount == 0)
@deal.post(lambda result: result.co_kwonlyargcount == 0)
@deal.post(lambda result: result.co_nlocals == 0)
@deal.post(lambda result: bool(result.co_code))
@deal.raises(SyntaxError, ValueError, TypeError)
@deal.has()
def compile_fixed_locations(contract: Contract) -> CodeType:
    """Compile full Deal contract AST, repairing source-location ranges only.

    Invariant: all executable AST nodes, lambda argument annotations, external
    dependencies, effect contracts and computed validator expressions are
    preserved unchanged. Only impossible location end markers are corrected.
    The compiled module is ordinary top-level Python bytecode.
    """
    module = ast.fix_missing_locations(contract.module)
    for node in ast.walk(module):
        start_line = getattr(node, "lineno", None)
        end_line = getattr(node, "end_lineno", None)
        if start_line is None or end_line is None:
            continue
        if end_line < start_line:
            node.end_lineno = start_line
            end_line = start_line
        start_col = getattr(node, "col_offset", None)
        end_col = getattr(node, "end_col_offset", None)
        if (start_line == end_line and start_col is not None
                and end_col is not None and end_col < start_col):
            node.end_col_offset = start_col
    return compile(module, filename="<ast>", mode="exec")
