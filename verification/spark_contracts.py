"""Inventory explicit contracts in this project's restricted Ada source subset.

This is a structural audit, not an Ada frontend or a proof of contract adequacy.
GNAT compiles the source; GNATprove independently reports body/spec coverage.
Top-level Pre/Post conjunctions, Contract_Cases alternatives, and each explicit
Global/Depends aspect count. Ghost, SPARK_Mode, subtype ranges,
assertions in bodies, implicit contracts, and repeated syntax do not count.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import deal

SCHEMA = "explicit-contract-clauses-v1"
MINIMUM = 5
# Staged target: structural inventory reports ten independently written
# explicit SPARK clauses/aspects without making ten mandatory globally.
TARGET = 10
ROOT = Path(__file__).resolve().parents[1]
SPACE = re.compile(r"\s+")
QUALIFIER = re.compile(r"\b(?:[a-z_]\w*\.)+")
MASK = re.compile(r'--[^\n]*|"(?:[^" ]| |"")*"|\'[^\n\']\'')


@deal.pre(lambda condition, message: isinstance(condition, bool))
@deal.pre(lambda condition, message: isinstance(message, str) and bool(message))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.has()
def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, str))
@deal.ensure(lambda text, result: len(result) == len(text))
@deal.raises()
@deal.has()
# A masked Ada source must never acquire new syntactic tokens or move
# native line offsets. The five additional laws check positional
# preservation, line widths, symbol conservation and delimiter bounds.
@deal.ensure(lambda text, result: result.count("\n") == text.count("\n"))
@deal.ensure(lambda text, result:
             [len(part) for part in result.split("\n")] ==
             [len(part) for part in text.split("\n")])
@deal.ensure(lambda text, result:
             all(actual == original or actual == " "
                 for original, actual in zip(text, result)))
@deal.ensure(lambda text, result:
             result.count("(") <= text.count("(") and
             result.count(")") <= text.count(")"))
@deal.ensure(lambda text, result:
             result.count(";") <= text.count(";") and
             result.count(",") <= text.count(","))
def masked(text: str) -> str:
    # Retain newlines and character positions for native source-location checks.
    return MASK.sub(lambda match: "".join("\n" if char == "\n" else " " for char in match.group()), text)


@deal.pre(lambda text, separator=",": isinstance(text, str))
@deal.pre(lambda text, separator=",": separator in {",", ";", r"\band\s+then\b|\band\b"})
@deal.post(lambda result: isinstance(result, list) and bool(result))
@deal.raises(ValueError)
@deal.has()
# A top-level split may remove separators and adjacent whitespace but
# cannot fabricate clause characters, reverse prefix/suffix fragments,
# change source token order or leave whitespace on returned fragments.
@deal.post(lambda result: all(isinstance(part, str) for part in result))
@deal.post(lambda result: all(part == part.strip() for part in result))
@deal.ensure(lambda text, separator=",", *, result:
             all(not part or part in text for part in result))
@deal.ensure(lambda text, separator=",", *, result:
             sum(len(part) for part in result) <= len(text))
@deal.ensure(lambda text, separator=",", *, result:
             text.strip().startswith(result[0]) and
             text.strip().endswith(result[-1]))
def split_top(text: str, separator: str = ",") -> list:
    result = []
    start = 0
    depth = 0
    for match in re.finditer(r"\(|\)|" + separator, masked(text), re.IGNORECASE):
        token = match.group()
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
            require(depth >= 0, "Unbalanced contract parentheses")
        elif depth == 0:
            result.append(text[start:match.start()].strip())
            start = match.end()
    require(depth == 0, "Unbalanced contract parentheses")
    return [*result, text[start:].strip()]


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, str))
@deal.ensure(lambda text, result: len(result) <= len(text))
@deal.raises(ValueError)
@deal.has()
# Parsing may remove only complete outer parenthesis pairs; no token may be
# synthesized, and ordinary top-level conjunctions must remain untouched.
@deal.ensure(lambda text, result: result == result.strip())
@deal.ensure(lambda text, result: result in text)
@deal.ensure(lambda text, result:
             result == text.strip() or text.strip().startswith("("))
@deal.ensure(lambda text, result:
             result == text.strip() or text.strip().endswith(")"))
@deal.ensure(lambda text, result:
             result == text.strip() or len(result) + 2 <= len(text.strip()))
def unparenthesized(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        closing = -1
        for index, char in enumerate(masked(text)):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closing = index
                    break
        require(closing >= 0, "Unbalanced outer parentheses")
        if closing != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, list))
@deal.post(lambda result: bool(result) and all(isinstance(item, str) and bool(item) for item in result))
@deal.raises(ValueError)
@deal.has()
def clauses(text: str) -> list:
    require(bool(text.strip()), "Empty behavioral contract clause")
    text = unparenthesized(text)
    require(bool(text), "Empty parenthesized behavioral contract clause")
    # An unparenthesized conditional or quantified expression is one clause:
    # splitting its inner conjunction would change the asserted proposition.
    if re.match(r"(?:if|for)\b", text, re.IGNORECASE):
        return [text]
    return split_top(text, r"\band\s+then\b|\band\b")


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, list))
@deal.post(lambda result: all(row["line"] > 0 and row["end_line"] >= row["line"] for row in result))
@deal.raises(ValueError)
@deal.has()
def declarations(text: str) -> list:
    code = masked(text)
    result = []
    for match in re.finditer(r"\b(function|procedure)\s+(\w+)\b", code, re.IGNORECASE):
        depth = 0
        boundary = None
        expression = False
        form = "declaration"
        profile_end = None
        for token in re.finditer(r"\(|\)|;|\bis\b", code[match.end():], re.IGNORECASE):
            position = match.end() + token.start()
            value = token.group().lower()
            if value == "(":
                depth += 1
            elif value == ")":
                depth -= 1
            elif depth == 0:
                boundary = position
                if value == "is":
                    form = "body"
                    profile_end = position
                    cursor = position + 2
                    while cursor < len(code) and code[cursor].isspace():
                        cursor += 1
                    if cursor < len(code) and code[cursor] == "(":
                        expression = True
                        form = "expression"
                        level = 0
                        for end in range(cursor, len(code)):
                            level += (code[end] == "(") - (code[end] == ")")
                            if level == 0:
                                boundary = code.find(";", end + 1)
                                break
                break
        require(boundary is not None and boundary >= match.end(), "Incomplete Ada subprogram header")
        header = text[match.start():boundary]
        # Expression functions place aspects after their expression; declarations
        # and bodies put aspects before their final ';' or 'is'.
        aspect = re.search(r"\bwith\b", masked(header), re.IGNORECASE)
        values = {}
        profile = header[:aspect.start()] if aspect else header[:profile_end - match.start()] if profile_end is not None else header
        if aspect:
            for item in split_top(header[aspect.end():]):
                # Remove only comments here. Preserve literal strings/characters
                # in the clause inventory, and retain source lines separately.
                item = MASK.sub(lambda match: "".join("\n" if char == "\n" else " " for char in match.group())
                                if match.group().startswith("--") else match.group(), item)
                pair = item.split("=>", 1)
                key = pair[0].strip().casefold()
                require(key not in values, "Duplicate Ada aspect")
                values[key] = pair[1].strip() if len(pair) == 2 else ""
        result.append({"name": match.group(2), "kind": match.group(1).lower(),
                       "line": text.count("\n", 0, match.start()) + 1,
                       "end_line": text.count("\n", 0, boundary) + 1,
                       "expression": expression, "form": form,
                       "profile": SPACE.sub(" ", profile).casefold(), "aspects": values,
                       "off": bool(re.search(r"\bspark_mode\s*=>\s*off\b", masked(header), re.IGNORECASE))})
    return result


@deal.pre(lambda aspects: isinstance(aspects, dict))
@deal.pre(lambda aspects: all(isinstance(key, str) and isinstance(value, str) for key, value in aspects.items()))
@deal.post(lambda result: isinstance(result, list))
@deal.raises(ValueError)
@deal.has()
# No generated clause may have a foreign aspect, lose its string source,
# or escape the exact two-field evidence representation.
@deal.post(lambda result: all(isinstance(row, dict) for row in result))
@deal.post(lambda result: all(set(row) == {"aspect", "clause"} for row in result))
@deal.post(lambda result: all(isinstance(row["clause"], str) for row in result))
@deal.ensure(lambda aspects, result: all(row["aspect"] in aspects for row in result))
@deal.post(lambda result: all(row["aspect"] in
             {"global", "depends", "pre", "post", "refined_post", "contract_cases"}
             for row in result))
def contract_entries(aspects: dict) -> list:
    result = []
    identities = set()
    for aspect, value in aspects.items():
        value = MASK.sub(lambda match: "".join("\n" if char == "\n" else " " for char in match.group())
                         if match.group().startswith("--") else match.group(), value)
        if aspect in {"global", "depends"}:
            pieces = [value or "True"]
        elif aspect in {"pre", "post", "refined_post"}:
            pieces = clauses(value)
        elif aspect == "contract_cases":
            pieces = split_top(unparenthesized(value))
        else:
            continue
        for piece in pieces:
            # Ada names are case-insensitive. Whitespace is immaterial outside
            # string/character literals, whose original text is retained here.
            identity = (aspect, SPACE.sub("", unparenthesized(piece)).casefold())
            require(identity not in identities, "Repeated explicit contract clause")
            require(identity[1] not in {"true", "false"},
                    "Literal Boolean padding is not a behavioral contract")
            identities.add(identity)
            result.append({"aspect": aspect, "clause": piece})
    return result


@deal.pre(lambda sources, coverage=None: isinstance(sources, dict) and bool(sources))
@deal.pre(lambda sources, coverage=None: all(isinstance(key, str) and isinstance(value, str) for key, value in sources.items()) and (coverage is None or isinstance(coverage, dict)))
@deal.post(lambda result: result["schema"] == SCHEMA and result["minimum_required"] == MINIMUM)
@deal.raises(ValueError)
@deal.has()
# This legacy inventory is intentionally source/evidence schema stable.
# Check five independent accounting equations without changing its keys:
# historical SPARK campaign audits compare complete inventory dictionaries.
@deal.post(lambda result:
           result["functions"] + result["procedures"] == len(result["entities"]))
@deal.post(lambda result:
           result["contracts"] == sum(row["contract_count"] for row in result["entities"]))
@deal.post(lambda result:
           result["minimum_observed"] == min(row["contract_count"] for row in result["entities"]))
@deal.post(lambda result:
           result["insufficient"] == [row["identity"] for row in result["entities"]
                                      if row["contract_count"] < MINIMUM])
@deal.post(lambda result:
           result["complete"] == (not (result["insufficient"] or
                                     result["missing_native"] or
                                     result["invalid_native"] or
                                     result["unmatched_native"])))
def inventory(sources: dict, coverage: dict | None = None) -> dict:
    candidates = {}
    excluded = []
    files = []
    for path, text in sorted(sources.items()):
        relative = Path(path)
        require(relative.suffix in {".ads", ".adb"} and not relative.is_absolute() and ".." not in relative.parts,
                "Expected a safe relative Ada source path")
        code = masked(text)
        require(re.search(r"\bpragma\s+SPARK_Mode\b", code, re.IGNORECASE) is None,
                "Pragma SPARK_Mode needs explicit parser support")
        package_off = bool(re.search(r"\bpackage\s+body\s+\w+\s+with\s+[^;]*?\bSPARK_Mode\s*=>\s*Off\b", code, re.IGNORECASE))
        files.append({"path": path, "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest()})
        for row in declarations(text):
            identity = relative.stem.casefold() + "." + row["name"].casefold()
            row.update(path=path, identity=identity)
            if package_off or row["off"]:
                excluded.append({"path": path, "line": row["line"], "name": row["name"], "reason": "SPARK_Mode Off completion"})
                continue
            candidates.setdefault(identity, []).append(row)
    rows = []
    native_seen = set()
    for identity, alternatives in sorted(candidates.items()):
        require(len(alternatives) <= 2, "Ambiguous spec/body pairing: " + identity)
        require(len({SPACE.sub("", QUALIFIER.sub("", row["profile"])) for row in alternatives}) == 1, "Overloaded subprogram needs explicit parser support: " + identity)
        declarations_only = [row for row in alternatives if row["form"] == "declaration"]
        bodies = [row for row in alternatives if row["form"] != "declaration"]
        require(len(declarations_only) <= 1 and len(bodies) <= 1, "Repeated subprogram name needs explicit parser support: " + identity)
        specs = [row for row in alternatives if row["path"].endswith(".ads")]
        require(len(specs) <= 1, "Ambiguous Ada specification")
        selected = specs[0] if specs else declarations_only[0] if declarations_only else alternatives[0]
        entries = contract_entries(selected["aspects"])
        statuses = set()
        if coverage is not None:
            for entity in coverage["entities"]:
                if entity["name"].rsplit(".", 1)[-1].casefold() == selected["name"].casefold() and any(Path(frame["file"]).name == Path(row["path"]).name and row["line"] <= frame["line"] <= row["end_line"]
                       for frame in entity["sloc"] for row in alternatives):
                    statuses.add(entity["status"])
                    native_seen.add((entity["name"], entity["file"], entity["line"]))
        rows.append({"identity": identity, "name": selected["name"], "kind": selected["kind"],
                     "path": selected["path"], "line": selected["line"], "contracts": entries,
                     "contract_count": len(entries), "native_statuses": sorted(statuses),
                     "imported": "import" in selected["aspects"]})
    require(bool(rows), "Empty SPARK contract inventory")
    insufficient = [row["identity"] for row in rows if row["contract_count"] < MINIMUM]
    missing_native = [row["identity"] for row in rows if not row["native_statuses"] and not row["imported"]] if coverage is not None else []
    invalid_native = [row["identity"] for row in rows if "no" in row["native_statuses"]]
    unmatched_native = []
    if coverage is not None:
        by_name = {Path(path).name: text for path, text in sources.items()}
        require(len(by_name) == len(sources), "Ambiguous source basenames in native audit")
        for entity in coverage["entities"]:
            if (entity["name"], entity["file"], entity["line"]) in native_seen:
                continue
            # Native metadata also lists packages and private types, which are
            # not subprograms and are outside this per-subprogram floor.
            non_subprogram = False
            for frame in entity["sloc"]:
                if Path(frame["file"]).name in by_name:
                    text = by_name[Path(frame["file"]).name]
                    lines = masked(text).splitlines()
                    require(0 < frame["line"] <= len(lines), "Native location outside pinned source")
                    declaration = re.search(r"\b(?:package(?:\s+body)?|type|subtype)\s+(\w+)", lines[frame["line"] - 1], re.IGNORECASE)
                    if declaration and declaration.group(1).casefold() == entity["name"].rsplit(".", 1)[-1].casefold():
                        non_subprogram = True
            if not non_subprogram:
                unmatched_native.append(entity["name"])
    return {"schema": SCHEMA, "minimum_required": MINIMUM,
            "minimum_observed": min(row["contract_count"] for row in rows),
            "functions": sum(row["kind"] == "function" for row in rows),
            "procedures": sum(row["kind"] == "procedure" for row in rows),
            "contracts": sum(row["contract_count"] for row in rows), "entities": rows,
            "sources": files, "excluded_completions": excluded,
            "insufficient": insufficient, "missing_native": missing_native,
            "invalid_native": invalid_native, "unmatched_native": unmatched_native,
            "native_cross_check": coverage is not None,
            "complete": not insufficient and not missing_native and not invalid_native and not unmatched_native}



@deal.pre(lambda report: isinstance(report, dict))
@deal.pre(lambda report: isinstance(report.get("entities"), list))
@deal.post(lambda result: result["target_contracts"] == TARGET)
@deal.ensure(lambda report, result: result["total_entities"] == len(report["entities"]))
@deal.ensure(lambda report, result:
             result["entities_at_target"] ==
             sum(row["contract_count"] >= TARGET for row in report["entities"]))
@deal.ensure(lambda report, result:
             result["entities_below_target"] ==
             sum(row["contract_count"] < TARGET for row in report["entities"]))
@deal.post(lambda result:
           result["entities_at_target"] + result["entities_below_target"]
           == result["total_entities"])
@deal.post(lambda result: set(result) ==
           {"target_contracts", "total_entities", "entities_at_target",
            "entities_below_target"})
@deal.raises(KeyError, TypeError)
@deal.has()
def ten_contract_summary(report: dict) -> dict:
    """Summarize staged SPARK ten-clause progress without changing archive schemas.

    The immutable evidence campaigns persist the original inventory's exact
    keys. This separate derived report is not part of those archived checks.
    The target concerns clause-count coverage, not GNATprove proof status.
    """
    counts = [row["contract_count"] for row in report["entities"]]
    return {"target_contracts": TARGET, "total_entities": len(counts),
            "entities_at_target": sum(count >= TARGET for count in counts),
            "entities_below_target": sum(count < TARGET for count in counts)}


@deal.pre(lambda root: isinstance(root, Path))
@deal.pre(lambda root: root.is_dir())
@deal.post(lambda result: isinstance(result, dict) and bool(result))
@deal.raises(OSError, UnicodeDecodeError)
@deal.has("read")
# Return sorted, strictly source-root-relative Ada file receipts; every
# returned value is the exact current UTF-8 source, not a masked or
# normalized text that could be accidentally mistaken for native evidence.
@deal.post(lambda result: list(result) == sorted(result))
@deal.post(lambda result: all(Path(path).suffix in {".ads", ".adb"}
                              for path in result))
@deal.post(lambda result: all(path.startswith(("analyses/", "verification/"))
                              for path in result))
@deal.post(lambda result: all(not Path(path).is_absolute()
                              and ".." not in Path(path).parts
                              for path in result))
@deal.ensure(lambda root, result:
             all(root.joinpath(path).read_text(encoding="utf-8") == content
                 for path, content in result.items()))
def current_sources(root: Path) -> dict:
    paths = sorted(root.glob("analyses/*/ada/src/*.ad[bs]"))
    paths += sorted(root.glob("verification/*/src/*.ad[bs]"))
    return {path.relative_to(root).as_posix(): path.read_text(encoding="utf-8") for path in paths}


@deal.raises(SystemExit, OSError, ValueError, UnicodeDecodeError, TypeError, KeyError)
@deal.has("read", "stdout", "stderr")
@deal.pre(lambda: isinstance(sys.argv, list))
@deal.pre(lambda: all(isinstance(argument, str) for argument in sys.argv))
@deal.pre(lambda: ROOT.is_dir())
def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    result = inventory(current_sources(args.root))
    # Keep the evidence-sensitive inventory unchanged. Only the CLI report
    # contains the derived staged target accounting.
    print(json.dumps({**result, "ten_contract_target": ten_contract_summary(result)},
                     indent=2))
    raise SystemExit(0 if result["complete"] else 1)


if __name__ == "__main__":
    deal.enable(warn=False)
    main()
