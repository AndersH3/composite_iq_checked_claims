"""Audit explicit ghost models without promoting them to implementation proofs.

The checks below establish source-pinned modeling coverage and real contract
references. They do not prove that an excluded implementation refines its model.
"""
import hashlib
import re
from pathlib import Path

import deal

GHOST_SCHEMA = "spark-ghost-boundaries-v1"
PROJECT_NAMES = {"hoeflin", "towers"}
GLOBAL_OBLIGATION_SCOPES = {"numerical-backends", "runtime-and-io", "model-adequacy",
                            "psychometric-validity", "toolchain-and-provers"}
REQUEST_RECEIPTS = {"hoeflin_boundary_models.note", "towers_io_models.observe_trials",
                    "towers_io_models.observe_seed", "towers_io_models.request_report",
                    "towers_io_models.observe_normal_return"}
STRINGS = re.compile(r'"(?:""|[^"])*"')
COMMENTS = re.compile(r"--[^\n]*")
WITH = re.compile(r"\bwith\b", re.IGNORECASE)


@deal.pre(lambda condition, message: isinstance(condition, bool) and isinstance(message, str))
@deal.post(lambda result: result is None)
@deal.raises(ValueError)
@deal.reason(ValueError, lambda condition, message: not condition)
@deal.has()
def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)
    return None


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: isinstance(result, str))
@deal.raises()
@deal.has()
@deal.ensure(lambda text, result: len(result) <= len(text))
def ada_code(text: str) -> str:
    """Remove strings and comments before checking Ada identifiers/contracts."""
    without_strings = STRINGS.sub('""', text)
    return COMMENTS.sub("", without_strings)


@deal.pre(lambda code, start: isinstance(code, str))
@deal.pre(lambda code, start: type(start) is int and 0 <= start <= len(code))
@deal.post(lambda result: type(result) is int and result >= 0)
@deal.raises()
@deal.has()
def declaration_end(code: str, start: int) -> int:
    depth = 0
    for index in range(start, len(code)):
        char = code[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == ";" and depth == 0:
            return index
    return len(code)


@deal.pre(lambda text, entity: isinstance(text, str))
@deal.pre(lambda text, entity: isinstance(entity, str) and bool(entity))
@deal.post(lambda result: isinstance(result, str) and bool(result))
@deal.raises(ValueError)
@deal.has()
def operation_body(text: str, entity: str) -> str:
    """Select a named body and exclude nested subprogram bodies from its link.

    The project uses named-end bodies and expression functions. Ambiguous or
    missing selected bodies fail closed; this is not a general Ada parser.
    """
    code = ada_code(text)
    definitions = []
    for match in re.finditer(r"\b(?:function|procedure)\s+(\w+)\b", code, re.IGNORECASE):
        header_end = declaration_end(code, match.end())
        header = code[match.end():header_end]
        body_start = re.search(r"\bis\b", header, re.IGNORECASE)
        if body_start is None:
            continue
        start = match.end() + body_start.end()
        tail = code[start:header_end].lstrip()
        named_end = re.search(r"\bend\s+" + re.escape(match.group(1)) + r"\s*;",
                              code[start:], re.IGNORECASE)
        end = header_end + 1 if tail.startswith("(") or named_end is None else start + named_end.end()
        definitions.append((match.group(1).casefold(), match.start(), start, end))
    leaf = entity.rsplit(".", 1)[-1].casefold()
    selected = [value for value in definitions if value[0] == leaf]
    require(len(selected) == 1, "Ghost coupling body is missing or ambiguous: " + entity)
    _, outer_start, start, end = selected[0]
    body = code[start:end]
    nested = sorted((a, b) for _, a, _, b in definitions if outer_start < a < end and b <= end)
    for a, b in reversed(nested):
        body = body[:a - start] + " " * (b - a) + body[b - start:]
    require(bool(body), "Ghost coupling body is empty")
    return body


@deal.pre(lambda text, reference: isinstance(text, str))
@deal.pre(lambda text, reference: isinstance(reference, str) and bool(reference))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
def contract_reference(text: str, reference: str) -> bool:
    """Only references in a Pre/Post aspect count, not comments or body calls."""
    code = ada_code(text)
    pattern = r"\b" + re.escape(reference).replace(r"\.", r"\s*\.\s*") + r"\s*\("
    for match in re.finditer(r"\b(?:Pre|Post)\s*=>", code, re.IGNORECASE):
        end = code.find(";", match.end())
        if end < 0:
            end = len(code)
        if re.search(pattern, code[match.end():end], re.IGNORECASE):
            return True
    return False


@deal.post(lambda result: isinstance(result, bool))
@deal.raises()
@deal.has()
@deal.ensure(lambda value, result: not result or isinstance(value, dict) and bool(value))
@deal.ensure(lambda value, result: not result or all(isinstance(key, str) and isinstance(text, str) for key, text in value.items()))
def source_mapping(value: object) -> bool:
    return isinstance(value, dict) and bool(value) and all(
        isinstance(key, str) and isinstance(text, str) for key, text in value.items())


@deal.pre(lambda text: isinstance(text, str))
@deal.post(lambda result: bool(result))
@deal.post(lambda result: isinstance(result, str))
@deal.raises(ValueError)
@deal.has()
def ghost_package(text: str) -> str:
    """Select a SPARK model package, including mixed ordinary/Ghost packages.

    Individual registered entities are checked separately. Package membership
    alone does not make an ordinary declaration Ghost.
    """
    header = re.search(r"\bpackage\s+(\w+)\s+with\s+([^;]*?)\bis\b",
                       ada_code(text), re.IGNORECASE)
    require(header is not None
            and re.search(r"\bSPARK_Mode\b", header.group(2), re.IGNORECASE) is not None
            and re.search(r"\bSPARK_Mode\s*=>\s*Off\b", header.group(2), re.IGNORECASE) is None,
            "Model must belong to a declared SPARK package")
    return header.group(1)


@deal.pre(lambda text, entity: isinstance(text, str))
@deal.pre(lambda text, entity: isinstance(entity, str) and bool(entity))
@deal.post(lambda result: result in {"ghost", "pure-function", "request-receipt"})
@deal.raises(ValueError)
@deal.has()
def model_entity_kind(text: str, entity: str) -> str:
    """Require Ghost observations or an explicit ordinary model role.

    Ordinary functions must declare Global=>null. The five named ordinary
    receipt updates mutate explicit request state; they make no physical IO
    guarantee. This source check is deliberately limited to the project's
    unoverloaded model declarations; native SPARK coverage is checked as well.
    """
    code = ada_code(text)
    package = ghost_package(text)
    require(entity.casefold().startswith(package.casefold() + "."),
            "Model entity belongs to another package")
    header = re.search(r"\bpackage\s+\w+\s+with\s+([^;]*?)\bis\b", code, re.IGNORECASE)
    if re.search(r"\bGhost\b", header.group(1), re.IGNORECASE) is not None:
        return "ghost"
    leaf = entity.rsplit(".", 1)[-1]
    declarations = list(re.finditer(r"\b(function|procedure)\s+" + re.escape(leaf) + r"\b",
                                   code, re.IGNORECASE))
    require(len(declarations) == 1, "Model declaration is missing or ambiguous: " + entity)
    selected = declarations[0]
    declaration = code[selected.end():declaration_end(code, selected.end())]
    require(re.search(r"\bSPARK_Mode\s*=>\s*Off\b", declaration, re.IGNORECASE) is None,
            "Model declaration cannot disable SPARK: " + entity)
    aspects = WITH.split(declaration)
    contract = aspects[-1] if len(aspects) > 1 else ""
    if re.search(r"(?:^|,)\s*Ghost\s*(?:,|$)", contract, re.IGNORECASE) is not None:
        return "ghost"
    require(re.search(r"\bGlobal\s*=>\s*null\b", contract, re.IGNORECASE) is not None,
            "Ordinary model must declare Global => null: " + entity)
    if selected.group(1).casefold() == "function":
        require(re.search(r"\bSide_Effects\b", contract, re.IGNORECASE) is None,
                "Ordinary model function must be pure: " + entity)
        return "pure-function"
    require(entity.casefold() in REQUEST_RECEIPTS,
            "Model observer/check procedure must be explicitly Ghost: " + entity)
    return "request-receipt"


@deal.pre(lambda sources, source_root: isinstance(sources, list))
@deal.pre(lambda sources, source_root: isinstance(source_root, Path) and source_root.is_dir())
@deal.post(source_mapping)
@deal.raises(OSError, FileNotFoundError, PermissionError, ValueError, UnicodeDecodeError)
@deal.has("read")
def pinned_ada_sources(sources: list, source_root: Path) -> dict:
    result = {}
    for entry in sources:
        require(isinstance(entry, dict), "Ghost source inventory entry must be an object")
        relative = entry.get("path")
        expected = entry.get("sha256")
        require(isinstance(relative, str) and bool(relative), "Ghost source path is missing")
        path = Path(relative)
        require(not path.is_absolute() and ".." not in path.parts, "Unsafe ghost source path")
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected) is not None,
                "Ghost source hash is invalid")
        if path.suffix not in {".ads", ".adb"}:
            continue
        require(relative not in result, "Duplicate ghost source path")
        actual = source_root.joinpath(path)
        require(actual.is_file() and not actual.is_symlink(), "Ghost source must be a regular file: " + relative)
        raw = actual.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == expected, "Ghost source hash differs: " + relative)
        result[relative] = raw.decode("utf-8")
    require(bool(result), "No pinned Ada sources for ghost coverage")
    return dict(result)


@deal.pre(lambda texts: isinstance(texts, dict))
@deal.pre(lambda texts: all((isinstance(k, str) and isinstance(v, str) for k, v in texts.items())))
@deal.post(lambda result: isinstance(result, dict)
           and all(isinstance(k, str) and isinstance(v, str) for k, v in result.items()))
@deal.raises(ValueError)
@deal.has()
def foreign_imports(texts: dict) -> dict:
    """Collect project foreign declarations, including imports absent from .spark."""
    found = {}
    for relative, text in texts.items():
        code = ada_code(text)
        package = re.search(r"\bpackage\s+(?:body\s+)?(\w+)\b", code, re.IGNORECASE)
        for start in re.finditer(r"\b(?:function|procedure)\s+(\w+)\b", code, re.IGNORECASE):
            end = declaration_end(code, start.end())
            header = code[start.end():end]
            if not re.search(r"\bImport\b", header, re.IGNORECASE):
                continue
            require(package is not None, "Foreign declaration must belong to an explicit package")
            name = package.group(1) + "." + start.group(1)
            key = name.casefold()
            require(key not in found, "Duplicate foreign declaration: " + name)
            found[key] = relative
    return found


@deal.pre(lambda texts: isinstance(texts, dict))
@deal.pre(lambda texts: all((isinstance(k, str) and isinstance(v, str) for k, v in texts.items())))
@deal.post(lambda result: isinstance(result, set) and all(isinstance(value, str) for value in result))
@deal.raises()
@deal.has()
def external_dependencies(texts: dict) -> set:
    internal = {Path(path).stem.replace("-", ".").casefold() for path in texts}
    units = set()
    for text in texts.values():
        code = ada_code(text)
        unit = re.search(r"\b(?:package|procedure|function)\s+(?:body\s+)?\w+\b", code, re.IGNORECASE)
        context = code if unit is None else code[:unit.start()]
        for match in re.finditer(r"\bwith\s+([A-Za-z][\w.]*(?:\s*,\s*[A-Za-z][\w.]*)*)\s*;",
                                 context, re.IGNORECASE):
            units.update(unit.strip().casefold() for unit in match.group(1).split(","))
    return units - internal


@deal.pre(lambda text, reference, entity, kind: isinstance(text, str))
@deal.pre(lambda text, reference, entity, kind: isinstance(reference, str) and bool(reference) and isinstance(entity, str) and bool(entity) and isinstance(kind, str))
@deal.post(lambda result: isinstance(result, bool))
@deal.raises(ValueError)
@deal.has()
def coupling_reference(text: str, reference: str, entity: str, kind: str) -> bool:
    require(kind in {"contract", "ghost-call", "model-call"}, "Unknown ghost coupling kind")
    if kind == "contract":
        leaf = entity.rsplit(".", 1)[-1]
        code = ada_code(text)
        for match in re.finditer(r"\b(?:function|procedure)\s+" + re.escape(leaf) + r"\b", code, re.IGNORECASE):
            end = declaration_end(code, match.end())
            if contract_reference(code[match.start():end], reference):
                return True
        return False
    body = operation_body(text, entity)
    qualified = r"\b" + re.escape(reference).replace(r"\.", r"\s*\.\s*") + r"\s*\("
    if re.search(qualified, body, re.IGNORECASE):
        return True
    package, leaf = reference.rsplit(".", 1)
    used = re.search(r"\buse\s+" + re.escape(package) + r"\s*;", ada_code(text), re.IGNORECASE)
    return used is not None and re.search(r"(?<![\w.])" + re.escape(leaf) + r"\s*\(", body, re.IGNORECASE) is not None


@deal.pre(lambda entries, texts, analyzed, math_dependency: isinstance(entries, list))
@deal.pre(lambda entries, texts, analyzed, math_dependency: isinstance(texts, dict) and isinstance(analyzed, dict) and isinstance(math_dependency, bool))
@deal.post(lambda result: isinstance(result, list) and len(result) in {0, 2})
@deal.raises(ValueError)
@deal.has()
def validate_standard_models(entries: list, texts: dict, analyzed: dict,
                             math_dependency: bool) -> list:
    expected = {"ada.numerics.long_elementary_functions.cos", "ada.numerics.long_elementary_functions.sin"} if math_dependency else set()
    names = [entry.get("entity") for entry in entries if isinstance(entry, dict)]
    require(len(names) == len(entries) and all(isinstance(name, str) for name in names)
            and len({name.casefold() for name in names}) == len(names)
            and {name.casefold() for name in names} == expected,
            "Standard-library model inventory differs")
    for entry in entries:
        model_file = entry.get("model_file")
        require(isinstance(model_file, str) and model_file in texts, "Standard model source is not pinned")
        package = ghost_package(texts[model_file])
        models = entry.get("model_entities")
        refs = entry.get("contract_refs")
        require(isinstance(models, list) and bool(models) and all(isinstance(model, str) for model in models)
                and isinstance(refs, list) and len(refs) == 1 and refs[0] in models,
                "Standard ghost model entities are invalid")
        for model in models:
            model_entity_kind(texts[model_file], model)
            row = analyzed.get(model.casefold())
            require(row is not None and model.casefold().startswith(package.casefold() + ".")
                    and Path(row.get("file", "")).name == Path(model_file).name,
                    "Standard ghost model body was not analyzed")
        require(entry.get("implementation_proved") is False and entry.get("model_adequacy_proved") is False,
                "Standard ghost model must not claim backend or adequacy proof")
        source = entry.get("contract_file")
        operation = entry.get("contract_entity")
        argument = entry.get("observed_argument")
        callee = entry.get("source_callee")
        require(isinstance(source, str) and source in texts and isinstance(operation, str) and bool(operation)
                and isinstance(argument, str) and re.fullmatch(r"[A-Za-z]\w*", argument) is not None
                and isinstance(callee, str) and bool(callee), "Standard model coupling fields are invalid")
        require(operation.casefold() in analyzed, "Standard model caller body was not analyzed")
        obligations = entry.get("obligations")
        require(isinstance(obligations, list) and bool(obligations)
                and all(isinstance(value, str) and bool(value.strip()) for value in obligations),
                "Standard model obligations are missing")
        code = ada_code(texts[source])
        short = entry["entity"].rsplit(".", 1)[-1]
        unit = "Ada.Numerics.Long_Elementary_Functions"
        require(callee.rsplit(".", 1)[-1].casefold() == short.casefold(), "Standard model callee differs")
        if "." not in callee:
            require(re.search(r"\buse\s+" + re.escape(unit) + r"\s*;", code, re.IGNORECASE) is not None,
                    "Unqualified standard callee is not imported")
        elif callee.rsplit(".", 1)[0].casefold() != unit.casefold():
            alias = callee.rsplit(".", 1)[0]
            require(re.search(r"\bpackage\s+" + re.escape(alias) + r"\s+renames\s+" + re.escape(unit) + r"\s*;",
                              code, re.IGNORECASE) is not None, "Standard callee alias is not bound")
        body = operation_body(texts[source], operation)
        require(model_entity_kind(texts[model_file], refs[0]) == "ghost",
                "Standard-library observer must be Ghost")
        assignment = re.search(r"\b" + re.escape(argument) + r"\s*:=\s*" + re.escape(callee) + r"\s*\(", body, re.IGNORECASE)
        observation = re.search(r"\b" + re.escape(refs[0]) + r"\s*\(\s*" + re.escape(argument) + r"\s*\)",
                                body, re.IGNORECASE)
        require(assignment is not None and observation is not None and assignment.start() < observation.start(),
                "Standard model does not observe the actual cached result after its call")
    return entries


@deal.pre(lambda register, project, coverage, sources, source_root: isinstance(register, dict))
@deal.pre(lambda register, project, coverage, sources, source_root: isinstance(project, str) and isinstance(coverage, dict) and isinstance(sources, list) and isinstance(source_root, Path) and source_root.is_dir())
@deal.post(lambda result: isinstance(result, dict) and result["coverage_complete"] is True
           and result["implementation_proved"] is False and result["model_adequacy_proved"] is False
           and result["boundary_count"] == len(result["boundaries"]) and result["boundary_count"] > 0)
@deal.raises(OSError, FileNotFoundError, PermissionError, ValueError, UnicodeDecodeError)
@deal.has("read")
def validate_boundaries(register: dict, project: str, coverage: dict,
                        sources: list, source_root: Path) -> dict:
    require(register.get("schema") == GHOST_SCHEMA, "Unknown ghost boundary schema")
    global_obligations = register.get("global_unproved_obligations")
    require(isinstance(global_obligations, dict) and set(global_obligations) == GLOBAL_OBLIGATION_SCOPES
            and all(isinstance(value, str) and bool(value.strip()) for value in global_obligations.values()),
            "Global unproved obligation inventory differs")
    projects = register.get("projects")
    require(isinstance(projects, dict) and set(projects) == PROJECT_NAMES,
            "Ghost register must include exactly both projects")
    require(project in PROJECT_NAMES, "Unknown ghost project")
    entries = projects[project]
    require(isinstance(entries, list) and bool(entries), "Ghost boundary inventory is empty")
    rows = coverage.get("entities")
    require(isinstance(rows, list) and bool(rows), "Native entity inventory is missing")
    require(all(isinstance(row, dict) and isinstance(row.get("name"), str)
                and row.get("status") in {"all", "spec", "no"} for row in rows),
            "Native ghost entity inventory is malformed")
    require(not any(row["status"] == "no" for row in rows),
            "Non-SPARK declarations require an explicit modeled interface")
    spec = {row["name"].casefold() for row in rows if row["status"] == "spec"}
    analyzed = {row["name"].casefold(): row for row in rows if row["status"] == "all"}
    texts = pinned_ada_sources(sources, source_root)
    imports = foreign_imports(texts)
    external = register.get("external_dependencies")
    require(isinstance(external, dict) and set(external) == PROJECT_NAMES,
            "External dependency project inventory differs")
    dependencies = external[project]
    require(isinstance(dependencies, dict) and set(dependencies) == external_dependencies(texts)
            and all(isinstance(value, str) and bool(value.strip()) for value in dependencies.values()),
            "External dependency obligation inventory differs")
    standard = register.get("standard_library_models")
    require(isinstance(standard, dict) and set(standard) == PROJECT_NAMES
            and isinstance(standard[project], list), "Standard-library model projects differ")
    standard_models = validate_standard_models(standard[project], texts, analyzed,
        "ada.numerics.long_elementary_functions" in dependencies)
    private = set()
    for relative, text in texts.items():
        code = ada_code(text)
        package = re.search(r"\bpackage\s+body\s+(\w+)\s+with\s+SPARK_Mode\s*=>\s*Off\s+is\b",
                            code, re.IGNORECASE)
        if package is not None:
            for match in re.finditer(r"\b(?:function|procedure)\s+(\w+)\b", code, re.IGNORECASE):
                qualified = (package.group(1) + "." + match.group(1)).casefold()
                if qualified not in spec and qualified not in imports:
                    private.add((relative, match.group(1).casefold()))
    modeled_private = set()
    seen = set()
    modeled_spec = set()
    modeled_imports = set()
    normalized = []
    for entry in entries:
        require(isinstance(entry, dict), "Ghost boundary entry must be an object")
        name = entry.get("entity")
        require(isinstance(name, str) and bool(name), "Ghost boundary name is missing")
        key = name.casefold()
        require(key not in seen, "Duplicate ghost boundary: " + name)
        seen.add(key)
        kind = entry.get("kind")
        require(kind in {"spec-only", "foreign-import"}, "Unknown ghost boundary kind")
        source = entry.get("source")
        require(isinstance(source, str) and source in texts, "Boundary source is not pinned: " + name)
        if kind == "spec-only":
            require(key in spec, "Mapped spec boundary is absent from native coverage: " + name)
            native_sources = {Path(row.get("file", "")).name for row in rows
                              if row["name"].casefold() == key and row["status"] == "spec"}
            require(Path(source).name in native_sources, "Boundary declaration differs from native source: " + name)
            modeled_spec.add(key)
        else:
            require(imports.get(key) == source, "Mapped foreign import is absent from source: " + name)
            modeled_imports.add(key)
        require(entry.get("implementation_proved") is False and entry.get("model_adequacy_proved") is False,
                "Ghost coverage must not claim excluded implementation or model adequacy proof")
        obligations = entry.get("obligations")
        require(isinstance(obligations, list) and bool(obligations)
                and all(isinstance(value, str) and bool(value.strip()) for value in obligations),
                "Ghost boundary obligations are missing: " + name)
        model_file = entry.get("model_file")
        require(isinstance(model_file, str) and model_file in texts,
                "Ghost model source is not pinned: " + name)
        model_package = ghost_package(texts[model_file])
        models = entry.get("model_entities")
        refs = entry.get("contract_refs")
        require(isinstance(models, list) and bool(models)
                and all(isinstance(value, str) and bool(value) for value in models)
                and len({value.casefold() for value in models}) == len(models),
                "Ghost model entity inventory is empty or duplicated: " + name)
        require(isinstance(refs, list) and bool(refs)
                and all(isinstance(value, str) and value.casefold() in {model.casefold() for model in models}
                        for value in refs), "Contract references must name registered ghost models: " + name)
        for model in models:
            model_entity_kind(texts[model_file], model)
            row = analyzed.get(model.casefold())
            require(row is not None and model.casefold().startswith(model_package.casefold() + ".")
                    and Path(row.get("file", "")).name == Path(model_file).name,
                    "Ghost model body is not analyzed at its declared source: " + model)
        contract_file = entry.get("contract_file")
        require(isinstance(contract_file, str) and contract_file in texts,
                "Ghost contract source is not pinned: " + name)
        contract_entity = entry.get("contract_entity", name)
        link_kind = entry.get("link_kind", "contract")
        require(isinstance(contract_entity, str) and bool(contract_entity) and isinstance(link_kind, str),
                "Ghost coupling operation is invalid")
        if link_kind in {"ghost-call", "model-call"}:
            require(all((model_entity_kind(texts[model_file], ref) == "ghost")
                        == (link_kind == "ghost-call") for ref in refs),
                    "Model coupling kind differs from the declared Ghost role")
        paired_spec = str(Path(contract_file).with_suffix(".ads"))
        contract_text = texts[contract_file]
        if paired_spec != contract_file and paired_spec in texts:
            contract_text += "\n" + texts[paired_spec]
        require(all(coupling_reference(contract_text, ref, contract_entity, link_kind) for ref in refs),
                "Ghost model is not linked from the actual named operation: " + name)
        helpers = entry.get("excluded_helpers", [])
        require(isinstance(helpers, list) and all(isinstance(value, dict) for value in helpers),
                "Excluded helper inventory is malformed")
        for helper in helpers:
            helper_name = helper.get("entity")
            helper_file = helper.get("contract_file")
            helper_refs = helper.get("contract_refs")
            require(isinstance(helper_name, str) and bool(helper_name)
                    and isinstance(helper_file, str) and helper_file in texts
                    and isinstance(helper_refs, list) and bool(helper_refs)
                    and all(isinstance(ref, str) and ref.casefold() in {model.casefold() for model in models}
                            for ref in helper_refs),
                    "Excluded helper mapping is invalid")
            helper_key = (helper_file, helper_name.rsplit(".", 1)[-1].casefold())
            require(helper_key in private and helper_key not in modeled_private,
                    "Excluded helper is absent or duplicated")
            helper_kind = helper.get("link_kind", "contract")
            if helper_kind in {"ghost-call", "model-call"}:
                require(all((model_entity_kind(texts[model_file], ref) == "ghost")
                            == (helper_kind == "ghost-call") for ref in helper_refs),
                        "Helper coupling kind differs from the declared Ghost role")
            helper_text = texts[helper_file]
            paired_spec = str(Path(helper_file).with_suffix(".ads"))
            if paired_spec != helper_file and paired_spec in texts:
                helper_text += "\n" + texts[paired_spec]
            require(all(coupling_reference(helper_text, ref, helper_name,
                                           helper.get("link_kind", "contract")) for ref in helper_refs),
                    "Excluded helper model is not linked from its named operation")
            modeled_private.add(helper_key)
        normalized.append(entry)
    require(modeled_spec == spec, "Native spec-only ghost boundary inventory differs")
    require(modeled_imports == set(imports), "Foreign-import ghost boundary inventory differs")
    require(modeled_private == private, "Private excluded helper ghost inventory differs")
    return {"schema": GHOST_SCHEMA, "project": project, "coverage_complete": True,
            "implementation_proved": False, "model_adequacy_proved": False,
            "boundary_count": len(normalized), "native_spec_entities": sorted(spec),
            "foreign_imports": sorted(imports), "external_dependencies": dependencies,
            "global_unproved_obligations": global_obligations,
            "standard_library_models": standard_models,
            "private_helpers": sorted([list(value) for value in modeled_private]), "boundaries": normalized}
