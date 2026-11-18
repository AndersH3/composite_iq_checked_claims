"""Load the standalone analysis scripts without confusing their module names."""
import importlib.util
import hashlib
from pathlib import Path
import sys
from types import ModuleType

import deal
import pytest

ROOT = Path(__file__).resolve().parents[1]
# Guard active Dask inputs and independent reference CSVs during tests.
# Archived compiler evidence remains accessible through Git history only.
_PROTECTED_PATHS = tuple(sorted([
    ROOT / "reporting/run.json",
    *(ROOT.glob("analyses/*/simulation-data/summary.json")),
    *(ROOT.glob("analyses/*/simulation-data/moments.csv")),
    *(ROOT.glob("analyses/*/simulation-data/events.csv")),
]))
_PROTECTED_HASHES = tuple((path, hashlib.sha256(path.read_bytes()).hexdigest())
                          for path in _PROTECTED_PATHS if path.is_file())
_REFERENCE_HASHES = tuple((path, hashlib.sha256(path.read_bytes()).hexdigest())
                          for path in sorted(ROOT.glob("analyses/*/data/*.csv")))
if not _REFERENCE_HASHES:
    _REFERENCE_HASHES = ((ROOT / "reporting/run.json",
                          hashlib.sha256((ROOT / "reporting/run.json").read_bytes()).hexdigest()),)

deal.enable(warn=False)


@deal.pre(lambda: bool(_PROTECTED_HASHES) and all(
    isinstance(path, Path) and path.is_absolute() and path.is_relative_to(ROOT)
    and isinstance(digest, str) and len(digest) == 64
    for path, digest in _PROTECTED_HASHES))
@deal.post(lambda result: isinstance(result, bool))
@deal.ensure(lambda *, result: not result or all(
    path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest
    for path, digest in _PROTECTED_HASHES))
@deal.has("read")
@deal.raises()
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def protected_history_intact() -> bool:
    """Observe the immutable-input frame used at test entry and normal return."""
    try:
        return all(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest
                   for path, digest in _PROTECTED_HASHES)
    except OSError:
        return False


@deal.pre(lambda: bool(_REFERENCE_HASHES) and all(
    isinstance(path, Path) and path.is_absolute() and path.is_relative_to(ROOT)
    and isinstance(digest, str) and len(digest) == 64
    for path, digest in _REFERENCE_HASHES))
@deal.post(lambda result: isinstance(result, bool))
@deal.ensure(lambda *, result: not result or all(
    path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest
    for path, digest in _REFERENCE_HASHES))
@deal.has("read")
@deal.raises()
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def reference_inputs_intact() -> bool:
    """Observe the separate frame protecting published tables and reports."""
    try:
        return all(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest
                   for path, digest in _REFERENCE_HASHES)
    except OSError:
        return False


@deal.pre(lambda name, relative: isinstance(name, str) and name.isidentifier()
          and isinstance(relative, str) and (ROOT / relative).resolve().is_relative_to(ROOT)
          and (ROOT / relative).is_file() and relative.endswith(".py"))
@deal.ensure(lambda name, relative, *, result:
             isinstance(result, ModuleType) and result.__name__ == name
             and Path(result.__file__).resolve() == (ROOT / relative).resolve())
@deal.ensure(lambda name, relative, *, result: sys.modules.get(name) is result)
@deal.raises(OSError, ImportError, SyntaxError, ValueError)
@deal.has("read", "write", "import", "global")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def load_script(name: str, relative: str) -> ModuleType:
    """Load an analysis module from its canonical repository source path.
    
    A unique import name prevents similarly named report scripts from colliding.
    Reject missing or invalid module specifications rather than borrowing cached code.
    """
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(autouse=True)
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.post(lambda result: result is None)
@deal.has("global", "stderr", "read")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def contracts_enabled() -> None:
    """Activate real Deal runtime contract checks for the pytest session.
    
    The tests deliberately reject invalid numerical inputs through preconditions.
    Do not downgrade failures to mere warnings or bypass the maintained validators.
    """
    deal.enable(warn=False)


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.variance_factor) and callable(result.thresholds))
@deal.has("read", "write", "import", "global")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def hoeflin() -> ModuleType:
    """Provide the isolated Hoeflin report calculation module for regression tests.
    
    Load the production verifier rather than a test-only approximation.
    Keep the same source and strict Deal checks used to regenerate the report.
    """
    return load_script("checked_hoeflin_numbers", "analyses/hoeflin-ferguson/scripts/verify_calculations.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.joint_tail) and callable(result.admission_rows))
@deal.has("read", "write", "import", "global")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def towers() -> ModuleType:
    """Provide the isolated Towers admission reference implementation to tests.
    
    Use the maintained Gaussian quadrature module and its original constants.
    Avoid accidentally importing the unrelated Hoeflin verifier of the same name.
    """
    return load_script("checked_towers_numbers", "analyses/towers-multiple-test-admissions/scripts/verify_calculations.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
             and callable(result.audit_file) and callable(result.python_files))
@deal.has("read", "write", "import", "global")
# Independently guard source ownership, input integrity and required test infrastructure.
@deal.pre(lambda *args, **kwargs: ROOT.is_absolute())
@deal.pre(lambda *args, **kwargs: ROOT.is_dir())
@deal.pre(lambda *args, **kwargs: bool(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: bool(_REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: len({path for path, digest in _PROTECTED_HASHES}) == len(_PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _PROTECTED_HASHES))
@deal.pre(lambda *args, **kwargs: all(path.is_relative_to(ROOT) for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: all(len(digest) == 64 for path, digest in _REFERENCE_HASHES))
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("reporting","run.json").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","hoeflin-ferguson","data","thresholds.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("analyses","towers-multiple-test-admissions","data","admission_probabilities.csv").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_contract_coverage.py").is_file())
@deal.pre(lambda *args, **kwargs: ROOT.joinpath("verification","check_static_lint.py").is_file())
def coverage_checker() -> ModuleType:
    """Provide the exact repository-wide Deal contract auditor to pytest.
    
    Tests exercise its real AST parser and file inventory, not a mock checker.
    The fixture keeps expected negative controls separate from maintained modules.
    """
    return load_script("checked_contract_coverage", "verification/check_contract_coverage.py")
