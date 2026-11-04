"""Load the standalone analysis scripts without confusing their module names."""
import importlib.util
import hashlib
from pathlib import Path
import sys
from types import ModuleType

import deal
import pytest

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "verification/evidence/computer10-20261031/runtime"

# Tests may create deliberately damaged scratch copies. Retained evidence,
# reference tables and distributed reports are protected scientific inputs.
_PROTECTED_PATHS = tuple(sorted(
    path for checksum in (ROOT / "verification/evidence").glob("*/SHA256SUMS")
    for path in checksum.parent.rglob("*") if path.is_file()
))
_PROTECTED_HASHES = tuple((path, hashlib.sha256(path.read_bytes()).hexdigest())
                          for path in _PROTECTED_PATHS)
_REFERENCE_HASHES = tuple((path, hashlib.sha256(path.read_bytes()).hexdigest())
                         for path in sorted(list(ROOT.glob("analyses/*/data/*.csv"))
                                            + list(ROOT.glob("analyses/*/output/pdf/*.pdf"))))
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
def load_script(name: str, relative: str) -> ModuleType:
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
def contracts_enabled() -> None:
    deal.enable(warn=False)


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.variance_factor) and callable(result.thresholds))
@deal.has("read", "write", "import", "global")
def hoeflin() -> ModuleType:
    return load_script("checked_hoeflin_numbers", "analyses/hoeflin-ferguson/scripts/verify_calculations.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.joint_tail) and callable(result.admission_rows))
@deal.has("read", "write", "import", "global")
def towers() -> ModuleType:
    return load_script("checked_towers_numbers", "analyses/towers-multiple-test-admissions/scripts/verify_calculations.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.validate_calculations) and callable(result.wilson))
@deal.has("read", "write", "import", "global")
def hoeflin_validator() -> ModuleType:
    return load_script("checked_hoeflin_validator", "analyses/hoeflin-ferguson/ada/scripts/validate_results.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.validate) and callable(result.close))
@deal.has("read", "write", "import", "global")
def towers_validator() -> ModuleType:
    return load_script("checked_towers_validator", "analyses/towers-multiple-test-admissions/ada/validate_results.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
           and callable(result.report_summary) and callable(result.successful_checks))
@deal.has("read", "write", "import", "global")
def proof_runner() -> ModuleType:
    return load_script("checked_proof_runner", "verification/run_computer10.py")


@pytest.fixture(scope="session")
@deal.pre(lambda: protected_history_intact())
@deal.ensure(lambda *, result: protected_history_intact())
@deal.ensure(lambda *, result: reference_inputs_intact())
@deal.ensure(lambda *, result: isinstance(result, ModuleType)
             and callable(result.audit_file) and callable(result.python_files))
@deal.has("read", "write", "import", "global")
def coverage_checker() -> ModuleType:
    return load_script("checked_contract_coverage", "verification/check_contract_coverage.py")
