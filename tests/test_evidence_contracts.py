"""Source identity checks keep missing history and changed Ada observable."""
import hashlib
import json
from pathlib import Path
import subprocess
from subprocess import CalledProcessError, TimeoutExpired
import sys

import deal
import pytest

from conftest import ROOT
from verification import verify_evidence as auditor


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_current_source_returns_its_nonempty_absolute_path(tmp_path):
    relative = "verification/verify_evidence.py"
    current = ROOT.joinpath(relative)
    expected = hashlib.sha256(current.read_bytes()).hexdigest()
    result = auditor.evidence_source(relative, expected, tmp_path.joinpath("unused.json"))
    assert result == str(current)
    assert Path(result).is_absolute()


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_changed_ada_cannot_use_historical_python_fallback(tmp_path):
    with pytest.raises(ValueError, match="Proof source changed"):
        auditor.evidence_source("analyses/hoeflin-ferguson/ada/src/hoeflin_core.ads",
                                "0" * 64, tmp_path.joinpath("unused.json"))


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_missing_historical_git_object_has_an_explicit_error(tmp_path):
    relative = "verification/verify_evidence.py"
    history = tmp_path.joinpath("history.json")
    history.write_text(json.dumps({"files": [{"path": relative, "sha256": "0" * 64,
                                             "git_blob": "0" * 40}]}))
    with pytest.raises(ValueError, match="Historical Git object is missing"):
        auditor.evidence_source(relative, "0" * 64, history, tmp_path.joinpath("missing.git"))


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_malformed_source_history_preserves_json_decode_error(tmp_path):
    history = tmp_path.joinpath("history.json")
    history.write_text("{")
    with pytest.raises(json.JSONDecodeError):
        auditor.evidence_source("verification/verify_evidence.py", "0" * 64, history)


@deal.post(lambda result: result is None)
@deal.raises(OSError, ValueError, subprocess.SubprocessError, CalledProcessError, TimeoutExpired)
@deal.has("read", "write", "syscall", "stdout", "stderr")
def test_optimized_auditor_cli_keeps_json_failure_observable(tmp_path):
    history = tmp_path.joinpath("history.json")
    history.write_text("{")
    process = subprocess.run([sys.executable, "-O", str(ROOT.joinpath("verification/verify_evidence.py")),
                              "--source-history", str(history)], capture_output=True, text=True, timeout=15)
    assert process.returncode != 0
    assert "JSONDecodeError" in process.stderr
    assert "RaisesContractError" not in process.stderr
