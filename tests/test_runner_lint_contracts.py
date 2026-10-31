"""Exercise literal toolchain exports and unchecked version-process failures."""
import os
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

import deal
import pytest


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr")
def test_version_record_retains_nonzero_exit_and_both_streams(proof_runner):
    executable = Path(sys.executable)
    result = proof_runner.version_record(executable, ["-c", "import sys; print('out'); print('err', file=sys.stderr); sys.exit(7)"], os.environ.copy())
    assert result["returncode"] == 7
    assert result["output"] == "out\nerr"
    assert result["sha256"] == proof_runner.digest(executable)


@deal.post(lambda result: result is None)
@deal.has("read", "write", "syscall", "time", "stdout", "stderr")
def test_version_record_kills_and_reaps_timed_out_process(proof_runner, tmp_path):
    pid_file = tmp_path.joinpath("child.pid")
    script = ("import os,time; from pathlib import Path; Path(" + repr(str(pid_file))
              + ").write_text(str(os.getpid())); time.sleep(60)")
    with pytest.raises(subprocess.TimeoutExpired):
        proof_runner.version_record(Path(sys.executable), ["-c", script], os.environ.copy())
    pid = int(pid_file.read_text())
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


@pytest.mark.parametrize("extra", [
    "export PATH='unterminated",
    "export PATH='/tmp'; touch /tmp/not-executed",
    "export UNEXPECTED='/tmp'",
    "export PATH='/first'\nexport PATH='/second'",
])
@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr", "global")
def test_environment_rejects_malformed_unknown_or_duplicate_exports(proof_runner, tmp_path, extra):
    process = subprocess.CompletedProcess(["alr"], 0, stdout=extra, stderr="")
    with patch.object(proof_runner.subprocess, "run", return_value=process):
        with pytest.raises(ValueError):
            proof_runner.environment(tmp_path)


@deal.post(lambda result: result is None)
@deal.has("read", "syscall", "stdout", "stderr", "global")
def test_environment_preserves_quoted_values_without_shell_expansion(proof_runner, tmp_path):
    literal = "/tmp/quoted path:$HOME:$(touch /tmp/not-executed)"
    exports = "\n".join([
        "export GNATPROVE_ALIRE_PREFIX='/tmp/prove'",
        "export GNAT_NATIVE_ALIRE_PREFIX='/tmp/gnat'",
        "export GPRBUILD_ALIRE_PREFIX='/tmp/gprbuild'",
        "export PATH='" + literal + "'",
    ])
    process = subprocess.CompletedProcess(["alr"], 0, stdout=exports, stderr="")
    with patch.object(proof_runner.subprocess, "run", return_value=process):
        result = proof_runner.environment(tmp_path)
    assert result["PATH"].endswith(literal)
    assert result["GNATPROVE_ALIRE_PREFIX"] == "/tmp/prove"
