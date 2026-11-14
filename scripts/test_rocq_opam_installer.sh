#!/usr/bin/env bash
# Check installer command planning and opam isolation without installing Rocq.
# No network access, package mutation, or real opam invocation occurs.
set -euo pipefail
cd "$(dirname "$0")/.."

# Prefer the interpreter that already has the project's Deal dependency.
# Allow a caller to override it explicitly when testing other environments.
# CI has Deal installed in its python3, while Debian users commonly install
# Deal only in .venv and do not activate that environment before running us.
if [[ -n "${ROCQ_TEST_PYTHON:-}" ]]; then
    test_python="$ROCQ_TEST_PYTHON"
elif [[ -x .venv/bin/python ]]; then
    test_python=.venv/bin/python
else
    test_python=python3
fi

if ! "$test_python" -c 'import deal' >/dev/null 2>&1; then
    printf 'Deal is missing from %s. Install it there or set ROCQ_TEST_PYTHON.\n' "$test_python" >&2
    exit 2
fi

"$test_python" - <<'PY'
import deal
from scripts.install_rocq_opam import (
    OCAML_COMPILER, RELEASE_REPOSITORY, ROCQ_CORE, SWITCH, SWITCH_OPTION,
    installation_plan,
)

deal.enable(warn=False)
for switch_exists in (False, True):
    for repository_exists in (False, True):
        plan = installation_plan(switch_exists, repository_exists)
        assert plan[-2] == ("opam", "install", SWITCH_OPTION, "--yes", "rocq-prover", ROCQ_CORE)
        assert plan[-1] == ("opam", "exec", SWITCH_OPTION, "--", "rocq", "--version")
        assert (("opam", "switch", "create", SWITCH, OCAML_COMPILER, "--yes") in plan) == (not switch_exists)
        assert (("opam", "repository", "add", "rocq-released", RELEASE_REPOSITORY,
                 SWITCH_OPTION, "--yes") in plan) == (not repository_exists)
        assert len(plan) == 4 + (not switch_exists) + (not repository_exists)

for bad in (("yes", False), (False, None)):
    try:
        installation_plan(*bad)
    except deal.PreContractError:
        pass
    else:
        raise AssertionError("A malformed switch-state flag was accepted")
print("Deal plan contracts and four switch/repository states passed")
PY

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
mkdir -p "$work_dir/bin"
cat > "$work_dir/bin/opam" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >> "$OPAM_TEST_LOG"
if [[ "${1:-}" == "switch" && "${2:-}" == "list" ]]; then
    [[ "${MOCK_SWITCH_EXISTS:-0}" == "1" ]] && printf 'rocq-9.2\n'
    exit 0
fi
if [[ "${1:-}" == "repository" && "${2:-}" == "list" ]]; then
    [[ "${MOCK_REPOSITORY_EXISTS:-0}" == "1" ]] && printf 'rocq-released\n'
    exit 0
fi
exit 0
MOCK
chmod +x "$work_dir/bin/opam"

export OPAM_TEST_LOG="$work_dir/opam.log"
export PATH="$work_dir/bin:$PATH"
export MOCK_SWITCH_EXISTS=0 MOCK_REPOSITORY_EXISTS=0
"$test_python" scripts/install_rocq_opam.py --dry-run > "$work_dir/dry-run.txt"
test ! -e "$OPAM_TEST_LOG"
grep -Fq 'rocq-core=9.2.0' "$work_dir/dry-run.txt"
grep -Fq 'switch create rocq-9.2' "$work_dir/dry-run.txt"

"$test_python" scripts/install_rocq_opam.py > "$work_dir/first-install.txt"
grep -Fxq 'switch create rocq-9.2 ocaml-base-compiler.4.14.2 --yes' "$OPAM_TEST_LOG"
grep -Fxq 'repository add rocq-released https://rocq-prover.org/opam/released --switch=rocq-9.2 --yes' "$OPAM_TEST_LOG"
grep -Fxq 'install --switch=rocq-9.2 --yes rocq-prover rocq-core=9.2.0' "$OPAM_TEST_LOG"

: > "$OPAM_TEST_LOG"
export MOCK_SWITCH_EXISTS=1 MOCK_REPOSITORY_EXISTS=1
"$test_python" scripts/install_rocq_opam.py > "$work_dir/reinstall.txt"
if grep -Eq '^(switch create|repository add) ' "$OPAM_TEST_LOG"; then
    echo "Repeated installation recreated the existing switch or repository" >&2
    exit 1
fi
grep -Fxq 'exec --switch=rocq-9.2 -- rocq --version' "$OPAM_TEST_LOG"
echo "Rocq opam installer mock tests passed"
