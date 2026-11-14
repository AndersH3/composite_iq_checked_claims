#!/usr/bin/env bash
# Offline tests: no calls to opam, apt, network, or real tool installers.
# Exercise the pinned release manifest and Deal pre/postconditions.
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ -n "${FORMAL_TOOLS_PYTHON:-}" ]]; then
  py="$FORMAL_TOOLS_PYTHON"
elif [[ -x .venv/bin/python ]]; then
  py=.venv/bin/python
else
  py=python3
fi

if ! "$py" -c 'import deal' >/dev/null 2>&1; then
  printf 'Deal is unavailable in %s. Install deal==4.24.6 in that interpreter.\n' "$py" >&2
  exit 2
fi

"$py" scripts/install_formal_provers.py > /dev/null
for name in lean isabelle yices pvs colibri; do
  "$py" scripts/install_formal_provers.py --tool "$name" > /dev/null
done
# The official Clarkson mirror is a download-only option for Isabelle.
"$py" scripts/install_formal_provers.py --tool isabelle --mirror clarkson > /dev/null
if "$py" scripts/install_formal_provers.py --tool yices --mirror clarkson > /dev/null 2>&1; then
  echo "Rejected mirror unexpectedly accepted for Yices" >&2
  exit 1
fi

"$py" - <<'PY'
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import deal
from scripts.install_formal_provers import release_spec, verify_archive, download_url, SPECS, ISABELLE_CLARKSON

deal.enable(warn=False)
assert set(SPECS) == {"lean", "isabelle", "yices", "pvs"}
assert len({release_spec(tool)[3] for tool in SPECS}) == 4

for tool in SPECS:
    assert download_url(tool, "primary") == release_spec(tool)[0]
assert download_url("isabelle", "clarkson") == ISABELLE_CLARKSON
assert download_url("isabelle", "clarkson").endswith("Isabelle2026_linux.tar.gz")
for tool in ("lean", "yices", "pvs"):
    try:
        download_url(tool, "clarkson")
    except deal.PreContractError:
        pass
    else:
        raise AssertionError("Unsupported mirror accepted for " + tool)

for tool in SPECS:
    url, digest, size, directory = release_spec(tool)
    assert url.startswith("https://")
    assert len(digest) == 64
    assert size > 0 and directory

try:
    release_spec("colibri")
except deal.PreContractError:
    pass
else:
    raise AssertionError("Unverified classic COLIBRI archive was accepted")

with TemporaryDirectory() as root:
    path = Path(root, "test.tar.gz")
    data = b"formal-verification-bundle" * 64
    path.write_bytes(data)
    digest = sha256(data).hexdigest()
    assert verify_archive(path, digest, len(data))
    for bad_digest, bad_size in (("0" * 64, len(data)), (digest, len(data) + 1)):
        try:
            verify_archive(path, bad_digest, bad_size)
        except ValueError:
            pass
        else:
            raise AssertionError("Corrupted release was accepted")
    try:
        verify_archive(path, "bad-digest", len(data))
    except deal.PreContractError:
        pass
    else:
        raise AssertionError("Malformed checksum was accepted")

print("Four official pinned releases, mirror constraints, Deal contracts and checksum controls passed")
PY

echo "Offline installer plan tests passed"
