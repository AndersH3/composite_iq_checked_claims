#!/usr/bin/env bash
# Debian 13 / computer10: resume and securely install the pinned Isabelle2026.
# AI-assisted script. Official TLS certificate and SHA256 checks remain enabled.
# This script leaves Lean, Yices, PVS, Rocq, and COLIBRI2 untouched.
# Download the file, review it, then run: bash retry_isabelle_computer10.sh
set -euo pipefail

if [[ "$(hostname -s)" != "computer10" ]]; then
  printf 'ERROR: Run this script on computer10 (currently %s).\n' "$(hostname -s)" >&2
  exit 2
fi

repo="$HOME/src/composite_iq_formal_tools"
if [[ ! -d "$repo/.git" || ! -x "$repo/.venv/bin/python" ]]; then
  printf 'ERROR: Required checkout or Python venv missing: %s\n' "$repo" >&2
  exit 2
fi
cd "$repo"

branch="$(git branch --show-current)"
if [[ "$branch" != "tooling/formal-provers-debian13" ]]; then
  printf 'ERROR: Expected Git branch tooling/formal-provers-debian13, got %s\n' "$branch" >&2
  exit 2
fi

printf '\n== Updating the existing installer checkout ==\n'
git pull --ff-only origin tooling/formal-provers-debian13

printf '\n== Checking offline Deal contracts and installer metadata ==\n'
bash scripts/test_formal_provers.sh

# Use a resumable download stored outside the installer's temporary directory.
# A previously verified complete download can be reused without network access.
archive="$HOME/Isabelle2026_linux.tar.gz"
url="https://mirror.clarkson.edu/isabelle/dist/Isabelle2026_linux.tar.gz"
sha="858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d"
size=1412134191
valid=0

if [[ -f "$archive" && ! -L "$archive" ]] &&
   [[ "$(stat -c '%s' "$archive")" == "$size" ]] &&
   printf '%s  %s\n' "$sha" "$archive" | sha256sum --check --status; then
  valid=1
  printf '\n== Reusing previously verified Isabelle archive ==\n'
fi

if (( ! valid )); then
  printf '\n== Downloading or resuming Isabelle2026 (1.4 GB) ==\n'
  printf 'Source: %s\n' "$url"
  curl --fail --location --continue-at - --retry 5 --retry-delay 3 \
       --proto '=https' --proto-redir '=https' \
       --output "$archive" "$url"
fi

printf '\n== Verifying exact archive size and vendor-published SHA256 ==\n'
[[ -f "$archive" && ! -L "$archive" ]]
[[ "$(stat -c '%s' "$archive")" == "$size" ]] || {
  printf 'ERROR: Isabelle archive size does not match the pinned release.\n' >&2
  exit 3
}
printf '%s  %s\n' "$sha" "$archive" | sha256sum --check

printf '\n== Installing Isabelle2026 from verified local archive ==\n'
"$repo/.venv/bin/python" scripts/install_formal_provers.py \
  --tool isabelle --install --archive "$archive"

printf '\nDone: Isabelle2026 extracted. Check its launcher before claiming full functional verification.\n'
find "$HOME/.local/opt/formal-provers/isabelle-2026" \
  -type f -path '*/bin/isabelle' -print
