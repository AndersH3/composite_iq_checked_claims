#!/usr/bin/env bash
# Debian 13 / computer10: resumable, detached Isabelle2026 installation.
# AI disclosure: generated with OpenAI assistance; vendor SHA256 and TLS
# certificate verification remain mandatory. Installer does not alter Lean,
# Yices, PVS, Rocq, COLIBRI2, opam switches, or system packages.
#
# Usage (run from any directory on computer10):
#   bash scripts/retry_isabelle_computer10.sh --detach
#   bash scripts/retry_isabelle_computer10.sh --status
#   bash scripts/retry_isabelle_computer10.sh --run
#
# --detach isolates the job from SSH using setsid + nohup, redirects all output
# to ~/isabelle2026-install.log, and returns control to the invoking shell.
# A reboot still stops the job; rerunning --detach resumes its partial archive.
set -euo pipefail

repo="$HOME/src/composite_iq_formal_tools"
script="$repo/scripts/retry_isabelle_computer10.sh"
log="$HOME/isabelle2026-install.log"
lock="$HOME/.cache/isabelle2026-install.lock"

mode="${1:---run}"
case "$mode" in
  --help|-h)
    printf 'Usage: bash %s [--detach | --status | --run]\n' "$script"
    printf '%s\n' '--detach: start the resumable job outside the current SSH session'
    printf '%s\n' '--status: check the lock and show the most recent log messages'
    printf '%s\n' '--run: execute in the foreground (default)'
    exit 0
    ;;
  --detach|--status|--run)
    ;;

  *)
    printf 'ERROR: Unknown option: %s\n' "$1" >&2
    exit 2
    ;;
esac

if [[ "$(hostname -s)" != "computer10" ]]; then
  printf 'ERROR: Run this script on computer10 (currently %s).\n' "$(hostname -s)" >&2
  exit 2
fi

if [[ ! -d "$repo/.git" || ! -x "$repo/.venv/bin/python" ]]; then
  printf 'ERROR: Missing repo or Python venv at %s\n' "$repo" >&2
  exit 2
fi

mkdir -p "$HOME/.cache"

if [[ "$mode" == "--status" ]]; then
  exec 8>"$lock"
  if flock -n 8; then
    printf '%s\n' 'Status: no installer process holds the installation lock.'
  else
    printf '%s\n' 'Status: the Isabelle installation job is running.'
  fi
  if [[ -e "$HOME/Isabelle2026_linux.tar.gz" ]]; then
    printf 'Archive bytes downloaded: '
    stat -c '%s' "$HOME/Isabelle2026_linux.tar.gz"
  fi
  if [[ -f "$log" ]]; then
    printf '\nRecent log output: %s\n' "$log"
    tail -n 25 "$log"
  fi
  exit 0
fi

if [[ "$mode" == "--detach" ]]; then
  if ! command -v setsid >/dev/null || ! command -v nohup >/dev/null ||
     ! command -v flock >/dev/null; then
    printf '%s\n' 'ERROR: setsid, nohup and flock (Debian coreutils/util-linux) are required.' >&2
    exit 2
  fi
  # The detached worker obtains an exclusive lock. A duplicate launch stops
  # immediately instead of downloading or extracting twice.
  printf 'Launching detached Isabelle2026 installation job.\n'
  printf 'Log: %s\n' "$log"
  setsid -f nohup bash "$script" --run >>"$log" 2>&1 < /dev/null
  printf '%s\n' 'To check progress:'
  printf 'bash %s --status\n' "$script"
  exit 0
fi

# Only the worker holds this exclusive lock. It is automatically released on
# process exit, including failure or an interrupted transfer.
exec 9>"$lock"
if ! flock -n 9; then
  printf '%s\n' 'Another Isabelle job is already running. Check --status.' >&2
  exit 4
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

# Keep the partial file in the user's home directory, not a temporary folder.
# Each curl invocation recomputes the current file offset (curl -C -), so
# aborted transfers do not cause a fresh 1.4 GB download from byte zero.
archive="$HOME/Isabelle2026_linux.tar.gz"
url="https://mirror.clarkson.edu/isabelle/dist/Isabelle2026_linux.tar.gz"
sha="858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d"
size=1412134191

if [[ -L "$archive" ]]; then
  printf '%s\n' 'ERROR: The archive path is a symbolic link; refusing to use it.' >&2
  exit 3
fi

verified=0
if [[ -f "$archive" ]] &&
   [[ "$(stat -c '%s' "$archive")" == "$size" ]] &&
   printf '%s  %s\n' "$sha" "$archive" | sha256sum --check --status; then
  verified=1
  printf '\n== Reusing previously verified Isabelle2026 archive ==\n'
fi

if (( ! verified )); then
  printf '\n== Resuming official Isabelle2026 archive (1,412,134,191 bytes) ==\n'
  printf 'Source: %s\n' "$url"
  success=0
  for attempt in {1..40}; do
    printf '\nAttempt %d of 40; existing archive size: ' "$attempt"
    if [[ -e "$archive" ]]; then
      stat -c '%s bytes' "$archive"
    else
      printf '0 bytes\n'
    fi
    if curl --fail --location --continue-at - \
       --connect-timeout 30 --speed-limit 1024 --speed-time 120 \
       --proto '=https' --proto-redir '=https' \
       --output "$archive" "$url"; then
      success=1
      break
    else
      rc=$?
    fi
    # Do not repeatedly retry certificate failures, invalid URLs or
    # servers that reject resumable Range requests.
    if [[ "$rc" == 22 || "$rc" == 33 || "$rc" == 60 ||
          "$rc" == 77 ]]; then
      printf 'ERROR: Non-retriable curl failure (%s).\n' "$rc" >&2
      exit "$rc"
    fi
    if (( attempt == 40 )); then
      break
    fi
    printf 'Download interrupted (curl code %s); partial file preserved.\n' "$rc"
    sleep 15
  done
  if (( ! success )); then
    printf '%s\n' 'ERROR: All download attempts failed; partial file preserved.' >&2
    exit 5
  fi
fi

printf '\n== Verifying exact archive length and published SHA256 ==\n'
[[ -f "$archive" && ! -L "$archive" ]]
if [[ "$(stat -c '%s' "$archive")" != "$size" ]]; then
  printf '%s\n' 'ERROR: Archive size mismatch; partial file was preserved.' >&2
  exit 3
fi
printf '%s  %s\n' "$sha" "$archive" | sha256sum --check

printf '\n== Installing Isabelle2026 from the verified local archive ==\n'
"$repo/.venv/bin/python" scripts/install_formal_provers.py \
  --tool isabelle --install --archive "$archive"

printf '\nDone: Isabelle2026 extracted. Verify the launcher separately.\n'
find "$HOME/.local/opt/formal-provers/isabelle-2026" \
  -type f -path '*/bin/isabelle' -print
