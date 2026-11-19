#!/bin/sh
# Install the dependencies of the already checked-out pinned FormalML source.
#
# This script runs only after GitHub Actions has checked every tracked *.sh
# with ShellCheck; never invoke it as a replacement for that lint gate.
# The package graph is resolved by opam from FormalML's own metadata.
# Retries tolerate transient upstream source failures (e.g. Coquelicot
# release servers returning HTTP 502); a persistent failure exits nonzero.
# No theorem statement, compiler option, or dependency pin is weakened.
#
# Researcher/requester: Anders Hellström.
# AI disclosure: AI-assisted dependency-retrieval reliability adjustment.
set -eu

attempt=1
max_attempts=3
while [ "$attempt" -le "$max_attempts" ]; do
  if opam install -y -j 2 --deps-only .; then
    exit 0
  fi

  if [ "$attempt" -eq "$max_attempts" ]; then
    printf 'FormalML opam dependency installation failed after %s attempts.\n' "$max_attempts" >&2
    exit 1
  fi

  printf 'FormalML dependency attempt %s failed; retrying without changing pins.\n' "$attempt" >&2
  attempt=$((attempt + 1))
  sleep 5
done
