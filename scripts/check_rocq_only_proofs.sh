#!/bin/sh
# Rocq-only formal proof language guard.
#
# Researcher/requester: Anders Hellström.
# Purpose: Reject the introduction of Lean/Lake proof artifacts into the
# mathematical verification repository. The formal results must be checked
# by the Rocq kernel, including those that use third-party Rocq libraries
# such as MathComp-Analysis or FormalML. A successful build in any other
# proof assistant is not a substitute for Rocq kernel checking.
#
# Scope: Tracked repository paths, not external library sources fetched
# during GitHub Actions. This guard checks proof-language policy only;
# it does not claim that a Rocq proof exists for an open theorem.
#
# AI disclosure: This audit script was AI-assisted. The policy is a
# researcher-specified verification requirement.
set -eu

if ! command -v git >/dev/null 2>&1; then
    echo 'Rocq-only audit requires git.' >&2
    exit 1
fi

violations=$(git ls-files -- '*.lean' 'lean-toolchain' 'lakefile.lean' \
    'lakefile.toml' 'lake-manifest.json' '.github/workflows/*-lean.yml')
if [ -n "$violations" ]; then
    echo 'Non-Rocq proof artifacts are prohibited:' >&2
    printf '%s\n' "$violations" >&2
    exit 1
fi

printf '%s\n' 'Rocq-only audit passed: no tracked Lean/Lake proof artifacts.'
