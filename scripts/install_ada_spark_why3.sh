#!/usr/bin/env bash
# Debian 13 (computer10): install Ada, SPARK and Why3 prover prerequisites.
# AI disclosure: generated with AI assistance, and untested on computer10.
# Sources: Debian Trixie, Alire (gnatprove), Why3 and Joe Hurd's Metis.
# All mutating operations require an explicit flag. No system repositories
# are changed, no opam switch is touched, and existing prover setups remain.
# IMPORTANT: Debian's "metis" package is a graph partitioner, NOT this prover.
set -euo pipefail

# This manifest intentionally contains only packages established to exist
# in Debian 13/Trixie. In particular, the Alt-Ergo, MLton and Poly/ML
# packages are not assumed to be available in this stable distribution.
ADA_PACKAGES=(
  gnat gprbuild alire gdb gcc g++ make git perl ca-certificates curl
  gappa why3 why3-examples z3 cvc5 eprover
)
METIS_URL="https://github.com/gilith/metis.git"
METIS_SHA="7a23e4ea68bc92927716777ebc98bea09e91fe24"
METIS_DIR="$HOME/.local/src/metis-pinned"
SPARK_PREFIX="$HOME/.local/opt/ada-spark"
SPARK_VERSION="16.1.0"

mode="${1:---plan}"
case "$mode" in
  --help|-h)
    printf '%s\n' 'Usage: bash scripts/install_ada_spark_why3.sh [action]'
    printf '%s\n' '  --plan           print actions without changing the computer'
    printf '%s\n' '  --install-apt    explicitly install Debian GNAT/Why3/SMT packages'
    printf '%s\n' '  --install-spark  explicitly install GNATprove using Alire'
    printf '%s\n' '  --metis-source   fetch a pinned official Metis theorem prover Git commit'
    printf '%s\n' '  --metis-build    build pinned Metis using an EXISTING Standard ML compiler'
    printf '%s\n' '  --detect         detect Why3 backends and inspect command availability'
    printf '%s\n' '  --smoke-ada      compile and run a disposable Ada program with GNAT'
    exit 0
    ;;
  --plan|--install-apt|--install-spark|--metis-source|--metis-build|--detect|--smoke-ada)
    ;;
  *)
    printf 'Unknown option: %s\n' "$mode" >&2
    exit 2
    ;;
esac

if [[ "$mode" == "--plan" ]]; then
  printf 'Debian 13 Ada/SPARK/Why3 stack; no changes made.\n'
  printf 'Debian apt packages:'
  printf ' %s' "${ADA_PACKAGES[@]}"
  printf '\nGNATprove: alr -n get gnatprove=%s into %s\n' "$SPARK_VERSION" "$SPARK_PREFIX"
  printf 'Metis prover: official development snapshot %s\n' "$METIS_SHA"
  printf '%s\n' 'NOTE: apt install metis is WRONG (graph partitioning).'
  printf '%s\n' 'NOTE: Metis build needs a separate MLton, Poly/ML or Moscow ML compiler.'
  printf '%s\n' 'For the GNATprove Alire workspace, use: alr with gnatprove; alr gnatprove'
  printf '%s\n' 'Why3 integration is verified by: why3 config detect'
  exit 0
fi

if [[ "$mode" == "--smoke-ada" ]]; then
  if ! command -v gnatmake >/dev/null; then
    printf '%s\n' 'GNAT compiler is missing; run --install-apt first.' >&2
    exit 3
  fi
  workdir="$(mktemp -d)"
  trap 'rm -rf -- "$workdir"' EXIT
  cat >"$workdir/smoke_ada.adb" <<'ADA'
-- Minimal Ada compiler smoke test, deliberately not a SPARK verification.
-- This standalone source validates GNAT compilation, linking and execution;
-- it does not assert that SPARK program contracts have been proved.
with Ada.Text_IO;
procedure Smoke_Ada is
begin
   Ada.Text_IO.Put_Line ("Ada compiler smoke test succeeded");
end Smoke_Ada;
ADA
  (
    cd "$workdir"
    gnatmake -q -gnat2022 smoke_ada.adb
    ./smoke_ada
  )
  exit 0
fi

if [[ "$mode" == "--install-apt" ]]; then
  if [[ ! -f /etc/debian_version ]]; then
    printf 'This apt profile targets Debian 13 only.\n' >&2
    exit 2
  fi
  if command -v lsb_release >/dev/null &&
     [[ "$(lsb_release -rs)" != "13" ]]; then
    printf 'Distribution release does not match Debian 13.\n' >&2
    exit 2
  fi
  for package in "${ADA_PACKAGES[@]}"; do
    candidate="$(apt-cache policy "$package" | sed -n '/Candidate:/s/.*Candidate: //p' | head -n 1)"
    if [[ -z "$candidate" || "$candidate" == "(none)" ]]; then
      printf 'Missing package candidate: %s; check apt sources first.\n' "$package" >&2
      exit 3
    fi
  done
  printf 'Installing reviewed Debian 13 packages via sudo apt-get.\n'
  sudo apt-get install --no-install-recommends "${ADA_PACKAGES[@]}"
  exit 0
fi

if [[ "$mode" == "--install-spark" ]]; then
  if ! command -v alr >/dev/null; then
    printf 'Alire is missing. First use --install-apt.\n' >&2
    exit 3
  fi
  # Debian 13 packages Alire 1.2.1. Its CLI has "get" and "with", but
  # NO "install" subcommand. Retrieve a versioned binary crate without
  # installing a different Alire release or modifying the system PATH.
  mkdir -p "$SPARK_PREFIX"
  wrapper_dir="$SPARK_PREFIX/bin"
  wrapper="$wrapper_dir/gnatprove"
  if [[ -x "$wrapper" ]]; then
    printf 'Existing GNATprove wrapper: %s\n' "$wrapper"
    "$wrapper" --version
    exit 0
  fi

  printf 'Retrieving GNATprove %s using Alire 1.2-compatible get.\n' "$SPARK_VERSION"
  (
    cd "$SPARK_PREFIX"
    alr -n get "gnatprove=$SPARK_VERSION"
  )
  # Alire get produces a versioned directory gnatprove_VERSION_HASH.
  # Restrict discovery to the requested version, not arbitrary binaries
  # from other releases or other crates in the prefix.
  mapfile -d '' -t candidates < <(
    find "$SPARK_PREFIX" -type f -perm /111 \
      -path "*/gnatprove_${SPARK_VERSION}_*/bin/gnatprove" -print0
  )
  if (( ${#candidates[@]} != 1 )); then
    printf 'ERROR: Expected exactly one GNATprove %s executable; found %s.\n' \
      "$SPARK_VERSION" "${#candidates[@]}" >&2
    printf 'Check release layout under %s before continuing.\n' "$SPARK_PREFIX" >&2
    exit 4
  fi
  binary="${candidates[0]}"
  binary_dir="$(dirname "$binary")"

  # A wrapper supplies the vendor bundle's own executables and solvers,
  # without changing PATH or system packages outside this process.
  mkdir -p "$wrapper_dir"
  printf -v quoted_binary '%q' "$binary"
  printf -v quoted_directory '%q' "$binary_dir"
  cat > "$wrapper" <<EOF
#!/usr/bin/env bash
# User-local GNATprove $SPARK_VERSION launcher for the Alire binary crate.
# Keep the crate's bundled prover executables available to GNATprove.
set -euo pipefail
export PATH=$quoted_directory:"\$PATH"
exec $quoted_binary "\$@"
EOF
  chmod 755 "$wrapper"
  if ! "$wrapper" --version; then
    rm -f -- "$wrapper"
    printf 'ERROR: GNATprove binary did not pass its version probe.\n' >&2
    exit 5
  fi
  printf 'GNATprove %s launcher: %s\n' "$SPARK_VERSION" "$wrapper"
  printf 'In an Alire project, use: alr with gnatprove; alr gnatprove\n'
  exit 0
fi

if [[ "$mode" == "--metis-source" ]]; then
  if [[ -e "$METIS_DIR" && ! -d "$METIS_DIR/.git" ]]; then
    printf 'Refusing to overwrite existing non-repository Metis path: %s\n' "$METIS_DIR" >&2
    exit 3
  fi
  if [[ ! -d "$METIS_DIR/.git" ]]; then
    mkdir -p "$(dirname "$METIS_DIR")"
    git clone "$METIS_URL" "$METIS_DIR"
  fi
  # Fetch only if the already cloned repository lacks the verified object.
  if ! git -C "$METIS_DIR" cat-file -e "$METIS_SHA^{commit}" 2>/dev/null; then
    git -C "$METIS_DIR" fetch origin "$METIS_SHA"
  fi
  git -C "$METIS_DIR" checkout --detach "$METIS_SHA"
  current="$(git -C "$METIS_DIR" rev-parse HEAD)"
  if [[ "$current" != "$METIS_SHA" ]]; then
    printf 'Wrong Metis source commit: %s\n' "$current" >&2
    exit 3
  fi
  printf 'Metis theorem prover source pinned to %s at %s\n' "$current" "$METIS_DIR"
  printf 'Compilation requires MLton, Poly/ML (polyc), or Moscow ML.\n'
  exit 0
fi

if [[ "$mode" == "--metis-build" ]]; then
  if [[ ! -d "$METIS_DIR/.git" ]]; then
    printf 'First run --metis-source.\n' >&2
    exit 3
  fi
  if [[ "$(git -C "$METIS_DIR" rev-parse HEAD)" != "$METIS_SHA" ]]; then
    printf 'Refusing to build an unpinned Metis checkout.\n' >&2
    exit 3
  fi
  if command -v mlton >/dev/null; then
    target=mlton
  elif command -v polyc >/dev/null; then
    target=polyml
  elif command -v mosmlc >/dev/null; then
    target=mosml
  else
    printf 'No supported Standard ML compiler is installed.\n' >&2
    printf '%s\n' 'Metis needs MLton, Poly/ML or Moscow ML; Debian 13 may need a separate build.'
    exit 4
  fi
  make -C "$METIS_DIR" "$target"
  executable="$METIS_DIR/bin/$target/metis"
  if [[ ! -x "$executable" ]]; then
    printf 'Metis did not produce the expected executable: %s\n' "$executable" >&2
    exit 5
  fi
  "$executable" --help || true
  printf 'Metis built: %s\n' "$executable"
  exit 0
fi

if [[ "$mode" == "--detect" ]]; then
  for binary in gnat gprbuild alr gnatprove gappa why3 z3 cvc5 eprover; do
    if command -v "$binary" >/dev/null; then
      printf 'FOUND %s: %s\n' "$binary" "$(command -v "$binary")"
    else
      printf 'MISSING %s\n' "$binary"
    fi
  done
  if [[ -x "$SPARK_PREFIX/bin/gnatprove" ]]; then
    printf 'FOUND pinned GNATprove: %s/bin/gnatprove\n' "$SPARK_PREFIX"
  fi
  if [[ -x "$METIS_DIR/bin/mlton/metis" ]]; then
    printf 'FOUND Metis theorem prover: %s/bin/mlton/metis\n' "$METIS_DIR"
  elif [[ -x "$METIS_DIR/bin/polyml/metis" ]]; then
    printf 'FOUND Metis theorem prover: %s/bin/polyml/metis\n' "$METIS_DIR"
  fi
  if command -v why3 >/dev/null; then
    # Debian 13 Why3 1.8.0 uses the "config detect" subcommand, not
    # "--detect". List installed known provers using the 1.8 top-level
    # option, rather than the 1.9-specific config list-provers command.
    why3 config detect
    why3 --list-provers
  fi
  exit 0
fi
