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
# Official upstream GNAT-FSF-builds release and Alire stable-1.4.0 index.
# Debian 13's Alire 1.2.1 (stable-1.2.1 index) does NOT list 16.1.0.
# Official release asset size was independently checked against GitHub.
SPARK_URL="https://github.com/alire-project/GNAT-FSF-builds/releases/download/gnatprove-16.1.0-1/gnatprove-x86_64-linux-16.1.0-1.tar.gz"
SPARK_SHA="82528bef29857e239373fcc36732837d743f5a00805d502c70455422ffc97191"
SPARK_SIZE=472919963
SPARK_ARCHIVE_NAME="gnatprove-x86_64-linux-16.1.0-1.tar.gz"
SPARK_INSTALL_DIR="$SPARK_PREFIX/gnatprove-$SPARK_VERSION"

mode="${1:---plan}"
case "$mode" in
  --help|-h)
    printf '%s\n' 'Usage: bash scripts/install_ada_spark_why3.sh [action]'
    printf '%s\n' '  --plan           print actions without changing the computer'
    printf '%s\n' '  --install-apt    explicitly install Debian GNAT/Why3/SMT packages'
    printf '%s\n' '  --install-spark  install checksum-pinned official GNATprove 16.1.0 (Linux x86-64)'
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
  printf '\nGNATprove %s: official release URL %s\n' "$SPARK_VERSION" "$SPARK_URL"
  printf 'GNATprove archive SHA256: %s; size %s bytes\n' "$SPARK_SHA" "$SPARK_SIZE"
  printf 'GNATprove prefix: %s\n' "$SPARK_INSTALL_DIR"
  printf '%s\n' 'NOTE: Alire 1.2.1 catalog lists only older GNATprove releases; do not try alr get gnatprove=16.1.0.'
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
  # The 16.1.0 crate exists in Alire stable-1.4.0, but Debian 13 has Alire
  # 1.2.1 whose stable-1.2.1 index only exposes older releases. Bypass
  # only that index-version mismatch by using the *same official artifact*
  # whose SHA256 is pinned in the newer upstream Alire manifest.
  # No opam switch, apt package, Alire index, or PATH entry is changed.
  if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
    printf 'ERROR: This GNATprove asset is only for Linux x86_64.\n' >&2
    exit 3
  fi
  for program in curl sha256sum tar stat find; do
    if ! command -v "$program" >/dev/null; then
      printf 'ERROR: Missing download tool %s.\n' "$program" >&2
      exit 3
    fi
  done

  wrapper_dir="$SPARK_PREFIX/bin"
  wrapper="$wrapper_dir/gnatprove"
  if [[ -x "$wrapper" ]]; then
    printf 'Existing user-local GNATprove wrapper: %s\n' "$wrapper"
    "$wrapper" --version
    exit 0
  fi
  if [[ -e "$SPARK_INSTALL_DIR" ]]; then
    printf 'ERROR: Existing GNATprove directory lacks a verified launcher: %s\n' \
      "$SPARK_INSTALL_DIR" >&2
    exit 4
  fi
  archive_dir="$SPARK_PREFIX/downloads"
  archive="$archive_dir/$SPARK_ARCHIVE_NAME"
  mkdir -p "$archive_dir"
  if [[ -L "$archive" ]]; then
    printf 'ERROR: Refusing to use symlinked archive: %s\n' "$archive" >&2
    exit 4
  fi
  archive_ok=0
  if [[ -f "$archive" && "$(stat -c '%s' "$archive")" == "$SPARK_SIZE" ]] &&
     printf '%s  %s\n' "$SPARK_SHA" "$archive" | sha256sum --check --status; then
    archive_ok=1
    printf 'Reusing SHA256-verified GNATprove archive: %s\n' "$archive"
  fi

  if (( archive_ok == 0 )); then
    # A 473 MB release download may be interrupted. Keep a dedicated
    # .partial file so subsequent explicit --install-spark calls can resume,
    # just as the existing Isabelle installer does. Never replace the
    # verified archive until the partial has passed length and SHA256.
    partial="$archive.partial"
    if [[ -L "$partial" || ( -e "$partial" && ! -f "$partial" ) ]]; then
      printf 'ERROR: Refusing non-regular partial archive: %s\n' "$partial" >&2
      exit 4
    fi
    printf 'Downloading/resuming GNATprove %s (%s bytes) to %s\n' \
      "$SPARK_VERSION" "$SPARK_SIZE" "$partial"
    curl --fail --location --continue-at - --retry 3 \
      --connect-timeout 30 --speed-limit 1024 --speed-time 120 \
      --proto '=https' --proto-redir '=https' \
      --output "$partial" "$SPARK_URL"
    if [[ "$(stat -c '%s' "$partial")" != "$SPARK_SIZE" ]] ||
       ! printf '%s  %s\n' "$SPARK_SHA" "$partial" | sha256sum --check --status; then
      printf 'ERROR: GNATprove download checksum/length mismatch; partial preserved for inspection.\n' >&2
      exit 4
    fi
    # Replace an old invalid archive only after the new file verifies.
    mv -f -- "$partial" "$archive"
  fi

  # Never make a partial extracted directory appear as an installed
  # release. Keep all extraction in a temporary sibling until complete.
  tmpdir="$(mktemp -d "$SPARK_PREFIX/.gnatprove-extract.XXXXXXXX")"
  trap 'rm -rf -- "$tmpdir"' EXIT
  tar --extract --gzip --file "$archive" --directory "$tmpdir" \
      --no-same-owner --no-same-permissions
  mapfile -d '' -t candidates < <(
    find "$tmpdir" -type f -perm /111 -path '*/bin/gnatprove' -print0
  )
  if (( ${#candidates[@]} != 1 )); then
    printf 'ERROR: Expected one upstream GNATprove executable; found %s.\n' \
      "${#candidates[@]}" >&2
    exit 4
  fi
  binary_rel="${candidates[0]#"$tmpdir"/}"
  mv -- "$tmpdir" "$SPARK_INSTALL_DIR"
  trap - EXIT
  binary="$SPARK_INSTALL_DIR/$binary_rel"
  binary_dir="$(dirname "$binary")"
  mkdir -p "$wrapper_dir"
  printf -v quoted_binary '%q' "$binary"
  printf -v quoted_directory '%q' "$binary_dir"
  cat > "$wrapper" <<EOF
#!/usr/bin/env bash
# Pinned upstream FSF GNATprove $SPARK_VERSION user-local launcher.
# The bundle's local bin directory is available to its subprocesses only.
set -euo pipefail
export PATH=$quoted_directory:"\$PATH"
exec $quoted_binary "\$@"
EOF
  chmod 755 "$wrapper"
  if ! "$wrapper" --version; then
    rm -f -- "$wrapper"
    printf 'ERROR: GNATprove launcher failed its runtime version probe.\n' >&2
    exit 5
  fi
  printf 'GNATprove %s verified and installed at %s\n' "$SPARK_VERSION" "$wrapper"
  printf '%s\n' 'No changes were made to Alire, GNAT or opam switches.'
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
