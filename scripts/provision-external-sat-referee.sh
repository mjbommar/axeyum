#!/usr/bin/env bash
# Provision the EXTERNAL SAT referee binaries (ADR-1910): CaDiCaL and Kissat.
#
# These are NOT Cargo dependencies and never become any. They are standalone
# binaries that read DIMACS text on the command line, which is the entire reason
# they are a stronger referee than the `rustsat-batsat` adapter they replace: an
# in-process referee handed our own `CnfFormula` cannot see a defect in our
# DIMACS writer or parser, and an external binary reading the text can. ADR-0002's
# no-C/C++-in-the-default-graph rule is untouched -- nothing links to these.
#
# Sources are the gitignored `references/` clones (`scripts/fetch-references.sh`
# repopulates them). Builds happen in a scratch COPY, never in the clone: the
# clones are shared across every lane on a host and a build tree in one of them
# is another lane's surprise.
#
# Usage:
#   scripts/provision-external-sat-referee.sh            # build + install both
#   scripts/provision-external-sat-referee.sh --verify   # report only, install nothing
#
# Install prefix: $AXEYUM_REFEREE_PREFIX, else ~/.local/bin -- the same location
# `tests/external_sat_referee.rs` and `scripts/check-external-sat-referee.sh`
# search after PATH.

set -uo pipefail

cd "$(dirname "$0")/.."
repo_root="$PWD"

prefix="${AXEYUM_REFEREE_PREFIX:-$HOME/.local/bin}"
verify_only=0
[ "${1:-}" = "--verify" ] && verify_only=1

report() {
  local name="$1" path
  if path="$(command -v "$name" 2>/dev/null)"; then
    echo "  $name: $path ($("$path" --version 2>&1 | head -1))"
  elif [ -x "$prefix/$name" ]; then
    echo "  $name: $prefix/$name ($("$prefix/$name" --version 2>&1 | head -1)) [not on PATH]"
  else
    echo "  $name: ABSENT"
    return 1
  fi
}

if [ "$verify_only" = "1" ]; then
  echo "external SAT referee binaries:"
  have=0
  report cadical && have=1
  report kissat && have=1
  if [ "$have" = "0" ]; then
    echo "provision-external-sat-referee: none present. Run this script without" \
         "--verify to build them from references/." >&2
    exit 1
  fi
  exit 0
fi

# One scratch root per invocation. A fixed name is a banned idiom here: several
# lanes share one host and one /tmp.
work="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-referee-build-XXXXXX")" || {
  echo "provision-external-sat-referee: mktemp failed" >&2; exit 1; }
trap 'rm -rf "$work"' EXIT

mkdir -p "$prefix"

built=0
for name in cadical kissat; do
  clone="$repo_root/references/$name"
  if [ ! -d "$clone" ]; then
    echo "provision-external-sat-referee: references/$name is absent." \
         "Run scripts/fetch-references.sh first." >&2
    continue
  fi
  echo "provision-external-sat-referee: building $name from references/$name"
  cp -r "$clone" "$work/$name" || { echo "  copy failed" >&2; continue; }
  rm -rf "$work/$name/.git"
  # Both projects use the same hand-written `./configure && make` shape and drop
  # the binary at build/<name>.
  if ! ( cd "$work/$name" && ./configure >"$work/$name.configure.log" 2>&1 \
         && make -j"$(nproc 2>/dev/null || echo 4)" >"$work/$name.make.log" 2>&1 ); then
    echo "  $name BUILD FAILED; tail of the log:" >&2
    tail -20 "$work/$name.make.log" >&2 2>/dev/null
    continue
  fi
  if [ ! -x "$work/$name/build/$name" ]; then
    echo "  $name built but no binary at build/$name" >&2
    continue
  fi
  # Probe before installing: a binary that does not answer --version is treated
  # as absent by the test's resolver, so installing one would create a referee
  # that is present on disk and invisible to the gate.
  if ! "$work/$name/build/$name" --version >/dev/null 2>&1; then
    echo "  $name does not answer --version; not installing" >&2
    continue
  fi
  install -m 0755 "$work/$name/build/$name" "$prefix/$name" || {
    echo "  install to $prefix failed" >&2; continue; }
  echo "  installed $prefix/$name ($("$prefix/$name" --version 2>&1 | head -1))"
  built=$((built + 1))
done

if [ "$built" -eq 0 ]; then
  echo "provision-external-sat-referee: FAILED -- no referee was installed." >&2
  exit 1
fi

echo "provision-external-sat-referee: $built referee binary/binaries installed in $prefix"
case ":$PATH:" in
  *":$prefix:"*) ;;
  *) echo "provision-external-sat-referee: NOTE -- $prefix is not on PATH." \
          "The referee finds it anyway (it searches ~/.local/bin), but add it to" \
          "PATH if you want to run cadical/kissat by hand." ;;
esac
