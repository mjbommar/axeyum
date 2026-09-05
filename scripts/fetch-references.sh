#!/usr/bin/env bash
# Fetch shallow clones of reference projects into references/.
# The clones are gitignored; this script is the reproducible record.
set -euo pipefail

cd "$(dirname "$0")/../references"

repos=(
  # Rust SAT solvers and SAT infrastructure
  https://github.com/chrjabs/rustsat
  https://github.com/jix/varisat
  https://github.com/shnarazk/splr
  https://github.com/c-cube/batsat
  https://github.com/sarsko/CreuSAT
  # Rust SMT bindings
  https://github.com/prove-rs/z3.rs
  # Symbolic execution / reverse engineering references
  https://github.com/angr/angr
  https://github.com/mjbommar/glaurung
  # Rewriting / e-graphs
  https://github.com/egraphs-good/egg
  https://github.com/egraphs-good/egglog
  # Proof checking and proof bridges
  https://github.com/ufmg-smite/carcara
  https://github.com/marijnheule/drat-trim
  https://github.com/cvc5/ethos
  https://github.com/ufmg-smite/lean-smt
  https://github.com/ammkrn/nanoda_lib
  # C/C++ solver design references
  https://github.com/Z3Prover/z3
  https://github.com/arminbiere/cadical
  https://github.com/arminbiere/kissat
  https://github.com/bitwuzla/bitwuzla
  https://github.com/niklasso/minisat
  https://github.com/msoos/cryptominisat
  # Word-level formats
  https://github.com/Boolector/btor2tools
  # String/automata solver references (QF_SLIA parity work)
  # Z3-Noodler won QF_SLIA at SMT-COMP 2025 with 99.6%; its stabilization-based
  # procedure and the MATA automata library are the state of the art to study.
  https://github.com/VeriFIT/z3-noodler
  https://github.com/VeriFIT/mata
  # General reasoning / proving horizon
  https://github.com/cvc5/cvc5
  https://github.com/vprover/vampire
  https://github.com/eprover/eprover
  https://github.com/leanprover/lean4
)

for url in "${repos[@]}"; do
  name="$(basename "$url")"
  if [ -d "$name" ]; then
    echo "pull $name"
    git -C "$name" pull --ff-only --quiet || echo "FAILED: $url"
  else
    echo "clone $name"
    git clone --depth 1 --quiet "$url" "$name" || echo "FAILED: $url"
  fi
done

# drat-trim is not just a reading reference — `scripts/check-claim-certificates.py
# --drat-checker references/drat-trim/drat-trim` runs the binary, so a clone alone
# is not enough. Its Makefile compiles with `-std=c99`, which hides the POSIX
# `getc_unlocked` it calls, and on this toolchain (gcc 15) the upstream target
# fails outright:
#
#   drat-trim.c:986:10: error: implicit declaration of function 'getc_unlocked'
#   make: *** [Makefile:6: drat-trim] Error 1
#
# `-D_GNU_SOURCE` exposes it without changing the standard's semantics. Built
# here so the checker is present rather than discovered missing by a gate.
if [ -d drat-trim ] && [ ! -x drat-trim/drat-trim ]; then
  echo "build drat-trim"
  ( cd drat-trim && gcc -std=c99 -D_GNU_SOURCE -DLONGTYPE -O2 -o drat-trim drat-trim.c ) \
    || echo "FAILED: building drat-trim"
fi

# --- The public Lean kernel conformance corpus (ADR-1663) -------------------
#
# `leanprover/lean-kernel-arena` is the corpus `docs/plan/lean-kernel-requirements-2026-08-13.md`
# §4.4 / R8.5 means by "a conformance corpus ... a `parse-only` checker scores
# ... on rejects". It is pinned at an EXACT commit here, not floated, because
# `scripts/check-kernel-conformance.py` scores against it and a floating corpus
# turns a score change into an unattributable one.
#
# Two artefacts, and both are needed:
#
#   * the repository       -- the test YAML (each case's expected outcome, the
#                             description, and the `parse-only` control's own
#                             definition) and the tutorial Lean sources.
#   * the published tarball -- the already-EXPORTED NDJSON for every case under
#                             10 MB, as `good/` (Lean accepts) and `bad/` (Lean
#                             rejects). Building these from source needs a Lean
#                             4.29.1 toolchain, `lake`, and network access to
#                             fetch `lean4export`; the tarball is what makes the
#                             corpus runnable on a host with none of that.
#
# The tarball is a release artefact, not a git object, so it is pinned by
# SHA-256 rather than by revision. A digest mismatch is reported and the old
# copy is kept: it means upstream regenerated the corpus, and the scored numbers
# in `artifacts/kernel-conformance/` were measured on the old bytes.
ARENA_REV=abc55357aee17c59dfdbf39c8a2e19739e23dd10
ARENA_TESTS_URL=https://arena.lean-lang.org/lean-arena-tests.tar.gz
ARENA_TESTS_SHA256=7e396d5de90e8871c9b1d7e2931f3efaba303056cdfd93e65f9ae1de628bf326

if [ ! -d lean-kernel-arena ]; then
  echo "clone lean-kernel-arena"
  git clone --quiet https://github.com/leanprover/lean-kernel-arena lean-kernel-arena \
    || echo "FAILED: lean-kernel-arena"
fi
if [ -d lean-kernel-arena ]; then
  echo "pin lean-kernel-arena at ${ARENA_REV}"
  git -C lean-kernel-arena fetch --quiet origin "$ARENA_REV" 2>/dev/null || true
  git -C lean-kernel-arena checkout --quiet "$ARENA_REV" \
    || echo "FAILED: pinning lean-kernel-arena at ${ARENA_REV}"
fi

mkdir -p lean-arena-tests
if [ ! -f lean-arena-tests/lean-arena-tests.tar.gz ]; then
  echo "fetch lean-arena-tests.tar.gz"
  curl -sSLo lean-arena-tests/lean-arena-tests.tar.gz.part "$ARENA_TESTS_URL" \
    && mv lean-arena-tests/lean-arena-tests.tar.gz.part lean-arena-tests/lean-arena-tests.tar.gz \
    || echo "FAILED: $ARENA_TESTS_URL"
fi
if [ -f lean-arena-tests/lean-arena-tests.tar.gz ]; then
  observed="$(sha256sum lean-arena-tests/lean-arena-tests.tar.gz | cut -d' ' -f1)"
  if [ "$observed" = "$ARENA_TESTS_SHA256" ]; then
    echo "unpack lean-arena-tests (sha256 ok)"
    tar xzf lean-arena-tests/lean-arena-tests.tar.gz -C lean-arena-tests
  else
    echo "FAILED: lean-arena-tests.tar.gz sha256 ${observed} != ${ARENA_TESTS_SHA256}"
    echo "        upstream regenerated the corpus; artifacts/kernel-conformance/ was"
    echo "        measured on the pinned bytes -- rescore before bumping the digest."
  fi
fi

echo "done"
