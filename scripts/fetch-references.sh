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

echo "done"
