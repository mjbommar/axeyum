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
  https://github.com/arminbiere/cadical
  https://github.com/arminbiere/kissat
  https://github.com/bitwuzla/bitwuzla
  https://github.com/niklasso/minisat
  https://github.com/msoos/cryptominisat
  # Word-level formats
  https://github.com/Boolector/btor2tools
  # General reasoning / proving horizon
  https://github.com/cvc5/cvc5
  https://github.com/vprover/vampire
  https://github.com/eprover/eprover
  https://github.com/leanprover/lean4
)

for url in "${repos[@]}"; do
  name="$(basename "$url")"
  if [ -d "$name" ]; then
    echo "skip $name (exists)"
  else
    echo "clone $name"
    git clone --depth 1 --quiet "$url" "$name" || echo "FAILED: $url"
  fi
done

echo "done"
