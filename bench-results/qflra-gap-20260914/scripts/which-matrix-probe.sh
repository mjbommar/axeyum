#!/usr/bin/env bash
# WHICH matrix eats the 8 GiB?  Mechanism, not inference.
#
# `lra::decide_within` has TWO quadratic allocations and, since 2026-09-08,
# the SIMPLEX one goes first at `SIMPLEX_FIRST_AT_CONSTRAINTS = 256`:
#
#   simplex dense tableau  m x (nvars + m) x 32 B   (`simplex::Tableau::new`)
#   FM Farkas multipliers  n x n x 32 B             (`lra::unit_vec` loop)
#
# Under the board's 8 GiB `ulimit -v` the process aborts before printing
# anything, so neither can be read.  Give it room instead (24 GiB) and read the
# engine's OWN counters off the `; lazy-smt` line -- `cube_simplex_calls`,
# `cube_matrices` (FM multiplier matrices built), `cube_simplex_ms`,
# `cube_fm_ms` -- plus peak RSS.  Those counters are incremented by the engines
# themselves, so they cannot agree with a wrong guess.
#
# `AXEYUM_LRA_ROUTE=fm-first` is the control: it sets
# `simplex_first_at_constraints = usize::MAX`, i.e. the pre-2026-09-08 order.
# If the simplex is the allocator, this arm must move the bytes to FM.
BIN=/nas3/data/axeyum/harness/qflra-gap/bin/smtcomp_cli-cfcae7fa7
F=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2

probe() {  # $1 = label, $2 = AXEYUM_LRA_ROUTE value ("" = shipped default)
  echo "### $1"
  if [ -z "$2" ]; then
    /usr/bin/time -f 'peak_rss_kb=%M wall=%e' \
      timeout 120 taskset -c 0,8 "$BIN" "$F" --timeout-ms 60000 --trace 2>&1 \
      | grep -oE 'cube_simplex_calls=[0-9]+|cube_matrices=[0-9]+|cube_simplex_ms=[0-9]+|cube_fm_ms=[0-9]+|cube_fm_declines=[0-9]+|atoms=[0-9]+|online_probe=[a-z-]+|peak_rss_kb=[0-9]+|wall=[0-9.]+|^(sat|unsat|unknown)$'
  else
    AXEYUM_LRA_ROUTE="$2" /usr/bin/time -f 'peak_rss_kb=%M wall=%e' \
      timeout 120 taskset -c 0,8 "$BIN" "$F" --timeout-ms 60000 --trace 2>&1 \
      | grep -oE 'cube_simplex_calls=[0-9]+|cube_matrices=[0-9]+|cube_simplex_ms=[0-9]+|cube_fm_ms=[0-9]+|cube_fm_declines=[0-9]+|atoms=[0-9]+|online_probe=[a-z-]+|peak_rss_kb=[0-9]+|wall=[0-9.]+|^(sat|unsat|unknown)$'
  fi
  echo
}

ulimit -v $((24 * 1024 * 1024))
probe "shipped default route (simplex first at 256 constraints)" ""
probe "AXEYUM_LRA_ROUTE=fm-first (pre-2026-09-08 order)" "fm-first"
