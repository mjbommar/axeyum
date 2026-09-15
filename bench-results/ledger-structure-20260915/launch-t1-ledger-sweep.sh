#!/usr/bin/env bash
# LEDGER-STRUCTURE lane (Phase 3 sizing for Phase 4, dispatch-and-instrumentation
# plan 2026-09-15). Fills the outcome ledger (ADR-2102/ADR-2105) over all seven
# Tier 1 divisions' pinned 200-file lists, one arm (`main`, commit db31113fa),
# 24 s wall / 8 GiB `ulimit -v` per file, --trace on.
#
# Sharding pattern copied from `bench-results/quant-ladder-ownership-20260915/
# launch-ab.sh`: one shard per PHYSICAL core pair, 3 hosts (s5/s6/s7) x 4 core
# pairs = 12 shards, matching the 12-way split of the Tier 1 pinned lists
# already on disk at
# `/nas3/data/axeyum/harness/postmerge-board-dt/lists/T1_<DIV>.<00-11>.txt`
# (verified byte-identical, as a set, to
# `bench-results/tier1-current-20260914/<DIV>.tsv`'s `file` column). Divisions
# run SERIALLY within one shard (mirrors `t1-driver.sh`) -- launching them
# concurrently on one pinned core pair oversubscribes it, which is exactly the
# 9x-oversubscription collapse this lane's brief named as the failure to avoid.
#
# # Why this runs off-worktree
#
# `/home/mjbommar/projects/personal/axeyum` (the main checkout) is local disk on
# s4 and is visible read-only-in-spirit on s5/s6/s7 as their OWN separate local
# checkouts -- but `.claude/worktrees/<this-lane>` is s4-local only and is NOT
# visible from s5/s6/s7 at all (verified: `ls` of the worktree path from any of
# the three remote hosts returns ENOENT). The corpus itself is reachable
# everywhere via the shared `nas3` NFS mount, so the fix is to ship the BUILT
# BINARY plus the four small orchestration files this sweep actually needs
# (`ledger-run-one.sh`, `ledger-sweeps/t1-board-run-ledger.sh`,
# `outcome_ledger.py`, `route_trace_reader.py`) to a scratch directory on each
# remote host rather than to try to make the worktree itself reachable. Ledger
# `append` never calls `git` (only `load`/`show`/`agg`/staleness do), so the
# remote deploy needs no repository at all -- confirmed by reading
# `outcome_ledger.py` before relying on it.
#
# Each shard writes into ITS OWN capture/ledger directory
# (`out/shard<NN>/{captures,board,ledger}`) rather than one shared
# `bench-results/ledger/` -- `ledger-run-one.sh`'s own comment names the reason:
# concurrent appends to one `INDEX.tsv` over NFS are a read-then-append race,
# and a row can exceed the 4 KiB that makes `O_APPEND` atomic. Consolidation
# (`consolidate.py`, run after every shard's `out/shard<NN>/DONE` marker exists)
# reads each shard's per-division ledger file through `outcome_ledger.py`'s
# `read_ledger`/`append_row` and merges them into ONE file per division under
# `bench-results/ledger/`, registering through the library, never by hand.
#
# This script is a RECORD of what was run, not a one-shot re-runnable driver:
# the actual dispatch used twelve separate `ssh -n -f ... nohup setsid`
# invocations (one per shard, so a transient SSH hiccup on one shard does not
# abort the other eleven) rather than one loop, for the same reason
# `launch-ab.sh` documents launching each shard as its own backgrounded
# process. The per-shard command line below is what each of the twelve ran;
# HOST and IDX/PIN vary per the table.
#
#   ssh -n -f "$HOST" \
#     "cd /tmp && nohup setsid bash /tmp/ledger-structure/deploy/shard-driver.sh \
#        $IDX $PIN [--invariance] \
#        > /tmp/ledger-structure/deploy/out/shard$IDX.log 2>&1 < /dev/null & disown"
#
# | idx | host | core pair | invariance |
# |-----|------|-----------|------------|
# | 00  | s5   | 1,9       | yes (112 files, >= the brief's 50-file floor) |
# | 01  | s5   | 3,11      | no |
# | 02  | s5   | 5,13      | no |
# | 03  | s5   | 6,14      | no |
# | 04  | s6   | 1,9       | no |
# | 05  | s6   | 3,11      | no |
# | 06  | s6   | 5,13      | no |
# | 07  | s6   | 6,14      | no |
# | 08  | s7   | 1,9       | no |
# | 09  | s7   | 3,11      | no |
# | 10  | s7   | 5,13      | no |
# | 11  | s7   | 6,14      | no |
#
# `shard-driver.sh`, deployed alongside the binary and copied here verbatim for
# the record:
#
#   #!/usr/bin/env bash
#   set -u
#   IDX="$1"; PIN="$2"; INV="${3:-}"
#   ROOT=/tmp/ledger-structure/deploy
#   LISTS=/nas3/data/axeyum/harness/postmerge-board-dt/lists
#   BIN="$ROOT/smtcomp_cli"
#   SHA=db31113fa
#   OUT="$ROOT/out/shard$IDX"
#   mkdir -p "$OUT/captures" "$OUT/board"
#   export AXEYUM_LEDGER_DIR="$OUT/ledger"
#   DIVS="AUFDTLIRA AUFLIRA QF_NIA UF UFDTLIRA UFLIA UFNIA"
#   for d in $DIVS; do
#     sl="$LISTS/T1_${d}.${IDX}.txt"
#     so="$OUT/board/${d}.tsv"
#     [ -f "$sl" ] || { echo "SKIP $d shard$IDX: no list $sl"; continue; }
#     [ -s "$so" ] && { echo "SKIP $d shard$IDX: $so already non-empty"; continue; }
#     "$ROOT/scripts/ledger-sweeps/t1-board-run-ledger.sh" \
#       "ledger-structure-20260915-${d}-shard${IDX}" "$d" "$sl" "$so" "$PIN" \
#       "$BIN" "$SHA" "$OUT/captures" 24 "$INV"
#   done
#   echo "SHARD-DONE idx=$IDX"
#   touch "$OUT/DONE"
#
# Completion is detected by polling for `out/shard<NN>/DONE` on each host (a
# file, per this repository's rule to watch artifacts rather than processes),
# never by `pgrep`.
set -u
echo "This file documents the sweep; it is not meant to be re-executed blind."
echo "See bench-results/ledger-structure-20260915/README.md for the consolidated result."
