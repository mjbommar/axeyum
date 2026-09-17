# ADR-2145: the retained-trail warm schedule on the pinned lists (one binary, two env values)

The A/B behind [ADR-2145](../../docs/research/09-decisions/adr-2145-the-warm-core-keeps-the-surviving-scopes-trail-across-pop-and-check.md):
what `AXEYUM_WARM_KEEP_TRAIL=on` costs or buys against the shipped reset
schedule on the 200-file `QF_BV` and `QF_ABV` pinned lists, so the ADR can
decide the default from a measurement.

- **Arms.** A = the variable unset (the schedule shipped from ADR-0009: the
  warm core unwinds its whole trail between solves); B =
  `AXEYUM_WARM_KEEP_TRAIL=on` (backtrack to the surviving assumption prefix,
  re-init list for clauses added in between, reset when under half the trail
  survives). One binary, `smtcomp_cli` built at lane commit `637c67d73`
  (sha256 `a9a66260…`, in every `.log`).
- **Lists.** [`../parity-lists/QF_BV.txt`](../parity-lists/QF_BV.txt) and
  [`../parity-lists/QF_ABV.txt`](../parity-lists/QF_ABV.txt), each split into
  two halves of 100 run concurrently on s7: `QF_BV` on physical core pairs
  `1,9` / `3,11`, `QF_ABV` on `5,13` / `6,14`.
- **Envelope.** 24 s wall, 8 GiB `ulimit -v`, arms interleaved per file and
  alternating in order (`ab-env.sh`, ADR-2140's harness with the variable
  renamed; `$EPOCHREALTIME` timing with the 200 ms sleep self-check, which
  read 204 ms on every shard).
- **Time movers** (either arm >10 % + 50 ms slower on a both-decided file)
  were rerun three times per arm, arms alternating within the passes, on one
  core pair (`recheck-time.sh`; `movers-*.tsv`, verdict/ms/rc per pass).
- **Replay.** A `sat` printed by `smtcomp_cli` has already replayed against
  the original terms inside the solver (a failed replay is `unknown`, never
  `sat`).

`summarize.py` (ADR-2140's, relabelled) produced the tables in the ADR:

| division | decided A / B | wall on both-decided | B slower / A slower | verdict movers / flips / `:status` disagreements |
| --- | ---: | ---: | ---: | ---: |
| `QF_BV` | 187 / 187 | 164.5 → 162.9 s | 3 / 3 (all equal on recheck) | 0 / 0 / 0 |
| `QF_ABV` | 189 / 189 | 171.1 → 175.2 s | 4 / 10 (9 stably faster, 1 stably slower, 4 equal on recheck) | 0 / 0 / 0 |

The one nonzero exit row (`QF_ABV/brummayerbiere/wchains140se.smt2`, rc 134)
is on both arms. `QF_BV`'s one-shot route does not build a warm solver, so
that list is the null; `QF_ABV`'s online array route does, which is where
the movers are.
