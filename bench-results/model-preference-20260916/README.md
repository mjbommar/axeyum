# ADR-2140: the price of `PreferZero` on `QF_BV` (one binary, two env values)

The A/B behind [ADR-2140](../../docs/research/09-decisions/adr-2140-which-model-a-sat-returns-is-a-policy-and-the-shipped-policy-is-todays-search.md):
what `AXEYUM_MODEL_PREFERENCE=zero` costs against the shipped `Any` on the
200-file `QF_BV` pinned list, so the ADR can say what it ships OFF.

- **Arms.** A = the variable unset (`ModelPreference::Any`, the shipped
  search byte for byte); B = `AXEYUM_MODEL_PREFERENCE=zero` (every SAT
  decision `false` first, then the replay-checked model shrink). One binary,
  `target/release/examples/smtcomp_cli`, hash in `half*.log`.
- **List.** [`../parity-lists/QF_BV.txt`](../parity-lists/QF_BV.txt), split
  into two halves of 100 files run concurrently on s7, each half pinned to one
  physical core pair (`1,9` and `3,11`).
- **Envelope.** 24 s wall, 8 GiB `ulimit -v`, arms interleaved per file and
  alternating in order (`ab-env.sh`, derived from
  `../route-ownership-20260915/ab-run.sh` with `date` replaced by
  `$EPOCHREALTIME` and a 200 ms sleep self-check, because s7's `date` is
  uutils and prints nanoseconds under `%3N`).
- **Movers** are re-checked three times per arm with
  `../route-ownership-20260915/recheck-movers.sh`; arm B is a wrapper script
  that sets the variable, so the two "binaries" hash differently as that
  script requires.
- **Replay.** A `sat` printed by `smtcomp_cli` has already replayed against
  the original terms inside `SatBvBackend` (a failed replay is `unknown`,
  never `sat`), so the replay pass rate is the count of `sat` rows with no
  replay-failure `unknown` underneath them; `replay-check.py` additionally
  replays every arm-B `sat` through `axeyum.smt.solve(...).replay()`.

Three runs, each two halves (`<run>1.tsv` on cores `1,9`, `<run>2.tsv` on
`3,11`), summarised by `summarize.py` into `summary-<run>.md`:

| run | arm B | binary (`sha256` prefix) |
| --- | --- | --- |
| `half*` (run B) | `AXEYUM_MODEL_PREFERENCE=zero`, SAT-core phase ON, shrink bounded by evaluations only | `b6f0c14f` |
| `c*` (run C) | `zero`, phase OFF (`AXEYUM_MODEL_PREFERENCE_PHASE=off`), shrink bounded by the solve's own time | `882b3137` |
| `d*` (run D) | `zero`, phase ON, shrink bounded by the solve's own time | `882b3137` |

Run C is the shipped `PreferZero`; runs B and D isolate the SAT-core phase.
`movers-b.tsv` is run B's three-pass recheck (1 STABLE-GAIN, 1 STABLE-LOSS);
run C had no movers; run D's two movers are the same two files as run B's. `replay-check.py` re-solved every run-B `sat` through
the Python binding: 52 replayed, 0 failed, 4 undecided within 24 s on s4.
