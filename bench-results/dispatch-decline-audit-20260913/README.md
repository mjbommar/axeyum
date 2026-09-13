# ADR-1966 — the dispatch refusal-propagation audit

What is here, what produced it, and which numbers are safe to quote.

The decision, the classification table and the reasoning are in
[ADR-1966](../../docs/research/09-decisions/adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md).
This file is the method and the index.

## The population

`refusal-propagation-baseline.json` — the pinned list of every site in the
solver dispatch path where a sub-solve's `SolverError::Unsupported` is
propagated rather than declined, produced by
[`scripts/enumerate-dispatch-refusal-propagation.py`](../../scripts/enumerate-dispatch-refusal-propagation.py).

```sh
python3 scripts/enumerate-dispatch-refusal-propagation.py            # list it
python3 scripts/enumerate-dispatch-refusal-propagation.py \
  --fail-on-new bench-results/dispatch-decline-audit-20260913/refusal-propagation-baseline.json
```

The ratchet exits 1 and names the site when a new propagation of this shape
appears. **Its negative control caught an inverted control in this lane**: the
baseline first stored ABSOLUTE paths, so on any other tree root every site read
as new and the ratchet fired on a clean tree. A gate that fails unconditionally
looks exactly like a working one until you check that it also passes when it
should. Paths are root-relative; re-introducing one closed site makes the
ratchet name that site and exit 1, while the restored tree exits 0.

## The measurement

| script | what it answers |
|---|---|
| `hit-rate.py` | how many files in a pinned list carry the SHAPE each fixed rung needs. **An upper bound on reachability, not a measure of it** — see the AUFLIRA correction below. |
| `guard-firing.sh` | how often each guard actually fires, read from the ROUTE TRAIL of the fixed binary. This is the measure that aims an A/B correctly. |
| `census-run.sh` | one binary over one pinned list, recording verdict, `attempts=` and the `give-up` line. `give-up kind=Error detail=unsupported by backend:` is the live defect; `detail=parse error:` is NOT — the same token covers both and mixing them inflates the population. |
| `ab-run.sh` | the per-file A/B: both arms back to back on ONE pinned core, arm order alternating per file, load sampled per row. |
| `ab-launch.sh` / `ab-launch2.sh` | the division sets, and why each was chosen. |
| `summarize.py` | scores an A/B run. **Refuses to score a malformed row** — the refusal sentence written into a row can split the record, and reading a parse failure of the results file as "no movement" manufactures a null. |
| `verify-new-verdicts.sh` | every new verdict against the declared `:status`, z3 (`-T:` SECONDS) and cvc5 (`--tlimit` MILLISECONDS). Exit status depends on the finding. |
| `mutation-control.py` | deletes one guard at a time in a `lane-snapshot.sh` copy — never the shared worktree — and reports which tests die. Refuses to score anything if the unmutated tree is not green first. |
| `ratchet-control.sh` | the negative control for `--fail-on-new`: re-introduces one closed site, requires exit 1 naming that site, and requires the restored tree to exit 0. |
| `ufnra-guard-firing-scan.sh` | the `uf-nra` guard over all 58 `QF_UFNRA` files — the only division whose logic can enter that route. |

Envelope: 10 s / 8 GiB per run for the A/B (24 s for the re-checks and the
`QF_ABV` firing population), `taskset` to one physical core per division, on a
box carrying other lanes throughout (load 9–24). Interleaving is what makes
that cancel in the difference; every moved row was re-run 3× per arm at 24 s
before being counted.

## Three corrections that cost more than they look

1. **`hit-rate.py` aimed the first A/B batch at `AUFLIRA`** — 184 of 200 files
   declare an array-valued uninterpreted function, the highest of any division.
   It moved nothing, because **186 of 200 never get past the parser** (nested
   array element sort, ADR-1955). A structural hit rate read out of file text
   cannot see a gate in front of the dispatcher.
2. **The obvious guard fixture was vacuous.** The refusing shape plus
   `x > 0 AND x < 0` is refuted by `int-box-eval` at `attempts=3`, before the
   rung under test, so both arms answer `unsat` and the test passes on the
   unfixed tree. Every fixture in
   `crates/axeyum-solver/tests/dispatch_rung_refusal_declines.rs` was checked
   against a binary built WITHOUT the guards and kept only because the arms
   differ.
3. **A 2 s screen found 0 refusal-errors in six divisions and that was nearly
   the headline.** It is a valid enumeration for THIS defect (the refusal
   arrives in ~1 ms, `total_ms=1` at `attempts=17`), but only because that was
   checked; a screen shorter than the rungs above the refusal would have
   reported a clean tree.
