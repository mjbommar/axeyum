# Notes: 202-frontier-split

Detail moved out of [`../status/202-frontier-split.md`](../status/202-frontier-split.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Also caught by measurement, not by the brief:** the brief's own method
(exact `Nat.log`/`Nat.sqrt`/`Nat.clog` name match) misses every Lean
dot-notation call (`n.sqrt` sugar for `Nat.sqrt n`) -- which is how MOST
`nat.sqrt` facts are actually written. Added binder-type resolution
(`(n : ℕ)` -> receiver `n` resolves to namespace `Nat`) so `n.sqrt`,
`n.succ.sqrt`, etc. resolve correctly. Documented, not silently patched
over: a COMPOUND receiver (`(n * n).sqrt`) is still invisible -- 2 of
`nat.sqrt`'s 10 open facts use one and are not flagged, though `Nat.sqrt`
is equally absent for them (under-reports, safe direction).

## Measured result

49 of 128 open facts flagged (not exactly 30 -- see below), naming 14
distinct missing declarations:

    14  Nat.sqrt        9  Nat.clog       3  Nat.multichoose   1  Nat.getI
    13  Nat.log          4  Nat.bit        2  Nat.ldiff         1  Nat.log2
                          3  Nat.bitwise    1  Int.gcdA          1  Nat.minFac
                                            1  Int.gcdB          1  Nat.fastFib
                                                                  1  Nat.bits

**Does this agree with the hand-measured 30?** Yes, once you account for
method. The brief's 30 = 12 `nat.log`(+`log2`) + 10 `nat.sqrt` + 8
`nat.clog`, counted from `declare_` function names across exactly three
families. This tool's family-matched counts: `nat.log` 11 (its own
`nat.log2` fact buckets separately at 1, 11+1=12, matching) + `nat.sqrt` 10
open, 8 flagged (2 missed by the compound-receiver gap, documented above,
not a disagreement) + `nat.clog` 8, all flagged = matches the 30 exactly
once `log`+`log2` are combined and the 2 known compound-receiver misses are
counted back in. **The other 19 flagged facts (`Int.gcdA`/`gcdB`,
`Nat.bit`/`bitwise`/`ldiff`/`bits`/`getI`, `Nat.multichoose`, `Nat.minFac`,
`Nat.fastFib`) are new findings this tool made that the brief's
three-family manual check never looked for** -- confirmed by hand-checking
each fact's `formal.statement` (e.g. `F:ml430-int-gcd-eq-gcd-ab-63005aef`:
`x.gcdA y`/`x.gcdB y` -- exactly the "genuine near-miss" the design review's
main body already diagnosed as needing a fresh computable
extended-Euclidean `Definition`, just not yet folded into its own addendum
count).

## Verified non-regression

- `--json`/`--output`/`--verify` are BYTE-IDENTICAL before/after this
  change (diffed directly) -- `build_machine_frontier` and `route_class`
  are untouched; only `describe()` (an added, optional trailing parameter,
  default `None`) and `main()`'s human-report path changed.
- `just next` / `just next-unlocks` still invoke the same entry point with
  no new required flags; `--kernel-projection <path>` is new and optional
  (tests/override only).
- 5 pre-existing failures in `scripts/tests/test_fact_frontier.py`
  (`ProducerContractDeclineTests`, `RealDeclineFeedbackLoopTests`) were
  found while running the suite. **Reproduced identically against the
  pre-change baseline** (same file swapped in place, same 5 tests, same
  assertions) -- ledger drift (a hardcoded `TARGET` fact id no longer
  matches current `admissible_fact_ids`), unrelated to this change and out
  of this lane's scope.

## Controls

`scripts/tests/test_frontier_definition_coverage.py`, 17 tests, all
mutation-verified by hand (delete the guard, confirm exactly the test
naming it fails, nothing else):

| guard | test | kills |
| --- | --- | --- |
| namespace known | `test_unknown_namespace_is_not_flagged` | isolated |
| not declared (exact match) | `test_declared_name_is_not_flagged` | isolated |
| not corroborated by a proved fact | `test_name_corroborated_by_a_proved_fact_is_not_flagged` | isolated |
| `KernelIndex.row_count == 0` rejected | `test_zero_row_index_is_rejected` | isolated |
| `KernelIndex` missing a positive control rejected | `test_index_missing_a_positive_control_is_rejected` | isolated |
| `describe()` blocker takes precedence over decidable/proof-route | `test_missing_definition_takes_precedence_over_decidable` | isolated |
| `load_kernel_index` degrades to `None`, never raises | `test_missing_captured_file_degrades_to_none` | isolated |

Auto-discovered by `scripts/run-python-controls.py` (`--list` confirms it;
no manual registration needed -- `test_fact_frontier` is already named
elsewhere, this new file is not).

## Known limitations (stated, not hidden)

- Compound-receiver dot calls (`(n * n).sqrt`) are invisible -- only a bare
  bound identifier resolves.
- Corroboration only suppresses false positives; it cannot manufacture a
  false negative (a name absent from both the environment and every proved
  statement stays flagged regardless of what else is proved).
- Only two Lean spellings parsed: `Nat.log b n` and `n.sqrt`. Anything
  written another way in `formal.statement` is invisible.
- This says nothing about whether a PROOF ROUTE exists once a fact IS
  statable -- that remains `route_class`'s question, unchanged.
- Coverage degrades to "not checked" (printed explicitly) when the prebuilt
  `kernel_declaration_projection` binary is absent -- never silently
  treated as "nothing missing".
- Running the check costs ~30s wall time when the binary IS present (it
  builds every constructed prelude, `creal`/`complex` included) on top of
  `fact-frontier.py`'s normal ~9s -- a real cost, not hidden, since `just
  next` is advisory rather than a hot gate.

## Next

- If `just next`'s ~30s added latency is unwelcome, cache the projection
  TSV to disk with a source-content staleness check (e.g. hash the `creal`/
  `nat_prelude`/... source trees) rather than re-running the binary every
  invocation.
- `Int.gcdA`/`Int.gcdB` closing needs the fresh computable
  extended-Euclidean `Definition` the design review's main body already
  scoped (`F:ml430-int-gcd-eq-gcd-ab-63005aef`) -- not a proof task, a
  construction task, exactly what this lane's split is for surfacing.
