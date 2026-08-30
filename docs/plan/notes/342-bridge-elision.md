# Notes: 342-bridge-elision

Detail moved out of [`../status/342-bridge-elision.md`](../status/342-bridge-elision.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Two earlier passes of this measurement were wrong and are recorded so nobody
repeats them. A first cut called **67 of 72** elided, because 139 of 174 settled
mirrors carry no `formal.kernel_statement` at all and silence was being read as
elision. The brief's own attempt returned zeros from a catalog whose keys were
guessed; the working key is `source_name → fact_id` over
`mathlib-nat-int-fact-catalog-v1.json`'s `kind == "external-source"` rows, which
is what the generator itself reads.

## The rule chosen, and why the alternatives are worse

**Keep promoting; label the reason.** The bridge is unchanged at 72 and nothing
is refused. `bridge_provenance` records, per constant, one of four derived
classes plus its witness counts, and `--statable` prints the conservative count
beside the headline one.

- `elaboration` (50) — a Lean instance or class projection. Notation, not
  vocabulary; the rendered-type test is meaningless for it and is not applied.
- `expressed` (2) — some settled witness's rendered kernel type mentions it.
- `elided` (8) — every witness with a rendered type fails to mention it.
- `unrendered` (12) — no witness carries a rendering; the ledger cannot say.

**The brief's candidate rule — promote only what the rendered kernel type
mentions — was implemented and refused.** Mathlib's pinned `type_repr` is 50/72
elaboration constants (`OfNat.ofNat` 73 witnesses, `instOfNatNat` 61,
`instHAdd`/`HAdd.hAdd` 32) which have no typeclasses to correspond to here and
can never appear in a kernel rendering by name. Applying it takes the statable
open pool from **24 to 0** against a defect worth 2 — roughly twelve times the
disease, and the mirror-image of the error being fixed.

**Folding `unrendered` into `elided` was refused** for the 139/174 reason above.

**Refusing elision-backed candidates was refused.** `elided` is a precision
flag, not a defect flag. `Monotone` is elided and safe (it unfolds pointwise
into env vocabulary, exactly as the frontier docstring already says of
`Nat.fib_mono`); `Set.Ioi` is elided and thin (it unfolds through a `Set` type
we lack). The classifier cannot separate those and does not claim to.

## Guards

- **V5** in `gen-autogenesis-statable-vocabulary.py`: the recorded provenance
  must be its derivation. Coverage gains four counters, guarded by V2.
- **S7** in `check-dispatchable-frontier.py`: the same, re-derived
  independently rather than imported — a gate consuming the producer's own
  classification cannot catch the producer being wrong. **Not evaluated when
  S1–S4 have already fired**, because S7 derives from the bridge and row set and
  would otherwise double-fire on every membership control. S2/S3 still bound the
  bridge from both sides, untouched.

## Mutation kill sets, as measured

`bash scripts/mutate-bridge-provenance-controls.sh` (isolated worktree only —
it edits tracked files in place).

    M1 V5 comparison deleted                  5   (exactly the five V5 cases)
    M2 is_elaboration instance branch        25
    M3 is_elaboration projection branch      25
    M4 is_elaboration all-caps spelling      25
    M5 unrendered class deleted              25
    M6 kernel_tokens last component          25
    M7 witness count zeroed                  20
    M8 rendered-witness count zeroed         20
    M9 provenance_coverage emptied           15
    N1 S7 comparison deleted                  2
    N2 S7 not-an-object branch                1
    N3 suspect_bridge filter emptied          1
    N4 S7's "skip when S1-S4 fired" removed   4

No survivors — after two fixes, and the fixes are the finding.

**M2–M9 kill 20–25 cases and that is not isolation.** V5 compares a fully
derived block against the committed artifact, so any edit to the derivation
invalidates that artifact in every case and V5 fires in cases expecting another
guard. Correct behaviour; only M1 isolates the guard itself. The frontier side
does isolate because S7's subject there is a fixture.

**Two survivors on the first run, both acted on rather than excused.**

`M6` survived, so the code was **deleted**. The `expressed` test read
`const in tokens or const.rsplit(".")[-1] in tokens`, but `kernel_tokens`
already emits both the qualified name and its last component, so the const-side
half only reached cases where a bare `Ioi` in an unrelated namespace would count
as expressing `Set.Ioi` — untested, and a loosening in the direction that turns
`elided` into `expressed`. M6 now targets the token side, which kills.

`N3` survived because nothing asserted the `--statable` report: the whole
`suspect_bridge` filter could be emptied with 38 cases green. A new case fixes
it and discriminates both ways — the fixture's `Test.fine` must be tagged and
`Test.also_fine` must not.

`M9` was my own bug, not a survivor: the mutation was `return {} or {...}`,
a no-op because `{}` is falsy. Corrected; it kills 15.

## Gates run, in the foreground

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1107|settled=0
      |references=0|verdict=PASS
    AUTOGENESIS_STATABLE_VOCABULARY|rows=174|bridge=72|elaboration=50
      |expressed=2|elided=8|unrendered=12|cached=202|verdict=PASS
    check-dispatchable-frontier.py                  OK, 17 dispatchable
    STATABLE_VOCABULARY_CONTROLS|cases=28|failures=0|verdict=PASS
    check-dispatchable-frontier controls: all 39 case(s) passed
    CONTROL_REGISTRATION|controls=31|orphans=0|py_orphans=0
    ADR_INDEX|rows=619|curated_summaries=524|duplicate_numbers=0166,0167

`scripts/check-fast.sh` exits 1, and it does so **independently of this lane**.
A/B against the merge base `c7b22c5dd` in a detached worktree:

    failing checks in this tree  42
    failing checks at the base   43
    failing ONLY in this tree     0

The one check that differed between the two captured logs,
`control-tests-reachable-controls`, fails **identically in both** when run
directly (`AssertionError: 15 != 16`, the same numbers), so the log difference
was a capture artifact rather than a change. Its assertion asks for
`ORPHAN_BASELINE` to be lowered to 15; that gain belongs to whoever earned it
and is deliberately not taken here, since lowering a baseline this lane did not
move could mask another lane's in-flight work.

No new script needs registering: both guards extend scripts already wired into
`check.sh` and the justfile, so `check-aggregate-scope.sh` is unaffected. The
measurement and mutation helpers are deliberately **not** under `scripts/tests/`
— the mutation harness edits tracked files and must never run in a shared
checkout.

## Landed changes

| what | where |
| --- | --- |
| `bridge_provenance` + four coverage counters + V5 | `scripts/gen-autogenesis-statable-vocabulary.py` |
| S7, the conservative `--statable` report, `suspect_bridge` | `scripts/check-dispatchable-frontier.py` |
| regenerated artifact (bridge unchanged at 72) | `artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` |
| V5 controls; row-removal case repointed to a bridge-neutral row | `scripts/tests/test-gen-autogenesis-statable-vocabulary.sh` |
| S7 controls, fixture provenance, elision-split report control | `scripts/tests/test-dispatchable-frontier.sh` |
| blast-radius measurement | `scripts/measure-bridge-elision-radius.py` |
| mutation harness | `scripts/mutate-bridge-provenance-controls.sh` |
| the decision | `docs/research/09-decisions/adr-0631-*.md` |

## Next

- `elided` and `unrendered` shrink as mirrors record `formal.kernel_statement`.
  Recording it for the 139 settled mirrors that lack one is the single cheapest
  way to sharpen this measurement, and it needs no proof work.
- Neither count is a ratchet today and neither should become one without a
  further decision — the classifier cannot tell a safe elision (`Monotone`) from
  a thin one (`Set.Ioi`), and a ratchet would imply it can.
