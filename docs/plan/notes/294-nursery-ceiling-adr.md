# Notes: 294-nursery-ceiling-adr

Detail moved out of [`../status/294-nursery-ceiling-adr.md`](../status/294-nursery-ceiling-adr.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**So 300 is the upper end of a design-time sizing envelope.** In every consumer
the **floor** is what does work:
`docs/autogenesis/11-nursery-foundation-result.md` names *"the 100--300
population floor"* first among nine `ready=false` blockers. The maximum had
never rejected anything until today.

**And it never governed the sum.** `check-autogenesis-nursery.py` sets
`NURSERY = artifacts/autogenesis/nursery-v1.json` and computes its `evaluation`
list from that manifest's own entries -- so `100..300` is a **per-manifest**
bound on v1's 214. R3 applied it to `V1_EVALUATION_ENTRIES + len(entries)`
across two manifests. Nothing required that reading, and it is the reading that
made a second draw arithmetically impossible.

## The two blockers nobody had measured

Both were live on `main`, and neither is arithmetic.

**1. Fact clobber.** `gen-autogenesis-nursery-refill.py --check` was already
red:

```
autogenesis-nursery-refill: 39 generated file(s) are stale, first
  artifacts/facts/F-ml430-int-add-le-add-a76ad5ce.json; regenerate without --check
```

39 is exactly the number of draw-1 mirrors lanes closed today. The generator
rebuilt every fact file for every entry, so **its own printed advice would have
overwritten 39 `proved` facts with fresh `open` stubs**, discarding evidence
rows and status flips from five lanes.

**2. Silent repartition.** `assign_partitions()` derived every family's
partition from one cycle over the whole of `FAMILY_MODULES`, and the generator
never read its own prior output. Simulated by adding four plausible new
families to draw 1's eight:

| family | draw 1 | after adding 4 |
| --- | --- | --- |
| integer-order | development | train |
| natural-division | **train** | **held-out** |
| natural-divisibility | held-out | development |
| natural-lcm | development | train |
| integer-parity | train | development |
| natural-parity | held-out | train |
| natural-totient | development | train |

**Seven of eight move**, including `natural-division` (8 of its 10 mirrors
`proved`) into held-out -- a blind population manufactured from published
answers. Neither existing guard sees it: **R6** re-derives the assignment from
the same function the emitter used, so both agree on the new wrong answer, and
**R1** only forbids a family crossing partitions *within* one manifest.

## What held-out is worth, quantitatively

67 rows / 5 families / **16 distinct `<family>:<statement-shape>` split keys**
before the draw. But the number that decides sizing is the **attrition**: v1
froze with four held-out families and **two were amended away within seven
days** (ADR-0542: `natural-gcd` 08-22, `natural-binomial` 08-25). Neither loss
came from dispatching at a held-out row -- one was an operation registered
against one, the other was **ordinary unrelated development in `choose.rs`**
that had already proved 5 of 20 rows.

So the blind population decays at roughly **half its families per week, driven
by the development happening beside it.** The right target is therefore not a
row count but **replenishment at or above attrition, in families not under
concurrent development** -- and screening every held-out row's `source_name`
against the environment snapshot (2,207 declarations; controls `Nat.add`
present, `Bogus.zzz` absent) shows the second half was not being met:

| family | already-declared here | partition |
| --- | --- | --- |
| natural-logarithm | 0/21 | held-out (v1) |
| natural-square-root | 0/16 | held-out (v1) |
| integer-division | 0/10 | held-out (v2) |
| **natural-divisibility** | **4/10** | held-out (v2) |
| natural-parity | 0/10 | held-out (v2) |

`Nat.dvd_add`, `Nat.dvd_add_iff_right`, `Nat.dvd_antisymm`, `Nat.dvd_mod_iff` --
preregistered blind **today**, against a snapshot the generator itself loads.
The `natural-binomial` signature in a family six hours old.

## Whether the 40-row atom is the thing to change -- yes, in the other direction

A minimum-compliant draw assigns held-out, development, train, held-out: **20
held-out, 10 development, 10 train, so 20 dispatchable rows.** Against 60
closures per day that is about **eight hours of queue**; the 80-row draw yielded
50 dispatchable and its first 39 went in under two hours. **40 rows is roughly
one working session, not a coarse atom.** Shrinking `PER_FAMILY` is the wrong
direction on every axis.

**Variable yield.** `check-autogenesis-already-proved.py` measures 0 of the 11
prior dispatchable rows as already-proved, while `natural-lcm` was 5 of 10 free.
So N dispatchable rows buy between N/2 and N units of work, varying per family.
That argues for drawing **larger**, and for running the already-proved screen at
**dispatch** time (where a lane can act on it) rather than at draw time (where
nothing can be done). It is deliberately not a rejection screen -- a mirror we
close in an afternoon is a good row.

## The decision: ADR-0615

**Four changes; raising the ceiling is not one of them.**

1. The envelope is applied **per cohort**, as written. `EVALUATION_CEILING` (a
   sum bound) becomes `EXTENSION_CEILING = V1_EVALUATION_ENTRIES`, and v1's own
   range is now *asserted* rather than assumed. The rule: **the unattested
   cohort may never outweigh the attested one** -- ADR-0601's "scaffolding,
   never headline" made checkable. When it binds, the exit is re-attestation
   (`scripts/provision-lean-import-toolchain.sh`, ~5 min on this host), not
   another raise.
2. **A draw is incremental** (new guard **R8**): a preregistered family keeps
   its partition; the cycle runs over new families only. The manifest is trusted
   only against its own `extension_sha256`, so a hand-edit cannot become the
   freeze.
3. **A fact is emitted once and never rewritten.** Immutable in what
   preregistration binds (`id`, `title`, `formal.*`), mutable in what the ledger
   owns (`epistemic_status`, `evidence`, `depends_on`).
4. **A held-out candidate whose Mathlib name we already declare is refused**
   (new guard **R9**) -- the `natural-binomial` contamination caught before
   preregistration rather than three days after.

All three options the refusing lane named are **rejected**, with reasons, in the
ADR's *Alternatives*: raising 300 leaves the misattribution in place and both
data-destroying blockers untouched; extending an existing family buys
dispatchable rows with zero held-out breadth (the resource with the measured
attrition) and routes around R5 rather than reconsidering it; shrinking
`PER_FAMILY` is refuted by the consumption arithmetic above.

R4 and R5 are scoped to what a draw **adds** -- otherwise, once a second draw
exists, both would pass on draw-1's rows while the new draw contributed nothing.

## Draw 2

    Init.Data.Int.LemmasAux   integer-natcast                      held-out
    Init.Data.Nat.Coprime     natural-coprimality                  development
    Init.Data.Nat.Mod         natural-modulus                      train
    Mathlib.Data.Nat.Init     natural-induction-and-divisibility   held-out

22 modules carry >= 10 fully screened, unused candidates, so **supply was never
the constraint**. The constraint is one no existing rule states and R2 cannot
see: R2 forbids reusing a v1 family **name**, but a new family over the same
**mathematics** as an already-partitioned one leaks exactly as much. That rules
out `Mathlib.Data.Nat.ModEq` (68 candidates), `*.Gcd` (117 + 82), `*.Prime.*`
(29 + 29), `*.Factorial.*`, `*.Choose.*`, `*.Bitwise.*` -- each adjacent to a v1
family, and adjacency in the held-out -> development direction is the one that
costs.

The four chosen are the only remaining coherent modules whose **every adjacency
lands in the same partition**: coprimality beside v1 `natural-gcd` (both
development), modulus beside v2 `natural-division` (both train), the `dvd` rows
of `Mathlib.Data.Nat.Init` beside v2 `natural-divisibility` (both held-out), and
`integer-natcast` adjacent to nothing since no family covers the N -> Z cast.
What was chosen by judgement is the **set**; the assignment is still the
mechanical module-path cycle, and no target outcome was consulted -- only
already-published partitions, which is not an outcome.

**That the honest answer is four is itself the finding**: after two draws,
held-out-eligible supply is nearly exhausted at the **family** level while
2,700+ statable statements remain. The blind population's binding constraint is
adjacency, not rows.

## Checks (all foreground)

| check | result |
| --- | --- |
| `check-autogenesis-holdout-isolation.py` **BEFORE** | `held_out=67\|files_scanned=1105\|settled=0\|references=0\|PASS` |
| `check-autogenesis-holdout-isolation.py` **AFTER** | `held_out=87\|files_scanned=1105\|settled=0\|references=0\|PASS` |
| `check-dispatchable-frontier.py` | exit 0, **DISPATCHABLE 31** (was 11) |
| `--statable` on the 120-row manifest | 120 candidates, 0 blocked, 0 unstatable, exit 0 |
| `--screen` on the 120-row manifest | 120 candidates, 0 blocked, exit 0 |
| `validate-facts.py` | exit 0, 2074 facts, 0 errors |
| `check-fact-depends-derived.py` | exit 0, `missing_edges=0` (the 8 errors a sibling lane reported were repaired by `e7097524f`) |
| `create-autogenesis-chain-catalog.py --check` | exit 0, `edges=11638` |
| `scripts/tests/test-dispatchable-frontier.sh` | 25/25 |
| `scripts/tests/test_gen_autogenesis_nursery_refill.py` | 20/20, before and after the draw |
| mutation verification, 12 mutants | 12/12 killed, 11 by exactly one test |
| `check-control-registration.sh` | exit 0, `controls=25\|orphans=0\|py_controls=386\|py_orphans=0` |
| `gen-adr-index.py` / `--check` | `rows=609`, green |
| `check-links.sh` | all links ok |
| `gen-plan.py --check` | green after regeneration |
| `check-autogenesis-already-proved.py` | 31 screened, **0** name-matched -- the whole queue is real work |
| workspace cargo gate | **not run** -- no `crates/` file touched |

Mutation verification ran in a `copytree`'d scratch root with `__pycache__`
cleared between iterations, never a tracked source. The one mutant killed by two
tests is the never-overwrite guard, which is correct: rewriting the file is what
both the closed-fact revert and the drift report observe.

## Found and NOT repaired here (both owed elsewhere)

- **`F:ml430-nat-totient-eq-zero-3be161d6` had its preregistered
  `formal.statement` replaced** with the kernel's rendered `AxNat` type
  (`lean4-surface` -> `lean4`). 38 of the 39 closures preserved theirs, so this
  is an outlier rather than the mirror-flip pattern. Reported by name on stderr;
  `--check` treats it as fatal, a draw does not, because blocking every future
  draw on one lane's edit to one settled fact is the wrong trade. Nothing is
  written to it in either mode.
- **4 of 10 `natural-divisibility` held-out rows are not blind** (above). R9
  refuses this shape for new draws; the existing rows are **grandfathered**,
  because moving a preregistered partition is an ADR-0542 amendment with a
  recorded breach, never a regeneration. The amendment is owed to whoever owns
  that repair, and the brief's non-negotiable ("do NOT modify any existing
  entry's partition") is why it was not done here.
- `gen-autogenesis-nursery-refill.py --check` is a meaningful reproduction gate
  now, and is **deliberately still unregistered** in `check.sh` / the justfile:
  it is red on arrival from the drift above. Registering it is owed once that is
  resolved.

## Limitation carried forward

`HELD_OUT_CONSTRUCTIONS` still lists only the two surviving **v1** held-out
constructions (`Nat.log`/`clog`/`log2`/`sqrt`). Extending it to the v2 and draw-2
held-out constructions would exclude candidates from every other family in the
same run and break reproduction of the earlier draws, so it is not a change a
draw can make. R9 covers the sharper case (a name we already declare); the
looser case (a *construction* a held-out family owns) is not screened.

## Next

The queue is 31 and its whole content is unproved by the name-match proxy. Two
follow-ups, in order:

1. **The `natural-divisibility` amendment** -- an ADR-0542 breach record moving
   that family out of held-out, by whoever owns partition repairs. Until then,
   87 is an overstatement of blind breadth by up to 10 rows.
2. **Re-attest, don't re-raise.** The quoted cohort is 120 of 214. The way to
   grow past that is `scripts/provision-lean-import-toolchain.sh` plus a fresh
   `SURFACE_ATTESTATION_SHA256`, which merges the two cohorts into one attested
   population and removes the ceiling question entirely.
