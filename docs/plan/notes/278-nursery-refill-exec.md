# Notes: 278-nursery-refill-exec

Detail moved out of [`../status/278-nursery-refill-exec.md`](../status/278-nursery-refill-exec.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The bridge is derived, never asserted.** It is exactly
`{constants of settled ml430 mirrors} \ env`, so an entry exists only because
the ledger closed a mirror stated with it. Three things live there and none of
them needs a kernel counterpart:

- typeclass / notation elaboration -- `HAdd.hAdd`, `instHAdd`, `OfNat.ofNat`,
  `LE.le`, `instLENat`, `Dvd.dvd`, `Nat.cast`;
- Mathlib abbreviations that unfold into kernel vocabulary -- `Nat.Coprime`
  (`gcd a b = 1`), `Nat.ModEq` (`a % n = b % n`), `Nat.Prime`, `Even`, `Odd`,
  `ite`;
- order abbreviations that unfold the same way -- `Monotone`, `StrictMono`,
  `StrictMonoOn`, `Set.Ici`, `Symmetric`, `Function.swap`.

`Nat.fib_strictMonoOn` is the clearest witness: `proved`, with the kernel type
`2 <= a -> 2 <= b -> a < b -> fib a < fib b`. `Set.Ici 2` was unwound to two
explicit bounds and `StrictMonoOn` never needed to exist here.

### The surviving count

```
pinned theorem records                                    9,729
after dropping compiler-generated / hygienic names        9,134
already in the ml430 catalog                                202
unused supply                                             8,932
  of which STATABLE HERE                                  2,773   (31.0%)
```

**The screen is not vacuous: it rejects 6,159 of 8,932 (69.0%).** The constants
doing the rejecting are exactly the structures the previous lane predicted, now
counted rather than inferred:

```
  631  instSubNat        377  Finset            269  Nat.decLe
  582  List              369  Array             263  Set
  498  Std.PRange.*      363  MulZeroClass.*    258  instNatPowNat
  471  Lattice.*         340  AddMonoidWithOne  256  Ring.*
  428  Membership.mem    322  Nat.decLt         217  Ring
  381  LinearOrder       294  instPowNat        207  List.length
```

**And it is not a false-positive machine: all 156 settled `ml430` mirrors
pass.** That is the G3-shaped control -- run against the real population on
every invocation, not against a fixture.

After the divergence registry and the held-out-construction exclusion are
applied too, **2,399** survive, distributed over the modules the existing family
taxonomy already covers plus several it does not.

**Supply was never the bottleneck.** What follows is about the constraints on
preregistering, which are.

---

## (2) The refill

### Why this does NOT grow `nursery-v1.json`

`create-autogenesis-mathlib-fact-catalog.py` refuses to emit a catalog whose
generated Lean surface module differs from `SURFACE_ATTESTATION_SHA256` --
*"the generated surface module changed without a new real-Lean attestation"*.
That guard is correct and this lane did not defeat it. Attesting new statements
needs `import Mathlib` against a **built** Mathlib;
`/data0/axeyum/lean-import-toolchain/mathlib4` is at the pinned commit
`c5ea0035…` with **no `.lake/build`**, and building it is not a bounded step
inside one lane.

So the refill lands as an **additive** manifest,
`artifacts/autogenesis/nursery-v2-extension.json`, with its own explicitly
weaker grade:

| | v1 (214 rows) | v2 (80 rows) |
| --- | --- | --- |
| grade | real-Lean round trip | **quotation** |
| method | every statement re-elaborated as an axiom after `import Mathlib` and accepted | `formal.statement` is a **byte-identical quotation** of the pinned extractor's `type` field |
| binding | `generated_module_sha256` | per-row `source_statement_sha256` |
| limitation | -- | a pretty-printed type is not guaranteed to re-parse |

Nothing is transcribed, so there is no transcription to attest -- but the two
must never be reported as one attested population, and every generated fact says
so in its `notes`. `create-autogenesis-mathlib-nursery-split.py --check` stays
green (`evaluation=214`, `amendments=2`, digest unchanged) and **no v1 entry
moves partition**.

### What was preregistered

80 rows, 8 new families, 10 each. Every candidate passed **both** screens plus
one further exclusion before entering the manifest.

| family | partition | primary Mathlib module |
| --- | --- | --- |
| `integer-division` | **held-out** | `Init.Data.Int.DivMod.Lemmas` |
| `integer-order` | development | `Init.Data.Int.Order` |
| `natural-division` | train | `Init.Data.Nat.Div.Basic` |
| `natural-divisibility` | **held-out** | `Init.Data.Nat.Dvd` |
| `natural-lcm` | development | `Init.Data.Nat.Lcm` |
| `integer-parity` | train | `Mathlib.Algebra.Group.Int.Even` |
| `natural-parity` | **held-out** | `Mathlib.Algebra.Group.Nat.Even` |
| `natural-totient` | development | `Mathlib.Data.Nat.Totient` |

```
held-out     30      development  30      train  20
combined evaluation population   294  of the 300 ceiling
```

### How the partitions were assigned

`split_freeze: before-target-outcomes` is the hard part of a refill, and the
previous lane was right that it is a discipline question. This lane made it a
**mechanical** one instead, stated in code and re-derived by `--check`, so the
assignment cannot be hand-edited without editing a rule that is legible:

> New families are ordered by the **lexicographic path of their primary Mathlib
> defining module** -- a property of the external source, decided by Mathlib's
> own directory layout and not by anything we know about our capability.
> Walking that order, partitions are assigned by the repeating cycle
> **held-out, development, train**.

The cycle starts at held-out because the measured deficiency is held-out
breadth: of twelve v1 families exactly **two** were still open and blind
(`natural-logarithm`, `natural-square-root`), so the surviving evaluation
population tested two capabilities. It now tests five.

Guard **R6** re-derives every row's partition from that rule; **R5** refuses a
refill adding fewer than two held-out families; **R4** refuses one where nothing
is dispatchable; **R1** applies v1's three leakage rules (family, proof shape,
source group) to the new rows; **R2** refuses a family name that collides with a
v1 family; **R3** enforces the 300 ceiling.

### The exclusion the split key demands

A route for one member is evidence about its siblings, so a refill row over a
**held-out family's construction** would spend blind-evaluation value without
anyone touching a partition. `Nat.log`, `Nat.clog`, `Nat.log2` and `Nat.sqrt`
are excluded by construction, not by care.

### Holdout isolation, before and after

```
BEFORE  AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1103|settled=0|references=0|verdict=PASS
AFTER   AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

37 -> 67 is the 30 new held-out rows. v1's 37 are unchanged.

**The gate earned its keep immediately, against this lane.** The first draft of
`mathlib-statable-vocabulary-v1.json` keyed its rows by `fact_id`, and the check
went red with **35 held-out references** -- every held-out `natural-logarithm`
and `natural-square-root` row, named in a file that is not a population file.
The artifact is now keyed by **Mathlib `source_name`**, and the checker joins to
a fact through the catalog, which *is* a population file and may name them.

`check-autogenesis-holdout-isolation.py` itself had to change: it read
`nursery-v1.json` only, so the 30 new held-out rows would have been unprotected
while it printed PASS. It now requires **both** manifests and refuses a manifest
that contributes no held-out rows.

---

## (3) The gate

```
open ml430 mirrors: 138
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 50

OK -- the dispatchable set is non-empty and the divergence registry is
witnessed against the pinned statements.
```

**0 -> 50.** `check-dispatchable-frontier.py` now reads partitions from v1 *and*
the extension, both REQUIRED: skipping an unreadable manifest would reclassify
its held-out rows as dispatchable, which is a gate that hands a lane a blind
proposition.

---

## Guards added, and their controls

`scripts/tests/test-dispatchable-frontier.sh` went 12 -> **25 cases**, each
asserting both that its own guard fired and that no other did.

| guard | what it prevents |
| --- | --- |
| **S1** stale-environment-snapshot | count disagreeing with the list; a snapshot missing declarations every kernel has (rejects everything, *looks strict*); a snapshot containing a name no declaration can carry (**admits everything** -- the direction nobody notices) |
| **S2** unwitnessed-bridge-constant | a bridge entry no settled mirror witnesses; and one for a name the kernel *does* declare, which hides a rename instead of recording an elaboration |
| **S3** screen-rejects-a-settled-mirror | the false-positive control, against all 156 closed rows |
| **S4** vocabulary-status-drift | a row listed as settled that the ledger says is open (adding one promotes its constants into the bridge, so **S2 alone is satisfiable by assertion**); and a settled mirror *dropped* from the list, which narrows the population S3 runs over |
| **S5** unstatable-candidate | `--statable` rejects before preregistration |

Mutation-verified in a `copytree`'d scratch root (`scripts/`, `artifacts/`,
`docs/` -- G5 reads `recorded_in` paths, so the real-tree false-positive control
needs `docs/`): **11 mutants, every one killed by exactly one case.** Two of
them are not S-guards -- "every partition manifest is required" and "a candidate
must carry its constants" -- and both were added because the natural
implementation of each is to skip quietly.

Three more against `check-autogenesis-holdout-isolation.py`: reading only v1,
dropping the per-manifest held-out requirement, and dropping the extension from
`POPULATION_FILES`. All three killed; its suite went 15 -> **19 tests**.

**False-positive controls** (a gate that fires on healthy input is the same end
state as no gate): the healthy synthetic fixture, the real repository tree, a
clean `--screen` candidate set, a clean `--statable` candidate set, and
`--statable` over the **real** 80-row extension -- which means the preregistered
population is re-screened on every gate run, not only when it was written.

Registered in `scripts/check.sh` (`dispatchable-frontier-statable`) and the
`justfile`; `check-control-registration.sh` reports `controls=25|orphans=0`.

---

## Checks run (foreground)

| check | result |
| --- | --- |
| `scripts/tests/test-dispatchable-frontier.sh` | **25/25 pass** |
| mutation verification (copied tree, 11 mutants) | each killed by **exactly one** case |
| `python3 -m unittest scripts.tests.test_check_autogenesis_holdout_isolation` | 19/19 pass |
| mutation verification (copied tree, 3 mutants) | all killed |
| `scripts/check-dispatchable-frontier.py` | exit 0, **DISPATCHABLE 50** |
| `… --statable artifacts/autogenesis/nursery-v2-extension.json` | exit 0, 80 candidates, 0 blocked, 0 unstatable |
| `scripts/check-autogenesis-holdout-isolation.py` | PASS before (`held_out=37`) and after (`held_out=67`), `references=0` both |
| `python3 scripts/validate-facts.py` | exit 0, **0 errors**, 2,033 facts |
| `scripts/create-autogenesis-mathlib-nursery-split.py --check` | OK, `evaluation=214` unchanged, `amendments=2` |
| `scripts/check-autogenesis-holdout-contamination.py` | exit 0 |
| `scripts/check-control-registration.sh` | exit 0, 25 controls, 0 orphans |
| `python3 scripts/gen-plan.py --check` | regenerated |
| `scripts/check-autogenesis-nursery.py` | **exit 1 -- PRE-EXISTING on `main`**, verified by stashing this diff and re-running: `evaluation population shares a component with Autogenesis-1`. Not caused here and not repaired here. |
| workspace cargo gate | **not run** -- this lane touched no Rust |

---

## What this lane did NOT do, and what it costs

- **No real-Lean attestation.** The 80 new statements carry the quotation grade.
  Upgrading them needs a built Mathlib (`lake exe cache get` plus an
  `import Mathlib` elaboration); until then v1 and v2 are two populations with
  two grades and must be reported as such.
- **The `natural-logarithm` / `natural-square-root` held-out families are
  untouched**, deliberately: growing them would have been safe (it spends
  nothing) but it does not widen what the blind population *tests*, which was
  the measured deficiency.
- **`check-autogenesis-nursery.py` is still red.** It is red on `main` for a
  reason unrelated to this diff, and repairing it inside a large additive change
  would hide a pre-existing failure.
- **The environment snapshot is a point-in-time read.** It can only go stale in
  the fail-closed direction (a declaration that landed after it reads as
  absent), and S1 cannot detect that -- regenerate it with
  `gen-autogenesis-nursery-refill.py --snapshot-from <shape_search stdout>`
  before any future refill. This is the prebuilt-`shape_search` hazard moved
  into an artifact.

## Next

The queue holds 50 dispatchable rows across five families
(`integer-order` 10, `natural-lcm` 10, `natural-totient` 10,
`natural-division` 10, `integer-parity` 10). `natural-lcm` and
`natural-division` sit directly on constructions the kernel already has
(`Nat.lcm`, `Nat.div`, `Nat.mod` are all in the environment), so they are the
cheapest first draw.
