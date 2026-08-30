# 353 — nursery draw 7: every measurement, and how to re-run it

Detail behind [`../status/353-nursery-draw-7.md`](../status/353-nursery-draw-7.md)
and [ADR-0654](../../research/09-decisions/adr-0654-draw-7-is-authored-and-the-lawful-family-set-was-forced-not-chosen.md).

Nothing here is carried from ADR-0645, ADR-0653 or the draw-6b notes. Every
number was re-derived on this tree and several differ from theirs — the
environment grew 2,374 → 2,383 and the dispatchable count **fell 6 → 4**
between the brief for this lane and the lane's own first measurement.

## Probe 1 — the ready set, from the generator's own screens

Unchanged from [`351-nursery-draw-6b.md`](351-nursery-draw-6b.md); the generator
is authoritative because the generator is what draws. `propose-nursery-refill.py`
applies different screens and is not used for any number here.

```python
import importlib.util, json, pathlib
from collections import defaultdict

spec = importlib.util.spec_from_file_location(
    "refill", pathlib.Path("scripts/gen-autogenesis-nursery-refill.py").resolve())
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)

env       = set(R.load_json(R.ENV_SNAPSHOT)["declarations"])
inventory = R.read_inventory()
catalog   = R.load_json(R.CATALOG)
registry  = R.load_json(R.REGISTRY)["constructions"]
facts     = {}
for p in sorted(R.FACTS.glob("*.json")):
    f = json.loads(p.read_text()); facts[f["id"]] = f
vocabulary = R.read_vocabulary(env, inventory, catalog, facts)   # ADR-0652: read, never write
adm        = R.admissible(env, vocabulary)
catalogued = {r["source_name"] for r in catalog["facts"] if r["kind"] == "external-source"}
owned      = {m: fam for fam, ms in R.FAMILY_MODULES.items() for m in ms}

per_module = defaultdict(list)
for name in sorted(inventory):
    rec = inventory[name]
    if name in catalogued or R.HYGIENE.search(name):
        continue
    constants = set(R.CONST_RE.findall(rec["type_repr"]))
    if constants - adm or constants & R.HELD_OUT_CONSTRUCTIONS:
        continue
    if R.blockers_for(rec["type"], registry):
        continue
    per_module[rec["module"]].append(name)

for m, rows in sorted(per_module.items(), key=lambda kv: -len(kv[1])):
    if m in owned or len(rows) < R.PER_FAMILY:
        continue
    bad = [r for r in rows[:R.PER_FAMILY] if r in env]      # the R9 screen
    print(f"{len(rows):4d}  R9 {len(bad)}/{R.PER_FAMILY}  {m}  {bad}")
```

Result on this tree — `env=2383`, `admissible=2455`, `inventory=9729`:

      33  R9 0/10  Init.Data.Nat.Bitwise.Lemmas
      29  R9 0/10  Mathlib.Data.Nat.Prime.Basic
      29  R9 0/10  Mathlib.Data.Nat.Prime.Defs
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic     ['Nat.ascFactorial_succ']
      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic
      18  R9 2/10  Mathlib.Data.Nat.Dist   ['Nat.dist_comm', 'Nat.dist_self']
      13  R9 0/10  Mathlib.NumberTheory.Fermat
      11  R9 0/10  Mathlib.Data.Nat.Nth
      10  R9 1/10  Mathlib.Data.Int.GCD                 ['Nat.gcd_eq_gcd_ab']

Positive control printed in the same run — the largest **owned** modules, so a
run in which every screen misfired cannot look like a run that found nothing:
`Init.Data.Int.Order` 303, `Init.Data.Nat.Lemmas` 212,
`Init.Data.Int.DivMod.Lemmas` 196, `Init.Data.Nat.Basic` 189.

Dist is contaminated exactly as ADR-0653 measured, unchanged at R9 2/10.

## Probe 2 — is the family set forced?

The interesting question is not "which set is good" but "how many sets are
lawful". Lawful means: every cycle position ≡ 0 mod 3 is held-out-safe, and
R5's two-held-out-family minimum holds.

Held-out-safe = R9-clean in the first ten **and** no published v1 family over
the same mathematics. The v1 partitions that decide the second half:

    development  natural-binomial, natural-bitwise, natural-gcd,
                 natural-logarithm, natural-modular-equivalence, natural-primes
    train        integer-fibonacci, integer-gcd, integer-modular-equivalence,
                 natural-factorial, natural-fibonacci
    held-out     natural-square-root

So of the eleven ready modules, nine are adjacent to a published family and one
(Dist) is R9-contaminated. **Two qualify.** Enumerating all subsets:

    held-out-safe modules (2): ['Mathlib.Data.Nat.Nth', 'Mathlib.NumberTheory.Fermat']
    LAWFUL family sets found: 1
        Mathlib.Data.Nat.Nth            held-out
        Mathlib.Data.Nat.Prime.Basic    development
        Mathlib.Data.Nat.Prime.Defs     train
        Mathlib.NumberTheory.Fermat     held-out

Why, without the enumeration: R5 forces `ceil(n/3) = 2`, so `n ∈ {4,5,6}`;
Fermat sorts last of all eleven so it sits at index `n-1`, which must be 3;
hence `n = 4` and Nth is index 0; and only the two Prime modules sort strictly
between them.

This is also why **Dist cannot be taken as development or train** in this draw,
which ADR-0653's closing recommendation asks for. Dist sorts *before* Nth, so
any set containing it either puts Dist at index 0 (held-out, R9 refuses) or
pushes Fermat off index 3.

## Probe 3 — the real `select` and `guard`, in memory

`R.FAMILY_MODULES` / `R.FAMILY_ROUTES` mutated in memory, then `R.select(...)`
and `R.guard(entries, R.load_json(R.AUTOGEN / "nursery-v1.json"), env,
R.surface_validation(entries, None))`. Both are pure; nothing was written.

    === mechanical partition assignment for the NEW families ===
      Mathlib.Data.Nat.Nth            natural-nth-selector             held-out
      Mathlib.Data.Nat.Prime.Basic    natural-prime-arithmetic         development
      Mathlib.Data.Nat.Prime.Defs     natural-prime-characterizations  train
      Mathlib.NumberTheory.Fermat     fermat-numbers                   held-out

    select -> 300 entries
    GUARD PASSED -- 300 entries, 120 held-out

The dry run was done **before** any file was edited. R1..R10 judged the draw
rather than the lane arguing about them.

## Both screens, for each held-out family

R9 is a name screen and draw 5 established that a name screen is structurally
blind to a proposition proved under a different name
(`F:ml430-nat-dvd-mul-right` satisfied by a declaration named `Nat.dvd_mul`).
So a second screen is run: a namespace sweep of the environment for every
declaration mentioning the family's operator.

    fermat-numbers        screen 1: 0/10   screen 2: 1 decl  -- Nat.fermatNumber
    natural-nth-selector  screen 1: 0/10   screen 2: 2 decls -- Nat.nth, Nat.nthAux

    positive controls, same run:
      Nat.dist     8   (Nat.dist, dist_comm, dist_eq_sub_of_le,
                        dist_eq_sub_of_le_right, dist_self, dist_succ_succ,
                        dist_zero_left, dist_zero_right)
      Nat.gcd     17
      /[Pp]rime/  65
      /dist/i     40

The Dist control is the one that matters: the same sweep over a family we *did*
prove into returns eight, so a sweep returning one is a clean family rather
than a misaimed screen.

**Recorded as a limitation, unchanged from draw 6b:** the environment snapshot
carries names only (`values_indexed=false`), so a true *type* screen cannot be
run from it, and `prelude_theorem_inventory --release` needs a cold kernel
build this lane did not pay for (no prebuilt binary exists under
`target/release/examples/`). A row proved under a wholly unrelated name would
be caught by neither screen run here.

## ADR-0653's construction-only rule is now measurable

ADR-0653 established: *a lane sent to unblock a held-out family declares the
CONSTRUCTION and nothing else.* The namespace sweep is the test of compliance,
and both unblocking lanes passed it — `Nat.fermatNumber` alone, `Nat.nth` plus
its auxiliary. The `dist` lane's eight is what non-compliance looks like.

## Generator yield per family, after the generator's own filters

| module | probe rows | drawn | R9 first-10 | partition |
| --- | --- | --- | --- | --- |
| `Mathlib.Data.Nat.Nth` | 11 | 10 | 0/10 | held-out |
| `Mathlib.NumberTheory.Fermat` | 13 | 10 | 0/10 | held-out |
| `Mathlib.Data.Nat.Prime.Basic` | 29 | 10 | 0/10 | development |
| `Mathlib.Data.Nat.Prime.Defs` | 29 | 10 | 0/10 | train |

The three known proposer/generator divergences still fire —
`HELD_OUT_CONSTRUCTIONS = {Nat.log, Nat.clog, Nat.log2, Nat.sqrt}` collapses
`Mathlib.Data.Nat.Log` and `Mathlib.Data.Nat.Sqrt` to zero.

## The stated limitation of this draw

Two of `fermat-numbers`' ten blind rows mention `Nat.Prime`:

    Nat.fermat_primeFactors_one_lt
    Nat.pow_of_pow_add_prime

and this same draw dispatches twenty prime rows. That is shared **vocabulary**,
not a shared statement — neither name appears in either Prime pool, checked by
listing both pools — and a blind family must be allowed to use developed tools
or nothing could ever be held out. Recorded because it is the nearest thing to
an adjacency here, and because the next lane should know it was judged rather
than missed.

## Gates, and two that were already red on `main`

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, 4 dispatchable, floor 10 | **exit 0, 24** |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1107 settled=0 references=0 PASS` | `held_out=136 … settled=0 references=0 PASS` |
| `gen-autogenesis-nursery-refill.py --check` | **exit 1, stale before this lane** | exit 0 |
| `gen-autogenesis-statable-vocabulary.py` | `rows=176 bridge=72 PASS` | same, file byte-identical |
| `check-generated-artifact-ownership.py` | `artifacts=1 producers_run=5 fails=0 PASS` | same |
| `validate-facts.py` | — | 2,262 facts, 0 errors |
| `check-draw7-frozen-families.py` | — | `frozen=26 moved=0 new=4 control=FIRES PASS` |

Final generator line:

    AUTOGENESIS_NURSERY_REFILL_OK|entries=300|settled_mirrors_admitted=176
      |bridge=72|env=2383|development=100|held-out=120|train=80|combined=514
      |attested=411|unattested=103

Attested is **unchanged at 411**; unattested 63 → 103, which is the 40 new rows
arriving unattested exactly as ADR-0616 requires.

### The refill `--check` was red at the merge-base

Established rather than assumed, because attributing a pre-existing red to your
own diff is how a lane wastes an afternoon:

    git show HEAD:scripts/gen-autogenesis-nursery-refill.py > scripts/zz-tmp.py
    python3 scripts/zz-tmp.py --check     # exit 1, same staleness
    python3 scripts/zz-tmp.py             # produced exactly the committed diff

(The temporary copy must live under `scripts/` — the generator resolves `ROOT`
as `parents[1]` of its own path.) The cause is benign: `Nat.log2` landed on
main, so two rows moved from `not-statable-here` to `held-out-construction`.
Committed on its own in `635bc8576`.

### `check-control-registration.sh` is red at the merge-base

Two hyphenated Python files under `scripts/tests/` are unreachable both by the
`test_*.py` discovery glob and by `python3 -m unittest`:
`check-countrange-bijection-numerics.py` and
`check-totient-mul-coprime-numerics.py`. Left alone — not this lane's — but
they are two controls that cannot run.

This lane's own `check-draw7-frozen-families.py` first tripped the same rule
and was moved from `scripts/tests/` to `scripts/`: it is a gate invoked by
path, not a unittest control.

## `check-fast.sh`, baselined as a SET comparison

A raw failure count from one tree says nothing — this gate fails 27 steps at
the merge-base. So both runs were captured and their FAILED blocks compared as
sets, with a control that refuses an empty parse:

```sh
W=/data0/axeyum/scratch/wt-nursery-draw-7-baseline
git worktree add --detach "$W" 4cd995620
bash scripts/check-fast.sh > after.txt 2>&1                  # this tree
cd "$W" && bash scripts/check-fast.sh > before.txt 2>&1       # merge-base
```

    baseline (merge-base 4cd995620) failures = 27
    this tree failures                       = 25

    FIXED by this lane (2):
      + autogenesis-nursery-refill
      + dispatchable-frontier
    NEW failures introduced by this lane (0):
      (none)

### The three failures this lane did introduce, and how they were closed

The first pass showed 28. Comparing sets rather than counts named them
immediately — a count alone would have said "one worse" and hidden that two
were fixed and three were new.

1. **`propose-nursery-refill` and its controls.** The proposer refused with
   `R2 stale-snapshot` on `drawn_modules` and `used_source_names`, plus
   `R4 module-already-drawn` naming all four modules draw 7 took.
   `refill-headroom-v1.json` is the proposer's own snapshot and goes stale by
   construction when a draw lands; `--remeasure` is its documented update path.
   After it: already-drawn 260 → 300, survivors 2,289 → 2,249, ready families
   18 → 14, and the four drawn modules correctly leave the ready list.
   The control `remeasure-reproduces-the-committed-snapshot` additionally
   requires the snapshot to be **committed**, so leaving it dirty fails too.
2. **`autogenesis-holdout-isolation-tests`** pins `held_out=116` and the draw
   raises it to 136. Moved to the value the checker reports, not to 116+20 by
   arithmetic: the composition is 16 in v1 + 120 in the extension, and the
   generator's own line says `held-out=120`.

Neither is a defect in the draw; both are the maintenance a draw requires, and
neither would have been found by reading the diff.

## The frozen-families checker, and proof it can fail

`scripts/check-draw7-frozen-families.py` compares each preregistered family's
partition before and after, reading the "before" from git rather than from a
literal. It carries its own negative control — it moves one frozen family and
requires the comparison to notice — so a bug that empties the "before" set
cannot report PASS.

Mutation-verified rather than claimed:

    # compare() replaced with one that always returns []
    CONTROL FAILED: moving 'descent-and-well-ordering' was not detected
    exit 1

Restored, it prints `DRAW7_FROZEN|frozen=26|moved=0|new=4|control=FIRES|verdict=PASS`.

## What draw 8 needs

Held-out supply is exhausted again — every remaining un-owned module at the
floor is adjacent to a published v1 family, and Dist is permanently
R9-contaminated for held-out. One more constant, declared **construction-only**:

| declare | opens | rows | note |
| --- | --- | --- | --- |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | judge `Nat.ToInt.*` against `HYGIENE` first — it may be `omega` certificate vocabulary |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | a genuine well-founded construction |

`Mathlib.Data.Nat.Dist`'s 18 rows remain real supply for development or train
in a draw whose held-out slots come from elsewhere and whose cycle positions
allow it.
