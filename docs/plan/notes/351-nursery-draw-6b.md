# 351 — nursery draw 6b: every measurement, and how to re-run it

Detail behind [`../status/351-nursery-draw-6b.md`](../status/351-nursery-draw-6b.md)
and [ADR-0653](../../research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md).

Nothing here is carried from ADR-0620 or ADR-0645. Every number was
re-derived on this tree, and several differ from theirs — the environment
grew from 2,207 declarations to 2,374 between the two runs, which moves the
drawable set, the ready-module count, and the R9 screen.

## Why a probe rather than the proposer

`propose-nursery-refill.py` and `gen-autogenesis-nursery-refill.py` apply
**different screens**, and the generator is the authoritative one because
the generator is what draws. On this run the proposer reports **17** ready
families and the generator yields **10**.

So every measurement below imports the generator and calls its own
functions. Reimplementing a screen is how the divergences got missed in the
first place.

## The probe

Reproducible from the repository root. It prints its own positive control —
the largest owned modules — so a run in which every screen misfired cannot
look like a run that found nothing.

```python
import importlib.util, json, pathlib
from collections import Counter, defaultdict

spec = importlib.util.spec_from_file_location(
    "refill", pathlib.Path("scripts/gen-autogenesis-nursery-refill.py").resolve())
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)

snapshot  = R.load_json(R.ENV_SNAPSHOT)
env       = set(snapshot["declarations"])
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

**Dry-run a candidate draw through the real guard** by mutating
`R.FAMILY_MODULES` / `R.FAMILY_ROUTES` in memory and calling
`R.select(...)` then `R.guard(entries, R.load_json(R.AUTOGEN /
"nursery-v1.json"), env, R.surface_validation(entries, None))`. Both are
pure; nothing is written, and R1..R10 judge the draw instead of you arguing
about them.

## Screens, both of them, for each candidate

R9 is a **name** screen. Draw 5 established that a name screen is
structurally blind to a proposition proved under a different name
(`F:ml430-nat-dvd-mul-right` satisfied by a declaration named
`Nat.dvd_mul`), so a **type** screen is also required.

`kernel-environment-snapshot-v1.json` carries names only — its own coverage
line says `values_indexed=false` — so a type screen cannot be run from it,
and the type-bearing route (`prelude_theorem_inventory --release`) needs a
cold kernel build this lane did not pay for. What was run instead, and it is
weaker in a stated direction: a **namespace sweep** of the environment for
every declaration whose name mentions the family's operator, which is what
catches a differently-named proof of the same proposition in practice.

    Nat.dist* — 8 env declarations:
      Nat.dist, Nat.dist_comm, Nat.dist_eq_sub_of_le,
      Nat.dist_eq_sub_of_le_right, Nat.dist_self, Nat.dist_succ_succ,
      Nat.dist_zero_left, Nat.dist_zero_right
    Nat.nth*  — 2 env declarations: Nat.nth, Nat.nthAux.  No Nat.nth_* lemma.
    positive controls: 40 env declarations match /dist/i (the wider sweep,
      catching Nat.mul_sub_left_distrib and friends); Nat.gcd* is 17.

The Dist sweep found the contamination the name screen also found, and found
two extra `Nat.dist_eq_sub_of_le*` lemmas that are not mirror rows. The Nth
sweep is clean by both screens. **Recorded as a limitation:** a Nth row
proved under a wholly unrelated name would not be caught by either screen
run here.

## Generator yield per family, after the generator's own filters

| module | proposer | generator | R9 first-10 | verdict |
| --- | --- | --- | --- | --- |
| `Mathlib.Data.Nat.Dist` | 18 | **18** | **2/10** | held-out REFUSED |
| `Mathlib.Data.Nat.Nth` | 11 | **11** | **0/10** | held-out safe |

The three known proposer/generator divergences all still fire.
`HELD_OUT_CONSTRUCTIONS = {Nat.log, Nat.clog, Nat.log2, Nat.sqrt}` collapses
`Mathlib.Data.Nat.Log` (36 → 0) and `Mathlib.Data.Nat.Sqrt` (24 → 0), which
is most of the 17 → 10 gap.

## The refusal, and the control that isolates it

    $ dry-run  natural-distance=Mathlib.Data.Nat.Dist
               natural-factorial-basic=Mathlib.Data.Nat.Factorial.Basic
               natural-gcd-basic=Mathlib.Data.Nat.GCD.Basic
               natural-nth-selector=Mathlib.Data.Nat.Nth

    natural-distance        held-out
    natural-factorial-basic development
    natural-gcd-basic       train
    natural-nth-selector    held-out

    GUARD REFUSED: R9 2 held-out candidate(s) already have a declaration of
    the same Mathlib name in the kernel environment, so they are not blind:
    [('natural-distance', 'Nat.dist_comm'), ('natural-distance', 'Nat.dist_self')]

Control — identical machinery, Dist moved off held-out by inserting a family
whose primary module sorts before it:

    GUARD PASSED -- 300 entries, 120 held-out

That control is **not a lawful draw** (`Mathlib.Data.Nat.Choose.Basic` sits
over `natural-binomial`, a development family — the natural-division
violation). It exists only to prove that R9-on-Dist is the sole mechanical
blocker, and that the rest of the draw is sound.

Note the partition cycle is mechanical over `FAMILY_MODULES[f][0]` sorted
lexicographically, starting at held-out. Dist and Nth alone put Dist at
held-out and Nth at **development**, which fails R5 for a different reason;
two fillers sorting between them are what place both at cycle positions
0 and 3.

## Gates

| check | result |
| --- | --- |
| `check-dispatchable-frontier.py` before | exit 1, `FAIL: G7 queue-below-floor: 6 dispatchable, floor 10` |
| `check-dispatchable-frontier.py` after | exit 1, identical — nothing drawn |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1107 settled=0 references=0 PASS` |
| `gen-autogenesis-nursery-refill.py --check` | `OK entries=260 bridge=72 env=2374 attested=411 unattested=63` |
| `gen-autogenesis-statable-vocabulary.py` | `rows=174 bridge=72 PASS` |
| `check-generated-artifact-ownership.py` | `artifacts=1 producers_run=5 fails=0 PASS` |
| FROZEN UNCHANGED | **True**, 26 frozen families, 0 moved; negative control FIRES |

The refill generator's `--check` is **green on this tree** — ADR-0645
recorded it RED, and ADR-0652 fixed the two-writers defect it named. The
generator now reads and cross-checks the vocabulary instead of silently
rewriting it, so authoring a draw no longer risks deleting
`bridge_provenance` and `row_digest`. Verified here rather than assumed:
`--check` green, the owner reports its own PASS, the ownership gate passes,
and the vocabulary file is byte-identical to the merge-base.

**A lane sent to unblock a held-out family declares the CONSTRUCTION and
nothing else.** Every mirror-named theorem it proves alongside subtracts a
row from the blind population it was sent to create. The `dist` lane did
good work by its own brief; the `nth` lane declared only the construction
and its auxiliary, and its family is the one that survived. Nobody had
stated the constraint.

Re-derived constant sweep, with the R9 screen ADR-0645's version lacked —
each opens a new un-owned module at the floor whose first ten are clean:

| declare | opens | rows | held-out-safe |
| --- | --- | --- | --- |
| `Nat.fermatNumber` | `Mathlib.NumberTheory.Fermat` | 13 | yes — no family names it |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | yes — beside held-out `integer-natcast` |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | yes — beside held-out `natural-square-root` |
| `Nat.centralBinom` | `…Choose.Central` | 14 | **no** — natural-binomial is development |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | **no** — natural-bitwise is development |

`Nat.fermatNumber` is cheapest (`2^(2^n)+1` over the existing `Nat.pow`; the
sweep confirms every other constant in all thirteen rows is already
admissible). **Draw 7 needs one more constant, not two** — `Nat.Nth` is
banked and clean — and `Mathlib.Data.Nat.Dist` should be drawn as
development or train, where its 18 rows are still real supply.

`check-dispatchable-frontier.py` stays RED at **6** against a floor of 10,
and **no draw can clear it**: R5 refuses any family addition that does not
add two held-out families. The other honest route is the eleven structurally
blocked mirrors, which is proof work.

Gates: holdout isolation `held_out=116 files_scanned=1107 settled=0
references=0 PASS` exit 0, unchanged; frontier exit 1 and byte-identical
before and after; refill `--check` green (`entries=260 bridge=72 env=2374
attested=411 unattested=63`, unchanged before and after); vocabulary owner
PASS; artifact-ownership gate PASS.

Detail, both screens, the probe and every command:
[`../notes/351-nursery-draw-6b.md`](../notes/351-nursery-draw-6b.md).
Decision: [ADR-0653](../../research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md).
