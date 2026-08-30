# 383 — nursery draw 8: every measurement, and how to re-run it

Detail behind [`../status/383-nursery-draw-8.md`](../status/383-nursery-draw-8.md)
and [ADR-0762](../../research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md).

Nothing here is carried from ADR-0645, ADR-0653, ADR-0654 or ADR-0695. Every
number is re-derived on this tree, and **two of draw 7's carried numbers are
wrong on it** — see "where draw 7's prediction fails".

Nothing was written by this lane except documentation. `FAMILY_MODULES`,
`FAMILY_ROUTES`, both manifests, the statable vocabulary, the environment
snapshot and the headroom file are byte-identical to the merge-base.

Merge-base: `4227fa9bc` (local `main`, fast-forwarded in at lane start).

## Probe 1 — the ready set, from the generator's own screens

Unchanged in form from [`353-nursery-draw-7.md`](353-nursery-draw-7.md) and
[`351-nursery-draw-6b.md`](351-nursery-draw-6b.md). The generator is
authoritative because the generator is what draws; `propose-nursery-refill.py`
applies different screens and supplies no number here.

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

`env=2383`, `admissible=2455`, bridge (`adm − env`) `=72`, `inventory=9729`,
`owned_modules=43`, `PER_FAMILY=10`.

      33  R9 0/10  Init.Data.Nat.Bitwise.Lemmas       []
      26  R9 1/10  Mathlib.Data.Nat.Factorial.Basic   ['Nat.ascFactorial_succ']
      26  R9 0/10  Mathlib.Data.Nat.GCD.Basic         []
      21  R9 0/10  Batteries.Data.Nat.Bitwise.Lemmas  []
      18  R9 0/10  Mathlib.Data.Nat.Choose.Basic      []
      18  R9 2/10  Mathlib.Data.Nat.Dist              ['Nat.dist_comm', 'Nat.dist_self']
      10  R9 1/10  Mathlib.Data.Int.GCD               ['Nat.gcd_eq_gcd_ab']

**Seven** un-owned modules at the floor, against draw 7's eleven. The four
missing are exactly the four draw 7 took (`Mathlib.Data.Nat.Nth`, both Prime
modules, `Mathlib.NumberTheory.Fermat`) — the arithmetic closes, so the screens
are behaving.

Positive control in the same run, so a run in which every screen misfired could
not look like a run that found nothing — the largest **owned** modules:
`Init.Data.Int.Order` 303 → integer-order, `Init.Data.Nat.Lemmas` 212 →
natural-basic-arithmetic, `Init.Data.Int.DivMod.Lemmas` 196 → integer-division,
`Init.Data.Nat.Basic` 189, `Init.Data.Int.Lemmas` 128, `Init.Data.Int.Gcd` 117.

Un-owned sub-floor remainder: **51 modules, 134 rows** (286 un-owned ready rows
in total across all un-owned modules).

## Probe 2 — held-out-safe is ZERO, and the enumeration says so

Held-out-safe = R9-clean over the first `PER_FAMILY` **and** no published
development/train v1 family over the same mathematics. The second half is read
from the manifests, not asserted:

| module at the floor | rows | R9 | why it is not held-out-safe |
| --- | --- | --- | --- |
| `Init.Data.Nat.Bitwise.Lemmas` | 33 | 0/10 | `natural-bitwise` — **development**, 19 rows, and its `land_bit`/`lor_bit`/`ldiff_bit` mirrors are open targets lanes are working now |
| `Batteries.Data.Nat.Bitwise.Lemmas` | 21 | 0/10 | same family |
| `Mathlib.Data.Nat.GCD.Basic` | 26 | 0/10 | `natural-gcd` — **development**, 19 rows (also `natural-gcd-algorithm` train, `integer-gcd` train) |
| `Mathlib.Data.Nat.Choose.Basic` | 18 | 0/10 | `natural-binomial` — **development**, 20 rows; this is ADR-0542's own breach family |
| `Mathlib.Data.Nat.Factorial.Basic` | 26 | 1/10 | `natural-factorial` — train; **and** R9-contaminated |
| `Mathlib.Data.Int.GCD` | 10 | 1/10 | `integer-gcd` — train; **and** R9-contaminated |
| `Mathlib.Data.Nat.Dist` | 18 | 2/10 | R9-contaminated (ADR-0653), unchanged |

    held-out-SAFE modules = 0   []
    LAWFUL family sets with no new constant = 0

Lawful means: R5's two-held-out-family minimum holds, and every cycle position
≡ 0 mod 3 is held-out-safe (`assign_partitions` → `_with_cycle` walks
`PARTITION_CYCLE = ("held-out", "development", "train")` over the NEW families
sorted by `FAMILY_MODULES[f][0]`, restarting at `held-out` for each draw).
Enumerated over all subsets of size 4, 5 and 6; **zero survive**, and the reason
is not the ordering — it is that the held-out-safe set is empty, so no position
can be filled.

## Probe 3 — where draw 7's prediction fails

Draw 7's handoff:

> Draw 8 has no held-out supply again. Every remaining un-owned module at the
> floor is adjacent to a published v1 family, and Dist is permanently
> R9-contaminated for held-out. **One more constant**, declared
> construction-only: `NatCast.natCast` (14 rows …) or `Nat.nthRoot` (13 rows).

**The first half holds, exactly.** Seven un-owned modules at the floor, all
seven adjacent to a published v1 family or R9-contaminated, Dist unchanged at
2/10. Re-derived above rather than inherited.

**The second half is wrong, and it is wrong by a whole constant.** With either
named constant declared alone, the enumeration still yields **zero** lawful
family sets:

    with ONLY Nat.nthRoot declared      LAWFUL family sets: 0
    with ONLY NatCast.natCast declared  LAWFUL family sets: 0
    with Nat.nthRoot AND Squarefree     LAWFUL family sets: 10

The mechanism is R5 (`len(new_held_out) < 2` raises) meeting a held-out-safe set
that is now **empty rather than one short**. Draw 7 could spend one constant
because `Mathlib.Data.Nat.Nth` was already banked and clean; draw 7 then spent
Nth as well. Nothing is banked now.

ADR-0695 does not restore any: amending `fermat-numbers` out of held-out moves
it to *development*, which removes blind supply rather than adding drawable
held-out supply. Held-out went 136 → 116 and `Mathlib.NumberTheory.Fermat`
became an owned development module, so it is not in probe 1's un-owned list at
all.

## Probe 4 — every single-constant unblock, with both screens

For every inventory row whose ONLY obstruction is exactly one missing constant,
attribute it to that constant; then per constant, group by module and take the
resulting pool, its first ten, R9 over them, and ADR-0695's closed-evaluation
classifier over them (`scripts/check-holdout-closed-evaluation.py`'s own
`is_closed_evaluation`, whose self-test is run in the same command and passes).

The complete set of single-constant unblocks that bring an **un-owned** module
to the floor, with its adjacency judged:

| declare | opens | pool | R9 first-10 | closed-eval spent | verdict |
| --- | --- | --- | --- | --- | --- |
| `Nat.nthRoot` | `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas` | **13** | **0/10** | 0 | **held-out-safe** — `natural-square-root` is itself held-out, so this is blind beside blind |
| `Squarefree` | `Mathlib.Data.Nat.Squarefree` | **11** | **0/10** | 0 | judgment — see below |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | 0/10 | 0 | **reject** — omega vocabulary, see below |
| `Nat.centralBinom` | `Mathlib.Data.Nat.Choose.Central` | 14 | 0/10 | **1** (`Nat.centralBinom_zero : Nat.centralBinom 0 = 1`) | not safe — `natural-binomial` development |
| `Nat.div2` | `Mathlib.Data.Nat.Bits` | 14 | 0/10 | 0 | not safe — `natural-bitwise` development |
| `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 12 | 0/10 | 0 | not safe — `natural-bitwise` development |

Larger unblocks exist (`instSubNat` attributes 292 rows, `Int.lcm` 77,
`Int.bmod` 73) but every module they bring to the floor is already owned or
already adjacent; they are listed here so the next lane does not re-derive
their exclusion.

### Screen 2 — the namespace sweep, with its controls

R9 is a name screen and draw 5 established that a name screen is structurally
blind to a proposition proved under a different name
(`F:ml430-nat-dvd-mul-right` satisfied by a declaration named `Nat.dvd_mul`).
So the environment is swept for any declaration mentioning each candidate's
operator, and the controls are printed in the same run:

    Nat.nthRoot   (candidate)                     0   []
    Squarefree    (candidate)                     0   []
    NatCast/ToInt (candidate)                     0   []

    -- control ^Nat.dist  (the contaminated family)   8
    -- control ^Nat.gcd                              17
    -- control /[Pp]rime/                            65
    -- control ^Nat.sqrt                              4  ['Nat.sqrt','Nat.sqrtAux','Nat.sqrt_one','Nat.sqrt_zero']
    -- control /totient/i                            10

The Dist control is the one that matters: the same sweep over mathematics we
*did* prove returns eight, so a sweep returning zero is a clean namespace and
not a misaimed screen.

**Checked and clean, because it would have been a real breach:** `Nat.sqrt_zero`
and `Nat.sqrt_one` ARE declared here, and `natural-square-root` is a held-out
family. Its sixteen rows were listed and none is a mirror of either name (they
are `nat-sqrt-le-self`, `nat-le-sqrt`, `nat-sqrt-lt`, `nat-sqrt-eq-zero`, …).
No existing held-out row is affected, and nothing was touched.

## Probe 5 — `NatCast.natCast` is rejected, not deferred

Draw 7 flagged this to be judged against the generator's `HYGIENE` rule, which
already drops `^Int\.Linear\.` and `^Nat\.Linear\.` as `omega`'s internal
certificate vocabulary. The judgment is that `Nat.ToInt.*` is the same
category, and the statements are what decides it — all ten of the rows
`Init.Data.Int.OfNat` would draw are `Nat.ToInt.*` transfer lemmas:

    Nat.ToInt.add_congr   ∀ {a b : ℕ} {a' b' : ℤ}, ↑a = a' → ↑b = b' → ↑(a + b) = a' + b'
    Nat.ToInt.div_congr   ∀ {a b : ℕ} {a' b' : ℤ}, ↑a = a' → ↑b = b' → ↑(a / b) = a' / b'
    Nat.ToInt.le_eq       ∀ {a b : ℕ} {a' b' : ℤ}, ↑a = a' → ↑b = b' → (a ≤ b) = (a' ≤ b')
    Nat.ToInt.of_not_le   ∀ {a b : ℕ} {a' b' : ℤ}, ↑a = a' → ↑b = b' → ¬a ≤ b → b' + 1 ≤ a'
    Nat.ToInt.sub_congr   … ↑(a - b) = if b' + -1 * a' ≤ 0 then a' - b' else 0
    Nat.ToInt.toNat_nonneg ∀ (x : ℕ), -1 * ↑x ≤ 0

Two tells, and neither is the name. First, the whole namespace is one uniform
schema — "if `a` and `b` transfer, so does `a op b`" — which is a preprocessing
interface, not a body of mathematics. Second, the normal form is `omega`'s own:
`toNat_nonneg` states nonnegativity as `-1 * ↑x ≤ 0`, and `sub_congr` carries a
guard written `if b' + -1 * a' ≤ 0`. Nobody writes `-1 * x ≤ 0` for `0 ≤ x`
except a linear-arithmetic certificate producer. `Int.Linear.*` (341 inventory
rows) and `Nat.Linear.*` (96) are already dropped for exactly this.

So `Nat.ToInt.*` should join `HYGIENE`, and `NatCast.natCast` should not be
declared to open a nursery family. **This lane did not make that edit**, and
the reason is mechanical rather than cautious: adding a `HYGIENE` alternative
changes the generator's rejection counters, which means `nursery-v2-extension.json`
must be regenerated — and `gen-autogenesis-nursery-refill.py --check` is
**already red at the merge-base** for an unrelated reason (below), so a
regeneration here would sweep another lane's in-flight fact edits into this
lane's diff. It is recorded as a one-line change for whoever clears that red.

## Probe 6 — `Squarefree` is a real candidate and a genuine judgment call

Not named in draw 7's handoff. `Mathlib.Data.Nat.Squarefree` is blocked by one
missing constant, and would yield a pool of 11 at R9 0/10 with 0 closed-evaluation
rows in the first ten. The ten it would draw:

    Nat.Squarefree.ext_iff             Squarefree n → Squarefree m → (n = m ↔ ∀ p, Nat.Prime p → (p ∣ n ↔ p ∣ m))
    Nat.coprime_div_gcd_of_squarefree  Squarefree m → n ≠ 0 → (m / m.gcd n).Coprime n
    Nat.coprime_of_squarefree_mul      Squarefree (m * n) → m.Coprime n
    Nat.sq_mul_squarefree              ∀ n, ∃ a b, b ^ 2 * a = n ∧ Squarefree a
    Nat.sq_mul_squarefree_of_pos       0 < n → ∃ a b, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
    Nat.sq_mul_squarefree_of_pos'      0 < n → ∃ a b, (b+1) ^ 2 * (a+1) = n ∧ Squarefree (a+1)
    Nat.squarefree_iff_prime_squarefree  Squarefree n ↔ ∀ x, Nat.Prime x → ¬x * x ∣ n
    Nat.squarefree_mul                 m.Coprime n → (Squarefree (m*n) ↔ Squarefree m ∧ Squarefree n)
    Nat.squarefree_mul_iff             Squarefree (m*n) ↔ m.Coprime n ∧ Squarefree m ∧ Squarefree n
    Nat.squarefree_pow_iff             n ≠ 1 → k ≠ 0 → (Squarefree (n^k) ↔ Squarefree n ∧ k = 1)

`Nat.squarefree_two : Squarefree 2` **is** a closed-evaluation row — it sorts
eleventh, so `pool[:10]` misses it by one position. That is luck, not design,
and the next lane must re-check it: one more name landing before
`squarefree_two` alphabetically pulls it into the draw.

Two reasons this lane does **not** recommend it as a held-out family, both
measured rather than felt:

- **Eight of the ten mention `Nat.Prime`, `Nat.Coprime` or `Nat.gcd`**, and
  `natural-primes` (development, 21 rows), `natural-coprimality` (development,
  10) and `natural-gcd` (development, 19) all publish that mathematics.
  `Nat.squarefree_iff_prime_squarefree` does not merely *use* primes — it
  characterises the whole predicate in terms of them. Draw 7 permitted two of
  ten `fermat-numbers` rows to mention `Nat.Prime` as shared vocabulary; eight
  of ten, with the defining biconditional among them, is a different thing.
- **`Squarefree` is a generic Mathlib predicate**, `Squarefree (r : R) : Prop :=
  ∀ x, x * x ∣ r → IsUnit x` over a monoid. Declaring a constant under that
  bare name for a `Nat`-only specialisation is the `Nat.multichoose` hazard:
  our definitional body would not be Mathlib's `def`. It is defensible (`IsUnit`
  in ℕ is `= 1`) but it needs stating and screening, not assuming.

Recorded with the numbers so a later lane can overrule this judgment with
evidence rather than re-measure it.

## Probe 7 — the real `select` and `guard`, in memory, and what it reveals

`R.FAMILY_MODULES` / `R.FAMILY_ROUTES` mutated in memory and `R.admissible`
monkeypatched to add the simulated declaration; then `R.select(...)` and
`R.guard(entries, R.load_json(R.AUTOGEN / "nursery-v1.json"), env,
R.surface_validation(entries, None))`. Both are pure; **nothing was written**,
and the run asserts `FAMILY_MODULES restored unchanged: True` at the end.

    A  no new constant, four largest un-owned modules at the floor
       Init.Data.Nat.Bitwise.Lemmas      natural-bitwise-core      held-out
       Mathlib.Data.Nat.Dist             natural-distance          development
       Mathlib.Data.Nat.Factorial.Basic  natural-factorial-basic   train
       Mathlib.Data.Nat.GCD.Basic        natural-gcd-basic         held-out
       select -> 340 entries
       GUARD PASSED -- 340 entries, 120 held-out rows, 12 held-out families

    B  Nat.nthRoot only          GUARD PASSED (index 3 is GCD.Basic, published)
    C  Nat.nthRoot + Squarefree  GUARD PASSED
    D  control, three families   REFUSED: RefillError: R5 the refill adds 1
                                 held-out families; the blind population is
                                 already down to two capabilities

**Scenario A is the finding.** The generator's ten rules do not refuse a draw
that puts `Init.Data.Nat.Bitwise.Lemmas` and `Mathlib.Data.Nat.GCD.Basic` into
**held-out** — beside `natural-bitwise` and `natural-gcd`, both *development*,
both actively worked by lanes today. R9 is a name screen and both modules are
R9 0/10, so nothing fires. The rule that forbids it is stated in ADR-0653 prose
and enforced by no code:

> a family may be blind only if its mathematics is unpublished.

Scenario D is the control that keeps A from being a vacuous observation: the
same machinery, one family fewer, refuses with R5 naming the count. So `guard`
is live and discriminating — it simply has no adjacency rule to discriminate
with. This is the checker-that-cannot-fail shape one arrow upstream, and it is
the reason this decline is a decline rather than a draw: **a lane that trusts
`GUARD PASSED` can author the ADR-0542 breach on purpose and see green.**

## Gates — before and after are the same, because nothing was written

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, **1** dispatchable, floor 10 | exit 1, **1** dispatchable, floor 10 |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1109 settled=0 references=0 PASS` | identical |
| `check-draw7-frozen-families.py` | `frozen=30 moved=0 new=0 control=FIRES PASS` | identical |
| `gen-autogenesis-statable-vocabulary.py` | see below | untouched, byte-identical |
| attested / unattested | **411 / 103** | **411 / 103** |

The one dispatchable mirror is `F:ml430-nat-fermat-primefactors-one-lt-58343c6f`,
which exists only because ADR-0695 amended `fermat-numbers` out of held-out.

`FROZEN UNCHANGED: True` — 30 preregistered families, 0 moved, 0 new, and the
checker's own negative control fires (`control=FIRES`; it is mutation-verified
in draw 7's notes, and this lane re-ran it rather than citing that).

Attestation is read through the generator's own `V1_EVALUATION_ENTRIES +
len(validation["attested"])` and `unattested_cohort`, not counted by hand:
buckets are `attested 197`, `not_elaborable 3`, `unattested 100` over the
extension, giving 214 + 197 = **411** attested and **103** unattested. **No
attestation was raised**, and none could be: no row was added.

## `gen-autogenesis-nursery-refill.py --check` is RED at the merge-base

Established before attributing anything to this lane. This lane's only diff at
the time of the run was one new documentation file, so the generator, both
manifests and every artifact it reads are byte-identical to `main`:

    git diff --stat main HEAD   ->  docs/plan/status/383-nursery-draw-8.md | 24 +
    python3 scripts/gen-autogenesis-nursery-refill.py --check   ->  exit 1

    autogenesis-nursery-refill: 2 fact file(s) disagree with the preregistration;
    first: artifacts/facts/F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7.json
    has drifted from its preregistration in ['statement']; a preregistered
    statement may not be rewritten

The cause is in another lane's path, not this one's: the totient lane's
`105550cdf` ("flip … open -> proved") and the repair before it, `e79804fdd`
("restore two totient mirrors' Mathlib statements, overwritten by our own
kernel rendering"), are the two commits touching those fact files. Left alone
deliberately — `artifacts/facts/` is not this lane's path, and a fix here would
mix two lanes' work into one diff.

It matters for draw 8 beyond bookkeeping: **the refill generator cannot be run
to completion on this tree**, so even a lawful family set could not have been
emitted today without first clearing that red. The in-memory `select`/`guard`
probe above bypasses it because it calls the two pure functions directly.

## What draw 9 needs, precisely

Two constructions, each declared **construction-only** per ADR-0653 and
screened for closed-evaluation rows per ADR-0695 **before** the declaration
lands, not after:

| declare | opens | pool | R9 first-10 | screen 2 | closed-eval in first 10 |
| --- | --- | --- | --- | --- | --- |
| `Nat.nthRoot` | `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas` | 13 | **0/10** | **0** declarations | **0** |
| a second, still unidentified | — | ≥10 | must be 0/10 | must be 0 | must be 0 |

`Squarefree` (11 rows, 0/10, sweep 0) is the only measured second candidate and
this lane judges it unsafe on adjacency; the section above gives the numbers to
overrule that with.

### Two warnings for the `Nat.nthRoot` lane specifically

- **`HYGIENE` already drops the equation lemmas, but not their consequences.**
  `Nat.nthRoot.eq_1/2/3` and the whole `Nat.nthRoot.go.*` family are dropped
  (`\.eq_\d+$`, `\.eq_def$`). What survives into the drawn ten includes
  `Nat.nthRoot_zero_left : ∀ (a : ℕ), Nat.nthRoot 0 a = 1` and
  `Nat.nthRoot_one_right : n.nthRoot 1 = 1`. If the construction is declared
  with `nthRoot 0 x = 1` as its first recursion equation — as Mathlib's is —
  then `nthRoot_zero_left` is `Eq.refl` the moment `add_declaration` returns.
  **ADR-0695's classifier will not catch it**, because `is_closed_evaluation`
  requires a binder-free statement and this one has `∀ (a : ℕ)`. The spend is
  real; only the screen is blind to it. Choose the construction's equations, or
  accept and record the spend, but do not read `closed-eval 0` as "nothing is
  spent".
- **`Nat.nthRoot.lt_pow_go_succ_aux` is in the drawn ten** and is an internal
  auxiliary about Mathlib's Newton iteration
  (`b ≠ 0 → a < ((a / b^n + n*b)/(n+1) + 1)^(n+1)`) that mentions `nthRoot`
  nowhere. It is honest mathematics but it is implementation-specific to a
  construction we would be writing ourselves, so it may not be a fair blind
  target. Judge it before drawing, not after.

Positive controls in the same sweep, so a misfiring screen cannot look clean:
`^Nat.dist` **8** (the contaminated family), `^Nat.gcd` 17, `/[Pp]rime/` 65,
`^Nat.sqrt` 4, `/totient/i` 10.

`NatCast.natCast` is rejected rather than deferred: all fourteen rows are
`Nat.ToInt.*` transfer lemmas, and `toNat_nonneg` states nonnegativity as
`-1 * ↑x ≤ 0` — `Int.Linear.*`'s normal form, which `HYGIENE` already drops.
`Squarefree` is a third candidate draw 7's handoff never named; eight of its
ten rows mention `Nat.Prime` / `Nat.Coprime` / `Nat.gcd`, all development.

## The finding that outlives the decline: `guard` has no adjacency screen

The real rule is ADR-0653's — *a family may be blind only if its mathematics is
unpublished* — and no code enforces it. Running the real `select` and `guard`
in memory over a set that violates it:

    Init.Data.Nat.Bitwise.Lemmas      natural-bitwise-core      held-out
    Mathlib.Data.Nat.GCD.Basic        natural-gcd-basic         held-out
    -> GUARD PASSED -- 340 entries, 120 held-out rows, 12 held-out families

Both beside *development* families lanes work today; both R9 0/10, so nothing
fires. The control in the same run refuses (`R5 the refill adds 1 held-out
families`), so the machinery is live — it has no rule to fire. A lane trusting
`GUARD PASSED` can author the ADR-0542 breach on purpose and see green.

No screen is added, deliberately: the two obvious derivations are a
hand-maintained adjacency table (measures the maintainer's memory) and
"shares a constant" (far too coarse — `Nat.pow` is everywhere). A threshold
picked to make today's seven modules come out right is fitted to its own
answer. Logged with the reproducing probe instead.

## Gates — before and after are identical

| check | before | after |
| --- | --- | --- |
| `check-dispatchable-frontier.py` | exit 1, **1** dispatchable, floor 10 | exit 1, **1** dispatchable, floor 10 |
| `check-autogenesis-holdout-isolation.py` | `held_out=116 files_scanned=1109 settled=0 references=0 PASS` | identical |
| `check-draw7-frozen-families.py` | `frozen=30 moved=0 new=0 control=FIRES PASS` | identical |
| `gen-adr-index.py` | — | `rows=636 duplicate_numbers=0166,0167` (grandfathered only) |
| attested / unattested | **411 / 103** | **411 / 103** |

**FROZEN UNCHANGED: True** — 30 families, 0 moved, 0 new, negative control
fires. **No attestation raised**, and none could be: no row was added.
**No held-out row touched** — `Nat.sqrt_zero`/`Nat.sqrt_one` are declared here
and `natural-square-root` is held-out, so its sixteen rows were listed and
neither name mirrors any of them.

## Two gates already red at the merge-base

- **`gen-autogenesis-nursery-refill.py --check`**, on two totient fact files
  whose `statement` drifted from their preregistration (the totient lane's
  `105550cdf` and `e79804fdd`). `artifacts/facts/` is not this lane's path, so
  it was left alone — but it means **the refill generator cannot be run to
  completion on this tree**, so even a lawful family set could not have been
  emitted today.
- `check-control-registration.sh` remains red on the two hyphenated Python
  files under `scripts/tests/` that draw 7 recorded; unchanged, not this lane's.

## What draw 9 needs

**Two constructions, each declared construction-only per ADR-0653**, and each
screened for closed-evaluation rows per ADR-0695 *before* it lands.
`Nat.nthRoot` is the one clean candidate; the second is unidentified.

Warning ADR-0695's screen cannot give: `Nat.nthRoot_zero_left :
∀ (a : ℕ), Nat.nthRoot 0 a = 1` is in the drawn ten and is `Eq.refl` once the
construction is admitted, if declared with that as its first recursion
equation. `is_closed_evaluation` requires a **binder-free** statement, so it
reports 0 spent. The spend is real; only the screen is blind to it.

`Mathlib.Data.Nat.Dist`'s 18 rows are finally drawable as development or train:
with held-out at indices 0 and 3, Dist fits at 1 or 2. ADR-0653's closing
recommendation becomes executable at draw 9.

## `check-fast.sh` was NOT run, and that is a reported gap

This lane's entire diff against its merge-base is **five `.md` files, 915
insertions, zero deletions** — no Rust, no Python, no JSON, no artifact.
Byte-identity of every file the draw would have touched is asserted with
`git hash-object` against `main`, with a positive control that fires:

    IDENTICAL  artifacts/autogenesis/nursery-v1.json
    IDENTICAL  artifacts/autogenesis/nursery-v2-extension.json
    IDENTICAL  artifacts/autogenesis/mathlib-statable-vocabulary-v1.json
    IDENTICAL  artifacts/autogenesis/refill-headroom-v1.json
    IDENTICAL  scripts/gen-autogenesis-nursery-refill.py
    IDENTICAL  scripts/gen-autogenesis-statable-vocabulary.py
    DIFFERS    PLAN.md   <-- control fires

`check-links.sh` (all links ok) and `check-merge-hygiene.sh` — which covers
generated-file freshness, conflict markers and duplicate ADR numbers — are
both green, and those are the two gates a documentation-only diff can move.
Baselining `check-fast.sh` honestly needs both this tree and a merge-base
worktree, roughly twelve minutes, to re-measure the merge-base's own failures.
Recorded as **did not run** rather than skipped silently.

## Landed changes

| commit | what |
| --- | --- |
| `2acd25b3d` | early status stub, before any measurement |
| `2155404c6` | notes: seven probes, every number re-derived on this tree |
| `67bf67f9b` | ADR-0762 and the regenerated ADR index |
| `8994636c2` | regenerate PLAN.md |
| `a8d81257e` | merge `main` (the 382 safety-matrix lane landed mid-run); both conflicts were in GENERATED files and were resolved by regenerating, never by hand |
| _this_ | record the byte-identity control and the `check-fast.sh` gap |
