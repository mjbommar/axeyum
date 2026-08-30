# 383 — nursery draw 8

<!-- plan-section: lane-status -->

**Status: DONE — draw 8 is DECLINED, for a reason draw 7's handoff could not
have measured.**
[`check-dispatchable-frontier.py`](../../../scripts/check-dispatchable-frontier.py)
stays RED at **1 dispatchable against a floor of 10**, and no refill can clear
it until **two** constructions land.

Decision record:
[ADR-0762](../../research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md).
Measurements and reproducible probes:
[`../notes/383-nursery-draw-8.md`](../notes/383-nursery-draw-8.md).

Nothing was written. `FAMILY_MODULES`, `FAMILY_ROUTES`, both manifests, the
statable vocabulary, the environment snapshot and the headroom file are
byte-identical to the merge-base; no row moved partition; no attestation count
was raised; no held-out row was touched.

## Draw 7's prediction: half right, and wrong by a whole constant

**Right.** The un-owned floor is down to seven modules — exactly the four draw 7
took, removed — and **not one is held-out-safe**. Each is adjacent to a
published development or train family, or R9-contaminated, or both. Dist is
unchanged at 2/10. Re-derived, not inherited.

**Wrong.** "One more constant" opens nothing. Enumerating all subsets of size
4, 5 and 6 with R5's two-family minimum and every cycle position ≡ 0 mod 3
required to be held-out-safe:

    no new constant                     LAWFUL family sets: 0
    with ONLY Nat.nthRoot declared      LAWFUL family sets: 0
    with ONLY NatCast.natCast declared  LAWFUL family sets: 0
    with Nat.nthRoot AND Squarefree     LAWFUL family sets: 10

Draw 7 could spend one constant because `Mathlib.Data.Nat.Nth` was banked and
clean. It spent Nth too, so the held-out-safe set is **empty rather than one
short**, and R5 is hard-coded at two.

## Both screens, for every candidate

| candidate constant | opens | pool | screen 1 (R9, exact name) | screen 2 (namespace sweep) | closed-eval spent | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | **0/10** | **0** declarations | 0 | **clean — the one candidate** |
| `Squarefree` | `Mathlib.Data.Nat.Squarefree` | 11 | **0/10** | **0** declarations | 0 | judged unsafe on adjacency |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | 0/10 | 0 | 0 | **rejected — omega vocabulary** |
| `Nat.centralBinom` | `…Choose.Central` | 14 | 0/10 | — | **1** | not safe — natural-binomial development |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | 0/10 | — | 0 | not safe — natural-bitwise development |

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
