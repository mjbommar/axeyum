# The divergence registry was missing gaps its own tree already documented (2026-09-01)

**Measured, not estimated.** `artifacts/autogenesis/mirror-divergence-registry.json`
recorded four diverging constructions (`Nat.testBit`, `Nat.multichoose`,
`Nat.minFac`, `Nat.fastFib`) and blocked 11 `ml430` mirrors. Several `nat_prelude`
module docs had already reached, and written down, the same conclusion for other
constructions -- and none of those had reached the registry, so
`scripts/check-dispatchable-frontier.py` kept offering the affected mirrors as
dispatchable. A lane spent real effort reaching a refusal `squarefree.rs`'s
module doc states in its first forty lines.

## What was registered

Read against the pinned Mathlib source at commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`
(v4.30.0), not inferred from prose:

| construction | Mathlib shape | ours | class | rows blocked |
| --- | --- | --- | --- | --- |
| `Squarefree` | `Mathlib/Algebra/Squarefree/Basic.lean:41`, `def Squarefree [Monoid R] (r : R) : Prop := ∀ x, x * x ∣ r → IsUnit x` | `nat_prelude/squarefree.rs`: `Squarefree (n : Nat) : Bool`, an executable decision procedure, deliberately with no `Prop` bridge (ADR-0653) | codomain | 1 |
| `Nat.nth` | `Mathlib/Data/Nat/Nth.lean:60`, `noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ`, decided by `Classical.propDecidable` and `Nat.Subtype.orderIsoOfNat` | `nat_prelude/nth.rs`: `Nat.nth (dec : Nat → Bool) (bound n : Nat) : Nat`, a fuel-bounded search -- extra explicit `bound`, `Bool`-decidable predicate instead of an arbitrary `Prop` | definitional | 10 |
| `Nat.findGreatest` | `Mathlib/Order/Basic.lean` (re-exported through `Mathlib.Data.Nat.Find`), `def Nat.findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ` | `nat_prelude/find_greatest.rs`: same structural recursion, but `DecidablePred` is an explicit argument (no instance implicits here) and the branch is `Decidable.byCases` rather than `ite` | definitional | 10 |
| `Nat.floorRoot` | `Mathlib/Data/Nat/Factorization/Root.lean:54`, a product over `a.factorization : Finsupp` | `nat_prelude/factorization_root.rs`: a bounded downward `Nat.rec` search; this kernel has no `Finsupp`/`Finset` | definitional | 1 |
| `Nat.ceilRoot` | same file, the adjoint product over `Finsupp` | same module: a bounded upward search with fuel `a` | definitional | 9 |

Each row was cross-checked against the live fact ledger before being added:
every matched `ml430` mirror is `open` (none `proved`), so none of these
entries block a mirror this project has already closed (the G3 false-positive
control `check-dispatchable-frontier.py` runs on every entry).

`Squarefree`'s `codomain_witness_regex` is `Squarefree\s+\S+\s*→`, matched
against `F:ml430-nat-squarefree-ext-iff-7218327d`'s own pinned statement
(`∀ {n m : ℕ}, Squarefree n → Squarefree m → …`): a `Prop`-valued predicate is
the only thing that can appear immediately before `→` as an implication
antecedent, so this re-derives Mathlib's `Prop` codomain from the statement
itself rather than taking this row's claim on trust -- the same discipline
`Nat.testBit`'s row established for the reverse direction (`Bool`, evidenced
by a `= true/false` occurrence).

`Nat.nth`'s surface form is `"Nat.nth "` (trailing space), not the bare `nth`
or `Nat.nth`: `Nat.nth` is a literal substring of `Nat.nthRoot`, a completely
unrelated, already-honest mirror family (`F:ml430-nat-nthroot-zero-left-8560aafb`).
The bare-`nth` and un-spaced forms were tried first and both false-matched;
the space is load-bearing.

## What was found and NOT registered, and why

**`Max.max`/`Min.min` (`nat_prelude/minmax.rs`).** The module doc's own words
say a mirror "stated against Mathlib's REAL, typeclass-elaborated `Max.max`/
`Min.min` stays `open`" -- but `nat_prelude/minmax_lemmas.rs`, written after
it, is an explicit CORRECTION: read at the pinned Lean toolchain
(`Init/Prelude.lean:1311`, `Init/Data/Nat/Basic.lean:873`), Lean's `max`/`min`
at `Nat` *are* `if a ≤ b then b else a` / `if a ≤ b then a else b`, decided by
`Nat.decLe` -- the same function this prelude declares. Only the *delivery*
(a class projection at an instance) differs, which is elaboration, not
content, and the twelve `Init.Data.Nat.MinMax`/`Init.Data.Nat.Lemmas` mirrors
this unblocked are confirmed **already `proved`** in the ledger
(`F:ml430-nat-max-comm-a9a3642b` and eleven siblings). Registering this
construction would have failed the registry's own G3 guard immediately
(blocks a settled mirror) -- this is exactly the over-blocking direction
CLAUDE.md warns is the expensive error, caught here before it was written
rather than after.

**`Nat.Abundant`/`Nat.Deficient` (`nat_prelude/abundant_deficient.rs`).** The
module doc states a genuine divergence (our body is provably equivalent to,
not definitionally identical with, Mathlib's proper-divisor-sum phrasing;
ADR-1100). But **no `ml430` mirror fact currently exists for either name** --
`Mathlib.NumberTheory.FactorisationProperties` has not been drawn into the
nursery as an `ml430` population yet. Registering it now would fail the
registry's own G1 guard (a blocker matching nothing is stale) the instant the
gate ran. Left unregistered; note this here so whichever lane preregisters
that module's mirrors adds this row at the same time, rather than
re-discovering the divergence from scratch.

**UPDATE, same day, lane `nat-mirror-residue`.** The nursery draw ADR-1100
anticipated has landed: `python3 scripts/check-dispatchable-frontier.py` now
shows 9 open `ml430` mirrors whose pinned statement mentions `Abundant` or
`Deficient`
(`ml430-nat-abundant-iff-not-perfect-and-not-deficient-9763e268`,
`ml430-nat-abundant-mul-left-4de4fbe7`, `ml430-nat-abundant-of-dvd-686548ce`,
`ml430-nat-abundant-twelve-24ce1ba6`,
`ml430-nat-deficient-iff-not-abundant-and-not-perfect-18bbe30a`,
`ml430-nat-deficient-one-75f44529`, `ml430-nat-prime-deficient-89e0badf`,
`ml430-nat-prime-deficient-pow-9c5e1fef`,
`ml430-nat-prime-not-abundant-d2558ed6`), plus one more that mentions only
`Perfect` (`ml430-nat-prime-not-perfect-15c1235d`, `Nat.Prime.not_perfect`).
So this is now the case the paragraph above was written to catch. Three rows
were added to the registry: `Nat.Abundant`, `Nat.Deficient` (both re-reading
`Mathlib/NumberTheory/FactorisationProperties.lean` at the pinned commit —
`Abundant`/`Deficient n := n <> ∑ i ∈ n.properDivisors, i`, Finset sums, vs
ours `Lt (mul 2 n) (sumDivisors n)`/`Lt (sumDivisors n) (mul 2 n)`), and
`Nat.Perfect` (`nat_prelude/perfect.rs`, independently checked against
`Mathlib/NumberTheory/Divisors.lean`'s `def Perfect (n : ℕ) : Prop := ∑ i ∈
properDivisors n, i = n ∧ 0 < n` — the same Finset-sum divergence, one step
stronger: ours has no positivity conjunct, so `Perfect 0` is actually TRUE
here (`sumDivisors 0 = 0 = mul 2 0`) against Mathlib's FALSE, an
extensional as well as constructional difference). All three are `class:
definitional`, matching the `Nat.multichoose`/`Nat.nth` shape rather than
`codomain`, since the divergence lives in the body, not something a pinned
statement can witness via regex. `check-dispatchable-frontier.py`'s G1/G3
guards pass (each entry matches >=1 open mirror; none of the matched mirrors
is `proved`). Net effect: DISPATCHABLE 19 -> 10 (fermat-primefactors-one-lt
plus the 5 `log`/`clog` mirrors this lane closed some of — see this lane's
status note for the final count), `blocked` 12 -> 22.

**`Nat.lt_xor_cases` (`nat_prelude/xor_order.rs`) and the Stirling numbers
(`nat_prelude/stirling_lemmas.rs`).** Both module docs use "stays open"
language, but for the ordinary reason: the statement is expressible and true
here and simply unproved (`lt_xor_cases` needs a highest-differing-bit
`testBit` induction; Stirling's own doc says its ten mirrors "flip honestly").
Neither is a divergence. Not registered.

## The Fermat case is a different category

`F:ml430-nat-fermat-primefactors-one-lt-58343c6f`
(`∀ n p, 1 < n → Prime p → p ∣ fermatNumber n → ∃ k, p = k·2^(n+2) + 1`) is
blocked on missing INFRASTRUCTURE -- multiplicative order of 2 mod p,
Fermat's little theorem via Lagrange, a quadratic-residue argument for the
`n+2` exponent -- not on a divergent construction. The statement is
expressible and true in this kernel; the machinery to prove it has not been
built. Registering it in the divergence registry would be a false claim that
it is unreachable in principle, which it is not.

A mechanism for "blocked on infrastructure" does already exist in this
repository -- `scripts/gen-infrastructure-frontier.py` /
`scripts/check-infrastructure-frontier.py` (ADR-0845), producing the L2 phase
G3 infrastructure frontier from a hand-curated candidate list
(`scripts/lib/infrastructure_frontier.py::ROW_CANDIDATES`) re-validated
against the live declaration graph and graph-join artifacts at generation
time. Populating it correctly needs those artifacts
(`artifacts/graph-join/<population>.join.json`,
`artifacts/declaration-graph/graph/<population>.{rows,edges}.json`) and is a
generation pipeline, not a hand-edited row list -- out of this sweep's scope.
This document records the category so the next lane that reaches for that
mechanism does not have to re-derive why Fermat belongs there rather than in
the divergence registry.

## Frontier counts

Measured with `python3 scripts/check-dispatchable-frontier.py --json`
(default facts dir), registry before = `git show HEAD:artifacts/autogenesis/mirror-divergence-registry.json`
prior to this sweep, registry after = the 5 new rows added:

|  | before | after |
| --- | --- | --- |
| registered constructions | 4 | 9 |
| `structurally blocked` bucket | 11 | 12 |
| `DISPATCHABLE` bucket | 20 | 19 |
| `held-out` bucket | 185 | 185 (unchanged) |
| guard failures | none | none |

Only **one** mirror actually moved buckets:
`F:ml430-nat-squarefree-ext-iff-7218327d`, dispatchable -> blocked. That is
the live gap this sweep was sent to close.

The other four new constructions (`Nat.nth`, `Nat.findGreatest`,
`Nat.floorRoot`, `Nat.ceilRoot`) block **31** `ml430` mirrors that were
already `held-out` before this sweep -- `classify()` in
`check-dispatchable-frontier.py` checks the held-out/mutation partition
before it ever calls `blockers_for`, so a held-out mirror never appears in
the `blocked` bucket or changes the dispatchable count regardless of whether
a registry entry names it. Registering them anyway is not decorative: the
registry is also read by `--screen`/`--statable` to reject new candidates
before preregistration, by G3 as a false-positive control the moment any of
these mirrors is (mis)closed, and it means a future nursery re-partition
that would otherwise move one of these 31 into circulation instead lands it
directly in `blocked`, not `dispatchable`.

No mirror this project has already closed was affected: every one of the 42
mirrors matched by the 5 new entries is `open` (checked against the ledger
before writing any entry, and confirmed again by the gate's own G3 guard,
which reported no failures).
