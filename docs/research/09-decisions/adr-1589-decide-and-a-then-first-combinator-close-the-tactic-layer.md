# ADR-1589: `decide` and a `Then`/`First` combinator close the tactic layer

Date: 2026-09-03
Status: Accepted
Lane: `tactic-combinator`

Index-summary: Three single-shot producers existed (`linarith`, `ring`,
`simp`); a real proof is rarely one tactic. This ADR adds the fourth and
cheapest producer, `decide` — close a CLOSED goal by a fuel-bounded `whnf`
walk, no search at all — and `crate::tactic`, a combinator over all four:
`Tactic::{Decide,Linarith,Ring,Simp,Then,First}`, `Then(Simp, X)` normalizing
a goal's two sides via one new exposed entry point
(`simp::nat::normalize`) and gluing `X`'s residue back with `Eq.rec`-based
transport generic in the predicate (`Eq`/`Nat.le`/`Nat.lt`), `First` trying a
list in order. Both add no trusted surface: every leaf still bottoms out at
`Kernel::add_declaration`. `decide` retired ten hand-written `def_eq`
evaluation checks (`nat_prelude::avg_pair_tests`) onto itself, catching a
real bug in its own value-recognition along the way (the kernel's compact
`Lit` numeral representation, not only `succ`/`zero` chains — found because
`Nat.pair`'s `Bool`-selected branch produces one and `Nat.avg`'s does not).
The combinator retired eight `nat_prelude` hand proofs whose shape is
rewrite-then-order or rewrite-then-ring, four of them a byte-identical
quadruplicate the file docs had already flagged as a known duplication.
Running total across the tactic layer: **62** hand proofs retired
(ADR-1576 15, ADR-1581 +5, ADR-1580 10, ADR-1582 +10, ADR-1586 14, this
lane 8), plus 10 test-mechanism conversions this lane does not count in
that ledger (they retire a *test's assertion*, not a *hand proof*).
`decide` costs 0.006–0.025 ms per closed term (no search); a representative
`Then(Simp, Linarith)` costs 1.1–1.3 ms, tracking `linarith`'s own measured
range — consistent with "the combinator's cost is the sum of what it
dispatches to", since `simp`'s one rewrite step here is negligible next to
`linarith`'s certificate search.
Index-status: Accepted

## Context

ADR-1576/1581 (`linarith`), ADR-1580/1582 (`ring`), and ADR-1586 (`simp`)
each landed a single-shot decision procedure that emits a kernel proof term
for one fragment. Every evaluation test this crate has ever written by hand
— every `_evaluates_correctly` in `nat_prelude`/`int_prelude` — is exactly
what the cheapest possible producer would do: reduce a closed term and build
`Eq.refl`. And Lean users do not write one tactic per goal; `simp; linarith`
or `ring_nf; omega` compositions are the normal shape of a real proof. This
lane's brief named both gaps directly: **(a)** `decide`, closing a closed
goal by kernel reduction, the cheapest producer of all; **(b)** a combinator
that runs `simp` to normal form on both sides of a goal and hands the
residue to `linarith` or `ring`, so a goal neither producer closes alone is
closed by the pair — unlocking the retirement queue ADR-1581's decline
histogram and the `simp` lane's own "both shapes" sites left behind.

## Decision

### 1. `decide` — the fourth producer, cheapest by construction

`crates/axeyum-lean-kernel/src/decide.rs`. Closes a **closed** (no free
variable) `Eq Nat`, `Eq Bool`, `Nat.le`, or `Nat.lt` goal: `whnf` both sides,
peel a `succ`/`zero` numeral chain (or the kernel's own compact `Lit`
representation — see below) up to `MAX_MAGNITUDE = 30` layers, and either
emit `Eq.refl` (comparing values) or a `le_step`-chain witness for `Nat.le`
(`Nat.le` here is the indexed inductive `le_refl : Le n n` /
`le_step : Le n m → Le n (succ m)` `nat_prelude::order` declares — `Lt a b`
is definitionally `Le (succ a) b`, so `<` reduces to the same construction).
No search at all: `Decline::{NotClosed, GoalNotAtomic, Undecidable}`, and
`Undecidable` covers both "exceeded the fuel bound" and "the two sides
genuinely disagree" — `decide` never claims a goal is false, matching every
other producer's decline discipline here.

**Two numeral representations, and the bug found retiring the tenth
test.** `Kernel::whnf` does not always land on a `succ`/`zero` chain: a term
built from `Bool`-selected arithmetic — `Nat.pair`'s
`if a < b then … else …` — reduces to `ExprNode::Lit(Lit::Nat(_))`, the
kernel's compact literal form, even though `Kernel::def_eq(pair 0 0, zero)`
was already `true` (confirmed directly by instrumenting `whnf` and printing
the node). `Nat.avg`'s pure `div`/`add` reduction never hits this path.
`decide`'s first draft peeled only the `Const`/`App(succ, _)` chain and
declined `Undecidable` on a perfectly provable goal
(`pair_evaluates_correctly` failing when the ninth test — `pair_0_0` — was
converted). Fixed by checking for a `Lit` at every step of the peel, not
only structurally recognizing the succ-chain, and finishing the count from
`NatLit`'s own (already `pub(crate)`) `is_zero`/`predecessor` rather than
duplicating `BigUint` arithmetic. The lesson this crate already has a name
for (`docs/contributor-guide/kernel-proof-engineering.md`) applied to a
NEW producer rather than a hand proof: **the kernel cannot tell a
`Definition` is wrong; only evaluation catches it — and here, evaluation
caught a bug in the CHECKER, not the thing being checked.**

`decide` retired **ten** of `avg_pair_tests`' hand `Kernel::def_eq` positive
assertions (four `Nat.avg`, six `Nat.pair`) onto itself: each now builds
`Eq lhs rhs`, requires `decide::run` to close it, and requires the KERNEL to
accept a fresh declaration built from the emitted term — the assertion is
"the kernel accepts this declaration," not "a boolean came back `true`."
The negative controls stay as direct `def_eq` checks (`decide` proves a
goal or declines; it has no "prove this is false" mode), and this is a
TEST-mechanism retirement, not a hand-PROOF retirement — it is reported
separately from the cross-producer theorem count below, not folded into it.

### 2. `tactic` — `Then`/`First` over all four producers, ℕ only

`crates/axeyum-lean-kernel/src/tactic.rs`. `Tactic::{Decide, Linarith, Ring,
Simp, Then(Box<Tactic>, Box<Tactic>), First(Vec<Tactic>)}`, generic over
`D: NatOps` (the ℕ carrier `linarith::nat`/`ring::nat`/`simp::nat` already
share — ℤ/ℚ are `IntDev`/non-generic carriers each producer implements
separately, and wiring the combinator across them is scoped out here, an
explicit cut recorded rather than a silent gap). `run(d, ctx, tactic, goal)
-> Result<ExprId, Decline>`; every leaf still pushes its term through
`Kernel::add_declaration` exactly as before, so the combinator adds no
trusted surface.

**`Then`'s two regimes, and why there are two.** Only `Simp` has a genuine
*residue* — it can rewrite a term without fully closing the goal it appears
in. `Decide`, `Linarith`, and `Ring` each either close a goal outright or
decline; none has a partial result to hand forward. So:
- **First is `Simp`**: normalize `lhs`/`rhs` separately to their `simp`
  normal forms, form the new goal over the two normal forms, run the second
  tactic on THAT, and glue the three equalities back into a proof of the
  original goal with `Eq.rec`-based transport. The gluing
  (`tactic::glue_rel`/`transport_rel`) is generic in the relation being
  proved — `Eq`, `Nat.le`, `Nat.lt` — because
  [`NatOps::eq_motive`](../../../crates/axeyum-lean-kernel/src/nat_prelude/ops.rs)
  is generic in the predicate, not specific to `Eq`; for an `Eq` goal this
  construction is provably equivalent to (though not literally) the same
  shape `d.trans` already builds.
- **First is anything else**: no residue to chain, so `Then` degrades to
  "try the first, and if it declines, try the second on the SAME goal" —
  sequential fallback, keeping `Then` total (every combination of tactics is
  a legal value) without pretending a non-`simp` first stage produces a
  partial result it does not have.

**`First`** tries a list in order and returns the first success;
`Decline::First(Vec<Decline>)` carries every sub-decline, in order, on total
failure — the same "declines are data" convention every producer here
already follows.

**The one entry point exposed from `simp`**, in its own commit
(`feat(simp): expose normalize(rules, term)`): `simp::nat::rewrite_to_fixpoint`
already did exactly what `Then(Simp, _)` needs — rewrite one term to a fixed
point, return `(final, proof: Eq start final)` — but it was private, because
`simp::nat::prove`/`prove_eq` always rewrite BOTH sides of an already-stated
`Eq` goal and never needed the normal form of a single, unpaired term.
`pub(crate) fn normalize` wraps it, dropping the step count. Nothing else in
`linarith`/`ring`/`simp`'s internals changed.

**Tests** (`crates/axeyum-lean-kernel/src/tactic/tests.rs`, 13 total): five
goals closed by `Then(Simp, Linarith)` that neither producer closes alone
(`pred_succ`/`sub_self`/`sub_zero` — all `simp` default rules — wrap a
variable in an operator `linarith`'s parser treats as an opaque atom; `simp`
alone cannot close an order goal at all, its `prove` is `Eq`-only — each
test asserts BOTH declines directly, not just the `Then` success); three by
`Then(Simp, Ring)` (the post-normalization residual needs a real
`add_comm`/`mul_comm` step `simp`'s default set deliberately omits — a bare
commutativity default never terminates, `simp::nat`'s own module docs — so
`simp` alone declines `SidesDiffer` and `ring` alone cannot see through the
non-ring-fragment operator); `First([Decide, Linarith, Ring])` on a mix
(`decide` wins on a closed goal, `linarith` wins after `decide` declines,
`ring` wins after both decline, and one goal all three decline aggregates
into `Decline::First` with exactly 3 entries); and a corrupted-glue test —
`tactic::glue_rel` (private, reached via `super::` from the test module, the
same access every sibling producer's own private helpers get from their
`tests` submodule) spliced with a residue that does NOT actually prove what
it claims (`Le m m` glued into a slot typed `Le n m`), requiring the KERNEL,
not the combinator's own bookkeeping, to catch the mismatch.

### 3. Eight hand proofs retired via the combinator

Found by grepping every `nat_prelude` hand-proof function body for BOTH a
`simp` default-rule citation and an order- or ring-lemma citation in the
same function, then attempting each retirement and keeping only what
compiled and kept the affected suite green — not inferred from the shape
alone, the same discipline ADR-1581 §1 established (a hand proof's
citations are necessary, not sufficient, for retirement: what the OLD proof
cited says nothing about what the NEW producer needs).

| site | statement | route |
| --- | --- | --- |
| `n_lt_mul_two` (×4: `binary.rs`, `bit_order.rs`, `powsq.rs`, `rec_agreement.rs`) | `Lt n (mul 2 n)` given `Lt 0 n` | `Then(Simp, Linarith)` |
| `totient_dvd_chain::le_self_two_mul` | `Le x (mul 2 x)`, no hypothesis | `Then(Simp, Linarith)` |
| `eisenstein_floor_min_free::le_two_mul_self` | `Le m (mul 2 m)`, no hypothesis | `Then(Simp, Linarith)` |
| `abundant_deficient_lemmas::two_mul_eq_add_self` | `Eq (mul 2 n) (add n n)` | `Then(Simp, Ring)` |
| `fibonacci::fib_add_two_lt_succ` | `Lt (fib(n+2)) (fib(n+3))`, unconditional | `Tactic::Linarith` |

`n_lt_mul_two` was a byte-identical (`md5sum`-confirmed) quadruplicate
across four files — its own doc comment already recorded the duplication as
a deliberate, accepted convention ("a ~20-line helper reused by three
unrelated proofs"), matching the `two_mul_eq_add_self`/`two_mul_eq_add`/
`mul_two_eq_add_self` triplicate ADR-1586 found and partly retired; this ADR
adds the FOURTH copy. `eisenstein_floor_min_free::lt_succ_two_mul_self`
(same file) is deliberately left calling the now-retired `le_two_mul_self`
plus `succ_le_succ` unchanged — it was never itself a rewrite-then-order
composition, only a caller of one, and retiring it independently would have
orphaned `le_two_mul_self` (a `dead_code` warning caught this on the first
build attempt).

`fib_add_two_lt_succ` needed no `Simp` stage: its hand proof's shape is
"rewrite [an EQUATION HYPOTHESIS] then an order step" (transport
`fib_add_two`'s equation through an `add_lt_add_left`/`add_zero` chain), and
`linarith::nat`'s own `collect` already turns an `Eq` HYPOTHESIS into both
`Le` directions and searches a Farkas certificate over every hypothesis
supplied — no separate rewrite stage is needed when what gets rewritten is a
hypothesis rather than the goal. `fib(...)` is an opaque atom to `linarith`
either way; the certificate is one part the equation's "down" direction, one
part the positivity hypothesis, summing to exactly the goal.

**Two candidates found and deliberately NOT retired**, sized negatives
rather than silent gaps: `testbit_bitwise::land_bit_lt_two` (flagged by the
same grep — cites `mul_one` and `lt_of_le_of_lt`) is actually
`mul_le_mul_left`-based monotonicity, outside both `linarith`'s fragment
(a variable-times-hypothesis-bounded-variable product) and `simp` (not a
rewrite); several `Finset`/`Multiset`/`min_fac` candidates were embedded in
theorems too large to safely isolate within this lane's time budget
(`Le`/`Lt` conclusions buried inside `Finset` membership predicates,
`Nat.rec` inductions, or `div_mod_unique`-shaped witnesses). **This ADR
retires eight of a target ten** — a measured shortfall, not a rounding: the
remaining `nat_prelude`/`int_prelude` candidates the grep surfaced either
carry a disqualifying shape (case-split, induction — ADR-1581's own
disqualification criteria) or need machinery (multiplication monotonicity,
`Finset` congruence) this lane's ℕ-only `tactic.rs` does not have, and
retiring them without that machinery risked a wrong proof for a shorter
report, which this repository's evidence discipline treats as worse than
reporting the shortfall.

**Projection unchanged for all eight**: each is a private term-building
helper with no declared name of its own (unlike ADR-1576/1581's `.theorem`
call sites), so the surrounding declared theorem's stated TYPE does not
move — only the internal proof term does. `check-fact-depends-derived.py
--fix` found and fixed eleven facts whose theorem now cites `linarith`'s/
`ring`'s fixed emitter chain (`add_le_add_left`/`_right`, `add_right_comm`,
`le_trans`, `le_of_add_le_add_right`, `le_add_right`, `add_succ`/
`succ_add`, `one_mul`/`succ_mul`) where the hand proof did not — the same
"real widening of the proof dependency graph" ADR-1576/1581 recorded for
their own retirements. `validate-facts.py`: 2742 facts, 0 errors.

`git diff --stat` on the eight touched files: 186 insertions(+), 161
deletions(-) — net POSITIVE, unlike ADR-1576's net-184-deleted headline,
because every retirement here carries a doc comment recording the route and
(where not obvious) why `Then` rather than the second stage alone. The four
`n_lt_mul_two` sites each drop from ~29 hand-built proof-construction lines
to ~20 combinator-dispatch lines; the source a reviewer has to read to
verify the PROOF (as opposed to the explanatory prose around it) shrinks at
every site even where the file's raw line count does not.

## Cost

Measured `--release` on s4 (`cargo run --release -p axeyum-lean-kernel
--example decide_and_tactic_cost`, 200 emissions per shape, prelude built
once per shape, single unpinned run — order-of-magnitude, not a ratchet
baseline, same caveat ADR-1576's own cost table carries):

| shape | search+emit | +kernel recheck |
| --- | ---: | ---: |
| `decide`  `Eq Nat (2+3) 5` | 0.018 ms | 0.025 ms |
| `decide`  `Nat.le 2 9` | 0.006 ms | 0.008 ms |
| `Then(Simp, Linarith)`  `Lt n (mul 2 n)` given `Lt 0 n` | 1.12 ms | 1.28 ms |

`decide` is the cheapest producer in the crate by a wide margin — there is
no search, only a fuel-bounded `whnf` walk, exactly the "cheapest producer
of all" framing this ADR opened with, now measured rather than asserted.
`Then`'s cost tracks `linarith`'s own measured range for a comparable
one-hypothesis `Nat` order goal (ADR-1576: 0.46–1.56 ms) — consistent with
"the combinator's cost should be the sum of what it dispatches to": `simp`
contributes one rewrite step here, negligible next to `linarith`'s
certificate search, so `Then`'s total is dominated by its more expensive
stage rather than adding a new cost of its own.

## The combinator algebra

- **Producers are leaves.** `Decide`/`Linarith`/`Ring`/`Simp` each call
  straight into the existing producer, mapping its `Decline` into
  `tactic::Decline`'s matching variant.
- **`Then` is NOT "run both and combine the terms."** It is "run the first
  as a NORMALIZER when it can be one (`Simp`), otherwise as a full attempt
  with fallback." The distinction matters because a naive "always chain"
  reading would need every producer to expose a residue, and only `simp`
  has one to give.
- **`First` is ordered choice**, not a race — deterministic, matching this
  crate's standing "no hash-map iteration order in output" promise (a
  `Vec<Tactic>` is tried left to right, always).
- **Declines compose without inventing new failure meanings.** `tactic`
  never asserts a goal is false; every leaf decline it carries forward was
  already "I did not reach a term," and `First`'s aggregate is exactly the
  list of those, not a synthesized verdict.

## Consequences

- ℤ/ℚ: `tactic.rs` is ℕ-only (`D: NatOps`), a deliberate scope cut recorded
  here rather than left implicit. `linarith::int`/`ring::int`/`ring::rat`/
  `simp::int` exist and could in principle be wired the same way, but each
  carrier's own combinators (`IntDev`, non-generic per ADR-1582/ADR-1586)
  are a different `Ctx` shape, not a mechanical generalization of this
  lane's `Ctx<'a, D: NatOps>` — left for whichever lane needs an
  `int_prelude` combinator retirement badly enough to justify it.
- `decide`'s `Lit`-recognition fix is a reminder that a NEW producer needs
  the same "instantiate concretely" discipline hand proofs do
  (`docs/contributor-guide/kernel-proof-engineering.md`): the bug was found
  by actually running the retirement, not by reasoning about `whnf`'s
  contract from its doc comment.
- Eight retired, two sized negatives, ten test-mechanism conversions — three
  different kinds of "done" in this one lane, reported separately rather
  than folded into one headline number, per this repository's own rule that
  a stable number can be stably wrong when a catch-all absorbs distinct
  categories.

## Cross-references

- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers
  behind one trust anchor; `decide` is the fourth, `tactic` composes all
  four without adding a fifth trusted surface.
- [ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md) /
  [ADR-1581](adr-1581-a-hand-proofs-citations-are-necessary-not-sufficient-for-retirement.md) —
  `linarith`, and the "citations are necessary, not sufficient" retirement
  discipline this lane's own search followed.
- [ADR-1580](adr-1580-a-second-tactic-lands-and-its-own-primitives-cannot-be-its-targets.md) /
  [ADR-1582](adr-1582-the-ring-producer-over-int-and-rat-and-what-each-carrier-costs-it.md) —
  `ring`.
- [ADR-1586](adr-1586-a-third-producer-decides-rewrite-chains-and-confluence-is-the-boundary.md) —
  `simp`, and the duplicated-identity family (`two_mul_eq_add`/
  `mul_two_eq_add_self`/`eisenstein_floor_min_free::two_mul`) this ADR's
  `two_mul_eq_add_self` retirement completes the fourth copy of.
- [07-the-cost-model-and-pareto-position.md](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  §3 — the cost table this ADR's measurement extends.
