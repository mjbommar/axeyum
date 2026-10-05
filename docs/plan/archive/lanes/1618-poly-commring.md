# Lane: poly-commring — `R[X]` is a commutative ring (W2-9's residue, ADR-1618)

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, poly-commring, 2026-09-04).** ADR-1609 stopped 20
of 23 fields into `AlgS.CommRing` for the polynomial ring over an abstract
`AlgS.CommRing`, and recommended moving the build position past `Nat` arithmetic
and restating convolution over `sumRange` with `Nat.sub`. **That recommendation
is declined on measurement and the walk closes instead** — twelve new
declarations at the SAME build position, no `Nat.add`, no `Nat.sub`, **zero
kernel rejections**.

The measurement that decides it: every `sumRange` reindexing lemma in the tree
is over a CONCRETE carrier folded with that carrier's own addition
(`Nat.sumRange : (Nat → Nat) → Nat → Nat`), so an abstract `AlgS.CommRing`
carrier reuses none of them — `grep sumRange` across the three `AlgS` modules
returns ONE hit, a comment. Route (a) would have to declare `AlgS.sumRange` and
reprove every reindexing lemma anyway, in a shape whose induction hypothesis is
weaker, after relocating a ~1,300-line block inside
`build_nat_prelude_uncached` (`declare_poly_setoid` at `nat_prelude.rs:6719`,
`declare_subtraction` at 8015).

What actually unblocked it is the **motive**, not the representation: `Nat.rec`
on the first walk index with `fun i => forall g, …` or `fun i => forall j, …`,
because the walk's successor step calls itself at `succ j` AND at a shifted
family. Landed: `antidiagFrom_shift` (what replaces the unwritable `j + n`),
`antidiagFrom_succ_last` (peel the LAST cell), `antidiagFrom_rev` (the
reversal), `antidiagFrom_tail_zero` / `antidiagFrom_head` (the collapse),
`antidiagFrom_mul_right`, `mul_succ`, `mulComm`, `mulOneR`, `mulOneL`,
`mulAssoc`, and **`AlgS.Poly.commRing : AlgS.CommRing -> AlgS.CommRing`**, all
23 fields.

`mulAssoc` — ADR-1609's "the hard one", sized as a two-dimensional exchange —
needs **no three-index machinery**: it is four applications of the
convolution's own `mul_succ` recursion plus `distribL`/`distribR`, joined by one
`R.mulAssoc` and one `R.addAssoc`. The three-index route was explored first and
is recorded in ADR-1618 so it is not re-derived.

**ℚ[X], ℝ[X] and ℂ[X] are machine-checked commutative rings**
(`tests/poly_comm_ring_concrete.rs`), each admitted through the trusted gate
with an empty axiom footprint, over `AlgS.CommRing.ofAlg Alg.Rat.commRing`,
`CReal.commRingS` and `Complex.commRingS`. They are admitted into a test-local
kernel, not landed as named prelude declarations — that is a small separate
step, sized in ADR-1618.

**Setoid cost of this lane: zero.** Every one of the twelve declarations would
read identically over `Eq`. The one place the discipline shows is a benefit,
unchanged from ADR-1609 and now carried through the whole ring rather than only
its additive group: the carrier is a function space, so the `Alg` spine's law
fields would be equalities of lambdas and would need `funext`. No evidence to
reopen ADR-1595.

**Two negatives, stated as precisely as the positives.**

- **`Complex.polyEval_polyMul` ALREADY EXISTS** (read from a freshly built
  `shape_search`, `declarations=3935`) — `complex/poly.rs` builds
  `Complex.polyMul` over `sumRange`/`Nat.sub` with `polyDegreeLt` hypotheses.
  ADR-1609's parenthetical that "evaluation is a ring homomorphism" is open for
  the same reason as the abstract case is **stale for ℂ** and accurate only
  for ℚ.
- **`Rat.polyEval_mul` did not land, and is not small.** `Rat.polyEval`,
  `_add`, `_smul`, `_succ`, `_zero`, `_deg1` exist; `Rat.polyMul` and
  `Rat.polyDegreeLt` do not. It is a port of `complex/poly.rs`'s ~800-line
  chain to the `Rat` carrier, and it is **not reachable from
  `AlgS.Poly.mulAssoc`**: the abstract theorem is about the antidiagonal walk,
  `Rat.polyEval_mul` would be about `Rat.sumRange` with `Nat.sub`, and no
  agreement lemma between the two representations exists in the tree. The
  cheaper route is that agreement lemma
  (`AlgS.Poly.mul (ofAlg Rat.commRing) p q n ~ Rat.polyMul p q n`), itself a
  reindexing obligation of the same family. `Complex.factorQuotient` is on the
  same far side and was likewise not connected. Do not price either as small.

<!-- plan-section: landed-changes -->

| 2026-09-04 | poly-commring | `AlgS.Poly.commRing` lands: the four `AlgS.CommRing` fields ADR-1609 left open (`mulOneL`, `mulOneR`, `mulComm`, `mulAssoc`) plus the six walk reindexing lemmas, at the same build position, zero kernel rejections (ADR-1618) |
| 2026-09-04 | poly-commring | ℚ[X], ℝ[X] and ℂ[X] admitted as `AlgS.CommRing` values with empty axiom footprints (`tests/poly_comm_ring_concrete.rs`) |
| 2026-09-04 | poly-commring | `poly_setoid_tests` 8 → 17: three evaluation tests at `n ≤ 3` plus five rejection controls, each with a positive twin; all five mutation-verified (exactly the five mutated tests died, the other twelve passed) |
