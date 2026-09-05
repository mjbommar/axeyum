# Lane: cas-multivariate — the multivariate CAS→kernel bridge, and the arity survey that shaped it

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (multivariate bridge landed with one reconstructed
fact; kernel-reconstructed 7 → 8; the arity survey refutes the fixed-arity
alternative for geometry and CONFIRMS it for WZ, so the two clusters do NOT
share one dependency)`, cas-multivariate, 2026-08-29).**

## Step 0: the sizing in `docs/plan/status/274-cas-row-three.md` re-verified

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 35 total -- kernel-reconstructed 7, cas-internal 28

Unchanged, and the cluster breakdown (NRA geometry 10, WZ 9, gf2 4,
real-algebraic 4, partial fractions 1) matches.

## The arity survey — measured from the certificates, not from the fact statements

### Geometry (10): arities 6–19. **The fixed-arity alternative is REFUTED.**

`artifacts/geometry-certificates/*.json` carry the actual `MvPoly` data:

| certificate | coords | sat vars | generators | conclusions | total vars | max total degree | max terms in one poly | total terms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| thales-right-angle-in-semicircle | 6 | 0 | 1 | 1 | 6 | 2 | 8 | 17 |
| medians-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 10 | 32 |
| orthocentre-altitudes-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 8 | 26 |
| parallelogram-diagonals-bisect | 8 | 1 | 3 | 2 | 9 | 3 | 8 | 47 |
| centroid-divides-medians | 8 | 1 | 3 | 2 | 9 | 3 | 10 | 55 |
| rhombus-diagonals-perpendicular | 8 | 1 | 4 | 1 | 9 | 3 | 12 | 73 |
| pappus-hexagon | 18 | 1 | 9 | 1 | 19 | 3 | 10 | 137 |
| euler-line | 10 | 1 | 5 | 1 | 11 | 6 | 74 | 331 |
| simson-line | 14 | 3 | 10 | 1 | 17 | 9 | 324 | 1992 |
| varignon-midpoint-parallelogram | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |

No small fixed arity covers even two of the ten. A bivariate/trivariate bridge
buys nothing here.

**Cofactor shape decides the cost, not the term count.** Only **two** of the ten
have CONSTANT cofactors — `orthocentre-altitudes-concurrent` and
`medians-concurrent`, both `(-1, -1)`. The other eight need polynomial ×
polynomial (cofactors up to 324 terms in `simson-line`).

### Two of the ten carry a VACUOUS identity, and that is a finding

The certificate's obligation is `conclusion = Σᵢ cofactorᵢ · generatorᵢ`
**between polynomials already in the CAS's canonical form**. For two of them
that identity is empty:

- **varignon** — `generators: []`, and BOTH conclusion polynomials are
  `{"terms": []}`. There is nothing to prove; the CAS's normalisation already
  discharged it. A kernel reconstruction of the certificate as stated is `0 = 0`.
- **thales** — one generator, one conclusion, single cofactor the constant `1`,
  and the conclusion polynomial is **byte-identical** to the generator. The
  obligation is `refl`.

So the two facts that look cheapest by term count are cheapest because the
certificate carries no content. The real modelling work — that
`(bx+cx)/2 − (ax+bx)/2` *is* the polynomial named — happens in
`axeyum_cas::geometry`'s construction of the `MvPoly`, upstream of anything the
certificate serialises, and reconstruction does not reach it.

### WZ (9): arities 2–4. **Here the fixed-arity alternative HOLDS.**

Measured from `artifacts/cas-certificates/*.json` (8 committed; the ninth,
`chu-vandermonde-convolution-recurrence`, has no committed certificate file):

| certificate | vars | names | recurrence length | cert numerator terms | cert denominator terms | max degree |
| --- | --- | --- | --- | --- | --- | --- |
| alternating-binomial-row-sum-zero | 2 | k,n | 1 | 1 | 1 | 1 |
| binomial-row-sum-two-power | 2 | k,n | 2 | 1 | 3 | 1 |
| weighted-binomial-row-sum | 2 | k,n | 2 | 4 | 3 | 2 |
| squared-binomial-row-sum-central | 2 | k,n | 2 | 3 | 6 | 3 |
| franel-numbers-recurrence | 2 | k,n | 3 | 18 | 28 | 8 |
| apery-numbers-recurrence | 2 | k,n | 3 | 8 | 15 | 7 |
| cross-binomial-row-sum | 3 | k,m,n | 2 | 1 | 3 | 2 |
| chu-vandermonde-convolution | 4 | k,m,n,p | 2 | 3 | 3 | 2 |

**Six of eight are bivariate in `(n, k)`.** So the two clusters do *not* share
one dependency: geometry needs an n-ary construction, WZ would be well served
by a bivariate one. The design review's framing — "one piece of infrastructure
unblocks 19 of 28" — is right that both blockers are *called* multivariate
polynomial identity checking, and understates how differently they are shaped.

**And for WZ the identity is not the whole obligation.** The Zeilberger
certificate equation `Σⱼ aⱼ(n)·F(n+j,k) = G(n,k+1) − G(n,k)` becomes a rational
identity in `(n,k)` only after dividing by `F(n,k)` and using that the shift
quotients are rational — so a reconstruction of the cleared-denominator
polynomial identity establishes the *certificate equation* and none of: that
`F` is the binomial coefficient it is named after (the Gamma-to-factorial
modelling step), that summing the telescoped equation over `k` kills the
boundary terms (`check.window`, and the `cas.symbolic-gamma-arguments-avoid-
poles` axiom several of these carry), or the induction on `n` with its base
case. Sizing the WZ cluster at "one dependency away" would overstate it in the
same direction the review warns about for geometry.

## What landed: the bridge, and one reconstructed fact

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_bridge_tests.rs`
(new file, 3 tests) and
`artifacts/facts/F-geometry-orthocentre-cofactor-identity-kernel-checked.json`.

    cas-certificate: 36 total -- kernel-reconstructed 8, cas-internal 28

**The 28 did not shrink**, for the same reason it did not shrink for lane
cas-row-three: this is a new kernel-reconstructed *sibling* fact, not a
relabelling of the parent. Nothing was relabelled and no checker was weakened.

### The representation, and why no new kernel type

**The ambient `Rat` ring expression, with the CAS's canonical sparse form as the
NORMAL FORM rather than as a kernel datatype.** Reasoning, in the order it
actually decided the design:

1. A certificate's obligation is a single **closed** identity — there is no
   quantification over polynomials to support, so a polynomial *type* would
   carry no statement the plain expression cannot. This is the one respect in
   which the multivariate case is genuinely unlike `Rat.polyEval`, which exists
   so that a statement can range over a polynomial.
2. Arities 6–19 rule out fixed-arity currying (`polyEval2 … polyEval19`) and
   would make a `Nat.Pair`-nested exponent tuple nest to depth 19.
3. A general `Nat → Nat` exponent vector avoids the nesting but needs a
   product-over-range: a degree-2 monomial in 8 variables unfolds to an
   eight-factor product with **six `Rat.one`s**, each a `mul_one` rewrite. At
   24 monomials that is ~150 rewrites of pure padding. This obstacle is
   RETIRED-AS-PRESENT: `Rat.prodRange` landed 2026-09-02
   (`68f452c23`, "feat(rat): Rat.prodRange and Rat.sumMaps, the two
   aggregates obligation 1 needs"), so the new `Definition` this step named
   as missing now exists; whether it is actually wired into this obligation
   is a separate, unverified question.
   <!-- was-absent: Rat.prodRange -->
4. The `polyEval` design principle is **preserved exactly**: term count,
   variable support and every exponent come from the translator, and nothing in
   the kernel ever computes a degree or a support.

**The inductive list, measured rather than inherited.** A throwaway probe
iterating `kernel.environment()` for `Declaration::Inductive` over the `Rat`
prelude (the one this bridge builds) printed **16**:

    Acc  And  Bool  Decidable  Eq  Exists  False  Iff
    Int  Nat  Nat.Fin  Nat.Pair  Nat.le  Or  Rat  True

Two corrections to the list the brief quotes. **`Int` and `Rat` are themselves
inductives** and the brief's list omits them — `Rat` is a two-field structure,
so it is not true that `Nat.Pair` is the only product-*shaped* declaration in
the kernel, only that it is the only *generic* one. And `Char` does not appear
here because the string prelude is not built by this bridge, not because it is
absent — a coverage gap in the probe, not a finding about the kernel. The
conclusion the design rested on is unaffected: there is no generic `Prod`, and
`Nat.Pair` was not needed.

### What makes it tractable: the atoms are opaque

Every monomial is built by ONE Rust function from the same variable list in the
same order, so two syntactically equal monomials are the **same `ExprId`**. The
cofactor identity therefore never needs `mul_comm` or `mul_assoc` *inside* a
monomial — it is a purely **linear** identity over an ordered basis of opaque
atoms. That reduced a ring-normalisation problem to two proof-emitting
primitives of ~90 lines each:

- `prove_scale` — `k · Σ cᵢmᵢ = Σ (k·cᵢ)mᵢ`, via `left_distrib`, `mul_assoc`
  (reversed), `Rat.ofInt_mul` (reversed), and one defeq ascription that
  re-normalises the `Int.mul` tree to the canonical literal.
- `prove_merge` — a sorted merge of two canonical sums, via `add_assoc`, a
  derived `add_left_comm` (`add_assoc` + `add_comm`; the kernel has no
  `add_left_comm`), `right_distrib` (reversed) and `Rat.ofInt_add` (reversed) —
  and **dropping** a monomial whose combined coefficient is zero, via
  `mul_comm`/`mul_zero`/`zero_add`. Orthocentre exercises that drop four times.

Wall clock: **7.09 s for all three tests together**, including the one-time
`Rat` prelude build — comparable to the univariate concrete-point bridges
despite being symbolic in eight variables. `rat`'s stack pin was not
approached; nothing here needed a bigger stack than the existing
`on_a_deep_stack` wrapper the sibling bridges already use.

### Mutation-verified, both halves separately

Two mutations, each killing **exactly one** test and leaving the other two
green (run in this lane's own worktree, never the shared checkout):

- **Statement check.** `scaled_head`'s coefficient `k * c` → `k * c + 1`: dies
  at the `merged == conclusion` assertion, printing a 12-term wrong normal form
  against the 8-term conclusion. The statement is pinned to the *certificate's*
  conclusion, not to whatever the emitter produced.
- **Kernel gate.** One lemma swapped in the zero-drop path, `Rat.zero_add` →
  `Rat.add_zero` (same arity, same argument, wrong direction): dies with
  `TypeMismatch` out of `Kernel::add_declaration` in 6.93 s. The proof is
  genuinely re-derived by the trust anchor, and a wrong rewrite is refused in
  **bounded** time — worth stating, since a failing defeq has no early exit.

Also: the evaluation triple in the translator test was first written by hand as
`(-4, -3, 7)` and is actually `(-3, -1, 4)` — **wrong in all three slots**. The
test caught it. That is the whole argument for asserting against numbers.

## What the reconstruction does NOT establish

Four things, each recorded in the fact's `axiom_footprint` so a reader of the
ledger cannot miss them:

1. **It does not prove the geometry.** The kernel sees eight `Rat` variables and
   an algebraic identity. That `ax` is a point's abscissa, that
   `ax·bx + ay·by − …` is perpendicularity, and that the hypotheses describe two
   altitudes, are modelling choices made in `geometry_corpus` and reproduced by
   the translator. Reconstruction **relocates** that assumption into a kernel
   definition choice; it does not discharge it.
2. **It does not establish the geometric conditional.** The theorem is the
   identity `f = −g₀ − g₁`. The implication `g₀ = 0 ∧ g₁ = 0 → f = 0` is one
   `Rat` rewrite away and is *not* taken: no hypothesis is discharged and no
   implication is declared.
3. **It says nothing about non-degeneracy.** Orthocentre's `saturations` list is
   empty. For the six certificates that DO saturate, the `d·z − 1` generator is
   an extra variable and an extra generator whose meaning is a further
   assumption.
4. **It is over `Rat`, not `CReal`.** Nothing here says the coordinates are real
   numbers; a rational-coefficient identity holds in every ℚ-algebra.

## What the remaining 18 need

| what | count | needs |
| --- | --- | --- |
| geometry, non-constant cofactors | 8 | **polynomial × polynomial**: a `prove_mul` emitting `mul_assoc`/`mul_comm` proofs to sort a product of two monomials into canonical variable order, then reusing `prove_merge`. The atoms stop being opaque here — this is the one genuinely new piece. `parallelogram-diagonals-bisect` (2–4-term cofactors, 47 terms total) is the cheapest; `simson-line` (1992 terms, 324-term cofactors) is the hardest by two orders of magnitude and should not be attempted until the cost curve is measured on the small ones. |
| geometry, `medians-concurrent` | 1 | constant cofactors, so `prove_scale`/`prove_merge` suffice — but **all coefficients are ±1/2**, so it needs a general fractional-literal builder (`Rat.ofRat`-style), the same missing piece `F:cas-partial-fractions-mixed-general-case` is blocked on. Doing that once unblocks both. <!-- absent: Rat.ofRat --> |
| geometry, `varignon` + `thales` | (2, already counted above) | nothing worth doing on this route: the certificate identity is `0 = 0` and `refl` respectively. If they are to be reconstructed at all, the honest target is the *normalisation* step, which the certificate does not carry. |
| WZ | 9 | bivariate/4-ary polynomial identity checking (the linear-over-opaque-atoms trick does **not** apply — the shift quotients multiply polynomials, so `prove_mul` is a prerequisite here too), PLUS the three steps listed above that the identity does not reach. Sizing this at "one dependency" would overstate it. |
| gf2 | 4 | GF(2) polynomial arithmetic; nothing modular or characteristic-2 exists anywhere in `rat_prelude`/`int_prelude`. Untouched. |
| real-algebraic | 4 | already partly covered by the four sibling facts landed by lanes bridge-ivt and cas-row-three; the unclaimed parts (root containment, Sturm counts) need `Rat` polynomial division and a Sturm chain in the kernel. |
| partial fractions | 1 | the fractional-literal builder above. |

**The single highest-leverage next piece is `prove_mul`** — it is the only thing
standing between this bridge and 8 more geometry certificates, and it is also a
prerequisite for WZ. The second is the fractional-literal cast, which unblocks
two facts in different clusters for one build.

## Gates run (all foreground)

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib rat_prelude::cas_geometry` — **3 passed, 0 failed**, 7.09 s
- Both `checker_command`s re-run standalone through `/usr/bin/grep -cE` (GNU grep explicitly, not the interactive ugrep) — each prints `1`, exit 0
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
- `cargo fmt --all --check` — clean
- `python3 scripts/validate-facts.py` — 1954 facts, **0 errors**

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `creal/`, `ipc_heyting.rs`,
`artifacts/kernel-stack-envelope.tsv`, and `axeyum-cas` itself (read-only — the
translator only reads existing public certificate fields). No existing fact was
relabelled and no checker was weakened. Nothing pushed.

<!-- plan-section: landed-changes -->

| 2026-08-29 | `94292a1fb` | arity survey of the 10 geometry certificates; fixed-arity alternative refuted for geometry (arities 6–19); varignon and thales identified as carrying vacuous identities |
| 2026-08-29 | `1cd4aa0ab` | `rat_prelude/cas_geometry_bridge_tests.rs` — the multivariate bridge: representation choice, `prove_scale`/`prove_merge`, translator tests green |
| 2026-08-29 | (this commit) | `F:geometry-orthocentre-cofactor-identity-kernel-checked` — the first multivariate CAS→kernel reconstruction, symbolic in 8 variables, axiom-free, mutation-verified both halves; cas-certificate kernel-reconstructed 7 → 8 |
