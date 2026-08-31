# The dominance claim, verified across three domains

Status: verification (2026-08-31), lane `three-domain-dominance-verification`

This document exists so a referee can check the project's central claim in one
sitting. That claim is spread across a dozen ADRs and three curriculum notes,
and no single artifact stated it end to end. Everything below was **re-measured
in this lane**, on this tree; nothing is quoted from an ADR as a number.

**It is a verification, not an advocacy document.** Five things it found do not
hold up, and they are in the body rather than in a footnote. The most useful is
§7.4: a producer/verifier layer for number theory now exists in code and
**no fact names it**, which is precisely the failure ADR-0875 diagnosed for EVT,
recurring in a different domain with nobody watching.

**There is no score in this document, deliberately.** A weighted number would
hide exactly the per-statement detail this document exists to expose.

## 0. How to check this yourself

Measurement base: local `main` at `f7adaf7c3` merged into this lane's worktree.
`origin/main` was `878c285d9`, **22 commits behind**, and my first sweep
therefore reported `CReal.lub_decides_em` and ADR-1010 absent when both exist.
That is worth stating up front: a referee who pulls a stale `origin/main` will
reproduce a *different and wrong* answer to two of the questions below.

Our side, one command, which prints the whole environment with a footprint
column and takes ~30 s after a release build:

```sh
cargo build --release -p axeyum-lean-kernel --example kernel_declaration_projection
./target/release/examples/kernel_declaration_projection --include-constructed
```

`--release` is mandatory. In debug this example aborts on stack depth
(SIGABRT), and an abort is indistinguishable from an absent declaration.

Mathlib's side, at the pinned commit, needs no network and no Mathlib build:

```sh
scripts/provision-lean-import-toolchain.sh --verify
cd /data0/axeyum/lean-import-toolchain/mathlib4 && \
  ~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lake env lean <probe.lean>
```

`command -v lean` prints nothing on this host and has already caused one lane
to report a whole capability as impossible. Resolve the toolchain, do not probe
the `PATH`.

## 1. The environment, measured

`kernel_declaration_projection --include-constructed`, release, this worktree:

```
rows=12049   distinct_names=2558
theorem 2100 | definition 349 | constructor 31 | axiom 30 | recursor 24 | inductive 24
```

Every one of the 30 axiom-bearing names is in `axreal`, the legacy
*axiomatized* ordered-field package. `logic`, `nat`, `integer`, `rat`,
`characterization`, `string`, `creal`, `complex` and `cpoint` all read **0**.

Two names differ by one letter and disagree about the headline metric, so:
`CReal` is the **constructed** reals, trusted surface 0, and it is what every
statement in this document reasons over. `AxReal` is the axiomatized package at
30. `AxNat` — which appears in every rendered type below — is *not* an
axiomatized `Nat`; the `Ax` is *axeyum*, and `nat` measures 0.

## 2. The two-axis test, applied per statement

The test has exactly two axes (ADR-0692): **trusted base** and **computational
content**. Breadth is a third thing that is *explicitly conceded and never
scored*. "Exact conclusion" is not a third axis — it is the computational-content
trade read from the other side, and counting both double-counts one trade.

Ours is `Kernel::axiom_footprint`, column 4 of the projection. Mathlib's is
`#print axioms` at pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`
under Lean 4.30.0 against cached oleans.

### 2.1 The measurement, both sides

Every substantive Mathlib theorem I probed lands on the same triple:

```
'intermediate_value_Icc'       depends on axioms: [propext, Classical.choice, Quot.sound]
'IsCompact.exists_isMaxOn'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.totient_mul'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.totient_prime_pow'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.exists_infinite_primes'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.Prime.dvd_mul'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.primeFactorsList_unique'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZMod.wilsons_lemma'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Matrix.det_mul'               depends on axioms: [propext, Classical.choice, Quot.sound]
'norm_inner_le_norm'           depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The controls are what make that worth anything, and they split three ways** —
which is the evidence that the probe is not printing three axioms for
everything:

```
'IsMaxOn'      does not depend on any axioms
'Nat.find'     does not depend on any axioms
'Nat.le_total' does not depend on any axioms
'Int.le_total' depends on axioms: [propext]
'Rat.le_total' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two names did not resolve, and I am recording that rather than silently
substituting: `Nat.factors_unique` is `Unknown constant` at this commit and has
been renamed `Nat.primeFactorsList_unique`; `inner_mul_le_norm_mul_norm` is
`Unknown constant` and the Cauchy–Schwarz statement is `norm_inner_le_norm`
(`Mathlib/Analysis/InnerProductSpace/Defs.lean:387`). The substring
`inner_mul_le` occurs in **zero** `.lean` files under `Mathlib/` at this commit,
against a positive control where `norm_inner_le_norm` hits three files.

### 2.2 Per statement

| our statement | ours | Mathlib counterpart | Mathlib | trusted base | comparable? |
|---|---:|---|---:|---|---|
| `CReal.ivt_approx` | 0 | `intermediate_value_Icc` | 3 | **ours** | approximate vs exact — §3 |
| `CReal.evt_approx_max` | 0 | `IsCompact.exists_isMaxOn` | 3 | **ours** | **different theorems** — §3 |
| `Nat.totient_mul_of_coprime` | 0 | `Nat.totient_mul` | 3 | **ours** | yes |
| `Nat.totient_prime_pow` | 0 | `Nat.totient_prime_pow` | 3 | **ours** | yes |
| `Nat.exists_prime_gt` / `Int.euclid_infinitude` | 0 | `Nat.exists_infinite_primes` | 3 | **ours** | yes |
| `Nat.euclid_lemma` | 0 | `Nat.Prime.dvd_mul` | 3 | **ours** | yes |
| `Nat.exists_prime_factorization` | 0 | `Nat.primeFactorsList_unique` | 3 | **ours** | **no** — existence vs uniqueness |
| `Int.wilson_iff` | 0 | `ZMod.wilsons_lemma` | 3 | **ours** | ours is the biconditional |
| `Rat.det2_mul` | 0 | `Matrix.det_mul` | 3 | **ours** | **no** — 2×2 fixed vs general `n` |
| `Rat.dotN_cauchy_schwarz` | 0 | `norm_inner_le_norm` | 3 | **ours** | **no** — ℚ at arbitrary `n` vs a normed inner-product space |
| `Rat.le_total` | 0 | `Rat.le_total` | 3 | **ours** | yes |
| `Int.le_total` | 0 | `Int.le_total` | 1 | **ours** | yes |
| `Nat.le_total` | 0 | `Nat.le_total` | **0** | **TIE** | yes |

### 2.3 What that table actually shows

Three of the thirteen rows are **not comparable statements**, and I have marked
them rather than counting them. A dominance claim is per statement or it is
nothing.

`Nat.le_total` is a **tie**, and it is the most useful row in the table.
Mathlib's is genuinely axiom-free, so on the one statement where our carriers
agree most closely, the trusted-base axis does not separate us at all. Anyone
quoting "0 against 3" as though it were uniform is overstating: the correct
form is *0 against 3 for the classical analysis and number theory, 0 against 1
for `Int.le_total`, and 0 against 0 for `Nat.le_total`*. Mathlib's three axioms
are the price of its classical, quotient-backed ambient structure, and it does
not pay that price everywhere.

On **computational content** the separation is cleaner and I did not find an
exception: `CReal.supOn` and `CReal.limit` are `Definition`s the kernel reduces,
where Mathlib's supremum-of-a-compact-image route is `noncomputable`.

## 3. EVT, stated honestly

Two asymmetries, and they must appear in the same breath as any EVT verdict.
Neither is softened below.

### 3.1 EVT here assumes strictly more

Read from the kernel, with its control in the same dump:

```
CReal.UniformlyContinuousOn : (CReal -> CReal) -> CReal -> CReal -> Sort (1)
CReal.le                    : CReal -> CReal -> Prop            (control)
```

`Sort 1` is `Type 0`. The uniform-continuity witness **carries the modulus, so
it is data**, while `hab : le a b` next to it is a proof-irrelevant `Prop`.
Mathlib assumes `ContinuousOn`, a `Prop`. So our hypothesis is stronger in two
independent ways: uniform rather than pointwise, and *data* rather than a
proposition.

The data-ness has a consequence that is easy to miss: `CReal.supOn F a b hab huc`
is **indexed by the modulus**, so two moduli for the same `F` give two `supOn`
terms the kernel does not identify. Nothing in the environment relates them.

And this kernel has **no pointwise-continuity predicate at all** —
`CReal.ContinuousOn` reads ABSENT in the projection, against `CReal.le`,
`CReal.lt` and `CReal.lt_cotrans` all FOUND in the same dump. So the hypothesis
gap cannot even be *stated* here. That is a boundary of the formalization, and
per ADR-0875 §8.2 it is a **named asymmetry inside the claim**, not something to
file under "not comparable" and drop.

### 3.2 EVT here concludes something else

Our row 1, rendered type read from the projection, transcribed:

```
CReal.evt_approx_max :
  forall F a b, le a b -> UniformlyContinuousOn F a b -> forall (n : Nat),
    exists x, le a x /\ le x b /\
      (forall y, le a y -> le y b -> le (F y) (add (F x) (ofRat (1/(n+1)))))
```

Mathlib's:

```lean
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x
```

Mathlib produces a point where the maximum **is achieved**. We produce, for each
`n`, a point that is within `1/(n+1)` of being a maximiser. **The witness `x`
sits under the `∀ n` and is never claimed to converge.** These are different
theorems, and the supremum *value* is what is constructive here; the argmax is
not, and cannot be with the tools this kernel has.

### 3.3 The strongest objection, and my answer

> A per-statement Pareto claim across two different statements is a category
> error. You have not dominated Mathlib's EVT; you have proved a different,
> weaker theorem with a stronger hypothesis and then compared axiom counts.

**I concede this for EVT, and I think it should be conceded in print.** The
two-axis test is defined as running "on a statement we actually ship that is
comparable in content to Mathlib's", and `evt_approx_max` is not comparable in
content to `exists_isMaxOn` — it differs in the hypothesis *and* in the
conclusion, in the same direction, and the axis on which we win is a third
thing. Calling that dominance stretches the word past use.

What survives is a real and checkable claim, and it is worth more than the
overclaim it replaces:

- Our row 1 and Mathlib's row 1 are **for the first time comparable at all** —
  before `CReal.supOn` landed there was no positive EVT content on our side.
- The classical conclusion is not merely unbuilt here: `CReal.evt_attained_max_decides_sign`
  is a kernel-checked theorem showing that an *attained* maximum for a
  particular function decides the sign of an arbitrary real, i.e. yields
  analytic LLPO. So the gap is a **boundary, not a hole**, and that is the honest
  claim about EVT.
- On the two axes taken alone, over the statement we ship, ours reads 0 against
  a measured 3 and reduces where Mathlib's is `noncomputable`.

The same objection does **not** land as hard on IVT. `CReal.ivt_approx` and
`intermediate_value_Icc` differ in exactness, target and ambient structure, but
they are the same *kind* of statement — a root/value is produced in the
interval — and the exactness difference is exactly the computational-content
trade the axis is about. IVT is defensible as a dominance example with its
caveats attached; EVT is not, and §7.1 records that the existing document leaves
that call undone.

## 4. The graded-family method across three domains

ADR-0603: a classical theorem lands as a family of **up to four rows** — (1)
constructive general form, (2) boundary certificate, (3) exact form on the
decidable fragment, (4) labeled import, excluded from headline counts.
Amendment 4 is the one that matters for reading the tables: **prose describing
an absence is not a row 2.**

Three kinds of empty, and they are not interchangeable:

- **empty by proof** — the reduction target is a landed theorem here, so a
  reduction to it would carry no information. This is a positive measurement.
- **empty by shape** — the classical proof contains no undecidable comparison,
  argued from the proof's structure and naming which principle *would* have been
  extracted (ADR-0603 Am. 3).
- **empty by omission** — nobody built it. Includes "unassessed", where it is
  not even settled which statement would need refuting.

### 4.1 Real analysis, over `CReal`

Row 2 is **live** here, because `CReal.le_total` and `CReal.lt_total` are both
ABSENT from the projection (control: `CReal.lt_cotrans`, `CReal.apart_cotrans`
FOUND, theorem, 0).

| family | row 1 | row 2 | row 3 | row 4 |
|---|---|---|---|---|
| IVT | `CReal.ivt_approx` (0) | `CReal.ivt_exact_root_decides_sign` (0) → **analytic LLPO** | CAS, `cas-internal` | **omission** |
| EVT | `CReal.evt_approx_max` (0) | `CReal.evt_attained_max_decides_sign` (0) → **analytic LLPO** | CAS `extremum`, `cas-internal` | **omission** |
| LUB | `CReal.limit`, `CReal.supOn` (0) | `CReal.lub_decides_em` (0) → **unrestricted EM** | polynomial range only | **omission** — no target axiom exists to import against |
| MVT | 7 substitutes (0), none registered as facts | **omission (unassessed)** | `polynomial_mvt` | **omission** |
| Taylor | not built | **omission (unassessed)** — which statement needs refuting is undecided | CAS series, not the remainder theorem | **omission** |
| FTA | not built | **shape** — candidate three-row family | not reachable | **omission** |

The ordering inside the live rows is the interesting part and it is not
cosmetic. IVT's and EVT's row 2 reach **analytic LLPO**, which is consistent
with Bishop's constructive mathematics. LUB's reaches **unrestricted excluded
middle**, which is not. Statement read from the projection:

```
CReal.lub_decides_em :
  forall (A : Prop) (s : CReal),
    (forall x, CReal.lubSet A x -> le x s) ->
    (forall z, lt z s -> exists w, CReal.lubSet A w /\ lt z w) ->
    Or A (Not A)
```

So `CReal.lub_decides_em` is strictly the stronger boundary, and the family
`CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))` has both of
classical LUB's hypotheses **proved** about it rather than assumed
(`CReal.lubSet_inhabited`, `CReal.lubSet_bounded`, both 0).

### 4.2 Number theory, over ℕ and ℤ

Row 2 **of the analysis kind** is empty by proof over ℕ, ℤ and ℚ, and this is a
measurement, not a failure to find something. The principle every analysis row 2
extracts is order totality, and here it is a landed theorem:

| declaration | verdict | kind | axioms |
|---|---|---|---|
| `Nat.le_total`, `Nat.lt_or_ge` | FOUND | theorem | 0 |
| `Int.le_total` | FOUND | theorem | 0 |
| `Rat.le_total`, `Rat.le_or_lt`, `Rat.ble_total` | FOUND | theorem | 0 |
| `CReal.le_total`, `CReal.lt_total` (contrast) | ABSENT | — | — |

A reduction terminating in something the environment already contains carries no
information. **But "no analysis-kind row 2" is not "no row 2", and the
distinction is load-bearing** — see §4.4.

| family | row 1 | row 2 | row 3 | row 4 |
|---|---|---|---|---|
| infinitude of primes | `Nat.exists_prime_gt`, `Int.euclid_infinitude` (0) | **proof** | Pratt certificate exists in code, **no fact** (§7.4) | **omission** |
| Fermat / Euler | `Nat.pow_prime_modeq_self` (0); Euler's theorem still ABSENT | **proof** | scenario `self_check`, not a producer/verifier pair | **omission** |
| totient | `Nat.totient_mul_of_coprime`, `Nat.totient_prime_pow` (0) | **proof** | not built as a certificate route | `ml430` mirrors |
| unique factorization | `Nat.exists_prime_factorization` (0) — **existence only** | **proof** for decision; **row 2′ (expressiveness) open** | factorization certificate in code, **no fact** (§7.4) | **omission** |
| Wilson | `Int.wilson`, `Int.wilson_converse`, `Int.wilson_iff` (0) | **proof** | correct, impractically slow | **omission** |
| quadratic reciprocity | ABSENT | **proof** | Legendre/Jacobi computed, **no certificate** (verified, §7.4) | **omission** |
| least-number principle | `Nat.least_divisor_search` (0) | **LANDED** — see §4.4 | row 1 and row 3 coincide (ADR-0825) | **omission** |

Unique factorization's row 2′ is a genuine and distinct thing: the obstruction
is not a missing decision but that **the classical statement cannot be written**
— this kernel has no `List`, no `Finset`, no polymorphic `Prod` and no quotient
by permutation, so multiset equality is not expressible. That is neither of the
three emptinesses above and ADR-0716 is right to give it its own label.

### 4.3 Linear algebra, over ℚ

Row 2 is empty by proof throughout, by `Rat.le_total` (FOUND, theorem, 0).

| family | row 1 | row 2 | row 3 | row 4 |
|---|---|---|---|---|
| matrix algebra | `Rat.matMul` + assoc / id / distrib / smul, `Rat.matTranspose_mul`, all at **symbolic dimension** over `Nat -> Nat -> Rat` (0) | **proof** | `matTranspose_mul_example` etc. at concrete 2×2 (0) | **omission** |
| determinant multiplicativity | **fixed size only** — `Rat.det2_mul` (2×2), `det3_*` (3×3), all 0 | **proof** | concrete entries; CAS `determinant`/`bareiss_determinant` ship **no certificate and no verifier** | **omission** |
| `Ax = b` solvability | not built as a kernel theorem | **proof** | **the strongest row 3 in the repository** — `simplex::feasible` + `check_farkas` and `lra::FarkasCertificate::verify`, two independent re-checkers, kernel-reconstructed | **omission** |
| rank / linear independence | not built; **no `rank` function at all** (0 matches in `matrix.rs`, against an 11-match `rref` control in the same file) | **proof** | 2×2 only (`Rat.det2_eq_zero_of_lin_dep`) | **omission** |
| inner-product geometry | `Rat.dotN_cauchy_schwarz` at **arbitrary `n`** (0); `CPoint` at dimension 2 | **proof** | `CPoint` facts | **omission** |

One correction to the received picture is worth pulling out, because it is
routinely stated too pessimistically: **matrix multiplication and transpose are
already at symbolic dimension**, with associativity, two-sided identity,
distributivity and `(AB)^T = B^T A^T` all axiom-free. It is specifically the
**determinant** that is fixed-size, and `rank` that does not exist. "General-
dimension linear algebra is not built" is wrong as a blanket; "the general-`n`
determinant and rank are not built" is right.

### 4.4 The claim the brief asked me to verify, and where it fails

The framing I was asked to verify is that, because row 2 is provably empty over
ℕ/ℤ/ℚ, **dominance in number theory and linear algebra must come from rows 1
and 3 under one trust anchor, not from row 2.**

For **linear algebra that is correct**, and I found no row 2 of any kind.

For **number theory it is wrong**, and this is the single largest correction in
this document. Number theory has a row 2, it is landed, and it is the strongest
boundary in the repository:

```
Nat.lnp_unrestricted_implies_em :
  (forall (P : Nat -> Prop), (exists n, P n) ->
     exists m, P m /\ (forall k, lt k m -> Not (P k)))
  -> forall (A : Prop), Or A (Not A)
```

`nat`, theorem, **footprint 0**. Its converse is also landed:

```
Nat.em_implies_lnp :
  (forall (P : Prop), Or P (Not P)) ->
  forall Q, (exists n, Q n) -> exists m, Q m /\ (forall k, lt k m -> Not (Q k))
```

`nat`, theorem, **footprint 0**.

Two things follow. First, the empty-by-proof result is narrower than it is
usually quoted: **order totality** is the principle that is unavailable as a
boundary over the discrete carriers, and ADR-0716 §2 correctly named unbounded
search as the boundary that survives. What has changed is that it is no longer
a plan — it is built (`nat_prelude/least_number.rs`, ADR-0725).

Second, and this is why it matters for the dominance argument rather than just
for bookkeeping: **this is the only row 2 in the tree pinned as an exact
equivalence.** The three `CReal` rows are one-directional implications — they
give a *lower bound* on what the classical statement costs. The LNP row gives
the price **exactly**, in both directions, over the same two `ExprId`s, checked
structurally rather than by `def_eq`. Number theory therefore has a *stronger*
row 2 than real analysis does, which inverts the ordering the curriculum
documents imply.

## 5. What the five-risk threat model actually buys

The five risks, from `docs/plan/trusted-library-safety-roadmap-2026-08-30.md`:

1. **kernel unsoundness** — substitution, conversion, universes, inductives,
   recursion, proof irrelevance or reduction accepts an invalid term.
2. **statement error** — the proved type mistranscribes or weakens the intended
   proposition.
3. **vacuity** — an impossible hypothesis or degenerate definition makes a
   readable theorem meaningless.
4. **contamination** — the target, an equivalent import, an axiom, an opaque or
   a quotient enters the dependency closure.
5. **false evidence** — a checker exits zero on completion, omits the subject,
   shares the implementation defect, or records stale ledger state.

An empty axiom footprint addresses only part of risks 4 and 5. It is silent on
1, 2 and 3 entirely.

**The replacement for "axiom-free", in the two lines a referee can check:**

> Every settled fact's admitted term has been walked to closure and contains no
> `Axiom`, `Opaque` or `Quotient` — that is risks 4 and 5 only, and only the
> closure half of them. It is **not** evidence that the type says what we meant
> (risk 2, bound by a statement pin, which catches drift after pinning and not
> a wrong statement at pinning time), nor that the hypotheses are satisfiable
> (risk 3, demonstrated load-bearing for a **single-digit** number of facts out
> of thousands), nor that the checker looked at the right subject (risk 5).

The specific numbers behind risk 3 and the census columns are re-measured in
§5.1. The two rules that survive regardless of where those numbers land, both
of which this repository learned the hard way:

- **Never quote the `semantic_falsification` column as a non-vacuity count.**
  It counts facts that *name* a control, not facts whose control was shown to
  be load-bearing, and the gap between those is more than an order of magnitude.
- **Never quote `independent_replay` in either direction.** It has been measured
  wrong *both* ways at once — crediting a fact whose "replay" was
  `check-lean-gate.sh` invoked with no arguments, while failing to credit the
  handful of facts that carry a genuine per-fact, name-and-type, real-Lean
  admission grade.

### 5.1 Re-measured

Every gate below was run bare in the foreground in this worktree and its **own**
exit status read — not a pipeline's, which reports the last stage and has
produced wrong answers here before.

```
validate-facts.py                      exit 0   2366 facts, 0 errors
                                                2182 settled, 2162 DISTINCT propositions
check-settled-fact-statements.py       exit 0   settled=2182 pinned=2182 unpinned=0
                                                identity_bound=1967 drifted=0
check-mirror-statement-fidelity.py     exit 0   mirrors=594 hash_verified=582 unpinned=12
check-semantic-control-fixtures.py     exit 0   fixtures=13 executed=9742 mutations=19
                                                killed=18 also_true=1 survived=0
                                                load_bearing=8 semantic_falsification=100
check-statement-identity-mutations.py  exit 0   5/5 rejected, tree restored
gen-safety-matrix.py --check           exit 0   proved=2180 commands=2376 PASS
check-autogenesis-holdout-isolation.py exit 0   held_out=146 references=0 PASS
tests/test-trust-closure.sh            exit 0   cases=17 mutations=15 not_exactly_one=0
```

`scripts/check-trust-closure.py` — the gate that produces the contamination
reach — **did not run**: it shells out to a `cargo run --release` kernel build,
which was out of scope for this lane. Its numbers below are read from its
committed pin, so they are floors it last ratcheted, not a live measurement,
and I am labelling them that way rather than presenting them as fresh.

The per-column census over `artifacts/safety-matrix/safety-matrix.tsv` (2,180
data rows), computed with awk and reproduced independently:

| protection | yes | no |
|---|---:|---:|
| `exact_statement` | 2180 | 0 |
| `kernel_theorem` | 2012 | 168 |
| `coverage_bearing_checker` | 1988 | 192 |
| `env_footprint` | 1914 | 266 |
| `semantic_falsification` | **100** | 2080 |
| `per_theorem_footprint` | 65 | 2115 |
| `mutation_control` | 15 | 2165 |
| `circularity` | 14 | 2166 |
| `independent_replay` | **7** | 2173 |

Protections held per fact: **82 facts hold none**, 97 hold exactly one, 38 hold
two, 1,919 hold three, 35 hold four, 9 hold five. My independently computed
histogram matches the TSV's own published `protection_count` column in all six
buckets, which is the control that says the awk is reading the right fields.

**Per risk, what it buys:**

- **Risk 1, kernel unsoundness.** The differential against Lean covers all eight
  roadmap subsystems; `test-trust-closure.sh` shows 15 guards each killed by
  exactly one case. Real coverage. The residual is that "8 of 8 mutants killed"
  is a pinned human measurement — the ratchet checks internal consistency and
  does not re-run the mutations.
- **Risk 2, statement error.** `exact_statement` is 2180 of 2180, and all five
  identity mutations are rejected. But read what that binds: **mutations 1–3
  were caught by the statement pin alone**, i.e. by the statement changing
  *after* pinning. It binds transcription drift, not whether the statement was
  right at pinning time. Nothing here reads intent.
- **Risk 3, vacuity. This is the binding gap and it is a single digit.**
  `load_bearing=8`, against `semantic_falsification=100` named and 2,180 proved.
  All eight are the `Nat.totient` multiplicativity and CRT counting family. No
  central gate covers the rest.
- **Risk 4, contamination.** Strongest of the five: 15 mutation-verified guards
  over a pinned population of 2,004 subjects and 2,548 declarations (read from
  `artifacts/trust-closure/population.json`, **not** re-derived here).
- **Risk 5, false evidence.** Partly covered — `coverage_bearing_checker` is
  1,988 of 2,180 — and structurally unenforced. **None of the L0 gates runs in
  `.github/workflows/ci.yml` or in `hooks/pre-push`.** Verified by grep with
  positive controls in the same command: zero hits for the seven gate names in
  `ci.yml` against 59 control hits over 367 lines, and zero in `hooks/pre-push`
  against 36 control hits over 566 lines. `hooks/pre-push` invokes no Python
  gate at all. They run only in the local aggregate battery, which means a
  referee cloning the repository and reading CI sees none of this machinery.

**Three ADR-1000 figures have moved, in the direction of improvement, and
should not be requoted:**

| | ADR-1000 (2026-08-31, earlier) | measured now |
|---|---|---|
| subjects chosen by the unreliable `theorem_of` regex | **548** (28%) | **9** of 2,105 (0.4%) — ADR-1005 bound 660 by explicit field |
| facts holding exactly one protection, and which | **434**, `env_footprint` | **97**, and mostly *not* `env_footprint`: 67 `semantic_falsification`, 21 `kernel_theorem`, 8 `env_footprint`, 1 `independent_replay` |
| `gen-safety-matrix.py --check` | **exit 1, stale** | **exit 0, PASS** |

The middle row is the one to be careful with. The thin spot got much smaller
*and moved*, so "434 facts protected only by a prelude-wide sweep" is wrong in
both the number and the identity. Facts holding **no** protection at all went
105 → 82.

What I could **not** check, stated rather than glossed: whether the seven
`independent_replay` facts are still disjoint from the nine checked-interchange
roots, and whether the one crediting `check-lean-gate.sh` invoked with no
arguments is still among them. That join remains unpublished, which is exactly
why the column stays unquotable in both directions.

## 6. What is conceded

**Breadth, explicitly and without qualification.** Mathlib states IVT for a
conditionally complete linear order with an order topology and a densely
ordered structure, and EVT for a continuous function on a compact set in a
topological space. We state both for a specific uniformly continuous function
on a specific closed interval of one specific constructed carrier. That is not
a smaller version of Mathlib's theorem; it is a theorem about a much smaller
world. Breadth is not scored on either axis and no count in this repository
should imply otherwise.

Also conceded, from the measurements above:

- **EVT is not a per-statement dominance example** (§3.3). The statements are
  not comparable.
- **`Nat.le_total` is a tie** (§2.2), so "0 against 3" is not uniform.
- **Row 4 is empty by omission in all three domains**, every family. There is no
  labeled classical import anywhere in this ladder, and for LUB there is not
  even a target axiom package to attach one to.
- **Row 3 is `cas-internal` for the analysis families** — the substantive half
  does not reach kernel reconstruction, so it is not under the one trust anchor
  the dominance argument leans on.
- **Unprovability is not machine-checked and cannot be.** Every row 2 shows that
  the classical statement *implies* a principle absent from this environment. A
  kernel that only accepts proofs cannot certify that the principle is
  unprovable. Row 2 is falsifiable in exactly the way ADR-0603 Am. 2 requires:
  land the principle and the boundary becomes a route.
- **`Nat.exists_prime_factorization` is existence, not uniqueness**, and the
  uniqueness statement is not expressible here at all.

## 7. Corrections, each with the measurement behind it

### 7.1 `08-ivt-and-evt-measured-against-mathlib.md` leaves EVT's verdict undone

That document's §4 EVT table carries a SUPERSEDED banner and its replacement
says a "fresh two-axis pass is needed", explicitly deferring the call. §3.3
above makes it: **concede it.** Measurement: the two rendered types in §3.2,
read from the projection.

### 7.2 The LUB row-2 absence assessment is closed

`docs/curriculum/graded-statement-families.md` was amended on `main` the same
day I ran, and correctly. Recorded here because my first sweep, against a
22-commit-stale `origin/main`, reported both `CReal.lub_decides_em` and ADR-1010
absent — with a perfectly convincing positive control beside it. **A stale base
produces a confident, wrong absence verdict**, which is exactly the failure mode
the row-2 discipline exists to prevent, arriving through the door marked
"I checked".

### 7.3 Number theory's row 2 is built, in a document that says it is not

`graded-statement-families-number-theory-and-linear-algebra.md:366` reads
"**Not built, and it is the highest-value unbuilt row in this note**", and `:639`
still lists it as a next target. Measurement: `Nat.lnp_unrestricted_implies_em`
and `Nat.em_implies_lnp`, both `nat`, both theorems, both footprint 0, in the
projection. Landed in `b81277a5c`; ADR-0725 documents it. Corrected in place.

### 7.4 Number theory's row 3 exists in code and no fact names it

Two documents state that `axeyum-cas` has **19** `verify_*`/`check_*` functions
and that **not one is number-theoretic**, concluding that "the classical
number-theory CAS is bare computation with no witness type and no verifier".

**Their method was sound and the tree moved under it** — worth saying plainly,
because the reflex here is to blame the probe. Re-running the curriculum note's
*exact* pattern, `^pub fn verify_|^pub fn check_` over `axeyum-cas/src/`, gives
**22 distinct** today rather than 19, and **six are number-theoretic** by that
same pattern.

A wider census, counting non-`pub` functions too and masking `#[cfg(test)]`
bodies out — because a bare grep counts test functions named `check_...` and
would have inflated the number:

```
SHIPPED (outside #[cfg(test)]): 27 distinct
NUMBER-THEORETIC among shipped:  7
  check_composite_certificate       check_crt_certificate
  check_factorization_certificate   check_irreducible_certificate
  check_irreducible_certificate_independent
  check_primality_certificate       check_primality_certificate_at
POSITIVE CONTROL verify_extremum_certificate found in shipped: True
```

`crates/axeyum-cas/src/ntheory_certify.rs` exports `PrattCertificate`,
`CompositeCertificate`, `FactorizationCertificate` and `CrtCertificate`, and its
checker's own doc records that it "shares no code with `certify_prime` or with
`ntheory::is_prime`; in particular the modular arithmetic is this module's own"
— which is exactly the producer/verifier separation ADR-0716's gap list asked
for. Three of that list's four items (primality, factorization, CRT) are closed.
The fourth is not: `legendre` matches **0** times in that file, against a
17-match `Pratt` positive control in the same command.

**And here is the part that matters more than the correction.** Facts naming any
of those three checkers:

```
count: 0
positive control (facts naming verify_extremum_certificate): 3
positive control (facts total): 2366
```

**Zero.** This is precisely the defect ADR-0875 diagnosed for EVT — *the content
exists and the bookkeeping that would let anyone verify it does not* — recurring
in a different domain, four weeks later, with no gate noticing. The row-3 claim
for number theory is currently unciteable for the same reason EVT's row 1 was.
That is the finding I would most want a referee to check, because it says the
failure is structural and not a one-off.

I have not repaired it: this is a verification lane and the ledger is out of
scope. It is written down here so the next lane does not have to rediscover it.

## 8. The weakest part of the claim as it now stands

**Row 3 is where the dominance argument is supposed to be strongest for the
decidable subjects, and it is the row with the least bookkeeping behind it.**
The argument for number theory and linear algebra is "one statement, one trust
anchor, three artifacts" — the theorem, an executable that settles any concrete
instance, and a certificate a third party re-derives. The first artifact is
solid and measured. The third now exists in code for primality, factorization
and CRT, and **no fact names it**, so a referee following the repository's own
instructions to look in the ledger will conclude it is absent — as two ADRs and
a curriculum note already did. Meanwhile the analysis families' row 3 is
`cas-internal`, which means it is not under the trust anchor the argument
invokes. So on the axis the decidable-subject dominance claim rests on, the
evidence a referee can actually check is thinner than the claim, in all three
domains, for two different reasons.
