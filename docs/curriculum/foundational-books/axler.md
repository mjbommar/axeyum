# Axler, *Linear Algebra Done Right* — the spine, audited

`docs/curriculum/foundational-books/spivak.md` gives calculus a chapter-by-chapter
route table, audited against the tree instead of asserted. Nothing does the same
for linear algebra or number theory. This document is that pass for **linear
algebra**, using Axler's *Linear Algebra Done Right* (3rd edition, 10 chapters)
as the spine.

## Why linear algebra, and why Axler

**Subject.** Both destinations have topic pages
([`03-destinations/linear-algebra.md`](../03-destinations/linear-algebra.md),
[`03-destinations/number-theory.md`](../03-destinations/number-theory.md)) and a
shared graded-families note
([`graded-statement-families-number-theory-and-linear-algebra.md`](../graded-statement-families-number-theory-and-linear-algebra.md),
846 lines). Number theory's is close to saturated already: Fermat, Euler,
Wilson (both directions), Euler's totient multiplicativity, Gauss's lemma and
the second supplementary law are all landed, general and axiom-free, and
`number-theory.md` already lists the kernel declaration next to each classical
theorem. A Stein-style spine for it would mostly restate that table.

Linear algebra is the opposite: its topic page and graded-families section were
each stale within a day of being measured (ADR-1120, ADR-1140, ADR-1155,
ADR-1205 — five upward revisions of the same "kernel declaration count" in one
week), and — checked directly against source for this document — a sixth wave
landed on top of ADR-1205's own count without any curriculum doc yet
mentioning it (`Rat.det_transpose`, `Rat.det_alternating`, `Rat.det_row_swap`,
`Rat.det_row_replaced`, `Rat.det_row_zero`, `Rat.det_row_smul`,
`Rat.det_row_multilinear`, `Rat.det_mat_mul_2`, `Rat.mul_perm4`, all in
`matrix_det.rs`). That volatility is exactly why a dated, source-audited
snapshot is worth having, and why a chapter-by-chapter pass finds real,
uncatalogued material.

**Text.** `source-tocs.md` already scores Boyd–Vandenberghe's *Introduction to
Applied Linear Algebra* chapter by chapter — but VMLS is deliberately
computational (row 3 in ADR-0603 terms: what a fixed instance decides), and its
own preamble says so. Axler's *Linear Algebra Done Right* is the proof-first
analogue Spivak is for calculus: abstract vector spaces, general dimension,
determinant deliberately delayed to the last chapter because Axler considers
coordinate-free reasoning (eigenvalues via invariant subspaces, not the
characteristic polynomial) the right foundation. That framing is pointed here
specifically: this repository just built the general-dimension determinant
(ADR-1120) and *left its central closure property — multiplicativity —
explicitly open* (ADR-1440, ADR-1470), with the open half named in a module
doc comment as precisely as this document can quote it (§"Determinant
multiplicativity" below). Auditing against Axler's chapter order surfaces that
tension directly, where auditing against VMLS's applied order would not.

## Method, and what was NOT run

Every verdict below was checked by reading the declaration or function in
source, not by trusting a prior doc's prose — three prior linear-algebra
curriculum claims turned out to be stale when checked this way (§"Corrections"
below). Specifically:

- **Kernel (K).** Read `crates/axeyum-lean-kernel/src/rat_prelude/matrix*.rs`,
  `vector.rs`, `creal_point.rs` directly: which `fn declare_*` exist, what each
  one's module-doc comment says it proves (and, where a doc explicitly says
  something is *not* proved — `matrix_det_selection.rs` does this in detail —
  quoted verbatim). Existence of a name was checked against `grep`, never
  inferred from a neighboring declaration.
- **CAS (C).** Read `crates/axeyum-cas/src/lib.rs` and `matrix.rs` directly for
  the function signature and doc comment, and checked for a same-named unit
  test (`#[test] fn …`) confirming the function is exercised, per this
  project's rule to check what a checker exercises rather than what prose
  names. Checked `artifacts/facts/*.json` for citations, and found almost
  none — most of this chapter's CAS capability is **unregistered** in the
  fact ledger, exactly the pattern `spivak.md` found for Chapters 5, 12, 13,
  14.
- **Solver (S).** Read `crates/axeyum-scenarios/src/linear_algebra.rs`
  directly for the scenario catalog.
- **What did NOT run.** `prelude_theorem_inventory --release
  --include-constructed` — the authoritative tool for an exact declaration
  count — was **not built or run** for this document; no host-shared prebuilt
  binary of it was found fresh (checked `/data0/axeyum/target/*/release/examples/`
  and this worktree's own `target/`, neither had one), and a cold build was not
  worth the time budget against a task whose verdicts are almost all
  existence/absence questions answerable by direct source read. Every
  **declaration-count** number below is therefore a proxy —
  `grep -c '^fn declare_'` per file — not the tool's environment-derived count,
  and is flagged as such inline. Every **existence/absence** verdict (does `X`
  exist, does a module doc say `Y` is not proved) is a direct source read and
  is not a proxy. This is marked explicitly rather than silently blended,
  because the two have different reliability.

## Route legend — a fourth axis this subject needs that Spivak's didn't

Spivak's four routes (S/K/C/X) were built for a constructive-vs-classical
boundary: `X` means the *general classical statement* is not constructively
provable, and `graded-statement-families.md` supplies the mechanism (LLPO,
LPO, excluded middle). That mechanism barely applies here.
[ADR-0716](../../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
already establishes why for the *decidable* linear-algebra content (matrices
over ℚ): `Rat.le_total` is a proved theorem, so there is no order-decision
boundary to extract, and row 2 of ADR-0603's four-row scheme is empty for
every family below that lives over ℚ.

But roughly half of Axler's chapters are not about ℚ at all — they are
**abstract**: "for every vector space `V` over every field `F`". This kernel
has no polymorphism, no typeclass or structure system, no `funext`. So a
second, distinct kind of `X` shows up here that Spivak's spine never needed:

- **S** — solver-decidable at a fixed instance (LRA/NRA/BV), self-checking via
  model replay or Farkas certificate.
- **K** — proved in `axeyum-lean-kernel`, axiom-free. Tagged further:
  **K-gen** (general symbolic dimension `n`, e.g. `Rat.dotN_cauchy_schwarz`),
  **K-fix** (a fixed small dimension, e.g. `Rat.det2_mul` at `n=2`).
- **C** — CAS, decidable fragment (ADR-0603 row 3): exact computation over a
  concrete numeric matrix with a re-checkable certificate (a zero-test against
  the reconstructed identity, or a self-verifying property stated in the
  function's own doc).
- **X-TA** — unavailable for a **type-theoretic abstraction** reason: the
  statement quantifies over an arbitrary vector space, field, or linear map as
  a first-class object, and this kernel has no structure/typeclass mechanism
  to express that quantification at all — not "not yet proved", but no
  *statement* exists to prove. This is permanent absent a change to the
  kernel's term language, not a proof debt.
- **X-UM** — unavailable because of a missing **algorithm or construction**
  on an otherwise-expressible fragment (e.g. complex root isolation), which is
  an engineering gap rather than a structural one — the same sense `X` carries
  in `spivak.md`.

A statement can be **X-TA in general and K-gen or C in its concrete
specialization** simultaneously — that is the normal case below, not an
exception, and it is the single most important thing this document has to say
about the subject.

## The spine

Chapter numbers and section groupings follow the 3rd edition (Springer UTM,
2015).

| Ch | Topic | Route | K — kernel | C — CAS | S — solver |
|---|---|---|---|---|---|
| 1 | Vector spaces (ℝⁿ/ℂⁿ, abstract vector space axioms, subspaces) | **X-TA** (abstract) / K-gen, K-fix (concrete instances) | `Rat`, `CReal`, `Complex` are each proved fields (ring axioms, commutativity, distributivity, multiplicative inverses), axiom-free — these ARE the scalar-field instances Axler's axioms assume, and `Nat → Rat` with pointwise operations is the ℚⁿ instance. But the **abstract statement** — `∀` a vector space `V` over `∀` a field `F`, the vector-space axioms hold — has no target to prove: grep confirms **zero** hits for `VectorSpace`, `vector_space`, a `Field` trait/struct, or `Subspace`/`subspace` anywhere in `crates/axeyum-lean-kernel/src/`. There is no polymorphism in this kernel's term language, so "for every vector space" cannot even be *stated*, let alone proved or refuted. This is the chapter that sets the pattern for the rest of the table | audited — none for an abstract vector-space structure; the CAS computes over `CasExpr`/`Rational`/matrices of those, i.e. one concrete field, not a parametrized one | N/A — nothing to decide about an abstract axiom set |
| 2 | Finite-dimensional vector spaces (span, linear independence, bases, dimension theorem) | **X-TA** (general) / C, S (fixed numeric instances) | **absent.** Grep of `rat_prelude/` for `span`, `linear_indep`/`LinIndep`, `basis`/`Basis` returns zero declaration hits (the one `span` hit in the whole prelude test suite is the English word "spans", unrelated). No dimension theorem, no basis-exchange lemma, at any generality. `Rat.det2_eq_zero_of_lin_dep` is the one fixed-`n=2` proxy for linear dependence, via the determinant, not via a general independence predicate | `Matrix::rref` (row-reduce), `matrix_rank` (`lib.rs:6883`, counts nonzero RREF rows — **this function did not exist when `graded-statement-families...md` §3.3 was written**, which says "no `rank` function at all (ABSENT)"; see §"Corrections" below), `null_space` (a certified kernel basis: "every returned `v` satisfies `A·v = 0` exactly"). All decidable-fragment, concrete-matrix only; no general "spanning set" or "basis" object | `linear_solve_2x2` (LRA, witness) tests membership of `b` in the column span of a fixed `2×2` `A`; nothing decides independence of `k` symbolic vectors directly |
| 3 | Linear maps (null space, range, matrix representation, invertibility, isomorphism, duality) | K-gen (composition/identity laws) / X-TA (null space & range as subspace objects, duality) | **K-gen, strong for the algebra of matrix multiplication itself.** `Rat.matMul`/`matId` at symbolic dimension `n` (`Nat → Nat → Rat`), with `mat_mul_assoc`, `mat_mul_add_left`/`_right` (distributivity), `mat_mul_smul_left`, `mat_mul_id_left`/`_right` — all general-`n`, axiom-free, all pointwise-stated (no `funext`). `Rat.matTranspose` general `n`, with `mat_transpose_transpose` and `mat_transpose_mul` ( `(AB)ᵀ = BᵀAᵀ` ) also general-`n`. `Rat.matInv2` proves BOTH `A·A⁻¹ = I` and `A⁻¹·A = I` at fixed `n=2`, conditioned on `det2 ≠ 0`. **But**: null space and range as *subspace objects* (rather than a solved system's solution set) don't exist as a concept — Ch.2's absence of `span`/`Subspace` propagates here — and duality (`DualSpace`, `LinearFunctional`) is entirely absent; grep for either is zero hits kernel-wide | audited — none for null space / range / dual space as objects; `Matrix::solve`/`null_space` give the *computational* content (a solution, a spanning set) without the abstraction | `linear_solve_2x2`, and the Farkas-certified `Ax=b` infeasibility route (this is `linear-algebra.md`'s named "strongest row 3 in the curriculum": `simplex::feasible`/`check_farkas`, `lra::FarkasCertificate::verify`, kernel reconstruction via `prove_unsat_to_lean_module`) |
| 4 | Polynomials (division algorithm, factorization, roots, FTA over ℂ) | X-UM (FTA over ℂ) / C (division, gcd, factorization over ℚ) | **absent for the division algorithm.** `Rat.polyEval` exists with `poly_eval_add`/`poly_eval_smul` (evaluation is an additive/scalar homomorphism), but no `poly_div`, `poly_mod`, or `poly_gcd` declaration exists in the kernel (grep of `rat_prelude/polynomial.rs` and `complex/poly.rs` confirms only evaluation infrastructure). Complex-side: `Complex.polyEval`, `polyAdd`, `polyScale`, `polyMul` are proved (spivak.md Ch.25–27), but FTA over ℂ itself is not attempted | **strong.** `lib.rs::poly_div`, `poly_gcd` (exact, over ℚ), `factor_int::factor_univariate_over_q` — complete factorization over ℚ into irreducibles (Berlekamp–Zassenhaus), cheaply certified by multiplying factors back and zero-testing. **FTA over ℂ: audited — none**, confirmed by spivak.md's own Ch.25–27 audit: `sturm.rs`/`algebraic.rs` isolate REAL roots only; complex root isolation is a genuinely missing algorithm, not an assembly gap | NRA decides fixed-degree univariate polynomial (in)equalities and, via `solve_polynomial_inequality`, exact sign-chart solution sets over isolated real roots |
| 5 | Eigenvalues, eigenvectors, invariant subspaces (existence of an eigenvalue over ℂ, upper-triangular representation, eigenspaces) | X-UM (general existence proof, needs Ch.4's FTA) / C (rational + real-quadratic + solvable-form spectrum, certified) | **absent.** Grep of the entire `axeyum-lean-kernel/src/` tree for `eigen` (any case) returns zero non-test hits. No eigenvalue, eigenvector, invariant-subspace, or upper-triangular-representation declaration exists | **the single best-covered CAS chapter after Ch.10.** `characteristic_polynomial` (`det(A − λI)`, expanded), `eigenvalues` (roots of the char. poly via `solve` — rational, real-quadratic, and complex-solvable forms), `eigenvectors` (grouped by eigenvalue; **"every returned `v` satisfies `Av = λv` exactly, which is the eigenvector certificate"**, per its own doc, for the *rational* spectrum — an irrational/complex eigenvalue is skipped rather than mislabelled), `companion_matrix` (**certified**: "the returned matrix's characteristic polynomial is verified equal to `(−1)ⁿ·(monic p)` by the zero-test" — this is existence-of-an-eigenvalue made constructive on the fragment where the characteristic polynomial's roots are expressible). All confirmed by unit test (`characteristic_polynomial_and_eigenvalues`, `companion_matrix_reproduces_the_polynomial`, `eigenvectors_certify_a_v_equals_lambda_v`, `eigenvectors_of_a_shear_and_a_repeated_eigenvalue`). **Zero fact-ledger citations** — unregistered capability, same pattern spivak.md flags for Ch.5/12/13/14 | none named; NRA can decide a fixed low-degree characteristic-polynomial root query but nothing in the scenario catalog targets eigenvalues specifically |
| 6 | Inner product spaces (inner products, norms, Cauchy–Schwarz, orthonormal bases, Gram–Schmidt, orthogonal complement, minimization) | **K-gen (the deepest general-dimension result in the subject)** / K-fix over `CReal` / C (Gram–Schmidt/QR, certified) | `Rat.dotN : (Nat → Rat) → (Nat → Rat) → Nat → Rat`, general symbolic `n`, with `dotN_comm`, `dotN_add_left`, `dotN_smul_left` (bilinearity), `dotN_self_nonneg` (semidefiniteness), and **`dotN_cauchy_schwarz` at arbitrary `n`** — all axiom-free. Note the boundary: only `dotN_self_nonneg` is proved, not a converse (`dotN v v = 0 → v` pointwise `0`) — mathematically true over an ordered field but not (yet) a kernel declaration. Separately, `creal_point.rs` builds `CPoint`, a fixed-dimension-2 inner-product space over the **constructed reals** — `dot`, `dot_self_zero_iff` (full positive-definiteness, both directions, unlike `dotN`), `dist_sq_eq_zero_iff`, `cauchy_schwarz` at `n=2`. It never builds an actual norm: `distSq` is used throughout, and although `CReal.sqrt` exists and is total and axiom-free (landed 2026-08-23, per spivak.md Ch.25–27), nothing in `creal_point.rs` applies it to `distSq` to construct `‖v‖`. Orthonormal bases and Gram–Schmidt need Ch.2's absent basis machinery and are not attempted; orthogonal complement / the minimization (best-approximation) problem need Ch.3's absent subspace objects and are likewise absent | `gram_schmidt` — "over rational vectors the output stays rational … every returned pair is certifiably orthogonal (`uᵢ·uⱼ = 0` decides via the zero-test)" — and `qr_decomposition`, which **certifies its own reconstruction** (`Q·R = A`, checked by the zero-test on every entry, doc'd with a runnable example). No orthogonal-projection / least-squares function exists (grep for `project`/`adjoint`/`orthogonal_complement` in `axeyum-cas/src/` returns zero hits outside an unrelated GF(2) name) | none named directly; norm/distance computations at fixed rational vectors are LRA/NRA-decidable in principle but no scenario targets Ch.6 specifically |
| 7 | Operators on inner product spaces (self-adjoint & normal operators, the spectral theorem, positive operators, isometries, polar/SVD decomposition) | **X-TA throughout — audited-none in every route** | absent — needs Ch.1's operator/vector-space abstraction plus Ch.6's missing orthonormal-basis machinery | **audited — none.** `Matrix::is_symmetric` exists as a boolean predicate (`matrix.rs:488`) but is used in exactly one unrelated test and is never composed with `eigenvalues`/`eigenvectors` to certify a spectral decomposition. No `adjoint`, `orthogonal_complement`, `svd`/`singular_value` function exists anywhere in `axeyum-cas/src/` (grep confirms). The pieces (`eigenvectors` + `is_symmetric` + `gram_schmidt`) are all individually present and *could* be assembled into a "symmetric matrix has an orthogonal eigenbasis" checker, but nothing does — an unbuilt assembly, not a missing primitive | none |
| 8 | Operators on complex vector spaces (generalized eigenvectors, nilpotent operators, characteristic & minimal polynomials, Jordan form) | X-TA (general operator theory) / **C, strong, on the decidable fragment** | absent — same reasons as Ch.5 and Ch.7 | `characteristic_polynomial` (reused from Ch.5/10), `minimal_polynomial` — its own doc and unit test name (`minimal_polynomial_annihilates_the_matrix`) state the certificate directly — and `jordan_form`, whose test `jordan_form_of_defective_and_diagonalizable_matrices` exercises both the diagonalizable and defective (non-diagonalizable, genuinely needing Jordan blocks) cases. `diagonalize` (`(P, D)` with `A = PDP⁻¹`, test `diagonalization_certifies`) is the Ch.5/Ch.8 boundary case made explicit. **Zero fact-ledger citations for any of the four** — unregistered capability | none |
| 9 | Operators on real vector spaces (complexification, operators on real inner-product spaces) | **X-TA, audited-none across every route** | absent | audited — none: grep for `complexif` (any case) across `axeyum-cas/src/` and `axeyum-lean-kernel/src/` is zero hits everywhere. Nothing in this codebase treats a real vector space's complexification as an object, which is unsurprising since `eigenvalues`/`solve` already returns rational, real, *and* complex roots directly — the CAS side never needed the detour Axler's abstract treatment requires | none |
| **10** | **Trace and determinant** (trace; determinant as the alternating multilinear normalized form; `det(AB)=detA·detB`; invertibility ⟺ `det ≠ 0`) | **K-gen for most of the characterizing structure; K-fix for multiplicativity; C for trace/char-poly; S for fixed small `n`** | **The deepest general-dimension chapter in the kernel, and its central closure property is the one place this document found a genuinely open, actively-worked, precisely-scoped gap.** `Rat.det : (Nat → Nat → Rat) → Nat → Rat` (ADR-1120) is a cofactor recursion via `mat_skip`/`mat_minor`/`alt_sign`, general `n`, with `det_eq_det2`/`det_eq_det3` identifying it with the fixed-size forms. `det_row_multilinear`, `det_alternating`, `det_row_swap`, `det_row_replaced`, `det_row_zero`, `det_row_smul`, `det_row_expansion`/`det_col_expansion` (Laplace, general `n`), `det_transpose`, `det_mat_id` — **this is essentially the whole "determinant is the unique alternating `n`-linear normalized function" characterization, general `n`, axiom-free.** But **`det(A·B) = det A · det B` at symbolic `n` is explicitly NOT proved**, and the reason is named precisely, not vaguely, in-tree: `matrix_det_selection.rs`'s own module doc states the general statement needs a "selection lemma" split into two obligations (ADR-1440); the free half (an explicit duplicate-index case, via `det_alternating`) is proved (`det_row_selection_of_duplicate`), and the *injective* half — "the real one" per that file's own words, needing a pigeonhole/2-point-swap cursor induction — is explicitly deferred (ADR-1470: "why it did not land this lane"). What IS proved is `det_matMul_2`, the concrete `n=2` instance, and its own doc comment says why the shortcut that makes `n=2` cheap (a `Nat.rec` base case collapsing under `Rat.zero_add`) does not generalize, and that `n=3` "is NOT done and is not cheap the same way" (18-variable identity, no `det3_mul`). Trace: **absent from the kernel** — grep of `rat_prelude/` for `trace` (excluding comments/tests) is zero hits | `trace` (`lib.rs:6901`, sum of diagonal, expanded to canonical form), `characteristic_polynomial` (reused), `Matrix::determinant`/`bareiss_determinant` (fraction-free, general size) — but per the graded-families note, "ships no certificate and no verifier", so unlike the kernel route this is exact computation without ADR-0603 row-3's re-checkability. Ledger: `F:determinant-multiplicative-over-constructed-rationals` (**proved**, `Rat.det2_mul`, `n=2`) and `F:cassini-as-determinant-of-a-matrix-power` (**proved**, `Rat.det2_fib` — the Fibonacci-matrix-power determinant read through `det2` IS Cassini's identity, with an explicit dependency check confirming the proof routes through `Int.fib_cassini` and NOT through `det2_mul`, so this is not a disguised multiplicativity result) | `det_product_2x2` (NRA), `det_product_3x3_f2` (BV over 𝔽₂), `transpose_product_2x2`, `mult_associative_2x2` — all fixed-`n` self-checking scenarios, all currently green in `crates/axeyum-scenarios/src/linear_algebra.rs` |

**Zero cells marked UNAUDITED.** Every route in every chapter above was checked
against source (a `grep` for the relevant name/pattern with a positive control
where the answer was a negative, per this project's own rule that an empty
result needs a control to be evidence) rather than asserted from a prior doc.

## The fault line here is abstraction, not constructivity

Spivak's spine has one organizing insight: Chapter 7 ("Three Hard Theorems")
is where the constructive/classical boundary bites, and every later `X` in
that table inherits from it (IVT, EVT, MVT via EVT, the general LUB property).
The mechanism is uniform: full excluded middle, or a weaker fragment of it
(LLPO/LPO), is needed and Bishop-style constructive mathematics does not have
it.

**Axler's spine has a different, and in this repository entirely
undocumented-until-now, fault line: it is not about what is constructively
*true*, it is about what can be *stated* at all.** Chapters 1, 2, 7, and 9 are
`X-TA` in every route not because some classical principle is missing, but
because this kernel has no mechanism to quantify over "an arbitrary vector
space" or "an arbitrary field" as first-class objects — no typeclasses, no
structures, no `funext` even for the concrete instances that do exist. Half of
Axler's chapter list is, from this kernel's point of view, not a hard theorem
to prove but a sentence it cannot write down.

The two boundaries interact in a specific, checkable way and do not just
coexist: **every chapter's *concrete* specialization inherits the
constructive/classical boundary from whatever theory it specializes into**
(ℚ is fully decidable per ADR-0716, so none of Chapters 1–3, 6, 10's ℚ-valued
content has a row-2 boundary at all; Chapter 6's `CPoint` specializes into
`CReal`, which *does* carry Spivak's constructive boundary — this is why
`CPoint` builds `distSq` and stops rather than building a norm via
`CReal.sqrt`: nothing forces it to stop for a Spivak-style reason, it simply
has not been done, since sqrt is total here). So a reader auditing this
subject needs to ask *two* independent questions per chapter, not one:
"does the kernel have the structure to state this at all" (Ch.1/2/7/9's
answer is no) and, only for what remains, "is the classical statement
constructively available" (this is where Spivak's machinery, and ADR-0716's
correction of it for decidable subjects, actually applies).

## Determinant multiplicativity: the freshest falsifiable claim in the repository

Worth stating on its own because it is the most precise, most recently-dated,
most falsifiable "open" verdict this document makes, and it directly answers
the task's own hint that general multiplicativity is open.

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det_selection.rs`'s module
doc states the counterexample to the naive general form directly:

> The naive target `det (B o g) n = det (matId o g) n * det B n`, with `g`
> totally unrestricted, is FALSE. Counterexample: `n=1`, `g 0 = 5`,
> `B 5 0 = 7`. Then `det (B o g) 1 = B 5 0 = 7` … while
> `det (matId o g) 1 = matId 5 0 = 0` … `7 != 0`.

and names the exact missing piece: a **selection lemma** with two proof
obligations (ADR-1440). The "free" obligation — an explicit duplicate index
pair — is proved (`det_row_selection_of_duplicate`). The "real" one — the
injective case, needing a pigeonhole argument via
`Nat.injective_on_imp_surjective_on`, a 2-point swap composed through `g`, and
`Rat.det_row_swap` — is explicitly not attempted in that file, with ADR-1470
recording why the attempt that was made did not land. `det_matMul_2` (the
`n=2` concrete instance) exists and its own comment explains why the shortcut
that makes it cheap — a `Nat.rec` base case collapsing under `Rat.zero_add`
against a *concrete* dimension bound — has no analogue at symbolic `n`, where
the same recursor is stuck on a bare free variable. This is as
falsifiable a claim as a curriculum document can make: the exact lemma name,
the exact ADR, and the exact reason a cheap route does not generalize are all
named in one place, dated to this session.

## Corrections this document makes to existing curriculum docs

1. **`graded-statement-families-number-theory-and-linear-algebra.md` §3.3
   (LA-3) says: "no `rank` function at all (ABSENT; control: `rref` matches
   11 times in the same file)".** `matrix_rank` now exists
   (`axeyum-cas/src/lib.rs:6883`), computed from `rref`'s nonzero-row count.
   The claim was correct when written and is stale now — dated evidence, not
   a wrong measurement.
2. **`03-destinations/linear-algebra.md`'s most recent count (ADR-1205: "90
   kernel declarations") is stale as of this document.** `matrix_det.rs` alone
   grew from the state ADR-1205 describes (it names only the Laplace
   row-expansion layer) to include `det_transpose`, `det_alternating`,
   `det_row_swap`, `det_row_replaced`, `det_row_zero`, `det_row_smul`,
   `det_row_multilinear`, and `det_mat_mul_2` — none named in that ADR. A
   proxy count (`grep -c '^fn declare_'` across the six `matrix*.rs` files)
   gives **123** as of this session, against ADR-1205's 90; this is a lower
   bound on the true environment-derived count (some `declare_*` functions
   register more than one kernel declaration) and is explicitly NOT the
   authoritative tool's number (see "Method" above — the tool was not run).
3. **Neither existing linear-algebra doc records that `matrix_det_selection.rs`
   already names the exact remaining obstruction to general-`n`
   multiplicativity**, with ADR numbers, a counterexample, and a description
   of which half is proved. `linear-algebra.md`'s LA-1 family entry (in the
   graded-families doc) says only "Row 1 (general `n`) not built, blocked only
   on a matrix product over the existing encoding and a recursive
   determinant" — written before that encoding and recursive determinant
   existed, so it undersells how close the remaining gap now is: the *whole*
   det/matMul/multilinearity apparatus is built, and the missing piece is one
   named combinatorial lemma.

## Most surprising verdict, in either direction

**Most surprising in the "landed" direction:** `Rat.dotN_cauchy_schwarz` at
genuinely symbolic `n`, with no `List`/`Finset`/product type anywhere in its
construction — a vector of dimension `n` is just `(v : Nat → Rat, n : Nat)`.
This is Axler's Chapter 6 in its full generality, over a field, and it exists
axiom-free in a kernel whose type theory has no polymorphism at all. It reads
like it should need the very abstraction Chapter 1 is missing, and it does
not.

**Most surprising in the "open" direction:** determinant multiplicativity, for
the opposite reason. Every *other* defining property of the determinant — the
multilinearity, the alternating property, the normalization at the identity,
agreement with the fixed-size forms, the Laplace expansion, invariance under
transpose — is proved at general symbolic `n`. The one property that makes a
determinant a *homomorphism* (from matrices under multiplication to the
scalar field under multiplication) is the one still missing, and it is missing
for a genuinely combinatorial reason (an injective reindexing needs a
pigenhole/swap argument this development has the *pieces* for —
`Nat.injective_on_imp_surjective_on`, `det_row_swap` — but has not yet
assembled) rather than a structural or constructive one. It is the single
place in this table where "everything around it is done and this one lemma
is not" is true to the letter.

## References

- Axler, *Linear Algebra Done Right*, 3rd edition (Springer UTM, 2015).
- [`../03-destinations/linear-algebra.md`](../03-destinations/linear-algebra.md),
  [`../graded-statement-families-number-theory-and-linear-algebra.md`](../graded-statement-families-number-theory-and-linear-algebra.md)
  — the topic page and the family-by-family treatment this document extends
  into a chapter spine.
- [ADR-0716](../../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
  — why row 2 is empty for the ℚ-valued content here.
- [ADR-1120](../../research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md),
  [ADR-1440](../../research/09-decisions/adr-1440-multiplicativity-needs-a-selection-lemma-not-a-leibniz-agreement.md),
  [ADR-1470](../../research/09-decisions/adr-1470-the-selection-lemma-needs-mapsinto-and-the-injective-case-is-still-open.md)
  — the general-dimension determinant and the precise, currently-open
  multiplicativity gap.
- [`spivak.md`](spivak.md) — the calculus spine this document's format and
  method extend.
