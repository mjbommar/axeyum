# Graded statement families beyond analysis: number theory and linear algebra

Status: measurement note (2026-08-30)

[ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
says a classical theorem lands as a graded family — constructive general form
(row 1), boundary/unprovability witness (row 2), exact form on the decidable
fragment (row 3), labeled import (row 4).
[`graded-statement-families.md`](graded-statement-families.md) applies it to
MVT, LUB, Taylor remainder and FTA. All four are Spivak; all four are real
analysis.

The curriculum names **three** destinations — calculus, number theory, linear
algebra. This note does the other two, and answers the question they force:

> **What is row 2 of a subject that is decidable?**

Short answer, measured rather than argued: for ℕ, ℤ and ℚ the decision
principle that every analysis row 2 extracts is **already a theorem in this
kernel**, so that mechanism is provably empty here. Two *different* boundaries
survive, one of them stronger than anything analysis produces, and where
neither applies the dominance argument moves off row 2 entirely. §1 works this
out; §2 and §3 give the families.

---

## Method

Every claim below traces to one of:

- the kernel, read from a **freshly built** `--release` binary — the
  stale-prebuilt trap makes an ABSENT verdict worthless, and this note turns
  on several ABSENT verdicts. Built this session with
  `scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
  prelude_theorem_inventory --example shape_search --example
  kernel_declaration_projection` (47.3 s, clean), then dumped in one pass:

      shape_search --include-constructed --kind theorem --kind definition \
        --kind axiom --kind inductive --kind constructor --kind recursor \
        --limit 9000 --show-consts
      -> coverage: groups=[logic,nat,axreal,integer,rat,characterization,
                           string,creal,complex,cpoint]
         declarations=2426 build=27.6s
         control: axiom=30 definition=336 theorem=1981 inductive=24
         verdict: FOUND 2426

  Full types and axiom footprints from `kernel_declaration_projection
  --include-constructed` (11,217 rows). **Every negative below is paired with a
  positive control of the same declaration kind**, named inline.

- `artifacts/facts/` (2,266 facts at the time of writing);
- an explicit gap, with its blocker named.

Two hazards this note navigates, both documented in `CLAUDE.md` and both hit
while writing it:

- `prelude_theorem_inventory` lists **theorems only**. `Rat.dotN` and
  `Nat.totient` are `Definition`s and return zero rows from it; the projection
  tool is what answers "does this definition exist".
- A name guess is not a search. `Rat.dot` returns **0** and `Rat.dotN` returns
  **9** — this note's central linear-algebra finding was nearly missed on
  exactly that, and was recovered by searching for the *shape*
  (`Cauchy–Schwarz`) rather than the name.

---

## 1. What row 2 means for a decidable subject

### 1.1 The analysis mechanism, and why it cannot fire here

ADR-0603 Amendment 2 fixed the vocabulary: a row 2 is an **unprovability
witness** — a kernel-checked declaration of the form

> classical statement ⟹ a decision principle this kernel demonstrably lacks

and Amendment 4 added that prose describing an absence is not one. For
`CReal`, that principle is order totality. `CReal.evt_attained_max_decides_sign`
extracts `∀ v, v ≤ 0 ∨ 0 ≤ v` from an attained maximum; the mechanism works
because `CReal.lt` is genuinely undecidable, which is why `CReal` carries
`lt_cotrans`/`apart_cotrans` as substitutes instead.

Measured over the 2,426-declaration dump, and this is the pivot of the whole
note:

| declaration | kind | axioms | present? |
|---|---|---|---|
| `Nat.le_total : ∀ a b, Or (le a b) (le b a)` | theorem | 0 | **FOUND** |
| `Nat.lt_or_ge` | theorem | 0 | **FOUND** |
| `Int.le_total` | theorem | 0 | **FOUND** |
| `Rat.le_total`, `Rat.le_or_lt`, `Rat.ble_total` | theorem | 0 | **FOUND** |
| `CReal.le_total` | — | — | ABSENT |
| `CReal.lt_total` | — | — | ABSENT |
| `CReal.lt_cotrans`, `CReal.apart_cotrans` (the substitutes) | theorem | 0 | FOUND *(control)* |

**Over ℕ, ℤ and ℚ the decision principle every analysis row 2 lands on is a
proved, axiom-free theorem in this environment.** So no number-theoretic
statement, and no statement of rational linear algebra, can have a row 2 of the
analysis kind: the reduction would terminate in something we already have, and
a reduction to an available principle carries no information.

This is *not* "we looked for a row 2 and did not find one" — the failure mode
ADR-0603 Amendment 4 exists to prevent. It is a positive measurement that the
mechanism is empty, and ADR-0603 Amendment 3 asks for exactly this shape of
argument ("an entry claiming 'no row 2 needed' must say which decision
principle would have been extracted and why the classical argument never
reaches it"). The gain here is that it can be said **once for a whole subject**
rather than theorem by theorem.

### 1.2 Two boundaries that survive

"Decidable" is *pointwise*. Two things remain undecidable about ℕ, and each
supports a genuine row 2 — of a different shape from the analysis ones.

#### (a) The unbounded-search boundary — and it is *stronger* than analysis's

Every ℕ-predicate this library forms is decidable at a point, but `∃ n, P n`
with no bound is not. Measured:

- **Bounded** minimization exists: `Nat.least_divisor_search` (theorem, 0
  axioms) returns `Or (∃ least divisor ≥ 2) (no divisor ≥ 2 below the bound)`;
  `Nat.minFacAux`/`Nat.minFac`/`Nat.minFacAuxMinimal` likewise.
- **Unbounded** minimization does not. A name search is weak evidence here, so
  this was checked by SHAPE: `shape_search --ns Nat --hyp Exists` — every `Nat`
  declaration taking an existential hypothesis — returns **FOUND 2**, and both
  are `Nat.cantor_diagonal_neg` / `Nat.cantor_no_fixed_point`, unrelated. So
  **no declaration anywhere in the `Nat` namespace has the form "given
  `∃ n, P n`, produce a witness or a least such `n`"**, which is exactly the
  `Nat.find` / LNP shape. The query answering FOUND 2 rather than erroring is
  its own positive control; `Nat.least_divisor_search` is unconditional (it
  returns an `Or`, taking no existential) and is the bounded counterpart.
- Unrestricted excluded middle does not exist either. The kernel has
  `Decidable.em`, which **takes a `Decidable` instance**; the unconditional
  form is absent. Positive controls of the same kind, all FOUND:
  `em_of_dne`, `em_of_peirce`, `dne_of_em`, `peirce_of_em` (each *conditional*,
  taking the other principle as a hypothesis) and `not_not_em : ¬¬(p ∨ ¬p)`,
  the constructively provable weak form. No `Classical`, no `choice`, no `LPO`,
  no `LLPO`, no `Markov` under any spelling — the two `Rat.markov_*` hits are
  Markov's *inequality* from the probability layer, a name false positive.

So number theory's row-2 target is the **least-number principle for an
arbitrary predicate**, and it reduces to full excluded middle:

> `LNP : ∀ (P : Nat → Prop), (∃ n, P n) → ∃ m, P m ∧ ∀ k, P k → m ≤ k`
> implies `∀ A : Prop, A ∨ ¬A`.

Proof sketch, entirely inside this kernel's means: given arbitrary `A`, take
`P n := (n = 0 ∧ A) ∨ (n = 1)`. `P` is inhabited at `1`, so `LNP` yields a
least `m`. `Nat.lt_or_ge m 1` splits: if `m < 1` then `m = 0`, so `P 0`'s left
disjunct gives `A`; if `1 ≤ m` then `A` is impossible, since `A` would make
`P 0` hold and minimality would force `m ≤ 0`. Hence `A ∨ ¬A`.

Three things make this the most valuable unbuilt row 2 in the repository:

1. **It lands on full EM, not LLPO.** `CReal.evt_attained_max_decides_sign`
   extracts analytic LLPO, which is consistent with BISH. This extracts
   excluded middle for an *arbitrary* proposition — a strictly stronger
   boundary result, and one no classical library states at all because
   classically the hypothesis is free.
2. **It is non-vacuous by construction**, which ADR-0603 Amendment 2 makes
   mandatory for this shape: the bounded LNP *is* a theorem here
   (`Nat.least_divisor_search`), so the row says precisely where "least
   element" stops being computable rather than asserting a blanket absence.
3. **It is falsifiable in the way Amendment 2 requires**: land an unrestricted
   `em` and the row stops being a boundary result.

#### (b) The expressiveness boundary — a different row, and it must not be called row 2

The existence half of unique factorization is landed:

    Nat.exists_prime_factorization : ∀ n, 2 ≤ n →
      ∃ k (f : Nat → Nat), (∀ i < k, Prime (f i)) ∧ prodRange f k = n

*(theorem, 0 axioms — note the encoding: a factorization is a **function plus a
length**, not a list.)*

Uniqueness is "the multiset of prime factors is unique", and this kernel has no
`List`, no `Finset`, no polymorphic `Prod` and no quotient by permutation. The
complete inductive census is `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/
Decidable/Nat.le/Nat.Fin/Nat.Pair/Char` (24 inductives in the dump).

**The obstruction is not a missing decision — it is that the classical
statement cannot be written.** Calling that row 2 would let an expressiveness
gap masquerade as a constructive-strength result, which is the same category
error Amendment 4 corrects from the other direction. It deserves its own row,
proposed here and adopted in
[ADR-0716](../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
as **row 2′, the expressiveness witness**: state the strongest form the type
theory admits, name the type the classical form would need, and *prove the
expressible form*.

For UFD the expressible form needs no new type at all. `Nat.countRange_permute`
(theorem, 0 axioms) already reindexes a bounded count along an injective
self-map of `[0,n)`:

    ∀ (p : Nat → Bool) (σ : Nat → Nat) (n : Nat),
      injectiveOn σ n → mapsInto σ n →
      countRange p n = countRange (p ∘ σ) n

— permutations of `[0,n)` are `Nat → Nat` plus `injectiveOn`/`mapsInto`, so
permutation-invariance is reachable without multisets. The honest uniqueness
statement is therefore *multiplicity agreement at each prime* (`∀ q, Prime q →
countRange (fun i => q == f i) k = countRange (fun i => q == g i) j`), which is
expressible today. This is the same distinction ADR-0668 draws between
**evaluating** an unavailable object and **inducting past** it.

### 1.3 Where neither boundary applies, the dominance argument must move

For analysis, dominance over Mathlib comes from row 2 — we prove *where* the
boundary is, with a machine-checked certificate, and a classical library has no
counterpart row (this is the axis
[`08-ivt-and-evt-measured-against-mathlib.md`](../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
measures). For most of elementary number theory, §1.1 says that axis is empty.
So the argument has to change, and pretending otherwise would be exactly the
unfalsifiable-claim failure this project audits against everywhere else.

The replacement, stated so it can be attacked:

> **For a decidable subject the family degenerates to rows 1 + 3, and row 3
> stops being a consolation prize — it becomes the entire claim. The axis is
> not "we prove more" but "one statement, one trust anchor, three
> artifacts": the general theorem, an executable that settles it at any
> concrete instance, and a certificate a third party re-derives — all admitted
> through `Kernel::add_declaration` (ADR-0601).**

Mathlib has `Nat.totient_mul`. It does not attach, to that same proposition, an
executable computing φ(n) and emitting a re-checkable receipt. That is a
per-statement dominance claim of the kind
[`07-the-cost-model-and-pareto-position.md`](../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
licenses — per-statement dominance plus uncontested axes, never coverage
parity — and it dies the day a classical library ships a checked decision
procedure bound to the same proposition. That falsifiability is the point.

Two honest consequences:

- **A three-row family (1, 3, 4) is the NORMAL case in number theory**, not a
  deficiency, exactly as ADR-0603 Amendment 3 concluded for FTA. What was a
  finding about one theorem is a property of a whole subject.
- **Row 3 must actually be built** for the argument to hold — and for classical
  number theory it very largely is not. This is the note's most actionable
  finding, so it gets its own section: §2.8.

---

## 2. Number theory (Stein ch. 1–6; Shoup ch. 1–4, 10–12)

A great deal landed in the 24 hours before this note. Every row-1 entry below
was read from the fresh dump with its axiom footprint, not from a report.

### 2.1 Family: infinitude of primes — *the cleanest no-row-2 case in the repo*

| Row | Status |
|---|---|
| **1** | **Landed.** `Nat.exists_prime_gt : ∀ n, ∃ p, n < p ∧ Prime p` (theorem, 0 axioms) and `Int.euclid_infinitude` (theorem, 0 axioms), the ℤ form. |
| **2** | **None, and argued from the shape** per ADR-0603 Am. 3. Euclid's proof is *fully computational*: it produces the bound `n! + 1` and searches below it, so there is no undecidable comparison and no unbounded search to extract. The decision it would need — order totality on ℕ — is `Nat.le_total`, a theorem here (§1.1). |
| **3** | Reachable and cheap: `exists_prime_gt` evaluated at a concrete `n`, with `minFac` naming the witness. **Not built as a certificate-producing routine** — `axeyum-cas`'s `is_prime` (`ntheory.rs:436`) returns a bare `bool` with no verifier (§2.8). |
| **4** | Not attempted. `ml430` mirrors exist in the ledger (514 `ml430` facts, 163 number-theory-flavoured). |

This is worth stating loudly because
[`03-destinations/number-theory.md`](03-destinations/number-theory.md) calls
"infinitely many primes" **Lean-horizon**, and it has been a kernel theorem for
some time. See §4.

### 2.2 Family: Fermat's little theorem / Euler's theorem

| Row | Status |
|---|---|
| **1** | **Half landed.** `Nat.pow_prime_modeq_self : ∀ p a, Prime p → a^p ≡ a (mod p)` (theorem, 0 axioms) — Fermat, general form. `Nat.add_pow_modeq_prime` (the freshman's dream, `(a+b)^p ≡ a^p + b^p`) is landed too, 0 axioms. **Euler's theorem `a^φ(n) ≡ 1 (mod n)` for coprime `a,n` is ABSENT** — positive controls of the same kind found by the same method: `Int.euler_criterion_pm_one`, `Int.euler_unit_coprime`, `Int.euler_unit_injective`. The two `euler_unit_*` lemmas are precisely the residue-permutation ingredients Euler's proof needs. |
| **2** | **None.** The classical proof permutes the residues mod `n` — a bijection of the *bounded* set `[0,n)`, whose constructive content is `Nat.countRange_permute` (landed). Nothing in it decides anything outside a finite range. |
| **3** | Modular exponentiation at fixed `p` ships in `axeyum-scenarios::number_theory` as a BitVec scenario validated by `self_check()`; it is a self-check, not a producer/verifier pair (§2.8). |
| **4** | Not attempted. |

**Highest-yield NT target.** Euler's theorem is one theorem away, with both
halves of the residue-permutation argument already landed and axiom-free.

### 2.3 Family: Euler's totient — *the strongest row 1 in the subject*

| Row | Status |
|---|---|
| **1** | **Landed, and unusually complete.** `Nat.totient_mul_of_coprime : gcd m n = 1 → φ(m·n) = φ(m)·φ(n)` and `Nat.totient_prime_pow : Prime p → φ(p^(k+1)) = p^(k+1) − p^k` (both theorems, 0 axioms), plus 12 more `Nat.totient_*`. Notably `totient_mul_of_coprime` goes through a CRT bijection over `countRange_permute` — **no Bézout witness and no factorization**. |
| **2** | **None.** Same shape as §2.2: a bijection of `[0,mn)`. |
| **3** | Not built as a certificate route. φ(n) from a factorization plus a verifier that re-derives it is assembly, not new mathematics — see §5. |
| **4** | `ml430` mirrors exist; two were repaired on `main` this session (`e79804fdd`). |

### 2.4 Family: unique factorization — *the row 2′ case*

| Row | Status |
|---|---|
| **1** | **Existence landed:** `Nat.exists_prime_factorization` (theorem, 0 axioms), via `prodRange f k`. `Nat.euclid_lemma` (`Prime p → p ∣ ab → p ∣ a ∨ p ∣ b`, 0 axioms) is the uniqueness half's engine and is landed. |
| **2′** | **Expressiveness, not decision.** No `List`/`Finset`/`Prod`/quotient — see §1.2(b). The multiset statement is unwritable; the multiplicity-agreement statement is writable today with `countRange_permute`. |
| **2** | **None** in the decision sense: nothing here needs an undecidable comparison. |
| **3** | Certified factorization of a fixed `n` with an independent verifier — **not built**. `Nat.minFac`/`minFacAuxMinimal` give the kernel side; `axeyum-cas`'s `factorize` (`ntheory.rs:459`) has no certificate (§2.8). |
| **4** | Not attempted. |

### 2.5 Family: Wilson's theorem — *complete row 1, both directions*

| Row | Status |
|---|---|
| **1** | **Landed both ways:** `Int.wilson`, `Int.wilson_converse`, `Int.wilson_iff` (theorems, 0 axioms). A biconditional row 1 is rare here and worth noting: it makes Wilson a *primality criterion*, not just a property of primes. |
| **2** | **None.** Finite pairing argument over `[1,p−1]`. |
| **3** | Wilson-based primality at fixed `n` — exact, decidable, and impractically slow, which is itself an honest row-3 entry: the decidable fragment is *correct*, not *fast*. |
| **4** | Not attempted. |

### 2.6 Family: quadratic reciprocity (Stein ch. 4) — *row 1 genuinely open*

| Row | Status |
|---|---|
| **1** | **Absent.** No reciprocity, Legendre or Jacobi declaration exists under any spelling tried (`reciproc`, `legendre`, `jacobi`, `quadratic_res`). Positive controls of the same kind, FOUND: `Int.euler_criterion_pm_one`, `Int.is_quadratic_residue`, `Int.is_quadratic_residue_mul`, `Int.is_quadratic_residue_one`. So the *criterion* is landed and the *reciprocity law* is not. |
| **2** | **None expected**, argued from shape: every classical proof (Gauss's lemma, Eisenstein's lattice count, Zolotarev) is a finite counting or pairing argument over `[1,(p−1)/2]`. Eisenstein's lattice-point count is a double `countRange`, which is the encoding this kernel already uses. |
| **3** | The Legendre symbol at fixed `p` is decidable by Euler's criterion, which is landed in the kernel, and `legendre_symbol`/`jacobi_symbol` already compute it (`ntheory_advanced.rs:145`, `:180`) — but with no witness type and no verifier, so this is a *cheap* row 3, not a built one (§2.8). |
| **4** | Not attempted. |

Reciprocity is the one item in `number-theory.md`'s "Lean-horizon" list that is
still honestly there. The other three are not (§4).

### 2.7 Family: the least-number principle — *the subject's only row 2*

| Row | Status |
|---|---|
| **1** | **Landed:** `Nat.least_divisor_search` (theorem, 0 axioms) — the bounded LNP, in exactly the `Or (found least) (none below bound)` shape a constructive least-element statement must take. `Nat.minFacAuxMinimal` is the same content for `minFac`. |
| **2** | **Not built, and it is the highest-value unbuilt row in this note.** `LNP ⟹ em`, per §1.2(a). Landing it makes number theory a *graded* subject rather than a flat one, and it is a stronger boundary than any analysis row 2 (full EM, not LLPO). |
| **3** | Bounded search *is* the decidable fragment; row 1 and row 3 coincide here. |
| **4** | Not attempted. |

### 2.8 Number theory's row 3 barely exists — and §1.3 says the whole argument rests on it

If the dominance argument for a decidable subject is "statement + executable +
re-derivable certificate under one trust anchor" (§1.3), then it is worth
knowing exactly how much of the certificate half exists. Surveyed this session
across `axeyum-cas`, `axeyum-solver` and `axeyum-scenarios`:

**What exists as a genuine producer/independent-checker pair:**

- `prove_lia_unsat_by_diophantine_certified` (`axeyum-solver/src/lia_gcd.rs:108`)
  with `check_diophantine_certificate` (`:172`) over a named
  `DiophantineCertificate` (`:250`). The checker "re-derives the combination
  from the *original* equalities and shares no code with the elimination that
  produced it" (`:243`), and the producer emits a certificate **only when its
  own independent checker accepts it** (`:100`). Kernel-reconstructed via
  `int_reconstruct/diophantine.rs:73`. This is integer-linear Diophantine
  solvability — Stein ch. 1 / Shoup ch. 4 material, and a real row 3.
- `int_euclidean_residue_refutation`
  (`axeyum-solver/src/quant_residue_cert.rs:49`), with a Lean leg at
  `int_reconstruct/euclidean_residue.rs:35` — Euclidean division.
- GF(2) polynomial irreducibility: `check_irreducible_certificate`
  (`axeyum-cas/src/gf2.rs:1785`) and an independent twin
  (`gf2_independent.rs:131`) — Shoup ch. 18–20 material.

**What does not, and the control that makes this a negative result rather than
an empty grep:** a sweep for `^pub fn verify_|^pub fn check_` across
`axeyum-cas/src/` returns **19 verifier functions** — in `mvt.rs`,
`extremum.rs`, `taylor.rs`, `real_algebraic.rs`, `partial_fractions.rs`,
`geometry_check.rs`, `telescoping_check.rs`, `gf2*.rs`, `sos/check.rs`,
`boolean_circuit.rs` — so the method finds verifiers where they exist. **Not
one of the 19 is number-theoretic.** The classical number-theory CAS is bare
computation with no witness type and no verifier:

| routine | file:line | returns |
|---|---|---|
| `is_prime` | `ntheory.rs:436` | a bare `bool` |
| `factorize` | `ntheory.rs:459` | factors, no certificate |
| `mod_inverse`, `crt`, `extended_gcd` | `ntheory.rs:397, 636, 332` | values only |
| `legendre_symbol`, `jacobi_symbol`, `sqrt_mod`, `discrete_log`, `solve_linear_congruence` | `ntheory_advanced.rs:145, 180, 290, 482, 368` | values only |

No Pratt, Pocklington or ECPP primality certificate exists under any spelling
(control: the same keyword grep locates the GF(2) certificate pair above).

And `axeyum-scenarios::number_theory` — the 11 families the curriculum cites —
is **BitVec-encoded SMT scenarios validated by `self_check()`** (SAT by witness,
UNSAT by bounded enumeration), never a `(witness, verifier)` pair. That is a
legitimate and useful artifact; it is not row 3 in ADR-0603's sense, and
`number-theory.md` currently presents it as the subject's testable core.

**So the honest position is:** number theory's row 1 is unusually strong and
almost entirely landed; its row 2 is provably empty in the analysis sense and
unbuilt in the one sense available to it (§2.7); and its row 3 — the axis §1.3
moves the dominance argument onto — exists for integer-linear Diophantine
solvability and essentially nowhere else. Saying that plainly is the price of
moving the axis, and it converts a vague "we should build row 3" into a
specific list: primality, factorization, CRT and the Legendre symbol each need
a witness type and a verifier that shares no code with the producer.

---

## 3. Linear algebra (Boyd–Vandenberghe) — the type-theory verdict

The brief for this lane asked whether Boyd–Vandenberghe's `computable` tag
survives contact with the kernel's type theory, given no `List`, no `Finset`
and no product type, and asked for a plain answer if it does not.

**It survives, and the premise is already refuted by a landed declaration.**
Measured:

    Rat.dotN : (Nat → Rat) → (Nat → Rat) → Nat → Rat            definition, 0 axioms

    Rat.dotN_cauchy_schwarz :                                    theorem, 0 axioms
      ∀ (u v : Nat → Rat) (n : Nat),
        Rat.le (dotN u v n * dotN u v n) (dotN u u n * dotN v v n)

with `dotN_comm`, `dotN_add_left`, `dotN_smul_left`, `dotN_self_nonneg`,
`dotN_zero`, `dotN_succ`, `dotN_two` — bilinearity, symmetry, positive
semidefiniteness and the recursion equations, all 0 axioms.

That is a **general-dimension inner product space over ℚ, with Cauchy–Schwarz
at arbitrary `n`, in the kernel today**. A vector of dimension `n` is
`(v : Nat → Rat, n : Nat)`. No list, no finset, no product type is involved —
it is the same finite-function encoding number theory already uses for
`prodRange` in `exists_prime_factorization`.

The two-index level is load-bearing too. 63 declarations take a
`Nat → Nat → Rat`, including:

    Rat.sumRange_swap : ∀ (f : Nat → Nat → Rat) (m n : Nat),          0 axioms
      Σ_{i<n} Σ_{j<m} f i j  =  Σ_{j<m} Σ_{i<n} f i j

    Rat.sumRange_diagonal, Rat.sumRange_rect_eq_diag_add_corner,
    Rat.mul_sumRange, Rat.sumRange_congr

`sumRange_swap` is exactly the interchange that matrix-product associativity
needs, so `(AB)C = A(BC)` at symbolic dimension is **assembly**, not new
mathematics — the same shape MVT's row 3 had.

### 3.1 What genuinely does not survive: equality of vectors

`funext` is **ABSENT** (positive control of the same kind, FOUND: `congrFun'`,
the other direction). So two pointwise-equal functions are not propositionally
equal, and that has a precise consequence:

- A statement whose **conclusion is a scalar** is fine, which is why
  `dotN_cauchy_schwarz` was reachable at all.
- A statement whose **conclusion is a vector or matrix equation** —
  `(AB)C = A(BC)`, `(AB)ᵀ = BᵀAᵀ`, `A·A⁻¹ = I` — cannot be stated as `Eq` of
  functions. It must be stated **pointwise**: `∀ i j, i < m → j < n → …`.
- Likewise every uniqueness statement ("the solution of `Ax = b` is unique")
  must be pointwise agreement, not function equality.

This is not a workaround invented here; it is the shape `Rat.sumRange_congr`
already uses (it takes pointwise equality as a hypothesis and returns equality
of sums). The honest bound is therefore: **general-dimension linear algebra is
available, stated pointwise; extensional statements about the vectors
themselves are not.**

Two smaller notes, both measured: `Nat.Fin` *does* exist as a genuine dependent
inductive (`Nat.Fin`, `.mk`, `.val`, `.isLt`, `.rec`, `.val_mk` — 6
declarations), so an index type is available if a lane wants bounds carried in
the type rather than as hypotheses; and `Nat.Pair` exists as a monomorphic
ℕ×ℕ (9 declarations). Neither is polymorphic.

### 3.2 What is actually built — and it is fixed-dimension

Despite the encoding being available, **every determinant declaration in the
kernel is fixed-size with entries passed as separate scalar arguments**:

- `Rat.det2` + `det2_mul` (multiplicativity), `det2_id`, `det2_swap_rows`,
  `det2_scale_row`, `det2_row_add`, `det2_eq_zero_of_lin_dep`, `det2_fib`;
- `Rat.det3` + `det3_cofactor_row1`, `det3_id`, `det3_scale_row`,
  `det3_ofInt`, and three worked examples.

16 declarations, all 0 axioms. The fact
`F-determinant-multiplicative-over-constructed-rationals` states `det(AB) =
det A · det B` by writing out all eight entries.

Separately, `CPoint` is a **116-declaration 2-D inner-product space over
`CReal`** — `dot`, `cross`, `distSq`, `dot_self_zero_iff`, `cauchy_schwarz`,
centroid/circumcentre/Euler-line geometry. It is the most developed linear
algebra in this repository and
[`03-destinations/linear-algebra.md`](03-destinations/linear-algebra.md) does
not mention the kernel at all (§4).

So the gap is **not a missing type**. It is that nobody has lifted the matrix
layer onto the `Nat → Nat → Rat` encoding that `sumRange_swap` and `dotN`
already sit on.

### 3.3 The families

**LA-1: determinant multiplicativity.**
Row 1 (general `n`) not built; blocked only on a matrix product over the
existing encoding and a recursive determinant (cofactor expansion is the
natural constructive definition — `det3_cofactor_row1` is the base case
already). Row 2: **none** — over ℚ every operation is decidable and
`Rat.le_total` is a theorem (§1.1). Row 3: **landed in the kernel at n = 2 and
n = 3** (`det2_mul`, the `det3_*` family, 0 axioms). The CAS computes it at any
size — `Matrix::determinant` (`axeyum-cas/src/matrix.rs:410`) and the
fraction-free `bareiss_determinant` (`:522`) — but **ships no certificate and
no verifier**, so the CAS side is exact computation, not row 3 in ADR-0603's
sense. Row 4: not attempted.

**LA-2: `Ax = b` solvability — the best row 3 in either subject.**
Row 1 (general `n`) not built. Row 2: **none**, same argument. Row 3 is the one
place a decidable subject already has the complete "statement + procedure +
certificate under one trust anchor" story that §1.3 moves the dominance
argument onto, and it is worth naming precisely because it is the template
everything else in this note should be measured against:

- **SAT side:** the model is replayed against the original query before it is
  returned (`axeyum-solver/src/lra.rs:226`, enforced at `:251`, failure path at
  `:334`).
- **UNSAT side, two independent re-checkers.** `simplex::feasible`
  (`simplex.rs:194`) returns Farkas multipliers over the input rows and
  **self-checks them before returning** (`:695`), with `check_farkas` (`:846`)
  as the standalone re-checker; separately `lra::FarkasCertificate::verify`
  (`lra.rs:499`) rebuilds the refutation from scratch. `simplex.rs:842` records
  that the two "verify differently" and share no helper.
- **Negative controls on the checker itself** exist, which is rare here:
  `check_farkas_accepts_valid_and_rejects_invalid` (`simplex.rs:1000`) and
  `farkas_holds_rejects_tampered_certificates` (`:1525`).
- **Kernel reconstruction:** `LraReconstructCtx::try_new_over_constructed_reals`
  (`reconstruct.rs:1987` — fallible-only by design) into
  `prove_unsat_to_lean_module` (`:2238`), gated by an explicit `False`-inference
  check (`lra_term_infers_false`, `:2026`).

Row 4: not attempted.

**LA-3: rank and linear independence.**
Row 1 not built (needs the matrix layer). Row 2: none. Row 3 partial —
`Rat.det2_eq_zero_of_lin_dep` is the 2×2 case, kernel-checked. The CAS has
`rref` (`matrix.rs:577`), `solve` (`:606`), `null_space` (`:666`) and `lu`
(`:709`), all exact, but **no `rank` function at all** (ABSENT; control:
`rref` matches 11 times in the same file) and no certificate layer over any of
them.

**LA-4: inner-product geometry.**
Row 1 **landed at general dimension over ℚ** (`Rat.dotN` family, Cauchy–Schwarz
included) and **at dimension 2 over `CReal`** (`CPoint`, 116 declarations).
Row 2: none. Row 3: the `CPoint` geometry facts in the ledger. This family is
in much better shape than any curriculum document says.

**LA-5: least squares / normal equations (BV Part III).**
Correctly `✗ horizon` in `source-tocs.md` for the *numerical* content. But the
exact normal-equations identity at symbolic dimension is now within reach given
`dotN`'s bilinearity plus `sumRange_swap`, so the `◐` in that row is if
anything conservative.

---

## 4. What should change in `docs/curriculum/`

Made in this commit:

1. **`03-destinations/number-theory.md` — the "Lean-horizon" paragraph is
   wrong.** It names four universal theorems as out of reach: *infinitely many
   primes*, *FTA in general*, *Fermat/Euler for all a*, *quadratic
   reciprocity*. Measured against the kernel, **three of the four are landed,
   axiom-free**: `Nat.exists_prime_gt`/`Int.euclid_infinitude`,
   `Nat.exists_prime_factorization` (existence half; uniqueness is row 2′,
   §2.4), and `Nat.pow_prime_modeq_self` (Fermat; Euler's theorem itself is
   genuinely absent). Only quadratic reciprocity is still correctly listed.
   Rewritten with the declaration names and a pointer here.

2. **`03-destinations/linear-algebra.md` — under-claims by omitting the
   kernel.** It describes only fixed-size scenario/solver content and does not
   mention `Rat.dotN` (general-`n` Cauchy–Schwarz), the `Rat.det2`/`det3`
   families, or `CPoint`'s 116 declarations. Its "Lean-horizon" line
   ("anything quantifying over all dimensions") is **half wrong**: general
   dimension is reachable for scalar-valued conclusions and is already used.
   Added a kernel section and the funext bound.

3. **`foundational-books/source-tocs.md` — its tags answer a different
   question than a graded family asks.** ✅/◐/✗ classify chapters by what the
   *solver* can decide at fixed instances, i.e. **row 3 only**. That taxonomy
   has no way to say "row 1 landed as a general kernel theorem", so
   `Nat.totient_mul_of_coprime` — general, axiom-free — sits under a chapter
   tagged ◐ *"fixed `n`"*. Added a lens note and a row-1 column of
   cross-references rather than re-tagging, since the existing tags are
   correct for what they measure.

4. **`DEPTH.md` — the number-theory row of the honest-comparison table**
   ("GCD/Bézout, CRT, residues, modular inverses, fixed-modulus exponentiation,
   parity … not analytic or general algebraic number theory") predates the
   kernel's general theorems and reads as a ceiling that has moved. Amended to
   separate the scenario layer from the kernel layer, which is the distinction
   DEPTH.md's own "three coverage layers" section already draws but does not
   apply to this table.

Not made, and deliberately left for a lane with the mandate:

5. **`curriculum.toml`** is untouched. The right change is a fourth status
   value distinguishing "a decidable exercise exists" from "a general kernel
   theorem exists" — today both read `covered`, which is why `number-theory`
   and `linear-algebra` look identical in the map while their kernel content
   is very different. That is a schema change with a validator, an
   `axeyum-scenarios::mathtour` mirror and an acyclicity gate behind it, and it
   should be proposed as its own ADR rather than smuggled in here.

---

## 5. Three targets a lane could start tomorrow

Ordered by yield per unit of work. Each names what already exists, so a lane
does not re-derive it — the retrieval failure
[`2026-08-27-retrieval-is-the-bottleneck.md`](../research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md)
measures as the binding constraint.

### (1) `Nat.lnp_unrestricted_implies_em` — number theory's only row 2

The single highest-value item in this note: it converts number theory from a
flat subject into a graded one, and lands a **stronger** boundary than any
analysis row 2 (full EM, not LLPO).

Already in the kernel: `Nat.least_divisor_search` and `Nat.minFacAuxMinimal`
(the bounded LNP, showing the row is non-vacuous — mandatory for this shape per
ADR-0603 Am. 2); `Nat.lt_or_ge` and `Nat.le_total` for the case split;
`em_of_dne`, `not_not_em`, `Decidable.em` as the surrounding logic layer;
`CReal.evt_attained_max_decides_sign` as the worked template for the whole
declaration shape.

Not in the kernel: any unrestricted `em` (verified ABSENT against the controls
above), which is what makes the reduction a boundary rather than a triviality.

Size: one declaration plus a non-vacuity control, in `nat_prelude/`. The proof
sketch in §1.2(a) is complete. **Note four sibling lanes are in `nat_prelude/`
— coordinate before starting.**

### (2) Euler's theorem, `a^φ(n) ≡ 1 (mod n)` for `gcd(a,n) = 1`

Completes §2.2's row 1 and is the natural capstone of the totient work that
landed today.

Already in the kernel, all 0 axioms: `Int.euler_unit_coprime` and
`Int.euler_unit_injective` — the residue-permutation ingredients; the whole
`Nat.totient_*` family (14 declarations) including `totient_mul_of_coprime` and
`totient_prime_pow`; `Nat.countRange_permute` (the reindexing lemma that made
`totient_mul_of_coprime` work without Bézout); `Nat.pow_prime_modeq_self` as
the prime-modulus special case to check against; `Nat.crt_unique`.

Verified absent: `Nat.euler_theorem` / `pow_totient` under any spelling
(controls: the three `Int.euler_*` above, FOUND).

Size: one theorem over a landed permutation argument. Row 2: none, argued from
shape (§2.2).

### (3) The matrix layer over `Nat → Nat → Rat`

Unlocks LA-1, LA-2 and LA-3's row 1 simultaneously, and is the difference
between "linear algebra is fixed-size here" and "linear algebra is general
here".

Already in the kernel, all 0 axioms: `Rat.dotN` with its full bilinear /
symmetric / PSD / Cauchy–Schwarz family — **the proof that the encoding carries
general-dimension theorems**; `Rat.sumRange_swap` (the double-sum interchange
matrix associativity needs); `Rat.sumRange_congr`, `Rat.mul_sumRange`,
`Rat.sumRange_diagonal`; `Rat.det2`/`det3` and their 14 lemmas as the
fixed-size cases any general definition must reduce to; `Nat.Fin` if a lane
wants indices bounded in the type.

The one design constraint, and it must be respected from the first
declaration: **`funext` is absent, so state every matrix identity pointwise**
(`∀ i j, i < m → j < n → …`), never as `Eq` of functions (§3.1). Getting this
wrong produces an `UnboundFVar`- or `TypeMismatch`-shaped failure a long way
from its cause.

Size: a new file. `matMul` plus pointwise associativity is the first slice and
is assembly over `sumRange_swap`, not new mathematics.

---

## Corrections this note makes to its own working assumptions

Recorded because each was wrong in the direction that would have produced a
weaker or false deliverable, and the correction came from a measurement rather
than from re-reading:

1. **"This kernel has no `Fin`."** It has `Nat.Fin`, a genuine dependent
   inductive with `val`/`isLt`/`mk`/`rec` (6 declarations). What it lacks is a
   *polymorphic* `Fin`, `List`, `Finset` and `Prod`.
2. **"Linear algebra needs a type this kernel does not have."** Refuted by
   `Rat.dotN_cauchy_schwarz` — general dimension, 0 axioms, landed. The
   near-miss is instructive: `Rat.dot` returns **0** matches and `Rat.dotN`
   returns **9**, so a name-shaped search reports the subject as absent. Found
   by searching for the mathematical *shape* instead, which is the technique
   the retrieval note prescribes.
3. **"Number theory has no row 2 at all."** Too strong. It has no row 2 of the
   *analysis* kind (§1.1, measured), and exactly one of a different kind
   (§1.2(a)), which is more valuable than the ones it lacks.
