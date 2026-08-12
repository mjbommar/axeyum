# Route C — the first machine-checked mathematics in axeyum's own Lean kernel

**Date:** 2026-08-12 · **Deliverable:** `crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs`
(new file, uncommitted) · **Evidence trail:** `route-c/LOG.md` (append-only lab notebook)

The Rado paper states that axeyum's in-tree Lean kernel "took no part in this
work." That is no longer true. This report says exactly how much is now true,
and no more.

**Headline:** four theorems and one bridging lemma about the shell
construction's arithmetic — each a `∀`-quantified statement over ℕ, i.e. an
infinite family — are now checked by `axeyum-lean-kernel`, **resting on zero
axioms**. The target level reached is **C2** (genuine induction), plus the
statement in the construction's own notation. **C3 was not reached**, and the
reason is *not* a kernel limitation; it is a missing library, measured
concretely below.

---

## 1. The kernel's capability boundary, as measured (not as documented)

Everything in this section was executed, not read off a doc comment.

### 1.1 What the kernel does support

| Capability | Measured how | Result |
|---|---|---|
| User-declared inductive types **with generated recursors** through the trusted gate | `add_inductive` for `Le` (1 param, 1 index, 2 ctors) | **Yes.** The kernel generated `Le.rec` itself, with ι-rules, and `infer`-checked it. |
| Structural recursion as `Definition`s, computing under `def_eq` | `rado.{add,mul,pow,geo,geo1,shellT,nshell}` defined by `Nat.rec`; checked `pow 3 3 ≡ 27`, `nshell 4 3 2 ≡ 312` | **Yes**, and δ/β/ι does a large share of the proof work: `f x 0` and `f x (succ j)` equations are `rfl`, no equation lemmas needed. |
| Induction into `Prop` from a `Type`-valued inductive (`Nat.rec.{0}`) | every lemma below | **Yes**, no large-elimination restriction on `Nat`. |
| Induction **on a derivation** of an indexed `Prop` relation | `le_succ_succ` via the generated `Le.rec` | **Yes.** |
| Prop/large-elimination discipline applied automatically | generated `Le.rec` has motive codomain fixed at `Prop` and **no** universe parameter; `Exists.rec` likewise | **Yes** — the kernel imposed the restriction unprompted. |
| Existential introduction **and** elimination | `dvd a n := ∃ q, n = a·q`; proved `a ∣ a·q` and `a ∣ m → a ∣ n → a ∣ (m+n)` | **Yes.** |
| Export to a self-contained real Lean module | `render_lean_module_compact_with_inductives` | **Yes**, 42 146 bytes, real `inductive AxNat`/`Eq`, ends with `#print axioms`. **Not run through Lean** — no toolchain on this box (see §6). |

### 1.2 What the kernel does *not* give you

These are all **library** gaps, not expressiveness gaps — each is definable with
the machinery in §1.1, none required an axiom:

- **No tactic layer, no elaborator, no unifier.** Every argument is explicit,
  including every `Eq.rec` motive. There is no `simp`, no `ring`, no `omega`,
  no implicit-argument inference, no proof search beyond `def_eq`.
- **No `Eq.symm`, `Eq.trans`, `congrArg`.** They are not in any prelude; I built
  all three out of `Eq.rec`. (`axeyum-solver`'s `reconstruct/arithmetic.rs` has
  the same combinators over the axiomatized `R` carrier — I ported the pattern
  to `Nat`.)
- **No arithmetic library whatsoever over `Nat`.** No `+`, `*`, `^`, no
  commutativity, no distributivity. I proved twelve lemmas from scratch
  (`zero_add`, `succ_add`, `add_comm`, `add_assoc`, `add_right_comm`, `zero_mul`,
  `succ_mul`, `mul_comm`, `mul_one`, `one_mul`, `left_distrib`, `mul_assoc`).
- **No order, no subtraction, no division, no `gcd`, no valuations, no
  `Decidable`, no `min`, no finite sets or intervals.**
- **No well-founded recursion helper** (`Acc`/`WellFounded` are not in the
  preludes, though the docs say `Acc`-shaped recursion is admissible).
- The **arithmetic prelude is axiomatic**: `build_arith_prelude` is a linear
  ordered field with **30 `Declaration::Axiom`s** (`build_int_prelude`: 34;
  string: 1 — counts asserted by the repo's own
  `examples/prelude_axiom_inventory.rs`). It has no induction and no naturals.
  **I deliberately did not use it** — see §3.

### 1.3 The one thing that genuinely surprised me

`build_logic_prelude` already contains **`Nat` as a real recursive inductive with
a real `Nat.rec`**, admitted through the same public trusted gate. The brief
anticipated that the only arithmetic on offer was the axiomatized ordered field.
It was not. That single fact is what moved this work from C1 ("state arithmetic
facts over 30 axioms") to C2 ("prove them over none").

---

## 2. What is now machine-checked

All statements are `Pi`-telescopes over `AxNat` (the prelude's `Nat`; the
pretty-printer renames it to avoid colliding with Lean core). Rendered forms are
in `LOG.md` Entries 2–3 verbatim; here they are in ordinary notation.

| Name | Statement | How proved |
|---|---|---|
| `solution_family` | `∀ a b y t, a·(y + b·t) = a·y + b·(a·t)` | equational; the **sufficiency** half of the brief's solution-form lemma: every `x = y + b·t`, `z = a·t` solves `E(a,b)`. |
| `defect_identity` | `∀ a b, a·(a·b·b + 1) = a·1 + b·(a·a·b)` | equational. In ℕ the Rado equation `a(x−y) = bz` is `a·x = a·y + b·z`; with `y=1`, `x=a·b²+1`, `z=a²·b` this is exactly the brief's closed-form defect family — proved for **all** `a,b`, not the four enumerated points. |
| `geo_closed_form` | `∀ a k, a·G(a,k) + 1 = G(a,k) + a^k`, `G(a,k) = Σ_{i<k} aⁱ` | **induction on `k`** (`Nat.rec`). The subtraction-free form of `(a−1)·G = a^k − 1`. |
| `shell_closed_form` | `∀ a m, T(a,m) = a^(m+1) + 2·(a·G(a,m))` where `T(a,0)=a`, `T(a,m+1)=a·T(a,m)+2a` | **induction on `m`**, using `geo_closed_form` in the step. |
| `geo_shift` | `∀ a m, a·G(a,m) = Σ_{i=1..m} aⁱ` | induction on `m`. |
| `nshell_closed_form` | `∀ a b m, N(a,b,m) = b·(a^(m+1) + 2·(a·G(a,m)))` | congruence from `shell_closed_form`. |
| `nshell_paper_form` | `∀ a b m, N(a,b,m) = b·(a^(m+1) + 2·Σ_{i=1..m} aⁱ)` | the brief's `N = b·(a^(k−1) + 2(a^(k−2)+…+a))` **verbatim**, with `m = k−2`. The ellipsis is not hand-waved: `Σ_{i=1..m} aⁱ` is `rado.geo1`, defined by structural recursion. |

Plus, from the capability probes: `zero_le`, `le_succ_succ`, `dvd_mul`,
`dvd_add`.

**What this means for the mathematics.** `shell_closed_form` / `nshell_paper_form`
prove that the shell's *level-capacity recurrence* and its *closed-form size* are
the same number, for every `a` and every `k` — a lemma the construction's
write-up needs, previously only checked at points. `defect_identity` proves the
`b = a+1` counterexample family really satisfies `E(a,b)` for every `a,b`, which
upgrades "verified at a=2,3,4,5" to a theorem. **Neither is the conjecture.**
Solution-freeness of the shell colouring remains unproved and unattempted here.

### Anti-vacuity: the definitions compute the brief's measured numbers

Checked by the kernel's own `def_eq` (δ/β/ι), not by a Rust evaluator:
`pow 3 3 ≡ 27`, `geo 3 3 ≡ 13`, `geo1 3 3 ≡ 39`, `shellT 3 1 ≡ 15`,
`nshell 3 2 1 ≡ 30` (brief row (3,2,3): N+1 = **31**), `nshell 4 3 1 ≡ 72`
(row (4,3,3): **73**), `nshell 3 2 2 ≡ 102` (row (3,2,4): **103**),
`nshell 4 3 2 ≡ 312` (row (4,3,4): **313**). With two negative reduction
controls: `nshell 3 2 2 ≢ 103` and `pow 3 3 ≢ 26`.

---

## 3. The complete axiom list

> **Zero.**

Measured, not asserted: the test `the_development_declares_no_axioms` walks
`kernel.environment()`, filters `Declaration::Axiom`, and prints the population:

```
axiom population: []
```

The generated Lean module likewise contains no `axiom ` line and ends with
`#print axioms shell_closed_form` for an independent audit.

This was a deliberate choice. The obvious route — the brief's own C1 — was to
work over `build_arith_prelude`'s ordered field, which would have put **30
axioms** under every theorem. Over the prelude's inductive `Nat` the same
statements are provable outright, and the Rado equation lives over ℕ anyway
(`x, y, z ∈ [1,n]`), written without subtraction as `a·x = a·y + b·z`.

**What is trusted instead of axioms** (stated plainly, because "zero axioms" is
not "zero trust"):

1. **The kernel implementation itself** — type checker, strict-positivity gate,
   recursor generator, `def_eq`. Trusted Rust code, not a verified artefact.
   (The repo cross-checks it against real Lean in CI via
   `tests/real_lean_*_crosscheck.rs`; I did not run those — no Lean here.)
2. **Inductive declarations**: `AxNat`, `Eq`, `Exists` (prelude) and `Le` (mine),
   each admitted through `add_inductive`.
3. **My definitions**: `rado.{add, mul, pow, geo, geo1, shellT, nshell, dvd}` —
   definitions with values, not assumptions. Their computational content is
   pinned by the numeric checks in §2.

I considered and **rejected** two axioms, both logged at the moment of decision
(`LOG.md` Entry 3): Gauss's lemma (which would have made the solution-form
*necessity* half a one-liner — and would have been a fraud, since it is
essentially the content of the statement), and an axiomatized `≤` (which probe 1
shows is definable, so axiomatizing it would have been laziness with a soundness
cost).

---

## 4. Negative controls — the kernel rejects broken proofs

Seven deliberate breakages, seven rejections, zero acceptances. Full verbatim
messages are in `LOG.md`; three representative ones:

**NC1 — a correct proof against a false statement.** The `defect_identity`
derivation, presented as a proof of `a·(a·b²+1) = a·1 + b·(a·a)` (a factor of
`b` dropped from `z`; false at `a=b=2`: 18 ≠ 10):

```
DeclarationValueMismatch
  declared : … ((rado.add ((rado.mul x0) (AxNat.succ AxNat.zero)))
                ((rado.mul x1) ((rado.mul x0) x0)))
  inferred : … ((rado.add ((rado.mul x0) (AxNat.succ AxNat.zero)))
                ((rado.mul x1) ((rado.mul ((rado.mul x0) x0)) x1)))
```
The rejected declaration never entered the environment (asserted separately).

**NC2 — two arguments swapped in a lemma application** (`mul_assoc b a a` where
`mul_assoc a a (b·b)` is required), inside an otherwise-correct chain:

```
TypeMismatch
  expected : Eq AxNat ((a*a)*(b*b))  (a*(a*(b*b)))
  got      : Eq AxNat ((b*a)*a)      (b*(a*a))
```

**NC3 — a broken induction**: the successor step returns the induction
hypothesis itself (proves `P j`, not `P (succ j)`):

```
TypeMismatch
  expected : Eq AxNat (add zero (succ _fvar.2)) (succ _fvar.2)
  got      : (fun x0 => Eq AxNat (add zero x0) x0) _fvar.2
```

Also: **NC4** `mul a b = add a b` with an `Eq.refl` proof → rejected (this is
simultaneously the control on `def_eq` — the kernel does not consider `mul` and
`add` definitionally equal); **NC5** a *true but not-thereby-proved* transposed
conclusion (`pow + geo` for `geo + pow`) with the unmodified proof term →
rejected, i.e. the kernel checks the term, not the intent; **NC6** `Le (succ n) n`
from `Le.refl n` → rejected; **NC7** `a ∣ m·n` from the `dvd_add` proof →
rejected.

---

## 5. Test name and passing output (nonzero count)

```
$ export CARGO_BUILD_JOBS=1
$ cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic

running 9 tests
test capability_probe_indexed_prop_relation_and_its_recursor ... ok
test capability_probe_existential_divisibility ... ok
test kernel_checks_the_defect_family_identity ... ok
test kernel_checks_the_geometric_sum_closed_form ... ok
test export_probe_renders_a_real_lean_module ... ok
test kernel_checks_the_shell_size_closed_form ... ok
test the_development_declares_no_axioms ... ok
test definitions_compute_the_measured_shell_values ... ok
test kernel_rejects_broken_proof_terms ... ok

test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.47s
```

Supporting runs: `cargo clippy -p axeyum-lean-kernel --test rado_shell_arithmetic
-- -D warnings` → clean (after adding a documented module-level `allow` for
`too_many_lines` / `type_complexity`; the first pass emitted 7 warnings that
would have failed CI while `cargo test` looked green — logged).
`cargo test -p axeyum-lean-kernel --lib` → **199 passed**, so the crate is
unaffected.

Nothing was committed. One new file:
`crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs`.

---

## 6. What it would take to reach C3, concretely

C3 = a kernel-checked lemma from the shell construction's **correctness**
(solution-freeness) proof. The blocker is not the kernel — probes 1 and 2 show
the needed constructs are all admissible. The blocker is roughly one chapter of
a `Nat` library. In dependency order, with what I already have marked:

1. **Order.** `Le` as an indexed inductive — **done** (probe 1), with `zero_le`,
   `le_succ_succ`. Still needed: `le_trans`, antisymmetry, totality
   (`Le m n ∨ Le n m`, using the prelude's `Or`), and `Lt`.
   *~10 lemmas, all `Le.rec`/`Nat.rec` induction, no new kernel feature.*
2. **Cancellation / truncated subtraction.** `add_left_cancel` needs `succ`
   injectivity, i.e. a `pred` selector via `Nat.rec` plus `congrArg pred` — all
   expressible. `mul_left_cancel` (for `a > 0`) then needs order + case analysis.
   *This is the first real cost; it is what makes valuations usable.*
3. **Divisibility.** `dvd` via `Exists` — **done** (probe 2), with `dvd_mul`,
   `dvd_add`. Still needed: `dvd_trans`, cancellation forms, `dvd_antisymm`.
4. **Euclidean division and `gcd`.** Needs **well-founded recursion**: define
   `Acc`/`WellFounded` as inductives (the kernel's docs say `Acc`-shaped
   recursion is admitted; I did **not** probe this — the one item here whose
   feasibility I have not measured) or bound the recursion with a fuel parameter
   and prove the bound. Then Bézout / Gauss's lemma
   (`gcd(a,b)=1 ∧ a ∣ b·c ⟹ a ∣ c`) — what the *necessity* half of the brief's
   solution-form lemma needs.
5. **`a`-adic valuation.** State it relationally
   (`v(j) = e ↔ a^e ∣ j ∧ ¬(a^(e+1) ∣ j)`), so no division is required; then
   `v(a·j) = v(j)+1`, which needs step 2.
6. **The colouring and the case analysis.** `χ` needs `min`, interval
   membership, and case splits driven by `Or`-elimination on totality from step 1
   (there is no `Decidable` typeclass machinery here). Solution-freeness is then a
   case analysis over the colours of `x`, `y`, `z` with a valuation argument per
   branch.

Two smaller, genuinely reachable next steps if the goal is *visible* progress
rather than the full conjecture:

- **Range and monochromaticity of the defect triple.** With step 1 alone one
  could prove `a·b² + 1 ≤ N_shell(a, a+1, k)` for `k ≥ 3` and turn
  `defect_identity` into a kernel-checked statement that the shell colouring's
  defect *lies in range* — half of "the construction is defective for `b > a`".
- **The competing bound.** `a^k` vs `N+1` (the brief's table) are order facts
  about closed forms already proved; step 1 suffices.

**Recommended framing for the roadmap:** the kernel is ready; what axeyum lacks
for mathematical (as opposed to certificate-level) proof is a `Nat` library. The
twelve lemmas in this file are the first ~2% of it, and they are axiom-free.

---

## 7. Honest summary

- **Reached:** C2, plus the construction's size formula in its own notation.
- **Not reached:** C3. Not attempted: solution-freeness, tightness, the necessity
  half of the solution-form lemma. None of them were axiomatized to fake progress.
- **Axioms introduced:** none.
- **Independent verification:** the development is checked by
  `axeyum-lean-kernel` only. It exports to a self-contained Lean module
  (`route-c/shell_closed_form.lean`, 42 KB, no `sorry`, no `axiom`), but **no
  Lean toolchain exists on this machine**, so that module has **not** been
  checked by real Lean. That is the single most valuable next measurement, and
  it is one `lean shell_closed_form.lean` away for anyone who has the binary.
