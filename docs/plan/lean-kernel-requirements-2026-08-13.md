# Lean kernel requirements

Status: requirements specification — measured baseline, gap set, and exits

Date: 2026-08-13

Owner: axeyum-lean-kernel / axeyum-lean-import

Parent program:
[`lean-system-implementation-plan-2026-07-21.md`](lean-system-implementation-plan-2026-07-21.md)
· [`lean4-complete-parity-contract-2026-07-22.md`](lean4-complete-parity-contract-2026-07-22.md)

Precursor:
[`06-kernel-gap-analysis.md`](../prover-track/research/06-kernel-gap-analysis.md)
(2026-07-15, 719 lines)

---

## 0. Why this document exists

The Rado paper prompted the question "can the kernel check this theorem?" and
the first three answers given were wrong. Recorded here so the failure mode is
not repeated:

| Claim made | Reality | How it was caught |
|---|---|---|
| "The kernel has no `Int`" | `int_prelude.rs`, 839 lines, ADR-0042 | malformed grep; re-run with a working pattern |
| "Valuations are not the blocker" | true *only* of the rigidity defect induction; `thm:main` needs `v_a` as a total function/relation, exactly as ADR-0385 says | read the full dependency graph, not one proof |
| "`Acc`-shaped recursion is not implemented" | its *kernel* content (reflexive fields) landed in TL2.11–TL2.12; the **declaration** is still absent | ran the admission census |
| "`≤`-inversion and subtraction exist in `nat_prelude`" | they do **not**; the grep matched a doc comment listing them as absent | exact-name search |
| "9 kernel-checked theorems" | 9 Rust `#[test]` functions; **7** `∀`-theorems admitted; 14 in the export | read the source |
| "The roadmap note on the `Nat` library is stale" | **it is accurate.** ADR-0385:96 and `next-actions…:246` both correctly list inversion, subtraction and divisibility/valuations as missing | read them verbatim |
| "~312 is the numeral ceiling" | not a ceiling — 1,501 costs <1 ms; the paper's `N = 740`/`1500` compute in ~14 ms | executed a probe |
| — (not found at all) | **the real blocker: no two preludes compose; it panics** | executed a probe |
| — (not found at all) | **`Quot.sound` does not exist** — quotients compute but are not quotients | grep with positive control |
| — (not found at all) | **universe equality diverges from Lean 4** — axeyum decides an equality Lean rejects | executed a probe |
| — (not found at all) | the nanoda `Prop`-projection soundness bug was **not** inherited | executed a probe |

Seven of these were errors of *reading* rather than of judgement, and five came
from greps that matched prose. **Every one of the four load-bearing findings —
the composition panic, the missing `Quot.sound`, the universe divergence, and
the guarded projection — came from executing a probe or a grep with a positive
control, not from reading.** The requirement that follows is **R6.3**.

The standing rule from `CLAUDE.md` applies to this document too: *prefer a
measurement over a message, an exit status, or a comment — including the ones
you just wrote.* Every number below names the command that produced it.

This document specifies **requirements**, not a schedule. Sizing appears only
where a prior document already sized the item.

---

## 1. Method

Three classes of statement appear, always labelled:

- **MEASURED** — a command was run in this session and its output is quoted.
- **CITED** — taken from a committed document or generated dashboard, with path.
- **UNKNOWN** — not established. Never inferred from an adjacent fact.

Counts from generated dashboards are cited rather than re-derived, because those
dashboards are `--check`-gated in `scripts/check.sh` and re-deriving them by hand
is exactly how a stale number enters a document.

---

## 2. Measured baseline

### 2.1 Toolchain — all real-Lean evidence is locally inert

**MEASURED.** `lean`, `lake`, `elan` are all absent on this host.

CI installs elan (`.github/workflows/ci.yml:182–190`) and gates the cross-checks
on `AXEYUM_LEAN_BIN`. Eight suites consult that variable and **skip** — they do
not fail — when it is unset:

```
crates/axeyum-lean-kernel/tests/real_lean_strict_positivity_crosscheck.rs
crates/axeyum-lean-kernel/tests/real_lean_nat_literal_crosscheck.rs
crates/axeyum-lean-kernel/tests/real_lean_inductive_crosscheck.rs
crates/axeyum-lean-kernel/tests/real_lean_structure_eta_crosscheck.rs
crates/axeyum-solver/tests/lean_crosscheck.rs
crates/axeyum-solver/tests/diophantine_lean_reconstruct.rs
crates/axeyum-solver/tests/int_inequality_lean_reconstruct.rs
crates/axeyum-solver/tests/regex_emptiness_lean_reconstruct.rs
```

97 `[skip]` markers exist across `crates/*/tests/*.rs`.

This is the **silent-inertness pattern** `CLAUDE.md` already names for the corpus
gate and `progress_frontier`: a green local run is not evidence that any
real-Lean differential ran. See **R0.1**.

### 2.2 Crate sizes

**MEASURED.** `axeyum-lean-kernel/src` has 15,770 lines across 15 top-level
Rust files (23,702 across all 23 Rust files including nested test modules);
`axeyum-lean-import/src` has 2,466 lines.

### 2.3 The preludes, and what is axiom versus theorem

This is the single most important distinction in the crate.

**MEASURED**, `grep -c "Declaration::Axiom"`:

| Prelude | Lines | Axiom decls | ADR |
|---|---:|---:|---|
| `nat_prelude.rs` | 1,824 | **0** | ADR-0385 / ADR-0389 / ADR-0390 / ADR-0391 |
| `int_prelude.rs` | 839 | 3 statements declaring 34 names | ADR-0042 |

`nat_prelude` is a genuinely *proved* development: `Nat` is a real inductive with
a real recursor, and the arithmetic is derived. `int_prelude` **axiomatizes** a
discretely-ordered commutative ring; it does not construct ℤ.

**MEASURED** — the complete integer axiom set (34 names):

```
Z, add, add_assoc, add_comm, add_le_add, add_lt_add_of_le_of_lt, add_neg,
add_zero, eq_em, euclidean_decomposition, le, le_of_lt, le_refl, le_total,
le_trans, left_distrib, lt, lt_irrefl, lt_of_le_of_lt, lt_of_le_of_ne,
lt_of_lt_of_le, lt_trans, mul, mul_assoc, mul_comm, mul_le_mul_of_nonneg_left,
mul_nonneg, mul_one, mul_zero, neg, no_int_between, one, zero, zero_lt_one
```

**MEASURED** — `nat_prelude` provides 6 definitions (`Nat.add`, `Nat.mul`,
`Nat.pow`, `Nat.sumRange`, `Nat.lt`, and `Nat.dvd`); one indexed `Prop` inductive `Nat.le` with
a kernel-generated recursor; and **27 checked theorems**: 8 defining equations,
5 additive, 7 multiplicative, 5 order, and 2 divisibility. Arithmetic
definitions recurse on the second argument, `lt n m` reduces to
`le (succ n) m`, and `dvd` reduces to an `Exists` witness proposition.

> **Correction.** An earlier pass of this document claimed `≤`-inversion and
> subtraction were present at that snapshot. Both were **absent then**. That
> grep matched the doc comment which listed them as absent, and
> `le_succ_succ` (forward monotonicity) was misread as
> `le_of_succ_le_succ` (inversion).
> At that snapshot, exact-name search confirmed the absence. ADR-0390 has since
> added `Nat.lt` and `Nat.le_of_succ_le_succ`; `Nat.sub`, `Nat.pred`,
> `Nat.le_antisymm`, and `Nat.le_total` remain absent.
>
> The current module contract says: *"No subtraction/predecessor, no
> antisymmetry, totality, `min`, or decidability of order, no quotient/remainder division, no
> `n ≠ succ n`-style discrimination."*
>
> This was the fourth grep-driven error in this workstream. See **R6.3**.

**MEASURED** — the logic prelude declares `True`, `False`, `Not`, `And`, `Or`,
`Iff`, `Eq`, `Exists`, `Bool`, `Nat`. It does **not** declare `Sigma`,
`Subtype`, or `Decidable`.

Consequence: `a ∣ b := ∃ k, a * k = b` is expressible today over the integer
prelude (`Exists` + `Eq` + `mul` are all present). Divisibility is not a missing
kernel capability; it is a missing *definition*.

### 2.4 The axiom ledger

**CITED**, `docs/plan/lean-axiom-ledger-v1.json` (`as_of` 2026-08-01), generated
by `cargo run -p axeyum-lean-kernel --example prelude_axiom_inventory`. Type
identity is the SHA-256 of `Kernel::render_lean(declaration.ty)`.

65 entries:

| Prelude | Classification | Discharge | n |
|---|---|---|---:|
| integer | derivable-theorem | planned | 4 |
| integer | external-assumption | retained | 22 |
| integer | primitive-interface | retained | 8 |
| real | derivable-theorem | planned | 3 |
| real | external-assumption | retained | 19 |
| real | primitive-interface | retained | 8 |
| string | primitive-interface | retained | 1 |

**Discrepancy to resolve (R6.1):** the parity contract §2 states "all 65
reconstruction-prelude assumptions remain semantically unclassified." The ledger
JSON carries classifications for all 65. The contract text (2026-07-22) predates
the ledger (2026-08-01). One of the two must be corrected; a reader today gets
opposite answers from two committed documents.

### 2.5 Kernel capability inventory

**MEASURED.** `cargo test -p axeyum-lean-kernel` → **306 passed, 0 failed**
across 23 binaries (206 of them `--lib`). Crate total 36,388 lines. Single
dependency `num-bigint`; `#![forbid(unsafe_code)]` (`lib.rs:52`).

**Term language** (`expr.rs:146-173`) — 10 of Lean 4's 12 constructors:
`bvar`, `fvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `lit`, `proj`.
**Missing: `mvar`, `mdata`** (0 hits with a positive control). Correct for a
kernel; blocking for an elaborator. Locally-nameless, hash-consed over a
64-shard interner, `ExprId(u32)` `Copy` handles.

**Universe levels** — `Zero`, `Succ`, `Max`, `IMax`, `Param`; **no `MVar`**.
`level.rs` is 46 lines only because the operations live in `lib.rs:481-769`:
normalization, substitution, and the full antisymmetric `leq_core` with
`leq_imax_by_cases` and the `IMax` distribution rewrites. Universe polymorphism
is real (`uparams` on every declaration, arity-checked). No universe
*unification* — correct scope.

**Definitional equality** (`tc.rs`, 2,089 lines) — beta, zeta, delta (with
lazy-delta height heuristics), iota, function eta, **structure eta**, **proof
irrelevance**, quotient reduction, projection reduction, Nat offset def-eq.
~45 `KernelError` variants, all returned rather than panicked.

**Inductives** (`inductive.rs`, 2,854 lines) — user declaration via
`add_inductive` / `add_mutual_inductive`; **strict positivity implemented** as a
preflight before provisional insertion (ADR-0352); recursor generation whose
generated type is itself `infer`-checked; parameters + indices; **mutual**
(ADR-0354) and **nested** (ADR-0355, bounded at 256 auxiliary families) groups;
**Lean-compatible `Prop` large elimination** via the syntactic-subsingleton rule
(ADR-0165). **K-like reduction: NOT present** (0 hits).

**Gaps that bear on this document:**

| Gap | Evidence | Consequence |
|---|---|---|
| **`Quot.sound` absent** | 0 hits, positive control passes; `PACKAGE_LEN = 4` (`quotient.rs:17`) — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` | Quotients **compute** but carry no propositional content. `r a b → Quot.mk r a = Quot.mk r b` is not available, so **ℤ cannot be constructed as a quotient of ℕ×ℕ today.** See **R2.1** |
| **All Nat literal arithmetic is inert** | `grep` for `Nat.add`/`mul`/`sub`/`div`/`decEq`/`gcd` fast paths in `tc.rs` → **0 hits**; `nat_literal_semantics.rs:190` asserts `Nat.add` stays inert | `Lit::Nat` is `BigUint` (ADR-0346), but only `succ`, one recursor literal layer, and offset def-eq reduce. All concrete arithmetic is **unary ι-reduction** |
| **Unary numerals** | `NatOps::num(n)` builds `succ^n zero` (`nat_prelude.rs:1416`) | 312 is the largest value *used* in `rado_shell_arithmetic.rs` — **not a ceiling**; measured directly in §2.6 Probe 3 |
| **String literals unsupported** | `Lit::Str` → `UnsupportedLit` (`tc.rs:1690`); ADR-0366 preregisters only | not on this document's path |
| **No `Decidable`, `Classical`, `propext`, `funext`** | 0 hits each | acceptable — all three Rado theorems are constructive (§3.4) |
| **No `Finset`, `Multiset`, intervals, `List`** | 0 hits each | required by `lem:structure(3)`; see **R4.5** |
| **No `Dvd` typeclass; constructive `Nat.dvd` foundation present** | `Nat.dvd := Exists (fun q => n = a*q)`, plus checked `dvd_mul` and `dvd_add` under ADR-0389 | transitivity/cancellation and congruence remain missing. See **R4.3--R4.4** |
| **`Acc` / `WellFounded` absent as declarations** | `Acc` 2 hits, both doc prose | the reflexive-field *shape* admits (Probe 2); nothing declares it |

**Export** (`lean_pp.rs`, 1,690 lines) emits **Lean 4 source text**, not the
lean4export format. `render_lean_module` produces a self-contained module opening
with `prelude` (avoiding clashes with Lean core) and appends
`#print axioms <name>` for auditing.

**Import** lives in a separate crate, `axeyum-lean-import` (5,925 lines
including tests): official `lean4export` NDJSON pinned at format `3.1.0`,
fail-closed, private staging kernel publishing only completed environments
(ADR-0348), ADR-0350 identity manifests, resource caps. **No `.olean` reader.**
No integration with `lean4lean` or `Trepplein` (0 hits).

### 2.6 Executed probes

#### Probe 1 — the preludes cannot coexist, and it panics

**MEASURED.** A scratch crate with a path dependency on `axeyum-lean-kernel`:

```rust
let mut k = Kernel::new();
build_arith_prelude(&mut k);   // ok
build_int_prelude(&mut k);     // panics
```

```
arith prelude: built
panicked at crates/axeyum-lean-kernel/src/prelude.rs:182:14:
  True should admit: DeclarationExists { name: NameId(1) }
R then Z in one kernel: PANIC
Nat then Int in one kernel: PANIC
```

Two findings:

1. The 2026-07-15 gap analysis reported this for ℝ + ℤ. **It also holds for
   ℕ + ℤ**, which was not previously recorded.
2. The collision is not the 28 shared arithmetic names. Every `build_*_prelude`
   re-builds the logic prelude and collides on `True` = `NameId(1)`. The trusted
   gate behaves correctly (`DeclarationExists`, a rejection, not a silent alias);
   the *library* then panics on that rejection via `.expect("True should admit")`.

The kernel is sound here. The prelude builder is not usable. See **R1.1**.

#### Probe 2 — reflexive inductives are now admitted

**MEASURED**, `crates/axeyum-lean-kernel/tests/strict_positivity.rs:14–15`:

```
current:         admit:360  recursive-indexed:0   reflexive:0    non-positive:270  invalid:210
TL2.11 baseline: admit:174  recursive-indexed:42  reflexive:144  non-positive:270  invalid:210
```

Reflexive declines went 144 → 0 and recursive-indexed 42 → 0; admissions
174 → 360. Non-positive (270) and invalid (210) still reject — the soundness
boundary held while the capability widened.

Per the gap analysis addendum, *"well-founded recursion's real kernel content is
`Acc.rec` — i.e. reflexive fields."* Those now admit. What remains absent is a
prelude that **declares** `Acc`/`WellFounded`, plus the elaborator-level
compilation that Lean performs before its own kernel ever sees a WF definition.

#### Probe 3 — unary numerals reach the paper's values comfortably

Because all Nat arithmetic is inert on literals (§2.5), every concrete value is
computed by ι-reduction over `succ^n zero`. The largest value in the existing
test is 312, which invited the inference that ~312 is a ceiling. **It is not.**

**MEASURED**, release build, one fresh `Kernel` per row:

| n | `def_eq (add n 0) n` | build | def-eq |
|---:|:--:|---:|---:|
| 50 | ✅ | 15 µs | 63 µs |
| 312 | ✅ | 57 µs | 236 µs |
| 741 | ✅ | 133 µs | 454 µs |
| 1501 | ✅ | 233 µs | 841 µs |

Linear, and 1,501 costs under a millisecond.

The arithmetic actually behind the paper's `k = 4` row —
`N = b(a^{k−1} + 2Σ_{k−2})`, i.e. `4·(5³ + 2·30) = 740` and
`5·(6³ + 2·42) = 1500`:

| computation | result | time |
|---|---:|---:|
| `pow 5 3` | 125 ✅ | 1.5 ms |
| `pow 6 3` | 216 ✅ | 2.2 ms |
| `pow 6 4` | 1296 ✅ | 11.8 ms |
| `mul 4 185` | 740 ✅ | 6.8 ms |
| `mul 5 300` | 1500 ✅ | 13.6 ms |

**Conclusion:** the numeral representation is *not* a blocker for stating or
checking the paper's closed-form arithmetic. It would become one for a
reflection route over the SAT search itself (hundreds of variables, combinatorial
enumeration), which is a different and much larger ask. See **R3.1**.

#### Probe 4 — the composition defect is broader than cross-theory

**MEASURED.** Calling `build_logic_prelude` and then `build_nat_prelude` on the
same kernel panics with the identical error as Probe 1. Every `build_*_prelude`
is monolithic: each re-declares the logic prelude, so **no two preludes compose
at all** — not merely ℝ+ℤ, and not merely across theories. This widens **R1.1**
from "namespace the arithmetic names" to "factor out the shared logic core and
make every builder idempotent."

#### Probe 5 — universe equality diverges from Lean 4 ⚠

Lean's kernel decides universe equality by **normalization**, and those rules are
**not complete** for `zero`/`succ`/`max`/`imax`. Trepplein and Carneiro's thesis
use case-splitting instead, which is *more* complete. ADR-0036 ports axeyum's
`leq_core` from nanoda, which follows that lineage.

Carneiro's own example (Zulip, *"rejected by leanchecker but accepted by
trepplein"*, May 2021) — `Sort (imax u (imax v w))` vs `Sort (imax (max u v) w)`:

**MEASURED:**

```
imax u (imax v w) == imax (max u v) w  : true
  Lean 4 says      : false (normalization is incomplete)
  trepplein/thesis : true  (case splitting)
  axeyum says      : true
=> DIVERGES FROM LEAN (more complete than the reference)
```

**This is not a soundness bug** — deciding *more* equalities cannot admit
`False`. It is a **conformance failure**, and it inverts the claim people
actually care about: *"axeyum checked it" does not imply "Lean would check it."*
A proof term axeyum accepts may be rejected by the official kernel.

The reference position is explicit: the conformance corpus records
*"Taking the official kernel as the specification, the answer is no"*. See
**R8.2**.

#### Probe 6 — the nanoda projection bug was **not** inherited

nanoda shipped a soundness bug (`nanoda_lib#8`, filed by nomeata):
`infer_proj` allowed projecting **data out of `Prop`**. Since axeyum ports from
nanoda, this is exactly the class of defect a port inherits.

**MEASURED: axeyum guards it.** `KernelError::ProjectionFromPropToType`
(`tc.rs:184`) is raised in **both** paths — the dependent-field loop
(`tc.rs:1750`) and the final field type (`tc.rs:1771`) — and it is tested
(`projection_inference.rs:360`).

Recorded as a positive result, and as the template for **R8.3**: shared ancestry
means every nanoda defect must be checked for explicitly, not assumed absent.

### 2.7 Programme status

**CITED**, `docs/plan/lean-system-implementation-plan-2026-07-21.md`, 123 rows:
**21 DONE, 5 PARTIAL, 1 WIP, 96 TODO**.

| Phase | DONE | PARTIAL | WIP | TODO |
|---|---:|---:|---:|---:|
| L0 contracts | 4 | 2 | | 2 |
| L1 importer | 5 | 1 | | 4 |
| L2 kernel breadth | 11 | 2 | 1 | 2 |
| **L3 libraries / trust closure** | | | | **12** |
| L4 elaborator | | | | 12 |
| L5 tactics | | | | 10 |
| L6 parser / macros | | | | 13 |
| L7 Lake / modules | | | | 10 |
| L8 LSP | | | | 10 |
| L9 compiler / runtime | | | | 13 |
| L10 mathlib ecosystem | 1 | | | 8 |

L0–L2 (contracts, importer, kernel breadth) are substantially complete.
**L3 is 0/12** — and L3 is the phase that supplies ℤ, `Dvd`, and finite sums
from an imported library rather than from hand-written axioms.

**CITED**, `docs/plan/generated/lean-compatibility.md` (generated; `--check`-gated):

| Profile | Meaning | Satisfied | Total |
|---|---|---:|---:|
| K0-checker | independent checker | 1 | 1 |
| K1-import | versioned declaration import | 5 | 5 |
| K2-source | native parsing + elaboration | 0 | 2 |
| K3-proof | goals and checked tactics | 0 | 1 |
| K4-workflow | project and editor | 0 | 1 |
| K5-runtime | evaluator / compiler | 0 | 1 |
| K6-ecosystem | pinned mathlib | 0 | 1 |

The complete-parity registry reports **zero** complete U0–U9 authorities, **zero**
complete A0–A11 axes, and zero satisfied terminal gates. That is deliberate: the
terminal denominator is explicit so that bounded evidence is not promoted.

### 2.8 Pinned upstream

**CITED**, roadmap completion audit §4:

- Lean `v4.30.0` @ `d024af099ca4bf2c86f649261ebf59565dc8c622`
- `lean4export` `v4.30.0` @ `a3e35a584f59b390667db7269cd37fca8575e4bf`, format `3.1.0`
- Mathlib `v4.30.0` @ `c5ea00351c28e24afc9f0f84379aa41082b1188f` —
  8,606 `.lean` files, 8,094 under `Mathlib/`

---

## 3. Driving requirement: what the Rado theorems need

The paper is the first concrete consumer that exceeds the kernel's reach, so its
dependency graph is used here as the requirement driver. Nothing in this section
is specific to Rado in the requirements it generates — order, divisibility,
valuation, intervals and finite sums are the same layer every future
formalization needs.

### 3.1 What is already kernel-checked — corrected

**MEASURED.** `cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic`
reports `9 passed`. **That 9 is a count of Rust `#[test]` functions, not of
theorems.** The development admits **7 `∀`-quantified theorems**
(`rado_shell_arithmetic.rs:700-707`), plus 4 more inside capability probes. The
Lean-syntax export carries **14** theorems (`shell_closed_form`'s transitive
closure only), which is what `\LeanTheorems` counts in the paper.

Zero axioms is real and mechanically enforced: `the_development_declares_no_axioms`
(`rado_shell_arithmetic.rs:841-866`) walks the environment, filters
`Declaration::Axiom`, and asserts the result is empty. There are also 7 negative
controls where deliberately broken proof terms are rejected (`:1323`).

The seven theorems:

| # | Name | Statement | Method |
|---|---|---|---|
| 1 | `solution_family` | `∀ a b y t, a·(y + b·t) = a·y + b·(a·t)` | equational |
| 2 | `defect_identity` | `∀ a b, a·(a·b·b + 1) = a·1 + b·(a·a·b)` | equational |
| 3 | `geo_closed_form` | `∀ a k, a·G(a,k) + 1 = G(a,k) + a^k` | induction on `k` |
| 4 | `shell_closed_form` | `∀ a m, T(a,m) = a^(m+1) + 2·(a·G(a,m))` | induction on `m` |
| 5 | `geo_shift` | `∀ a m, a·G(a,m) = Σ_{i=1..m} a^i` | induction on `m` |
| 6 | `nshell_closed_form` | `∀ a b m, N(a,b,m) = b·(a^(m+1) + 2·(a·G(a,m)))` | congruence |
| 7 | `nshell_paper_form` | `∀ a b m, N(a,b,m) = b·(a^(m+1) + 2·Σ_{i=1..m} a^i)` | 4 + 5 |

**Only two are load-bearing for the paper:**

- `geo_closed_form` ⇒ `eq:sigma`, used by `lem:gap`, `lem:size`, `prop:beat`.
- `shell_closed_form` / `nshell_paper_form` ⇒ the **second half** of
  `lem:structure(1)`, for a *recurrence-defined* `T(a,m)`. The equivalence of
  that recurrence to the paper's summation form `N = 2Σ_{i=2}^{k−1}L_i + L_k`
  is **not** proved. The **first half** (`c_i = bΣ_{i−1}`) is absent.

The rest is scaffolding, and one item is not in the dependency graph at all:
`defect_identity` proves a triple from an earlier draft (`x = ab²+1, y = 1,
z = a²b`), not the paper's `thm:sharp` witness `(N−ab+1, 1, a(N/b−a))`.

`solution_family` is `lem:solform`'s **sufficiency** direction only. The
necessity direction — the one every proof actually uses — is flagged in-source as
out of reach (`rado_shell_arithmetic.rs:369-370`).

The route report states the scope plainly
(`docs/plan/proof-approaches-2026-08-12/route-c/REPORT.md:91-96`):
*"**Neither is the conjecture.** Solution-freeness of the shell colouring remains
unproved and unattempted here."*

### 3.2 Cost order of the three theorems

**`thm:sharp` is by far the cheapest** and is the correct first target:

- no valuation machinery (`v(u)=1`, `v(Z)=2` are proved by explicit factoring);
- `gcd` is a standing hypothesis, never used in the proof;
- no induction;
- one explicit, closed-form witness.

Its hard parts are a re-indexed geometric sum after factoring `u = a·u'` (with an
empty-range corner at `k=3`), one signed rearrangement, and three colour
computations needing `a ∣ N`.

**`thm:main`** needs the full stack: `lem:val` (valuation of a difference),
`lem:solform` necessity (⇒ Gauss ⇒ Bézout ⇒ Euclidean division), `lem:gap`'s
rounding argument, and a fixed-depth case tree of 3 colour branches × up to 4
pair types.

**`thm:rigid`** transitively requires all of `thm:main` — but only through the
`M = N` half (`B_sharpness_proofs.tex:73`, "the canonical colouring is
solution-free by Theorem 1"). **The `M = N+1` half — the novel half — does not
depend on `thm:main`.** It needs `lem:width`, `prop:beat`, `lem:structure(5)`,
`eq:budget`, `def:shape`, and the defect induction. This makes the `M = N+1`
half a separable and much smaller target than the theorem as a whole. See
**R7.3**.

### 3.3 Where signedness is forced

- `thm:main`: **ℕ suffices** after reformulation. `a·x = a·y + b·z` is
  subtraction-free (already the kernel test's form,
  `rado_shell_arithmetic.rs:29-32`), and `lem:solform` gives `x > y` before any
  subtraction is used. Two rewrites are required: `eq:sigma` as
  `(a−1)Σ_m + a = a^{m+1}`, and `lem:val`'s bracket congruence restated
  positively.
- `thm:sharp`: one signed line (`N(a−b) ≤ a²b` with the left side ≤ 0 when
  `b > a`), dischargeable by a case split.
- `thm:rigid`: **ℤ is genuinely unavoidable.** `e_c := w_c − L_c` may be
  negative, `E_j` is a signed running total proved `≤ 0`, `E_{j−1} ≤ −1` is a
  strictly negative bound, and `E_{c−1} ≡ −1 (mod a)` is a congruence on a
  signed quantity. Alternative: re-encode as a ℕ-valued deficit `D_j := −E_j`
  with the trigger rewritten. See **R7.2**.

**This is what makes Probe 1 a hard blocker.** `thm:rigid` needs ℕ (shell
indices, cut vectors, counts) and ℤ (defects) in **one** environment. That
combination panics today.

### 3.4 Required capabilities, consolidated

| Capability | `thm:main` | `thm:sharp` | `thm:rigid` | Status |
|---|:--:|:--:|:--:|---|
| `≤` on ℕ, order lemmas | ✅ | ✅ | ✅ | partial (`nat_prelude`) |
| truncated subtraction / cancellation | ✅ | ✅ | ✅ | absent (`Nat.sub`/`Nat.pred`: 0 exact-name hits) |
| divisibility `a ∣ n` | ✅ | ✅ | ✅ | **probed working** (`dvd_mul`, `dvd_add` via `Exists`) |
| congruence mod `a` | ✅ | ✅ | **central** | absent |
| Euclidean division / division-with-remainder | ✅ (`lem:gap`) | ✗ | ✗ | absent |
| `gcd` + Bézout + Gauss | ✅ (`lem:solform` ⟹) | ✗ | ✗ | absent; needs WF recursion |
| `a`-adic valuation `v_a` | ✅ (as a total function/relation) | ✗ | only via `thm:main` | absent |
| `min` | ✅ | ✅ | ✅ | absent |
| finite sums `Σ`, powers | ✅ | ✅ | ✅ | partial (`geo`, `geo1`) |
| intervals, membership, partition | ✅ | ✅ | ✅ | absent |
| bounded induction over shell index | ✅ | minimal | ✅ | `Nat.rec` present |
| length-`(k−1)` monotone sequences | ✗ | ✗ | ✅ (cut vectors) | absent |
| signed arithmetic | reformulable | one line | **required** | axiomatized ℤ only |
| `Decidable` typeclass | not strictly | not strictly | not strictly | absent |
| classical logic / choice | **none** | **none** | **none** | n/a — all three are constructive |

All three theorems are **general in `(a,b)` and general in `k`**. Only `prop:k2`
is a fixed-`k` statement. Restricting to `k ∈ {3,4,5}` would remove
`lem:structure(1)`'s induction, the defect induction, the `T` sum in `lem:gap`,
and the cut-vector sequence type — but would **not** remove `(a,b)` generality,
`lem:val`, Gauss, or the `lem:gap` rounding argument.

### 3.5 The route report's own verdict

`route-c/REPORT.md:229-231`, and this document adopts it:

> "The blocker is not the kernel… The blocker is roughly one chapter of a `Nat`
> library."

Probe 2 corroborates: the expressiveness probes (an indexed `Prop` inductive
`Le` with a kernel-generated recursor; `dvd` via `Exists` with both intro and
elimination) succeeded. The kernel can *express* this mathematics. What is
missing is a **library**, plus the prelude-composition defect in Probe 1.

### 3.6 What the paper currently claims, and its one gap

**CITED**, `07_discussion.tex:21-27` and `proofs/README.md:75-77`: the
Lean-syntax export (14 theorems, no `sorry`, no axiom) **has never been checked
by real Lean**, because `lean`/`lake`/`elan` were absent on the producing
machine — still true here (§2.1). The paper states this. See **R0.2**.

## 4. Lean 4 conformance

### 4.1 The specification is the official kernel, including its incompleteness

The single most important conformance rule, and the least intuitive:

> **Matching Lean means matching what Lean *rejects*, not only what it accepts.**

Lean decides universe equality by normalization; those rules are provably
incomplete. Trepplein and Carneiro's thesis case-split and are more complete.
The conformance corpus resolves this against Lean: *"Taking the official kernel
as the specification, the answer is no."*

**axeyum currently fails this** (§2.6 Probe 5). It inherits the trepplein
position through nanoda. This is a live divergence, not a hypothetical.

### 4.2 The export format

`lean4export` **NDJSON, format 3.1.0** (`a6a63ccb0`, 2026-02-03) is what axeyum
pins, and it is current. History: text `0.1.2` → text `2.0.0` (2025-06-02) →
NDJSON `3.0.0` (2026-01-16) → `3.1.0`. There is no 1.x. The move to NDJSON was
driven by name-escaping — the text encoding was *"a classic SQL injection
attack"* (`lean4export#3`).

Details that bite implementers, and which axeyum already gets right:

- `natVal` serializes as a **string**, not a JSON number — arbitrary precision.
  This matches ADR-0346's `BigUint` choice.
- Ordering is topological and mandatory; forward references and duplicate
  declaration names must hard-fail. **MEASURED:** axeyum's importer rejects
  forward/missing name, level and expression references (`lib.rs:305,315,325`);
  duplicate declaration names are caught one layer lower, at the trusted gate,
  as `DeclarationExists` — fail-closed by a different mechanism, not a gap.
- `names[0]` is the anonymous name and `levels[0]` is universe zero; **neither
  is emitted**, so a reader must initialize them. **MEASURED:** axeyum does
  (`lib.rs:286`).
- **MEASURED:** `natVal` is parsed as a decimal **string** (`lib.rs:577`), not a
  JSON number — correct for arbitrary precision.
- **Recursors must be regenerated, never adopted from the export.** Lean 3 did
  not export them precisely to avoid *"fugazi recursors"*; Lean 4 emits them but
  the spec calls them *"for convenience"*. axeyum regenerates and then
  definitionally compares — correct.
- ⚠ The committed `examples/Nat.add_succ.ndjson` is **stale 3.0.0** and still
  wraps declarations in arrays. Do not use it as a 3.1.0 reference.

### 4.3 There is a round trip back into the real kernel

This is the most actionable finding in this section, and it changes **R0.2**.

An axeyum-emitted export can be fed back to the **official C++ kernel**:
`Export.parseStream` (a *library* in `lean4export`, not just the exe) →
`Environment.replay`, which is what `leanprover/comparator` does:

```lean
let solution ← Export.parseStream (← stringStream solutionExport)
let mut kernelEnv := (← Lean.mkEmptyEnvironment).toKernelEnv
let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]   -- kernel adds these itself
let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
kernelEnv ← kernelEnv.replay kernelConstMap
```

**Trap:** `Quot.mk`/`Quot.lift`/`Quot.ind` must be deleted before replay or the
kernel errors on double-add.

Today axeyum emits **Lean 4 source text** (`lean_pp.rs`), which needs a full
`lean` toolchain to check. Emitting NDJSON instead would let a proof be replayed
into the official kernel *and* into nanoda — two independent checks — without
elaboration. See **R8.1**.

### 4.4 What the ecosystem expects of an independent checker

- **Mathlib does not run `lean4checker` per PR.** `build_template.yml:889`
  verbatim: *"We no longer run `lean4checker` in regular CI, as it is quite
  expensive for little benefit. Instead we run it in a cron job on master."*
  Daily cron, `master` and `nightly`.
- **`leanprover/lean-action` ships `nanoda: true`** — *"an independent Lean 4
  type checker written in Rust"* — as a one-line CI input. That is the ceiling
  of "taken seriously," and a Rust kernel already occupies it.
- **A conformance corpus exists**: 189 tests, **121 accept / 62 reject / 6
  either**. A `parse-only` checker scores 121/121 on accepts and **6/62** on
  rejects — the built-in control proving positive-only results are worthless.
- **Publish a divergences ledger.** lean4lean's `divergences.md`, with the
  standing rule *"Unless specified here, any divergence between lean4lean and
  lean4 is a bug"*, is the most copyable artifact in the ecosystem.
- **Pollack-consistency outranks speed for mathematicians.** Wiedijk:
  consistency *"is not enough: it also should not be possible to think that a
  theorem that actually is false has been proved."* A kernel that prints back
  what it checked is worth more to that audience than one that is faster.

### 4.5 Decorrelation

The 2026-07 nested-inductive phantom-parameter bug (`lean4#14576`) hit **both**
official Lean and lean4lean — because lean4lean is a *port*. axeyum's ADR-0036
port-from-nanoda inherits nanoda's blind spots by the same mechanism.

Two data points: nanoda has had **two** soundness bugs of its own
(`nanoda_lib#8`, projection out of `Prop`; and an `imax` leq bug). §2.6 Probe 6
confirms axeyum guards the first. The second is **UNKNOWN** and Probe 5 shows
the level layer is exactly where the shared lineage is visible.

Also worth recording: the last three years of Lean kernel soundness bugs were
found by **fuzzing, formal verification, and AI red-teaming — not by review**
(`#8060` fuzzing, `#8554` lean4lean verification, `#10577` fuzzing, `#14484`
and `#14607–14616` AI models). axeyum already has `kernel_seam_fuzz`; that is
the right instrument, and it should be widened rather than supplemented by
inspection.

### 4.6 Known conformance gaps

| Gap | Evidence | Blocks |
|---|---|---|
| **Universe-level over-completeness** | §2.6 Probe 5, MEASURED | correctness of "Lean would accept this" |
| **No K-like reduction** | §2.5, 0 hits | conformance tests including the `rec-k-lie` / `nat-rec-k-lie` **soundness** cases |
| **No unit-like defeq** | agent audit | a block of conformance tests |
| **No `MData`** | §2.5, 0 hits | export/import fidelity |
| **No accelerated `Nat`** | §2.5; 14 operators incl. `gcd` | performance at Mathlib scale, not correctness |
| **String route** | `Lit::Str` → `UnsupportedLit` | must target `String.ofList`; `String.mk` was removed |

### 4.7 What could not be verified

Recorded rather than smoothed over: current Mathlib NDJSON export size and
declaration count (the corpus is listed at 5.2 GB; no independent figure);
Mathlib build time / `.olean` cache size (no primary source); the dating of
`mathlib_stats.html` (no timestamp); what format "1.0.0" was. Transitive-import
counts below are **source-derived, in-repo only, and therefore a lower bound** —
they exclude Lean core / Batteries / Aesop closures and cannot see
elaborator-synthesized edges.

Also: **there is no `bug: soundness` label in `leanprover/lean4`** (103 labels,
zero matching). Lean soundness bugs cannot be enumerated by label, and there is
no Lean equivalent of Rocq's `critical-bugs.md`.

---

## 5. The Mathlib import route, measured

This measures the current-development-snapshot form of **Q1**. It does **not**
close R5.1's pinned-tag exit: the census below used `5b8fb9a61c`, while the
program authority pins Mathlib v4.30.0 at `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Measured at mathlib4 `5b8fb9a61c` (2026-08-13): **8,322 `.lean` files,
2,293,484 lines**. Declaration counts vary threefold by method — source keywords
give 187,160 `theorem`+`lemma`; environment-level stats give 135,474 defs +
284,155 theorems; a dependency-graph paper gives 308,129 declarations over
8,436,366 edges.

**The target slice — divisibility + congruence + finite sums over ℤ:**

| Slice | Modules | Closure LOC | % of Mathlib |
|---|---:|---:|---:|
| ℤ gcd / divisibility (`Data.Int.GCD`) | 267 | 60,458 | 2.5% |
| ℤ congruence (`Data.Int.ModEq`) | 364 | 90,034 | 3.8% |
| finite sums (`BigOperators…Finset.Basic`) | 412 | 113,728 | 4.8% |
| **all three together** | **519** | **138,442** | **5.8%** |
| + `ZMod.Basic` + `Multiplicity` | 862 | 250,674 | 10.5% |
| `import Mathlib.Tactic` (what people write) | 2,731 | 888,580 | **37.4%** |

**Verdict: the typeclass hierarchy does not force whole-library closure.** 5.8%
is a real, bounded target. Three constraints shape it:

1. An **irreducible floor** of ~8,553 LOC / 39 modules (`Mathlib.Init`,
   linter-enforced).
2. **Tactic infrastructure dominates small slices** — 66% of the ℤ-gcd slice's
   LOC sits under `Mathlib/Tactic`. You pay the framework before any mathematics.
   For a kernel that only *re-checks* terms, much of this may be droppable;
   whether it is, is **UNKNOWN**.
3. **`import Mathlib.Tactic` is the trap, not the algebra** — 6.4× heavier than
   the slice, dragging in 254 `Topology` and 147 `CategoryTheory` modules.

What keeps slices small is `assert_not_exists`: **935 occurrences across 893
files (11% of Mathlib)**, a per-file machine-checked ceiling on hierarchy creep.

⚠ **Structural landmine for any importer:** Mathlib migrated to Lean's module
system (PR #31786, 2025-11-19). All 8,322 files begin with `module` and 8,306
use **`public import`**. **Tooling that parses imports with `^import ` is
broken.** Three paths commonly cited no longer exist: `Data/Int/Defs.lean`
(split), `Data/Int/ModCast.lean` (never existed in mathlib4 — a Lean-3 name),
and `Algebra/BigOperators/Basic.lean` (deleted).

Why direct import counts (3, 6, 11) mislead: the module DAG is **153 layers
deep**, 92.2% of cross-file declaration dependencies arrive transitively, and
**74.2% of dependency edges are invisible in source** — synthesized by the
elaborator via instances and the ℕ↪ℤ↪ℚ↪ℝ coercion chain. Mathlib is a monolith
**by distribution, not by file dependency**.

---

## 6. Prior art — and the template that already exists

This section changes the shape of the problem, and it should be read before any
of the requirements above are scheduled.

### 6.1 The template: LRAT-Catcher

**Szeider, arXiv:2607.00815 (1 July 2026),
`github.com/leansolving/lrat-catcher`, MIT, Lean v4.30.0.**

It does precisely what this document has been circling, for precisely this
problem shape: a **verified Lean encoding** of a Rado-type equation (`a+b=c`),
an external CaDiCaL solve, an LRAT certificate **imported by reflection**, and a
once-proved soundness lemma lifting `F.Unsat` to a statement about **colourings,
not CNF**. It produces `schurNumber 4 44` (i.e. **S(4) = 44**) and
`ramseyNumber 4 4 18` as genuine Lean theorems.

**The entire Schur development is 222 lines of Lean** [measured]:

- `encodeK k n : CNF Nat` — one variable per (element, colour), at-least-one
  clauses, and a not-all-three clause per Schur triple per colour. **No
  at-most-one constraints** — soundness needs only the "colouring ⟹ satisfies"
  direction. *(This is exactly the cover-composition observation already recorded
  in the paper's Lemma C.1: coverage, not partition.)*
- `no_k_schur_free_of_unsat : (encodeK k n).Unsat → ¬hasKSchurFreeColoring k n`
  — the soundness lemma, proof body **~8 lines**.
- `checkKSchurFree` + spec — the lower-bound witness checker.

Two things worth taking outright:

1. **Cover completeness is itself a SAT question.** Cube-and-conquer normally
   needs a trusted "these cubes cover the space" combinator. The negated-cubes
   formula being UNSAT *is* the coverage claim, so it enters as another LRAT
   certificate rather than as trusted glue. **This is convergent with the
   composition argument already in the paper's Appendix C** — independently
   arrived at, which is worth stating.
2. **Generate the DIMACS from the same Lean function you certify.** From the
   source header: *"The DIMACS file for the solver is produced by
   `lratcatch-gen` from the **same** `encodeK` function, so the certified CNF and
   the solved CNF coincide by construction."*

### 6.2 The gap this closes, and it is a real one

**Schur Number Five (Heule, AAAI 2018) explicitly did not verify the encoding.**
Verbatim: *"Only the encoding … was not checked using a theorem prover. We chose
to skip verification of this part because the encoding can be implemented using
a dozen lines of straightforward C code."*

For `a(x−y) = bz` that excuse does not hold. The coefficient arithmetic and the
range conditions are exactly where an encoding bug would hide — and this paper's
own history bears that out, since the reviews caught `a ∤ m'n'`, an attainment
overclaim, and a wrong `R_2` before publication.

Similarly, **Empty Hexagon** (ITP 2024) states its own weak point: it asserts
CNF unsatisfiability as a Lean **axiom** after external `cake_lpr` checking, and
*"trust that the CNF formula produced by the verified Lean encoder is the same
one whose unsatisfiability was checked."* Its authors call this out directly:
*"A key challenge for the community is to improve the connection between verified
SAT tools and ITPs."*

### 6.3 Nobody has formalized any of this mathematics

Verified by exhaustive search of Mathlib, the full AFP tree, Coq/Rocq, Mizar,
HOL Light, and Agda:

| Target | Result |
|---|---|
| Rado's theorem, Rado numbers, partition regularity of linear systems | **not formalized in any proof assistant** |
| Schur's theorem (the Ramsey-type one) | **not formalized anywhere** |
| Ramsey's theorem / Ramsey numbers **in Mathlib** | absent (exists in Isabelle AFP, HOL Light, Mizar, Coq) |
| van der Waerden in Mathlib | only as a Hales–Jewett corollary |
| Graham–Rothschild | not formalized |
| **A rigidity theorem in Ramsey theory** | **no formalized precedent at all** |

The closest structural analogue for the *construction* is Mathlib's **Behrend
construction** (489 lines) — a parameterized geometric construction with
solution-freeness proved from convexity.

### 6.4 The kernel-computation wall, measured

LRAT-Catcher Table 1 (Lean v4.30.0, CaDiCaL 3.0.0). This is decisive:

| Instance | Certificate | `native_decide` | `decide +kernel` |
|---|---:|---:|---:|
| php(6,5) | 12 KB | 30.9 s | 96.3 s |
| **Schur S(3)** | **22 KB** | 13.8 s | **245 s / 28.5 GB** |
| **php(7,6)** | **87 KB** | 14.8 s | **does not finish** |
| php(10,9) | 63 MB | 13.2 s | — (`lrat_proof` OOM at 95.7 GB) |
| **Schur S(4)** | **628 MB** | **77 s / 8.9 GB** | — |

**`decide +kernel` ceiling is tens of kilobytes of certificate.** Explicit proof
terms cost ~1500× the certificate in memory. Native reflection costs 14–35× and
is the only route that scales — at the price of one `native_decide` axiom per
evaluation, which puts the Lean compiler in the TCB.

Mathlib's `lrat_proof` is out on two counts: it is kernel-only (so it hits the
same wall) **and** it does not implement RAT steps at all — the source contains
`return Except.error "unimplemented: RAT step"`, and modern CaDiCaL inprocessing
emits RAT.

The paper's own verdict: *"Kernel mode is therefore a way to shrink the trusted
base rather than a faster checker, at a cost that confines it to small
certificates."*

**Consequence for axeyum:** this is a *general* result about kernel reduction,
not a Lean quirk. §2.6 Probe 3 shows axeyum's numerals handle the paper's
closed-form arithmetic fine, but that says nothing about reflecting a SAT search.
Q4 stands, and this table is the prior estimate to beat.

### 6.5 Effort data

Converged across three projects, two proof assistants, three decades:
**40–55 lines of formal proof per person-day**, de Bruijn factor **4** (5.6 for
hard research mathematics).

| Project | System | Size | Effort |
|---|---|---:|---|
| Diagonal Ramsey (Paulson) | Isabelle | 12,500 lines | **251 days, one person**; dB factor 5.6 |
| Empty Hexagon | Lean 4 | 4,700 lines (1,550 = encoding + symmetry) | **~300 h over 3 months**, experienced formalizers |
| Keller (ITP 2026) | Lean 4 | ~3,000 lines (**150 for the encoding**) | **~1 month** for the reduction |
| Boolean Pythagorean Triples | Coq | 1,946 lines | ~13 CPU years of checking |
| **LRAT-Catcher Schur** | Lean 4 | **222 lines** | — |

Applied to this paper:

| Component | Comparable | Estimate |
|---|---|---|
| Verified CNF encoding + soundness lemma + witness checker | LRAT-Catcher Schur (222 ln), Keller encoding (150 ln) | **300–800 lines; 2–6 weeks** using existing scaffolding |
| Certificate import + cube-cover composition | off-the-shelf | **days** |
| Shell colouring construction, parameterized in `k` | Behrend (489 ln) | **500–1,500 lines; 1–3 months** |
| Sharpness | — | comparable |
| **Rigidity** | **no precedent** | **dominant risk; budget generously** |

Total for the mathematics: roughly **2,500–4,000 lines and 6–12 months of one
experienced formalizer**. **The SAT-certified values are the cheap part.**

This supersedes the informal estimate given earlier in this workstream, which was
not grounded in comparables.

### 6.6 The uncomfortable implication

The fastest route to "this paper's results are kernel-checked" does **not** run
through axeyum's kernel. It runs through LRAT-Catcher or Trestle in real Lean 4,
where the encoding layer is 2–6 weeks rather than a library-building project, and
where `Dvd`/`Finset`/ℤ already exist.

That is worth stating plainly rather than discovering later. It does not make
axeyum's kernel pointless — an independent Rust checker is a decorrelation
asset, and `lean-action` shipping `nanoda: true` shows the ecosystem values
exactly that (§4.4). But **"axeyum should formalize this because axeyum can" is
not a technical argument**, and this document should not be read as making one.
See **R9**.

---

## 7. Two routes

The missing mathematics — order, divisibility, congruence, valuation, finite
sums, intervals — can be **built** natively or **imported** from Mathlib. These
are not exclusive, and the correct answer differs per layer.

### 7.1 Build (native library on `nat_prelude`)

Extend the zero-axiom `nat_prelude` upward. This is what `route-c/REPORT.md`
called *"roughly one chapter of a `Nat` library."*

- **Preserves the zero-axiom property**, which is the distinguishing claim.
- No dependency on a pinned Mathlib, no import-surface risk.
- Every lemma is a hand-built proof term or a Rust-side generator: **there is no
  tactic layer, no elaborator, no unifier, no `simp`/`ring`/`omega`.** This is
  the dominant cost, and it does not shrink with practice the way tactic-mode
  formalization does.
- The `gcd`/Bézout sub-tree additionally needs `Acc` declared and a
  well-founded-recursion route (§2.6 Probe 2: the *shape* admits; nothing
  declares it).

### 7.2 Import (Mathlib slice through L3)

Use the existing `axeyum-lean-import` reader to ingest a dependency-closed slice
of `Init`/`Std`/Mathlib and let the kernel re-check it.

- The infrastructure **already exists and is mutation-tested**: lean4export
  NDJSON 3.1.0, fail-closed, ADR-0348 owned publication, ADR-0350 identity
  manifests. K1 is 5/5.
- Mathlib supplies ℤ, `Dvd`, `Int.emod`, `ZMod`, `multiplicity`, `Finset.sum`
  and intervals directly — the entire §3.4 table below the fold.
- **The kernel re-checks whatever it reads**, so this is not a trust downgrade
  in the way an axiom is.
- Blocked on the whole of L3 (0/12) and gated by TL3.6–TL3.9. The pinned Mathlib
  is 8,094 files; a dependency-closed slice for divisibility + congruence +
  finite sums is a real but bounded subset. Its closure is measured on
  development snapshot `5b8fb9a61c` (§5); the corresponding pinned-v4.30.0
  closure and re-checking-only tactic share remain **UNKNOWN** (**R5.1**).
- Would import Mathlib's own axioms (`propext`, `Quot.sound`, `Classical.choice`),
  which the crate today has **none** of. That is a deliberate, explicit, and
  well-understood trust boundary — but it is a change, and it needs an ADR.

### 7.3 Recommendation

**Both, split by layer.** Build the order/divisibility/congruence layer natively
(it is small, it keeps the zero-axiom property, and it is the layer every future
axeyum formalization needs regardless). Import for anything requiring
`Finset`-scale library depth. Do not attempt `gcd`/Bézout natively before `Acc`
is declared and probed.

Crucially, **neither route is on the critical path for the paper.** See §9.

---

## 8. Requirement set

Each requirement states what must be true, how it is verified, and what it
blocks. Ordered by dependency, not by priority.

### R0 — Measurement integrity

| ID | Requirement | Exit |
|---|---|---|
| **R0.1** | No Lean-related gate may pass by being inert. The eight `AXEYUM_LEAN_BIN` suites (§2.1) must fail loudly in at least one enforced lane, and that lane's non-vacuity must be asserted by a **nonzero test count**, not an exit status. | A lane exists that fails when `lean` is absent; its assertion is a count, not `ok`. CI already has `AXEYUM_REQUIRE_LEAN=1` — verify it is actually reached. |
| **R0.2** | The export shipped with any publication must be checked by **real Lean** before the claim is made, or the claim must say it was not. | Either a green run, or the publication states the gap. *(The paper currently states the gap — met by disclosure.)* **Cheaper route: R8.1** — emitting NDJSON lets the official kernel replay it via `Environment.replay` with no toolchain install and no elaboration. |
| **R0.3** | Every capability claim about the kernel must cite a command and its output. Doc comments and planning prose are not evidence. | This document's §1 labelling discipline applied to all downstream claims. |

R0.1 implementation and local non-vacuity evidence are recorded in the
[`measurement-integrity result`](lean-r0-measurement-integrity-result-2026-08-13.md);
positive execution of the newly enforced commands remains a hosted-CI gate.

### R1 — Prelude composition (hard blocker)

| ID | Requirement | Exit |
|---|---|---|
| **R1.1** | Preludes must compose. Factor the shared logic core out of every `build_*_prelude`; make each builder **idempotent and fallible** rather than panicking on `DeclarationExists`. Namespace theory-specific names (`Int.add`, `Real.add`). | `build_logic + build_nat + build_int + build_arith` on one `Kernel` succeeds and every declaration keeps its own type. |
| **R1.2** | A regression test must pin mixed-theory environments. | A test builds all preludes in one kernel and checks a mixed ℕ/ℤ statement. |
| **R1.3** | No library-level code may `.expect()` on a kernel rejection. | Grep for `.expect(` in `prelude.rs`/`*_prelude.rs` returns only genuinely infallible sites. |

R1 / **TL3.3 is DONE**. The
[`R1 result`](lean-prelude-composition-r1-result-2026-08-13.md) records the
fallible whole-package transactions, exact repeat validation, `Int.*` /
`Real.*` / parameterized-string namespaces, mixed ℕ/ℤ proof, late-conflict
rollback control, regenerated 65-row ledger, and focused gates. This removes
the mixed-environment infrastructure blocker for `thm:rigid`; it does not
formalize either half of that theorem or choose its signed-defect encoding.

The follow-up [transaction/cache hardening](lean-kernel-transaction-cache-hardening-result-2026-08-13.md)
places unchecked environment removal behind one cache-clearing kernel rollback,
retains only one reachable WHNF revision, makes duplicate registration a
release-safe pre-insertion assertion, and gives string alphabet overflow its
real typed cause. Exact snapshot compaction remains measurement-gated.

### R2 — Foundations of ℤ

| ID | Requirement | Exit |
|---|---|---|
| **R2.1** | If ℤ is to be *constructed* rather than axiomatized, `Quot.sound` must exist. Today `PACKAGE_LEN = 4` and the soundness axiom is absent (§2.5), so quotients compute but carry no propositional content. The pinned official package is four members; `Quot.sound` would be a separate ordinary axiom, not a fifth privileged member. | **Met by decision:** accepted ADR-0388 keeps the current ℤ profile axiomatized. ADR-0365 remains separately proposed; any future construction must retain the canonical four-member package and ledger `Quot.sound` explicitly. |
| **R2.2** | The choice between constructed ℤ (zero **Int-specific** axioms but at least the framework `Quot.sound` axiom, plus large library cost) and axiomatized ℤ (34 axioms, available now) must be an **explicit, recorded decision**, not a default inherited from whichever prelude a caller happens to build. | **Met:** ADR-0388 retains the 34-assumption profile for reconstruction and selects a Nat prefix-deficit encoding for credited Rado rigidity; the generated axiom ledger references the decision. |
| **R2.3** | Any publication resting on `int_prelude` must state the axiom count in the claim itself. "Zero sorry, zero axiom" is true of `nat_prelude` and **false** of anything touching ℤ today. | Publication text names 34 axioms, or does not use ℤ. |

R2 is **DONE as a foundation decision**, with no theorem credit added. The
[`R2 result`](lean-integer-foundation-r2-result-2026-08-13.md) and
[accepted ADR-0388](../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md)
record the reconstruction/publication split, the corrected four-member
quotient boundary, and the subtraction-free Rado prefix invariant.

### R3 — Computation

| ID | Requirement | Exit |
|---|---|---|
| **R3.1** | Numeral strategy must be driven by a measured workload, not by assumption. Unary ι-reduction is **sufficient** for the paper's closed-form arithmetic (§2.6 Probe 3: 1,500 in ~14 ms). It is **not** established for reflection over a SAT-scale search. | Before any `decide`-style reflection route is planned, measure it. Do not extrapolate from Probe 3. |
| **R3.2** | If accelerated `Nat` operations are added (TL2.8), literal typing must remain gated on the checked canonical bootstrap (ADR-0347) and every accelerated op needs a differential test against the ι-reduction path. | Accelerated and unaccelerated paths agree on a generated corpus including degenerate arguments. |

### R4 — The missing library

The gating item, per ADR-0385:96 and `next-actions…:246`, both accurate.
Ordered by dependency.

| ID | Requirement | Needed by | Status |
|---|---|---|---|
| **R4.1** | Complete the order fragment: `lt`, antisymmetry, totality, `le_of_succ_le_succ` (inversion, needs a `pred`-style motive), `min`. | all three theorems | **WIP:** `Nat.lt` and checked successor inversion landed under [ADR-0390](../research/09-decisions/adr-0390-proved-nat-strict-order-and-successor-inversion.md); antisymmetry, totality, and `min` remain |
| **R4.2** | Truncated subtraction and cancellation. Called out in `route-c/REPORT.md` as *"the first real cost; it is what makes valuations usable."* | all three | absent |
| **R4.3** | Divisibility as a **prelude-level** definition with its lemma set. | all three | **WIP:** `Nat.dvd`, `dvd_mul`, and `dvd_add` are zero-axiom prelude declarations under [ADR-0389](../research/09-decisions/adr-0389-proved-nat-divisibility-foundation.md); transitivity/cancellation remain |
| **R4.4** | Congruence mod `a`. | central to `thm:rigid` | absent |
| **R4.5** | Intervals, membership, and the partition/covering lemma behind `lem:structure(3)`. Cardinality is needed only as a diameter bound and can be discharged as order arithmetic on endpoints. | all three | absent |
| **R4.6** | Finite sums `Σ` beyond the existing `geo`/`geo1`, including empty-range corners (`k = 3` in `thm:sharp`). | all three | **WIP:** generic `Nat.sumRange`, empty/successor equations, and the empty corner landed under [ADR-0391](../research/09-decisions/adr-0391-generic-nat-finite-range-sums.md); reindexing and sum algebra remain |
| **R4.7** | Euclidean division / division-with-remainder, for `lem:gap`'s integrality step. | `thm:main` | absent |
| **R4.8** | `gcd`, Bézout, Gauss's lemma — for `lem:solform`'s necessity direction. **Requires `Acc` declared first.** Explicitly rejected as an axiom in `route-c/REPORT.md:143-148` ("would have been a fraud, since it is essentially the content of the statement"). | `thm:main` | absent |
| **R4.9** | `a`-adic valuation, stated **relationally** (`v(j) = e :⟺ a^e ∣ j ∧ a^{e+1} ∤ j` plus existence/uniqueness for `j ≥ 1`) so no division is required. | `thm:main` | absent |

### R5 — Import route

| ID | Requirement | Exit |
|---|---|---|
| **R5.1** | **PARTIAL** (§5): at development snapshot `5b8fb9a61c`, divisibility + congruence + finite sums over ℤ = **519 modules / 138,442 LOC / 5.8% of Mathlib**. The pinned-v4.30.0 result and the share of tactic infrastructure a re-checking-only kernel can drop remain unknown. | A closure census against the pinned tag, with the tactic share separated. |
| **R5.2** | Importing Mathlib imports its axioms (`propext`, `Quot.sound`, `Classical.choice`). The crate today declares **none**. This trust change needs an ADR before, not after. | An accepted ADR; the axiom ledger gains the imported rows with explicit classification. |
| **R5.3** | The String closure's first blocker is still unmeasured (blocker census row 3, "NOT RERUN"). It must be refreshed before complete-K1 authority is claimed. | Regenerated stream, measured first blocker. |

### R6 — Documentation integrity

| ID | Requirement | Exit |
|---|---|---|
| **R6.1** | Resolve the axiom-ledger discrepancy: the parity contract §2 says all 65 assumptions are "semantically unclassified"; the ledger classifies all 65. Two committed documents give opposite answers. | One is corrected, or the contract cites the ledger as the authority. |
| **R6.2** | The `Acc` line in `next-actions…:248` ("the one capability not yet probed") is now **partially** outdated: the reflexive-field shape admits (Probe 2); the `Acc` declaration and elaborator route do not exist. Narrow the wording rather than deleting it. | Wording distinguishes *shape admitted* from *declaration absent*. |
| **R6.3** | Capability claims must not be made from substring greps. Five of this workstream's seven errors came from patterns that matched prose — including doc comments *listing what is absent*. Require an exact-name search plus a positive control, or an executed probe. | Adopted as review practice; this document's §0 is the standing example. |

### R7 — Theorem targets, in cost order

| ID | Requirement | Rationale |
|---|---|---|
| **R7.1** | **`thm:sharp` is the correct first target.** No valuation, no `gcd` in the proof, no induction, one explicit closed-form witness. Its only real cost is a re-indexed geometric sum with an empty-range corner. | §3.2 |
| **R7.2** | Decide `thm:rigid`'s encoding **before** starting it: axiomatized ℤ (available now, 34 axioms, needs R1.1) versus a ℕ-valued deficit `D_j := −E_j` with the trigger rewritten (keeps zero axioms, needs R4.1–R4.2). | §3.3 |
| **R7.3** | Treat the **`M = N+1` half of `thm:rigid` as a separate, smaller target.** It is the novel half and it does **not** depend on `thm:main` — only the `M = N` half cites it. | §3.2 |
| **R7.4** | Do not begin `thm:main` before R4.7–R4.9 exist. Its two hardest steps (`lem:gap`'s integrality argument, `lem:solform`'s necessity) are precisely the ones with no current foundation. | §3.2 |

### R8 — Lean conformance

| ID | Requirement | Exit |
|---|---|---|
| **R8.1** | Emit lean4export **NDJSON 3.1.0** in addition to Lean source text, so a proof can be replayed into the official C++ kernel via `Export.parseStream` → `Environment.replay` and independently into nanoda — **without needing elaboration or a full `lean` toolchain**. Delete `Quot.mk`/`Quot.lift`/`Quot.ind` before replay. | An axeyum-produced theorem replays green in `comparator` and in nanoda. This is a far cheaper route to R0.2 than installing Lean. |
| **R8.2** | **Match Lean's incompleteness, not only its soundness.** axeyum currently decides `imax u (imax v w) ≡ imax (max u v) w`, which Lean rejects (§2.6 Probe 5). Either restrict `leq_core` to Lean's normalization rules, or record the divergence explicitly and stop implying that axeyum-checked ⇒ Lean-checkable. | Probe 5 returns `false`, **or** a published divergences ledger contains this row. |
| **R8.3** | Every known nanoda defect must be **explicitly checked for**, never assumed absent, because ADR-0036 makes axeyum a port. Probe 6 is the template (the `Prop`-projection bug is guarded and tested). The nanoda `imax` leq bug is **UNKNOWN** for axeyum. | A test per known upstream defect, each citing the upstream issue. |
| **R8.4** | Publish a **divergences ledger** in the shape of lean4lean's `divergences.md`, with the standing rule that any unlisted divergence from Lean 4 is a bug. | The file exists, is `--check`-gated, and Probe 5's row is in it or fixed. |
| **R8.5** | Run against the public conformance corpus (189 tests: 121 accept / 62 reject / 6 either) and report **both** halves. A positive-only score is meaningless — the `parse-only` control scores 121/121 accepts and 6/62 rejects. | A scored run; the reject count is reported alongside the accept count. |
| **R8.6** | Close the known conformance gaps in §4.6, prioritising **K-like reduction** because it blocks the `rec-k-lie` / `nat-rec-k-lie` **soundness** cases, not merely feature tests. | Those cases pass. |
| **R8.7** | Widen `kernel_seam_fuzz` rather than relying on inspection. Every recent Lean kernel soundness bug was found by fuzzing, formal verification, or AI red-teaming — none by review. | Fuzz coverage includes each deferral's degenerate shape, per `CLAUDE.md`'s standing rule. |
| **R8.8** | Preserve **Pollack-consistency**: the kernel must be able to print back what it actually checked, independently of source notation. This is what buys mathematician trust; `lean_pp.rs` already provides it and must not regress. | Round-trip test: rendered output re-parses to a definitionally equal term. |

### R9 — Position against prior art

| ID | Requirement | Exit |
|---|---|---|
| **R9.1** | Any decision to formalize this mathematics **in axeyum's kernel rather than in real Lean 4** must be justified on its merits and recorded. LRAT-Catcher/Trestle already provide the encoding layer, and Mathlib already provides ℤ/`Dvd`/`Finset`. "axeyum can, therefore axeyum should" is not an argument. | An ADR stating the reason — decorrelation, no-C-dependency, self-containment — or a decision to use the existing tooling. |
| **R9.2** | The **encoding** is the part with no prior art worth having. `S(5)=160` skipped encoding verification on the grounds that it was *"a dozen lines of straightforward C"*; for `a(x−y)=bz` the coefficient arithmetic and range conditions are exactly where a bug would hide. If any part of this is formalized first, it is the encoding soundness lemma. | `encodeRado` + `no_rado_free_of_unsat` exist and are checked. |
| **R9.3** | Generate the DIMACS from the **same** function that is certified, so the solved CNF and the certified CNF coincide by construction. This closes the gap Empty Hexagon explicitly leaves open. | One generator, used by both paths; a test asserts byte-identity. |
| **R9.4** | Adopt cover-completeness-as-certificate rather than a trusted cover combinator. This is **convergent with the paper's Appendix C composition argument** and should be cross-referenced in both directions. | The cover claim is discharged by a checked certificate, not by glue. |
| **R9.5** | Do not plan a `decide`-style kernel-reflection route without measuring it first. The published ceiling is **tens of kilobytes of certificate** (245 s / 28.5 GB at 22 KB; non-terminating at 87 KB). This paper's instances are far past it. | Q4 answered by measurement against that table. |

---

## 9. Non-requirements and explicit non-claims

Recorded so that scope does not drift the way the phrase "end to end" did.

1. **None of this is on the critical path for the Rado paper.** The paper's
   claims are already scoped to what is checked, and it states the Lean gap
   explicitly (`07_discussion.tex:21-27`). Closing the gap is a capability
   project, not a publication blocker.
2. **This document does not claim the kernel is close to proving the theorems.**
   The kernel can *express* the mathematics — the capability probes settle that.
   It lacks the *library*, and the library is the work.
3. **No parser, elaborator, tactic layer, compiler, Lake, or LSP work is
   justified by anything here.** Those are L4–L9 and have their own drivers.
   The requirements above touch L2 (R1–R3) and L3 (R4–R5) only.
4. **"Lean parity" is not claimed and is not the goal of this document.** The
   parity contract's terminal denominator is explicit and currently reports zero
   satisfied terminal gates. Nothing here changes that.
5. **Sizing is deliberately absent** except where a prior document already sized
   an item. The last two sizing tables in this area both required correction
   (the gap analysis over-charged nested inductives and well-founded recursion
   by ~1,200–1,900 LoC). A size estimate that has not survived contact with the
   dependency spine is worse than none.

---

## 10. Open questions

| # | Question | Blocks | How to settle |
|---|---|---|---|
| Q1 | Transitive closure of a minimal Mathlib slice? **PARTIAL:** 519 modules / 138,442 LOC / 5.8% at development snapshot `5b8fb9a61c` (§5), not yet at the pinned v4.30.0 commit. Residual: can a re-checking-only kernel drop the 66% tactic-infrastructure share? | R5.1 | rerun against the pinned commit with the tactic share separated |
| Q6 | Does axeyum inherit nanoda's second soundness bug (the `imax` leq bug, commit `12838995c`)? Probe 5 shows the level layer is exactly where shared lineage shows. | R8.3 | build the upstream reproducer as a test |
| Q7 | Should `leq_core` be restricted to Lean's incomplete normalization, or should the divergence be documented and kept? Restricting costs completeness axeyum currently has; keeping it means axeyum-checked ⇏ Lean-checkable. | R8.2, R8.4 | ADR |
| Q2 | Does a WF-recursion route work end to end? **The shape question is already settled: yes.** `strict_positivity.rs` classifies the `Acc` shape as `Production::PositivePi` at `context_depth > 0`, whose declines went 144 → 0, and indexed profiles likewise 42 → 0. What is unsettled is whether a declared `Acc` generates a usable recursor and whether `gcd` by `Acc.rec` type-checks. | R4.8, hence `thm:main` | declare `Acc`, build one `gcd` by `Acc.rec`, check it — a build task, not a probe |
| Q3 | **Resolved for the credited Rado lane by ADR-0388:** use the ℕ prefix invariant `A_j ≤ C_j`; an axiomatized-ℤ version may be measured later but cannot improve the zero-axiom result. | R7.2 | [ADR-0388](../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md) |
| Q4 | What does reflection over a SAT-scale search actually cost in this kernel? | any `decide`-style route | measure; do **not** extrapolate from Probe 3 |
| Q5 | **R2 resolved by ADR-0388:** do not accept ADR-0365 or add `Quot.sound` to construct ℤ for the Rado lane. The official privileged package remains four members; `Quot.sound` is a separate axiom. ADR-0365's M4 conformance question remains open on its own evidence. | R2.1 closed; Lean conformance remains | [ADR-0388](../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md) |
