# 06 — Lean kernel gap analysis (post-P0)

Audit of `crates/axeyum-lean-kernel` (~15.5k lines incl. tests) as it stands
*after* the P0 `Prop` large-elimination fix (ADR-0165, commits `d26ad887`,
`a10c8cde`, `de249d48`, `e69a92da`). Companion to
[09-P0-kernel-unsoundness.md](09-P0-kernel-unsoundness.md); this note sizes the
**remaining** gaps for plan phase P6.0 and audits every deferral for the P0
pattern (deferred-by-*permission* rather than deferred-by-*rejection*).

Every claim below is `file:line` against the code, not the doc comments.

> **2026-07-21 refresh.** The stale `src/lib.rs` scope comment identified by the
> original audit is corrected, and row #14's initial import path has landed.
> The kernel-feature findings below remain current; §3 records the new exact
> import boundary and links the superseding interoperability measurements.

---

## 1. Current inventory

### `expr.rs` (99 lines) — the term language

`ExprNode` (`expr.rs:80-98`) has exactly nine variants: `BVar(u32)`,
`FVar(u64)`, `Sort(LevelId)`, `Const(NameId, Vec<LevelId>)`, `App`, `Lam`,
`Pi`, `Let`, `Lit`.

- **There is no `Proj` variant at all.** Confirmed by exhaustion of the enum
  (`expr.rs:80-98`) and stated at `expr.rs:13-16`. Structure projections are
  not representable.
- `Lit` (`expr.rs:61-66`) is `Nat(u128)` | `Str(String)`. **`Nat` is a `u128`,
  not a bignum** (`expr.rs:63`, deferral noted `expr.rs:56-59`).
- Locally-nameless: de Bruijn `BVar` + `FVar(u64)` with a side-table
  `LocalContext` for binder types (`tc.rs:29-46`).
- Cached intern-time metadata `ExprMeta { num_loose_bvars, has_fvars }`
  (`expr.rs:70-76`, computed `lib.rs:763-`) short-circuits traversal.

### `level.rs` (46 lines) — universes

`LevelNode` = `Zero | Succ | Max | IMax | Param` (`level.rs:35-46`) — complete
w.r.t. Lean. `simplify`/`subst`/antisymmetric `leq`/`is_equiv` ported
line-for-line from nanoda (`level.rs:8-13`). This is the full universe
algebra; no gap.

### `name.rs` (42 lines)

Hierarchical `Anonymous`/`Str`/`Num` names, interned. No gap.

### `tc.rs` (1356 lines) — the trusted core

Self-described trusted core (`tc.rs:5`). Reductions **present**:

| Reduction | Site |
|---|---|
| **beta** | `tc.rs:387-405` (peels lambdas, instantiates) |
| **zeta** (let) | `tc.rs:407-` |
| **delta** (δ-unfold `Definition`/`Theorem`) | `tc.rs:518-528`, value at `:492` |
| **eta** expansion | `tc.rs:701-727` (`try_eta_expansion`) |
| **proof irrelevance** | `tc.rs:729-740` (`proof_irrel_eq`) |
| **lazy-delta** (height-driven side choice + same-const short-circuit) | `tc.rs:842-882` |
| **iota** | *not here* — in `inductive.rs`, see below |

`whnf` (`tc.rs:451`) does beta+zeta+delta; `whnf_no_unfolding` (`tc.rs:368-372`)
omits δ so `lazy_delta_step` can drive it lazily (`tc.rs:905`). `def_eq` order
(`tc.rs:885-935`): whnf-no-δ → proof-irrelevance → lazy-delta → structural /
eta. `Opaque` is admitted but never δ-unfolds; `Axiom` never unfolds
(`tc.rs:25-26`).

Caches: `infer_cache: HashMap<ExprId, ExprId>` (`tc.rs:240`) and
`def_eq_cache: HashMap<(ExprId, ExprId), bool>` (`tc.rs:244`), **both cleared on
every local-context push/pop** (`tc.rs:277-278`, `:296-297`). See §6.

### `env.rs` (409 lines)

`Declaration` kinds: `Axiom`, `Definition`, `Theorem`, `Opaque`, `Inductive`,
`Constructor`, `Recursor` (+ `RecRule`, `ReducibilityHint`). **There is no
`Quot` declaration kind** (`env.rs:21` notes quotient reduction is out of
scope). Admission gate is `add_declaration` (`tc.rs`, per `tc.rs:22-23`).

### `inductive.rs` (1131 lines) — inductive gate, recursor generation, ι

Supports **parametric** (`m` params) + **indexed** (`k` indices) families
(`inductive.rs:1-25`). Generates the recursor *and infer-checks its own
generated type as a self-check* (`inductive.rs:67-71`) — a good pattern. ι-rules
are `RecRule`s built at `inductive.rs:61-66`.

**Families reachable today**: enums/structures (slice 4), direct-recursive
non-indexed (`Nat`, `List`, trees — slice 5), parametric (`List`, `Option`,
`Prod`, `Sum` — slice 6), non-recursive indexed (`Eq`, indexed enums — slice 7).
A field is "direct recursive" iff its type is *exactly* `I p_1…p_m` and `k = 0`
(`inductive.rs:26-28`) — trivially strictly-positive, so **no positivity checker
exists or is needed for the admitted fragment**.

**The P0 fix** lives at `inductive.rs:275-280`:

```rust
let allows_large_elimination = self.level_is_nonzero(result_level)
    || match checked.as_slice() {
        [] => true,                              // empty ⇒ anything
        [ctor] => ctor.exposes_non_prop_fields,  // syntactic subsingleton
        _ => false,                              // ≥2 ctors in Prop ⇒ Prop-only
    };
```

`level_is_nonzero` (`lib.rs:751-755`) is `leq(1, l)` — i.e. it only returns
`true` when the level is *provably* ≥ 1, and falls through to the restrictive
branch otherwise. **This is the conservative direction**: a level it cannot
prove nonzero (e.g. a bare `Param u`) is treated as possibly-`Prop` and gets the
restricted recursor. Correct default.

> **Independently re-validated by execution** (not by reading the fix). Driving
> the P0 shape through the public API on a throwaway probe — `Bool2 : Prop | tt
> | ff` via `add_inductive`, i.e. the exact non-subsingleton `Prop` family —
> confirms all three legs of the fix simultaneously:
>
> - `add_inductive` **admits** the family (`Ok(())`) — the fix constrains the
>   *eliminator*, not the *declaration*, as intended;
> - the generated `Bool2.rec` carries **zero universe parameters**, so
>   `Bool2.rec.{1}` fails `infer` with `UniverseArityMismatch { expected: 0, got:
>   1 }` and `whnf` refuses to ι-reduce it — large elimination is unreachable,
>   not merely discouraged;
> - `def_eq(tt, ff)` still returns **`true`** — proof irrelevance is retained.
>
> The pre-fix build reduces `Bool2.rec.{1} (fun _ => Prop) P Q tt` to `P` and the
> `ff` case to `Q`, separating two terms that proof irrelevance makes equal. That
> is the P0, reproduced and then observed to be closed. This matches what
> `tests/prop_large_elim_soundness.rs` asserts, and confirms those assertions
> bite rather than pass vacuously.
>
> One live hazard surfaced while doing this, worth recording because it is a
> *process* defect rather than a code one: the fix landed **mid-audit** (HEAD
> moved `d342ee90` → `f243d317`), and a stale `cargo` build served the pre-fix
> kernel to a probe run against post-fix sources — briefly manufacturing a
> convincing false positive. Any re-validation of a soundness fix in this shared
> checkout must confirm the HEAD it actually built against.

### The preludes — see §5. `lean_pp.rs` (1598 lines) — see §3.

---

## 2. The remaining gap list

For each: what it blocks, sizing, and — the load-bearing column — whether it is
deferred by **REJECTION** (kernel refuses; safe) or by **PERMISSION** (kernel
accepts something it cannot justify; the P0 pattern).

### 2.1 Sizing table

| # | Gap | Rejecting error variant (`file:line`) | Blocks in practice | Size | LoC | Sound-critical? | Deferral mode |
|---|---|---|---|---|---|---|---|
| 1 | **`Proj` / structure projections** | *none — not representable* (`expr.rs:80-98`) | Structure eta, `Prod.fst`-style defeq, most mathlib terms | **L** | ~600-900 | Yes | **REJECTION (by absence)** |
| 2 | **`Lit` typing/reduction** | `UnsupportedLit` (`tc.rs:120`, raised `tc.rs:1138`) | Any `Nat`/`String` literal in a goal | **M** | ~400-600 | Yes | **REJECTION** |
| 3 | **Bignum `Nat`** (`u128` payload) | *none — silent width* (`expr.rs:63`) | Literals ≥ 2^128; BV widths >128 | **S-M** | ~150-300 | Yes | **⚠ see §2.2** |
| 4 | **`Quotient` (`Quot`/`Quot.lift`/`Quot.ind`)** | *none — no decl kind* (`env.rs:21`) | `Int`/`Rat` as Lean defines them, setoids | **M** | ~300-500 | Yes | **REJECTION (by absence)** |
| 5 | **Recursive indexed inductives** | `RecursiveIndexedNotSupported` (`tc.rs:205`, raised `inductive.rs:423`) | `Vector`, `Fin`-indexed families, most DTT data | **L** | ~500-800 | Yes | **REJECTION** |
| 6 | **Reflexive / higher-order fields** | `ReflexiveOrNestedNotSupported` (`tc.rs:173`, raised `inductive.rs:512`, `:528`) | `W`-types, `(A → I) → I` | **L** | ~400-700 | Yes | **REJECTION** |
| 7 | **Nested inductives** | folded into `ReflexiveOrNestedNotSupported` (`inductive.rs:33-36`) | `Expr`-like ASTs (`List (Tree α)`) | **XL** | ~800-1200 | Yes | **REJECTION** |
| 8 | **Mutual inductives** | *no API to express* (`inductive.rs:36`) | Mutually-recursive ASTs | **L** | ~500-800 | Yes | **REJECTION (by absence)** |
| 9 | **Well-founded recursion** | *n/a — elaborator-level* | `WellFounded.fix` defs from real Lean exports | **L** | ~400-700 | No (kernel sees the term) | **REJECTION (by absence)** |
| 10 | **Definitional eta for structures** | *n/a — needs `Proj` first* | Structure defeq; blocked behind #1 | **M** | ~200-400 | Yes | **REJECTION (by absence)** |
| 11 | **Ill-shaped recursive self-ref** | `RecursiveInductiveNotSupported` (`tc.rs:162`, raised `inductive.rs:522`) | parametric/indexed self-refs | — | — | Yes | **REJECTION** |
| 12 | **Positivity checker** | *not needed for admitted fragment* (`inductive.rs:26-28`) | Prerequisite for #5-#8 | **M** | ~300-500 | **Yes — critical** | **REJECTION (vacuous today)** |
| 13 | **Prelude axioms undischarged** | *none — asserted* (`arith_prelude.rs`, `int_prelude.rs`) | — | **XL** | ~2000+ | **Yes** | **⚠ PERMISSION — see §2.2** |
| 14 | **Broad export-format admission** | initial fail-closed `lean4export` 3.1 reader admits two exact fixture profiles | Ingesting dependency-closed `Init`/`Std`/mathlib | **L, WIP** | reader landed; kernel breadth open | No (kernel re-checks) | **REJECTION with typed declines** |

> **Sizing caveat — read §2.3 before costing this table.** Checked against the
> Lean 4 kernel, rows **#7 (nested)** and **#9 (well-founded)** are *elaborator*
> features that never reach Lean's kernel; as kernel work they are ~zero, and the
> table over-charges them by ~1200–1900 LoC. Rows **#5 and #6** are a single work
> item in the reference implementation, not two. §2.3 restates the real blocking
> spine.

### 2.2 Audit for the P0 pattern — deferred-by-PERMISSION cases

I checked every deferral above against the P0 shape ("kernel *permits* a rule it
cannot justify"). **Gaps #1, #2, #4-#12 are all deferred by rejection**: each
either raises a `KernelError` before admission or is not expressible in the
data types at all. Rows #5, #6, #11 return errors from the `add_inductive` gate
*before* any recursor is generated, and the gate rolls the environment back on
failure (`inductive.rs:252-256`, `:295-301`) — so a rejected inductive leaves no
partial declaration behind. That is the safe shape. **No second instance of the
P0 kernel-rule pattern exists.**

Two findings do *not* fit the clean-rejection story:

> #### ⚠ Finding A — the prelude axioms are trust-by-assertion (row #13)
>
> `arith_prelude.rs` and `int_prelude.rs` do not *construct* ℝ or ℤ; they
> **axiomatize** them. The carrier `R : Type` is an opaque
> `Declaration::Axiom` (`arith_prelude.rs:20-21`, `:177`); ditto `Z : Type`
> (`int_prelude.rs:21-22`, `:219`). Every operation and every order/ring law is
> a further axiom, minted through a `declare_axiom` helper
> (`arith_prelude.rs:661-665`, `int_prelude.rs:829`).
>
> **Exact counts, by census rather than estimate.** Building each prelude and
> counting `Declaration::Axiom` in the resulting environment (an earlier estimate
> from `NameId` struct-field counts — "~35/~39/~7" — over-counted, since a field
> may name an inductive, ctor, or recursor rather than an axiom):
>
> | Prelude | **Axioms** | ind | ctor | rec | def |
> |---|---|---|---|---|---|
> | `prelude.rs` (logic) | **0** | 9 | 11 | 9 | 1 |
> | `arith_prelude.rs` | **30** | *(logic)* | | | |
> | `int_prelude.rs` | **34** | *(logic)* | | | |
> | `string_prelude.rs` | **1** (`axeyum.string.append`) | | | | |
>
> **The real arithmetic axiom surface is 64, not ~74** — and the logic prelude's
> zero is confirmed by execution, not by grep. The full arith set is `zero, R,
> add, mul, neg, one, le, lt, le_refl, le_trans, lt_irrefl, lt_trans,
> lt_of_lt_of_le, lt_of_le_of_lt, le_of_lt, add_le_add, add_comm, add_assoc,
> add_zero, add_neg, mul_le_mul_of_nonneg_left, zero_lt_one,
> add_lt_add_of_le_of_lt, mul_comm, mul_assoc, mul_one, mul_zero, left_distrib,
> mul_nonneg, sq_nonneg`; the int set is the same spine minus `sq_nonneg` plus
> `no_int_between, le_total, lt_of_le_of_ne, euclidean_decomposition, eq_em`.
> These two lists **are** the machine-checked inventory recommended in §5 —
> they cost one test to freeze.
>
> A side-effect worth recording: arith and int declare their operations under the
> **same anonymous-root names** (`add`, `mul`, `neg`, `one`, `le`, `lt`, `zero`),
> so the two preludes **cannot coexist in one `Kernel`** — a second build would
> hit `DeclarationExists`. Fine while a refutation is single-theory; a blocker the
> day a goal mixes LRA and LIA.
>
> The kernel type-checks each axiom's **type** at admission
> (`arith_prelude.rs:10-12`) — but a well-typed axiom is not a true axiom. The
> content of `mul_le_mul_of_nonneg_left`, `no_int_between`
> (`int_prelude.rs:34-35`), `euclidean_decomposition` (`int_prelude.rs:40-43`),
> `eq_em` (`int_prelude.rs:44-47`) is **asserted, never proved and never
> discharged against mathlib**. A single subtly-wrong axiom silently unsounds
> every LRA/LIA reconstruction built on it, and *no gate in the tree would
> catch it*.
>
> This is not the P0 rule-permission pattern, but it is the same *genus*:
> soundness resting on an unverified permission. It is the largest remaining
> soundness surface in the crate, and it is invisible to the current tests.
> **Crucially, the real-Lean cross-check cannot catch it** — see §3.
>
> Mitigation is cheap relative to the risk: emit each prelude axiom as a
> mathlib `theorem` obligation (`example : <axiom type> := by exact?`) and
> discharge it in CI against a mathlib toolchain. That converts **64** assertions
> into 64 checked theorems — and most are named exactly as their mathlib
> counterparts (`add_comm`, `mul_assoc`, `left_distrib`, `le_total`), so the bulk
> should discharge by `exact?` with no manual proof at all.

> #### ⚠ Finding B — `Lit::Nat(u128)` is a width, not a rejection (row #3)
>
> Unlike every other deferral, the bignum gap is **not** guarded by an error
> variant. `Lit::Nat` simply holds a `u128` (`expr.rs:63`). Today this is inert
> because `UnsupportedLit` (`tc.rs:1138`) rejects *all* literals before typing —
> so the truncation is unreachable and the gap is *currently* safe by accident,
> not by design. **The moment gap #2 (`Lit` typing) is implemented, this becomes
> a live silent-truncation hazard**: a `Nat` literal from a real Lean export
> exceeding 2^128 would need to either wrap, saturate, or be rejected, and
> nothing in the type forces that choice to be made explicitly.
>
> **P6.0 must land bignum `Nat` *before or with* `Lit` typing, never after.**
> If sequencing forces `Lit` typing first, the parser/ingest boundary must raise
> an explicit `LitTooWide` error rather than truncate. This is the one place in
> the crate where a future slice could reintroduce a P0-shaped defect by
> omission.

### 2.3 How the real Lean 4 kernel implements each gap

Sizing above is only defensible against a reference implementation. For each gap,
where the work lives in Lean 4 — and, decisively, **whether it is kernel work at
all**. Two rows (#7, #9) are *elaborator* features that never reach Lean's kernel,
which changes what "implementing" them means for us.

| # | Gap | How Lean 4 does it | Consequence for our sizing |
|---|---|---|---|
| 1 | `Proj` | `Expr.proj structName idx struct` is a **first-class term constructor**. `whnfCore` reduces `proj i (C params fields…)` → `fields[i]`; `inferProj` types it by walking the sole constructor's telescope, substituting earlier projections of the same struct into later field types. | Confirms **L**. It is a *term-language* change, not an add-on: every match on `ExprNode` changes. Our nine-variant enum becomes ten. |
| 2 | `Lit` | `Literal.natVal`/`strVal` are normal forms. Kernel special-cases **GMP-accelerated** `Nat.add/sub/mul/div/mod/decEq/decLt/decLe/beq/ble` (`reduceNat`/`reduceBinNatOp`), plus bidirectional `Nat.succ n ↔ lit (n+1)` and `strLitToConstructor` (`String` literal ↔ `String.mk (List.cons …)`). | Confirms **M**, and reveals scope our estimate understates: literal *typing* is easy; the **accelerated arithmetic reductions** are what make `Nat` usable. Without them, `2^64` unary-succs. |
| 3 | Bignum `Nat` | `Nat` literals are **arbitrary-precision** (GMP `mpz`, small-int fast path). There is no width. | Confirms **Finding B**: Lean has *no* truncation case because the type admits none. Our `u128` is a divergence from the reference, not a simplification of it. |
| 4 | `Quotient` | **Built-in, not user-declarable.** `addQuot` (`quot.cpp`) injects `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`; `quotReduceRec` in the type checker reduces `Quot.lift f h (Quot.mk r a) → f a` and `Quot.ind p (Quot.mk r a) → p a`. `Quot.sound` is an axiom. | Confirms **M**. It is a *closed, fixed* feature — four constants and two reduction rules, no general machinery. Well-bounded work. |
| 5 | Recursive indexed | `inductive.cpp` handles indices uniformly: motive is `Π indices (major : I params indices), Sort v`; for a recursive field of type `I params idxArgs…`, the IH is `motive idxArgs… field` — the recursive occurrence's **own** index arguments. | Confirms **L**. Our `mk_recursor` already threads *constructor* index expressions into minors (`inductive.rs:660`); the missing piece is doing the same for a *recursive field's* indices. Closer than the sizing implies. |
| 6 | Reflexive / higher-order | Supported natively: for a field `f : A → I params`, the IH is `Π (a : A), motive (f a)`. Same `mk_minor_premise` machinery, gated by the strict-positivity check. | Confirms **L**, and shows #5/#6 are **one body of work**, not two: both are "generalize the IH from `motive f` to `Π telescope, motive (f args)`". Landing them together is cheaper than the table's ~900–1500 combined suggests. |
| 7 | Nested | **The kernel never sees a nested inductive.** `Lean/Elab/Inductive` compiles nesting to *mutual* inductives over an auxiliary type, then derives the nested recursor as a definition. | **Re-sizes #7 (XL) downward as kernel work — to zero.** Nesting is a *front-end* obligation and is only reachable once #8 (mutual) exists. Our XL/~800-1200 estimate mis-attributes elaborator work to the kernel. |
| 8 | Mutual | Kernel `addInductive` takes a **list** of `InductiveType`s, emitting one recursor per type sharing minor premises; `RecursorVal.numMotives > 1`. | Confirms **L**, and identifies the concrete shape: our `Declaration::Recursor` already carries `num_motives` (`env.rs:202`), hard-wired to `1` (`inductive.rs:854`). The field was designed for this. |
| 9 | Well-founded recursion | **Elaborator-level.** `WellFounded.fix` + `WF.fix_eq`; the kernel only ever sees the resulting term. The kernel's real obligation is reducing `Acc.rec` — an inductive with a **reflexive** field. | **Re-sizes #9 as kernel work — to zero, but re-points it**: what we actually need is #6, since `Acc` is reflexive. `Acc.rec` is the hidden dependency behind every well-founded definition in a real export. |
| 10 | Structure eta | `isDefEqEtaStruct` in `type_checker.cpp`: if one side is a constructor application of a single-constructor non-recursive structure and the other is not, expand the other via projections and retry. | Confirms **M**, strictly behind #1 as stated. |
| 12 | Positivity | `inductive.cpp` checks `I` occurs **strictly positively** in every constructor argument — a real check, run at admission, on which #5–#8 all depend. | Confirms **M** and confirms the hazard: in Lean this check is *load-bearing from day one*. In ours it is vacuous only because the admitted fragment is so narrow. |
| 14 | Export reader | Lean itself does not read the export format — `lean4export` *writes* it; independent checkers (`trepplein`, `nanoda`, `lean4lean`) read it. **The format exists precisely for third-party kernels like ours.** | The initial reader now confirms the seam: flat and direct-recursive fixtures admit independently, while projection/literal/quotient records decline structurally. Broad dependency-closed admission remains the L-sized target. |

**Three corrections to §2.1 fall out of this comparison**, all in the same
direction — we have over-sized the inductive work by mis-attributing
elaborator features to the kernel:

1. **#7 (nested) and #9 (well-founded) are not kernel work.** Lean compiles both
   away before the kernel sees them. Together the table charges them ~1200–1900
   LoC of *kernel* effort that does not exist. #9's real kernel content is
   `Acc.rec`, i.e. #6.
2. **#5 and #6 are one work item.** Both generalize the induction hypothesis from
   `motive f` to `Π telescope, motive (f args…)`. Lean implements them in a single
   pass. Landing them separately means building the same machinery twice.
3. **The true blocking spine of the inductive layer is #12 → (#5 + #6) → #8**,
   and *that* is what unlocks `Vector`, `Acc`, well-founded recursion, and — via
   the elaborator-style nesting compile — #7. Positivity first is not merely
   prudent sequencing (§4's hazard); it is the reference implementation's own
   dependency order.

---

## 3. The export-format reader and the real-Lean cross-check

**2026-07-21 update:** there is now a separate, fail-closed
`axeyum-lean-import` reader for pinned `lean4export` 3.1 NDJSON. It keeps JSON
and malformed-input handling outside the zero-dependency kernel, then admits
supported records only through `Kernel::add_declaration` and
`Kernel::add_inductive`. The exact flat fixture becomes eight checked
declarations; direct-recursive `MiniNat`/`MiniList` becomes 11 with zero axioms.
Projection, literal, quotient, and harder-inductive constructs remain explicit
declines. Direct `.olean` parsing remains absent by design.

The [interoperability roadmap](../../plan/lean-system-compatibility-roadmap-2026-07-21.md),
[Rust import result](../../plan/lean4export-rust-import-prototype-2026-07-21.md),
and [official blocker census](../../plan/lean4export-official-blocker-census-2026-07-21.md)
supersede the original construction-only status. The architectural conclusion
survives: the interchange is the intended third-party seam, and parsing alone
never grants theorem credit.

### Does the cross-check actually run, or skip-and-pass?

**Correction after executing the solver-proof gate (2026-07-21):** the
standalone inductive test was fail-closed, but the CI job did not reach it and
the 71-family solver harness could still skip. The repaired state is:

- The test `restricted_prop_recursor_checks_in_real_lean`
  (`tests/real_lean_inductive_crosscheck.rs:83-126`) locates Lean via
  `AXEYUM_LEAN_BIN` or `PATH` (`:14-25`).
- On a missing binary it **does** early-return (`:92-100`) — *but* guarded by
  `assert_ne!(env::var("AXEYUM_REQUIRE_LEAN"), Ok("1"))` (`:93-97`). So a skip
  is a **hard failure** when the flag is set.
- CI sets `AXEYUM_REQUIRE_LEAN: 1`, installs checksum-pinned elan without
  requiring a Lake manifest, asserts `lean --version`, and runs the test.
- The solver harness now independently rejects a missing Lean binary or any
  incomplete required sweep and emits an exact checked-family attestation.
- A bounded local official-Lean run initially accepted 67/71 representative
  modules and exposed four export failures; after preserving the required
  Bool/BV iota rules and one measured elaborator-depth bound, the same cell
  accepts 71/71 with zero skips or failures. Remote CI acceptance remains open.

So: **skipping remains optional locally, while required runs now fail closed.**
The complete diagnosis, negative control, and non-claims are in the
[official-Lean gate audit](../../plan/official-lean-ci-gate-audit-2026-07-21.md).

**What it actually checks** (`:27-81`): it builds `Two : Prop | a | b` — the
exact P0 shape — through `add_inductive`, confirms Axeyum's restricted `Two.rec`
applies with a `Prop` motive, builds `Eq.{0} True selected trivial` proved by
`Eq.refl`, checks it with `infer`/`def_eq` (`:72-73`), then renders a Lean module
with **real `inductive` commands** (`render_lean_module_with_inductives`, `:75`)
and requires real Lean to accept it (`:115-119`). It asserts the module contains
`inductive Two : Prop where` and `@Two.rec` and — importantly —
**`!source.contains("axiom Two.rec")`** (`:89`) and `!contains("sorryAx")`
(`:90`, `:120`), plus a `#print axioms` audit (`:121-124`).

That `axiom Two.rec` negative assertion is the load-bearing one: it forces Lean
to *regenerate* the recursor from a real `inductive` command and check the iota
rule itself, rather than being handed Axeyum's claim as an axiom.

### The limit of this cross-check (ties to Finding A)

`lean_pp.rs` renders inductives/constructors/recursors as `axiom`s **by default**
(`lean_pp.rs:141-143`, `:427`, `:441`, `:469`, `:484`); only
`render_lean_module_with_inductives` (`:175-187`) emits real `inductive`
commands, and it **falls back to axiom rendering** for families that are
parametric or indexed (`lean_pp.rs:187`). Consequences:

1. The cross-check's teeth extend only to **non-parametric, non-indexed**
   families. `Eq`, `List`, `Nat` cross-checks would silently degrade to the
   axiom rendering, which Lean accepts vacuously.
2. **Any arith/int prelude module rendered to Lean is vacuous as to axiom
   *content***: Lean accepts any well-typed `axiom`. `#print axioms` confirms
   *which* axioms a proof depends on, never that they are *true*. The
   `#print axioms` audit is an *inventory*, not a *validation* — the note at
   `lean_pp.rs:144-146` ("only the expected uninterpreted/`em`/`propext`-class
   axioms") is the right framing, but it must not be read as discharging them.

---

## 4. Test posture (post-fix)

**~181 `#[test]`s**, all deterministic unit/integration tests:

| Location | Tests |
|---|---|
| `src/tests.rs` | 37 |
| `src/inductive/inductive_tests.rs` | 32 |
| `src/tc/tc_tests.rs` | 29 |
| `src/prelude/prelude_tests.rs` | 23 |
| `src/env/env_tests.rs` | 16 |
| `src/lean_pp.rs` | 12 |
| `src/string_prelude/tests.rs` | 12 |
| `src/arith_prelude/arith_prelude_tests.rs` | 9 |
| `src/int_prelude/int_prelude_tests.rs` | 7 |
| `tests/prop_large_elim_soundness.rs` | 2 |
| `tests/prop_large_elim_derives_false.rs` | 1 |
| `tests/real_lean_inductive_crosscheck.rs` | 1 |

**Negative testing exists and is decent.** Each deferral boundary has a test
asserting the *rejection*: `UnsupportedLit` (`tc/tc_tests.rs:341`,
`env/env_tests.rs:460-467`), `ReflexiveOrNestedNotSupported`
(`inductive/inductive_tests.rs:268`, `:1997`), `RecursiveIndexedNotSupported`
(`inductive/inductive_tests.rs:1795-1833`, with a real `Vector`-shaped
`V : Nat → Sort 1` family). This is the right discipline: *the deferral is
tested, not just documented.*

**The new boundary matrix** (`tests/prop_large_elim_soundness.rs`, 153 lines)
is the P0 regression. `non_subsingleton_prop_eliminates_only_into_prop`
(`:34-`) declares `Two : Prop | a | b`, `Answer : Type | yes | no`,
`True : Prop | intro` via a level-parameterized helper (`:13-32`) and asserts:

- proof irrelevance is *retained* — `assert!(k.def_eq(a, b))` (`:53`), with the
  comment (`:50-52`) making the design intent explicit: **constrain the
  eliminator, do not weaken defeq**. That is the correct fix axis.
- the restricted recursor carries **no fresh elimination-universe param**
  (`:56-60`).

It covers the matrix corners (Prop-2-ctor restricted; Type-2-ctor free;
Prop-1-ctor subsingleton), which is exactly the boundary the P0 crossed.
`tests/prop_large_elim_derives_false.rs` (203 lines) keeps the actual
`False`-derivation as a live regression.

**Differential testing against real Lean: exactly one test** (§3), covering one
family shape (nullary-ctor `Prop` enum). That is a keyhole, not a corpus.

### Untested classes at the audit point

- **At the audit point there was no fuzzing/property testing of any kind** in
  this crate — no differential term generator and no random well-typed-term
  round-trip. **Correction, 2026-07-21:** T6.0.3 now supplies a deterministic
  768-case generated seed over the four representable seams, with exact corner
  coverage, repeated summaries, and rejected `False` admission in every case.
  It is not an official-Lean differential term generator; projection/eta and
  quotient seams remain open under TL2.15.
- **No differential coverage** of: `def_eq` (eta × proof-irrelevance ×
  lazy-delta interaction), universe `leq` (ported but only nanoda's tests),
  parametric/indexed recursor generation vs Lean's, ι-reduction vs Lean's.
  The generated-recursor self-check (`inductive.rs:67-71`) is an *internal*
  consistency check — it verifies the recursor type infers, not that it matches
  what Lean would generate.
- **No negative test that the kernel rejects what Lean rejects** beyond the
  deferral boundaries — e.g. no test feeding a *non-positive* inductive
  (`Bad : Type | mk : (Bad → Bad) → Bad`) and confirming rejection. Today it
  *is* rejected, but incidentally, via `ReflexiveOrNestedNotSupported`
  (`inductive.rs:512`) rather than by a positivity checker. **When gaps #5-#8
  land, that incidental rejection disappears and positivity (row #12) becomes
  load-bearing overnight.** This is the single highest-risk sequencing hazard in
  P6.0 after Finding B.
- **The 64 arithmetic/integer prelude axioms are untested as to truth**, as is
  the string prelude's opaque `append` assumption (Finding A). The
  prelude tests (`arith_prelude_tests.rs`, 9; `int_prelude_tests.rs`, 7) build
  refutation proof *terms* on the axioms and `infer`-check them
  (`arith_prelude.rs:12-14`) — this validates the *reconstruction*, and assumes
  the axioms.

**Honest read**: the posture is *good on the shapes it knows about* and
*structurally blind on the shapes it doesn't*. Rejection-boundary discipline is
genuinely strong; the P0 regression is well-constructed and fixes the right
axis. But 181 hand-written examples + 1 real-Lean keyhole is thin for a trusted
core, and the CLAUDE.md hard rule — "a corpus sweep + a fuzz that avoids the
corner is not a soundness gate" — applies with full force here: **there is no
fuzz at all**, so every corner is a corner the gate avoids. The P0 itself was
found by reasoning, not by a test; nothing in the current suite would have
caught it before it was hypothesized.

---

## 5. The preludes

Four axiom sets, all admitted through the trusted `add_declaration` gate (so
every axiom's *type* is kernel-checked at admission):

| Prelude | What it is | ~Names/axioms |
|---|---|---|
| `prelude.rs` (1085) | **Logic**: `False`, `Not`, `And`, `Or`, `Eq`, `True`, + datatype families. Built from **real `add_inductive` calls**, not axioms | **0 axioms** (9 ind / 11 ctor / 9 rec / 1 def) |
| `arith_prelude.rs` (675) | **Axiomatized linear ordered field** ℝ for LRA/Farkas reconstruction (`:1-14`) | **30 axioms** |
| `int_prelude.rs` (839) | **Axiomatized discretely-ordered commutative ring** ℤ for LIA/Diophantine (ADR-0042) | **34 axioms** |
| `string_prelude.rs` (496) | String carrier + ops | **1 axiom** (`axeyum.string.append`) |

**The logic prelude is the healthy one**: it is *constructed* inductively, so
its recursors are generated and self-checked, and it carries zero axioms. The
arith/int preludes are the opposite: pure assertion (Finding A, §2.2).

**Axiom-tracking discipline: partial.** What exists is real but doesn't close
the loop:

- Every axiom flows through one `declare_axiom` helper
  (`arith_prelude.rs:661-665`, `int_prelude.rs:829`) — a single choke point,
  which is good and makes an audit tractable.
- Each axiom's exact type is documented on its `ArithPrelude`/`IntPrelude`
  struct field (`arith_prelude.rs:31-33`).
- `lean_pp.rs` emits `#print axioms <theorem>` (`:135`, `:353`) so a rendered
  refutation's axiom dependencies are enumerable, and the intent
  (`lean_pp.rs:144-146`) is that only expected uninterpreted/`em`/`propext`-class
  axioms appear.
- The int prelude is visibly *disciplined about scope*: `eq_em` is
  integer-specific decidable equality, "**not** unrestricted propositional
  excluded middle" (`int_prelude.rs:46-47`); `euclidean_decomposition` states
  the theorem "without adding division or modulo operations"
  (`int_prelude.rs:42-43`). Someone was thinking carefully about minimality.

**What's missing**: no machine-checked inventory (no test asserts "the arith
prelude declares exactly these N axioms and no more" — an axiom could be added
without any gate noticing), and, decisively, **no discharge of any axiom against
mathlib**. Minimality discipline without a truth check is necessary, not
sufficient.

---

## 6. Performance

**There are no benchmarks for this crate.** No `benches/` directory, no
`[[bench]]` in `crates/axeyum-lean-kernel/Cargo.toml`, no criterion dep, and
`axeyum-bench` has no kernel workload. Only `axeyum-solver` depends on the
kernel, optionally and feature-gated
(`crates/axeyum-solver/Cargo.toml:21`, `:45`).

This matters competitively: **`bv_decide`'s known bottleneck is kernel
reduction speed, not solve time**, and this kernel would sit in a goal layer's
inner loop. The crate is currently un-instrumented on exactly the axis that
decides whether a goal layer is viable. There is no baseline, so there is no way
to detect a regression — or to know whether the design choices below are paying
off.

**Interner design** (already thoughtfully built for scale — `lib.rs:81-167`):

- `EXPR_INTERN_SHARDS = 64` (`lib.rs:81`), `EXPR_ARENA_CHUNK_CAPACITY = 1 << 18`
  (`:82`).
- `SegmentedVec<T>` (`:90-93`): fixed chunks that **grow without relocating**, so
  a large proof arena never needs old+doubled buffers live simultaneously
  (`:84-88`). `ExprId` stays one monotone integer; segmentation is internal.
- `ExprInterner` (`:149-152`): 64 `HashMap<u64, ExprId>` shards + an explicit
  `collisions: HashMap<u64, Vec<ExprId>>` fallback — hash-consing that
  **handles collisions correctly** rather than trusting a 64-bit hash. Sharding
  bounds any one rehash to ~1/64 of the table (`:144-147`) and **preserves
  insertion-ordered `ExprId` assignment**; the shard hash is explicitly not
  observable in output (`:147`) — the determinism hard rule is respected.

**The likely hot spot nobody has measured**: `infer_cache` (`tc.rs:240`) and
`def_eq_cache` (`tc.rs:244`) are **fully cleared on every `LocalContext`
push/pop** (`tc.rs:277-278`, `:296-297`). Since opening *any* binder pushes a
local, checking a deeply-binder-nested term repeatedly discards all memoization.
The comment at `tc.rs:238-239` acknowledges this ("Push/pop clear this cache, so
open expression DAGs are shared…"), and it is the *conservative* choice — the
caches are context-sensitive, so retaining them across a context change would be
unsound. But nanoda and Lean both use context-aware caching to avoid exactly this
cliff. **Sizing: M (~200-400 LoC) to make the cache key context-aware; needs a
benchmark first to confirm it's the bottleneck rather than assumed.**

---

## What must be true before a goal layer can sit on this kernel

Ordered by whether they *block* a goal layer or merely bound its scope.

**Hard blockers (a goal layer cannot be built without these):**

1. **`Lit` typing + bignum `Nat`, landed together** (gaps #2 + #3). Any real
   goal contains numerals. Per **Finding B**, bignum must land *before or with*
   literal typing, or the ingest boundary must raise an explicit `LitTooWide`
   rather than truncate. Sequencing these wrong reintroduces a P0-shaped defect
   by omission. **M, ~550-900 LoC.**
2. **A positivity checker, landed *before* gaps #5-#8** (row #12). Today
   non-positive inductives are rejected *incidentally* by
   `ReflexiveOrNestedNotSupported` (`inductive.rs:512`). The moment recursive
   indexed / reflexive / nested families are admitted, that incidental
   rejection vanishes and positivity becomes the only thing standing between the
   kernel and `False`. **This is the highest-risk item in P6.0** and must be
   accompanied by a negative-test corpus (`Bad : Type | mk : (Bad → Bad) → Bad`
   and friends) that fails loudly. **M, ~300-500 LoC.**
3. **`Proj` in `ExprNode` + structure eta** (gaps #1 + #10). Not representable
   today; touches the term language, so every traversal, `instantiate`,
   `abstract`, `whnf`, `infer`, and `def_eq` site changes. **Land it early** —
   it is the most invasive change remaining and gets harder with every slice
   built on the current nine-variant enum. **L, ~800-1300 LoC.**
4. **A performance baseline** (§6). The kernel would sit in the goal layer's
   inner loop and `bv_decide`'s bottleneck is precisely kernel reduction speed.
   Building a goal layer on an un-benchmarked kernel means discovering it is too
   slow after the dependency is load-bearing. Baseline first, then decide on
   context-aware caching. **S to instrument, M to fix.**

**Soundness obligations (the goal layer's results are only as good as these):**

5. **Classify and discharge the 65 ledgered prelude assumptions** (Finding A).
   Until then, every LRA/LIA reconstruction rests on 64 unproven arithmetic/
   integer assertions, while string reconstruction rests on one opaque `append`
   assumption. No official-Lean cross-check can establish those premises (§3).
   This is the largest unguarded soundness surface in the crate.
   **XL as stated, but the first 80% is mechanical**: emit each axiom type as a
   mathlib obligation and discharge in CI.
6. **A machine-checked axiom inventory.** Assert that each prelude declares
   exactly its expected axiom set, so a new axiom cannot be added silently.
   **S, ~50-100 LoC.** Cheapest item on this list; do it now.
7. **Differential testing against real Lean, widened past the keyhole.** One
   test on one family shape is not a differential suite. Requires
   `render_lean_module_with_inductives` to stop falling back to axiom rendering
   for parametric/indexed families (`lean_pp.rs:187`) — otherwise widening the
   corpus silently widens the *vacuous* region. **M.**
8. **A fuzz/property layer.** There is none. Per CLAUDE.md's hard rule, a
   hand-written corpus that avoids a corner is not a gate on that corner — and
   right now every corner is avoided. Minimum: a well-typed-term generator
   round-tripped through `infer`/`def_eq`, plus a generator that deliberately
   emits each deferral's degenerate shape. **M-L.**

**Scope bounds (not blockers — they cap what the goal layer can express):**

9. `Quotient` (#4) blocks Lean-faithful `Int`/`Rat`; today the preludes route
   around it by axiomatizing the carriers, which is why #4 is not urgent — and
   also exactly why Finding A exists. Resolving #4 properly *retires* a chunk
   of Finding A's axiom surface. **M, ~300-500 LoC.**
10. Recursive-indexed (#5), nested (#7), mutual (#8) bound the data types
    expressible. `Vector` needs #5. Real mathlib ingest needs all of them.
11. An **export-format reader** (#14) is required to ingest real Lean/mathlib
    terms rather than only construct them via Rust builders. Not
    soundness-critical (the kernel re-checks whatever it reads), but it is the
    difference between a kernel that checks *our* terms and one that checks
    *Lean's*. **L, ~600-900 LoC.**

**The one-line summary:** the kernel is *honestly scoped and safely deferred* —
every gap except the prelude axioms (Finding A) and latent bignum truncation
(Finding B) is deferred by rejection, with a rollback-clean admission gate and
a negative test per boundary. **No second instance of the P0 permission pattern
exists in the kernel rules.** The exposure has moved out of the kernel and into
(a) the 65 unproven prelude assumptions the reconstruction layer trusts, and
(b) the sequencing hazards — bignum-after-`Lit`, and positivity-after-recursive
inductives — either of which would let a P0-shaped defect back in by omission
rather than by commission.

---

## Addendum (verified by execution, 2026-07-15)

Three corrections/extensions to the above, each checked by running code rather
than reading it.

### Historical helper-call census: 64, superseded by runtime population 65

By census of `declare_axiom(` call sites:

| prelude | axioms |
|---|---|
| `prelude.rs` (logic) | **0** |
| `arith_prelude.rs` (ℝ) | **30** |
| `int_prelude.rs` (ℤ) | **34** |
| `string_prelude.rs` | **0** |
| **total** | **64** |

The "~74" that circulated through the design docs was an estimate presented as a
count — the same unsourced-number sin this track flagged twice and then committed
a third time. This table correctly counts helper calls but incorrectly treats
them as the complete runtime population.

**Correction (runtime environment inventory, 2026-07-21):** constructing each
prelude in an independent kernel yields **65** admitted assumptions: real 30,
integer 34, and string 1. `axeyum.string.append` bypasses `declare_axiom(...)`
and is inserted directly as `Declaration::Axiom`, so the helper-call census
missed it. The [machine-checked ledger](../../plan/generated/lean-axiom-ledger.md)
binds all 65 names to canonical type digests and supersedes this call-site count.

### The ℝ and ℤ preludes cannot coexist in one `Kernel` — and it panics

`arith_prelude` and `int_prelude` declare **28 identically-named axioms off the
same anonymous root** (`add`, `mul`, `neg`, `zero`, `one`, `le`, `lt`,
`add_assoc`, `add_comm`, `mul_comm`, `le_trans`, `lt_irrefl`, `zero_lt_one`, …).
They are the same `NameId`.

Probed directly — `build_arith_prelude(&mut k)` then `build_int_prelude(&mut k)`:

```
arith prelude: built
thread '...' panicked at crates/axeyum-lean-kernel/src/prelude.rs:182:14:
True should admit: DeclarationExists { name: NameId(1) }
```

Two things follow, and they point in opposite directions:

1. **The trusted gate behaved correctly.** `add_declaration` *rejected* the
   duplicate with `DeclarationExists` rather than silently aliasing two different
   types (`add : R→R→R` vs `add : ℤ→ℤ→ℤ`) onto one name. Had it aliased, that
   would have been a second soundness hole of the P0's exact family. **Rejection,
   not permission — the discipline held where it mattered.**
2. **The prelude builder panics on the rejection** (`prelude.rs:182`
   `.expect("True should admit")`). It fails *earlier* than the 28 shared names:
   `build_int_prelude` re-builds the logic prelude and collides on `True`
   (`NameId(1)`).

**Consequence:** a goal mixing LRA and LIA cannot be reconstructed in one kernel
today, and the failure mode is a **panic in library code**, not an honest error.
This is not currently reachable — reconstruction builds one prelude per query —
but it is load-bearing the moment theory combination (already shipped: online
Nelson–Oppen, ADR-0060/0066) needs a mixed Lean route.

**Fix:** namespace the preludes (`Real.add`, `Int.add`) and make
`build_*_prelude` idempotent or fallible rather than panicking.

### Two sizing corrections to the table above

- **Nested inductives and well-founded recursion are not kernel work.** Lean
  compiles both away *before* its kernel sees them. The table over-charges by
  ~1200–1900 LoC. Well-founded recursion's real kernel content is `Acc.rec` —
  i.e. reflexive fields.
- **Recursive-indexed and reflexive/higher-order fields are one work item**: both
  generalize the induction hypothesis to `Π telescope, motive (f args)`.

**The real dependency spine is therefore:** positivity checker → (recursive-indexed
+ reflexive) → mutual. Positivity first is not a preference; today's rejection of
the later gaps is what is incidentally enforcing it.
