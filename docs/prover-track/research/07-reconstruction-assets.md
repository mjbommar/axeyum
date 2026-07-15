# 07 — Reconstruction assets: what a prover track could reuse

**Audit date:** 2026-07-15. Bottom-up read of the reconstruction stack, against
`docs/PARITY-STATUS-AND-PATH.md` and `bench-results/DOMINANCE.md`.

Reconstruction is the only existing producer of proof terms in the tree, so it is
the closest thing to a construction layer we have. This note establishes what is
actually there, and — the load-bearing question — how much of it a prover could
stand on.

Scale: `crates/axeyum-solver/src/reconstruct.rs` is 18 531 lines,
`int_reconstruct.rs` 8 880, `crates/axeyum-lean-kernel/src/lean_pp.rs` 1 598.

---

## 1. Inventory

### 1.1 The two-layer shape

Every route is the same pipeline:

```
certificate (Alethe / DRAT / Farkas / congruence / enumeration)
  → ReconstructCtx  (reconstruct.rs:200-260)
  → kernel ExprId proof term        [checked by axeyum-lean-kernel]
  → lean_pp render_lean_module      [optional Lean source text]
```

Both outputs exist for essentially every route: the `ExprId` term is always built
and always kernel-checked; the Lean *source text* is a second, optional rendering
of the same term. The `*_to_lean_module` entry points return `String`
(`reconstruct.rs:3710`), while `prove_unsat_to_lean` (`reconstruct.rs:2162`)
stops at the in-kernel term. So "Lean source" is a *serialization*, never a
separate proof; there is no path that emits Lean text that the in-tree kernel did
not already accept.

### 1.2 Dispatch is shape-recognition, not search

The public entry is `prove_unsat_to_lean_module` (`reconstruct.rs:3710`), and its
first act is:

```rust
let fragment = scan_proof_fragment(arena, assertions);
match reconstruct_proof_fragment_to_lean_module(fragment, arena, assertions) {
```

`scan_proof_fragment` (`reconstruct.rs:1839`) pattern-matches the assertion spine
into one of **40 `ProofFragment` variants** (`reconstruct.rs:1347`+), then
dispatches to a hardcoded reconstructor per variant. The variant list is the tell:
alongside general fragments (`QfBv`, `QfUf`, `Lra`, `Datatype`, `ArrayAxiom`)
sit `TwoByteMemcpy`, `TwoElementBubbleSort`, `TwoElementSelectionSort`,
`TwoCellXorSwap`, `TwoByteXorSwapRoundtrip`, `BinarySearch16`, `FifoBc04`
(`reconstruct.rs:1409-1428`). These are *named after individual benchmark
instances*. `FifoBc04` corresponds to the `fifo32bc04k05` row called out in
`docs/PARITY-STATUS-AND-PATH.md:116`.

This is a catalog of recognized shapes with a bespoke proof recipe behind each,
not a general construction engine. The same story shows in the exported surface
(`crates/axeyum-solver/src/lib.rs:343-517`): ~20 functions named
`reconstruct_<very_specific_shape>_to_lean_module`, e.g.
`reconstruct_bv_vacuous_exists_universal_counterexample_to_lean_module`
(`lib.rs:509`),
`reconstruct_single_pivot_equality_partition_to_lean_module` (`lib.rs:351`).
Each new shape is a new function, not a new lemma in a library.

### 1.3 Per-route table

| Route (file) | Fragment / theory | Input certificate | Output | Kernel-checked in tests |
|---|---|---|---|---|
| `reconstruct.rs` (18 531 L) | QF_BV, QF_UF, QF_UFBV, QF_ABV, arrays, datatypes, quantified BV; 40 `ProofFragment`s | Alethe + DRAT | `ExprId` + Lean text | yes (`prove_unsat_to_lean_module` errors unless the term checks to `False`, per its doc at `reconstruct.rs:3706-3709`) |
| `int_reconstruct.rs` (8 880 L) | Int inequality, Diophantine, affine growth, Euclidean residue, nested xor, counterexample cover | integer Farkas / Diophantine | `ExprId` + Lean text | yes (`tests/diophantine_lean_reconstruct.rs`, `tests/int_inequality_lean_reconstruct.rs`) |
| `word_reconstruct.rs` / `word_alethe.rs` | strings / word equations | Alethe | `ExprId` + Lean text | yes (`tests/word_alethe.rs`) |
| `regex_reconstruct.rs` | `RegexEmptiness` | emptiness witness | `ExprId` + Lean text | yes (`tests/regex_emptiness_lean_reconstruct.rs`) |
| `lex_reconstruct.rs` | lexicographic clash | lex certificate | Lean text (`lib.rs:360`) | yes (`tests/lean_crosscheck.rs`) |
| `reconstruct/quant_bv_instance_set_lean.rs` | quantified BV instance sets | instantiation set | `ExprId` + Lean text | yes (`justfile:29-30`, `--ignored` stress) |
| `qfbv_alethe.rs`, `qfabv_alethe.rs`, `qfufbv_alethe.rs`, `euf_alethe.rs`, `alethe_lra.rs`, `quant_alethe.rs`, `skolem_alethe.rs`, `qfdt_simp_alethe.rs`, `qfuflia_alethe.rs`, `qfabv_elim_alethe.rs`, `bitblast_alethe.rs` | per-theory Alethe *emitters* | solver trace | Alethe (feeds the above) | via consumers |

Note the `*_alethe.rs` files are the *producer* half (solver → Alethe); the
`*_reconstruct.rs` files are the consumer half (Alethe → Lean). The prover would
sit on neither — it has no certificate to consume.

---

## 2. Coverage — real numbers

From `bench-results/DOMINANCE.md:34-57` (audited rows only; the file itself warns
at line 11 that benchmark JSONs "do **not** yet record per-instance Lean
certificate coverage", so unaudited rows are readiness-queue entries, not claims).

Strong Lean-unsat coverage today:

| Division | Decided | Dominant% | Lean unsat |
|---|---|---|---|
| QF_ABV | 169 | 100% (169/169) | 100% (85/85) |
| QF_AUFBV (bitwuzla) | 41 | 100% | 100% (20/20) |
| QF_FF | 24 | 100% | 100% (10/10) |
| QF_FP | 16 | 100% | 100% (7/7) |
| QF_LIA | 10 | 100% | 100% (4/4) |
| QF_LRA | 9 | 100% | 100% (3/3) |
| QF_AX | 8 | 100% | 100% (5/5) |
| QF_BVFP | 7 | 100% | 100% (3/3) |
| QF_ALIA | 6 | 100% | 100% (5/5) |
| QF_DT | 3 | 100% | 100% (3/3) |

Weak / absent:

| Division | Decided | Dominant% | Lean unsat |
|---|---|---|---|
| BV (cvc5 quantified) | 54 | 93% | 78% (14/18) |
| QF_NIA | 33 | 61% | **13% (2/15)** |
| QF_NRA | 32 | 59% | **14% (2/14)** |
| QF_S | 87 | **9%** | 29% (8/28) |
| QF_AUFLIA | 5 | 60% | **0% (0/2)** |

`DOMINANCE.md:17`: "25 rows are decide-strong (Decide% >= 80). 21 have a current
Lean route worth auditing now."

The absolute numbers matter for the prover question: the largest audited
Lean-unsat count is **85** (QF_ABV). Every route above is quantifier-free or
near-quantifier-free. Nonlinear arithmetic (NIA/NRA) and strings — the fragments
where a prover would earn its keep — are exactly where the Lean route is thinnest
(13%, 14%, 29%).

---

## 3. The axiom story

### 3.1 What gets declared

`ReconstructCtx` (`reconstruct.rs:200-260`) declares three axiom classes:

- **EUF carrier-sort atoms** — `atom_const` (`reconstruct.rs:429`), each an
  opaque `_ : α`; and `funcs` (`reconstruct.rs:200`) via `func_const`
  (`reconstruct.rs:448`).
- **Propositional atoms** — `prop_atoms` (`reconstruct.rs:203-204`), documented
  as "the Boolean atoms of the **clausal** layer (a CNF variable / SAT atom),
  each an opaque `Axiom : Prop`".
- **Classical `em`** — `reconstruct.rs:205-213`:

  > The classical excluded-middle axiom `em : Π (p : Prop), Or p (Not p)`,
  > declared lazily on first use by the resolution layer (`None` until then).
  > This is the *only* addition to the trusted base for propositional
  > resolution… Note: the binary-resolution reconstruction this module builds is
  > in fact constructive (it case-splits on a premise it already holds), so it
  > does not consume `em`; `em` is declared to make the classical commitment
  > explicit.

So `em` is declared but not consumed on the binary-resolution path — an honest
over-declaration.

### 3.2 The `axiom_roles` discipline

`axiom_roles: BTreeMap<NameId, String>` (`reconstruct.rs:234`) exists to *audit
closedness*:

> Roles under which hypothesis/`em` axioms were declared during a
> reconstruction… Used to *audit* closedness: after a fused bitwise walk the only
> non-prelude axioms must be the input `assume` hypotheses and `em` — no
> `bridge`/`cong`/`trans`/`bitblast` axiom.

Read via `declared_axiom_roles()` (`reconstruct.rs:409`). The bar is stated at
`reconstruct.rs:12749`.

The mechanism that *earns* that bar is the `bridge` field
(`reconstruct.rs:229-232`) — when `Some`, a BV predicate atom's `Prop` is
*definitionally* its bit-level form, so:

> This makes the `bitblast_*`/`cong`/`trans`/`equiv1`/`equiv2` bridge
> **reflexive**: the bridge clauses become genuine `Prop` tautologies (`¬B ∨ B`)
> rather than opaque axioms, so the reconstructed `False` is closed over only the
> input-assumption hypotheses.

When `None` (the default — "EUF/propositional/per-step paths") "the clausal
translation is the original opaque one — atoms are uninterpreted Props".

**Fully axiom-free routes:** per `PARITY-STATUS-AND-PATH.md:57-60`, the datatype
field-axiom chain reconstructs "**axiom-free** to a kernel-checked `False`".
`PARITY-STATUS-AND-PATH.md:162-164` records a "structural Lean route with no
trust holes". Everything else carries at minimum the input-hypothesis axioms plus
opaque atoms — which is the *correct* encoding (an uninterpreted symbol should be
an axiom), not a defect.

---

## 4. The trusted-reduction ledger (ADR-0031 / P3.0)

`crates/axeyum-solver/src/trust.rs` (387 lines). Purpose (`trust.rs:1-18`):

> every reduction the stack relies on is a named, countable `TrustId` with a
> pedantic level, mirroring cvc5's `TrustId`. This turns the implicit "checked
> **modulo trusted reduction**" caveat into an auditable list — the precondition
> for shrinking the trusted base to zero.

The certified/hole distinction (`trust.rs:7-11`): a reduction is **certified**
when an independent per-query checker re-derives it, and a **trust hole** when it
is a sound (equi)satisfiability transform with no per-query certificate yet.
`ALL_TRUST_IDS` (`trust.rs:126-141`) is the canonical order; the rendered
`trust_ledger_markdown` (`trust.rs:348`) is golden-tested against
`docs/research/08-planning/trust-ledger.md`, "so the doc cannot drift".

### 4.1 Current state — 14 IDs, 8 certified, 6 open holes

Per `is_certified` (`trust.rs:283-300`) and `pedantic_level` (`trust.rs:187-200`):

**Certified (8):** `BitBlast` (ped 8), `Tseitin` (9), `SatRefutation` (9),
`TermLevelEnum` (10), `Farkas` (10), `LraDpll` (9), `Sos` (10), `Diophantine` (10).

**Open holes (6):**

| TrustId | Ped | Why still a hole (`trust.rs`) | ADR |
|---|---|---|---|
| `ArrayElim` | 4 | eager-elim UNSAT re-checkable, but "the lazy/CEGAR `sat` path, lazy extensionality, the array-combined `QF_AUFBV` route, and array `sat` models have no per-query certificate" (`:236-242`) | ADR-0010 |
| `Ackermann` | 4 | eager-elim UNSAT certified; "the lazy/CEGAR `sat` path, the array-combined `QF_AUFBV` route, and arithmetic-sorted function `sat` models" are not (`:228-234`) | ADR-0013 |
| `IntBlast` | **3** | proven-box bounded certified; "the sat-only width ladder / unbounded queries" are not (`:222-226`) | ADR-0014 |
| `DatatypeElim` | 4 | no sub-case certificate noted | ADR-0022 |
| `Fpa2Bv` | 5 | two sub-case witnesses; open for "the large formats (`F32`/`F64`/`F128`, only sampled) and any query using a rounding-bearing op (`fp.add`, `fp.mul`, `to_fp`, …)" — needs "the by-construction rounding-circuit proof (a funded arc, task #70)" (`:271-276`) | ADR-0023 |
| `XorGaussian` | **3** | pure-Gaussian-level-0 certified; "the **interleaved CDCL(XOR)** sub-case (branching needed) is still search-only with no per-query certificate" (`:211-215`) | ADR-0035 |

The ledger is deliberately **conservative**: `is_certified` returns `true` only
when *no* result relying on the reduction is trusted-uncertified. Five of the six
holes therefore have a certified sub-case; the bit is false because coverage is
partial. Per-run truth lives in `TrustStep::certified` (`trust.rs:336-347`), and
`trust.rs:200-210` is explicit that a reviewer "must therefore read
`TrustStep::certified`, not this ledger bit, to know whether a *particular* XOR
`unsat` was certified".

The two pedantic-3 entries (`IntBlast`, `XorGaussian`) are the sharpest: "a wrong
refutation is unsound with no recovery, so it grades low" (`trust.rs:197-199`).

### 4.2 Is `bitblast_miter` relevant?

Yes — it is the *pattern* the ledger's certified entries were built on, and the
template P3.5 wants extended. `crates/axeyum-solver/src/bitblast_miter.rs` (932 L
per `docs/plan/references/axeyum-current-state.md:24`) is described as an
"**exhaustive** DRAT-checked miter" (`docs/plan/references/proof-and-lean.md:14`).
It is why `BitBlast` reads certified (`docs/plan/track-3-proof-lean/P3.0-trust-ledger.md:23`,
task T3.0.4: "Mark which reductions are already certified (bit-blast via the
miter)"). T3.5.5 wants the same pattern for FP; T3.3.1/T3.3.4 want it converted
into per-lowered-operator Alethe steps.

**But it is not relevant to a prover.** The miter certifies a *reduction between
two circuits* by exhaustive equivalence checking. A prover produces goals, not
circuits, and has no second circuit to be equivalent to. The miter is a
decision-procedure asset.

---

## 5. THE KEY QUESTION — reusability

Reconstruction turns a *certificate* into a proof term. A prover builds proof
terms from *tactics and goals*. The gap is what follows.

### 5.1 What IS reusable — the kernel (genuinely strong)

`crates/axeyum-lean-kernel` (15 516 L) is a real, nanoda-derived kernel with a
complete locally-nameless term API. This is not ad-hoc:

- **Constructors** (`lib.rs:812-858`): `bvar`, `fvar`, `sort`, `const_`, `app`,
  `lam`, `pi`, `let_`, `lit` — all `ExprId`-returning, interned, `Copy`.
- **de Bruijn machinery** (`lib.rs:928-1249`): `instantiate`, `abstract_fvars`,
  `close_scoped_fvars`, `lift_loose_bvars`, plus cached `num_loose_bvars` /
  `has_fvars` metadata (`expr.rs:68-76`) to short-circuit traversal.
- **Universe levels** (`lib.rs:424-751`): `level_succ`/`max`/`imax`/`param`,
  `simplify`, `substitute_level`, `level_leq`, `level_is_equiv`.
- **Type checker** (`tc.rs`, 1 356 L) with `LocalContext` (`tc.rs:234`):
  `fresh_fvar` (`tc.rs:262`), an `infer_cache`, a `def_eq_cache`, `let_values`,
  `scoped_fvars`.
- **Inductives** (`inductive.rs`, 1 081 L): recursor generation, positivity.
- **Preludes** (`prelude.rs` 1 085, `int_prelude.rs` 839, `arith_prelude.rs` 675,
  `string_prelude.rs` 496).

`mk_app`/`mk_lambda` in the requested sense **exist** — as `Kernel::app` and
`Kernel::lam`. A prover would build on exactly these. This layer is theory-neutral
and does not know reconstruction exists.

### 5.2 What is NOT reusable — there is no proof-construction layer

**There is no metavariable. There is no goal. There is no obligation with holes.**
This is not a judgment call; it is a grep result over the whole kernel:

```
grep -rniE 'mvar|metavar|\bgoal\b|sorry|obligation|\bhole\b' crates/axeyum-lean-kernel/src/
  → lean_pp.rs, prelude.rs   (only)
```

And every hit is a false positive:

- `prelude.rs:6` — prose: "a Lean term whose type is the goal proposition".
- `lean_pp.rs:133-150` — `goal` as a **`ExprId` function parameter name**:
  `pub fn render_lean_module(&self, theorem_name: &str, goal: ExprId, proof: ExprId)`.
  A finished proposition to print, not an open obligation.
- `lean_pp.rs:140` — prose: "exactly the obligation the in-tree `Kernel`
  discharged" (past tense — already discharged).

`ExprNode` (`expr.rs:80-98`) has nine variants — `BVar`, `FVar`, `Sort`, `Const`,
`App`, `Lam`, `Pi`, `Let`, `Lit`. **There is no `MVar` variant.** A prover needs
one (or an equivalent assignment table); adding it touches every traversal in
`tc.rs`, `inductive.rs`, and `lean_pp.rs`, because every function currently
assumes terms are metavariable-free.

The two near-misses are worth naming precisely, because both look relevant and
neither is:

1. **`apply_func_with_hole`** (`reconstruct.rs:599-613`) — the word "hole" appears,
   but the body is:

   ```rust
   let mut e = self.kernel.const_(f_name, vec![]);
   for (j, &a) in args.iter().enumerate() {
       let arg = if j == hole { hole_expr } else { a };
       e = self.kernel.app(e, arg);
   }
   ```

   `hole` is a `usize` **index** and `hole_expr` is already-built. It is
   positional substitution for "the per-argument congruence motive's right-hand
   application" (`:598`). Nothing is ever left unknown.

2. **`LocalContext`** (`tc.rs:234`) — a *type-checker* binder stack: push on
   opening a binder, pop on closing (`tc.rs:230-233`), LIFO. It answers "what is
   the type of this fvar while I check under this binder", not "what must the user
   still prove". No decl carries an unproven goal.

Likewise `ReconstructCtx::fresh_local_fvar` (`reconstruct.rs:7921-7930`) mints ids
only "for transient `Exists.elim` binders", noting reconstruction "otherwise builds
closed terms" — the operative admission. Reconstruction is *closed-term
construction*: it always knows the whole answer before it starts building, because
the certificate told it.

### 5.3 The `mk_*` helpers are ad-hoc and private

`ReconstructCtx` has `mk_eq` (`:615`), `mk_eq_refl` (`:623`), `mk_eq_bool` (`:571`),
`mk_not` (`:4720`), `mk_or` (`:7984`), `mk_and` (`:10116`), `mk_iff` (`:10123`),
`mk_exists` (`:7647`), `mk_eq_rec_transport` (`:710`), `mk_exists_elim_false`
(`:7668`), `mk_iff_refl` (`:11670`).

Three observations. They are **private** (`fn`, not `pub fn`) — no external
consumer can reach them. They are **scattered** across an 18 531-line file at
lines 571…11670, accreted where each reconstructor needed them, not organized as
a library. And they are **thin** — `mk_eq` is four `kernel.app` calls hardcoded to
`self.alpha`, the single EUF carrier sort (`:396`), which a prover with real
polymorphism could not use as-is.

There is **no lemma-instantiation API**. Reconstructors reach for prelude constants
by name (`self.prelude.eq`, `self.prelude.eq_refl`) and hand-apply arguments. No
unifier, no implicit-argument elaboration, no instance resolution. `func_const`
(`:448`) takes an explicit `arity` because nothing infers it.

### 5.4 Verdict

| Prover component | Status |
|---|---|
| Term representation, interning, de Bruijn | **Reusable as-is** (`lib.rs:812-1249`) |
| Type checker / def-eq | **Reusable as-is** (`tc.rs`) |
| Inductives + recursors | **Reusable as-is** (`inductive.rs`) |
| Preludes / lemma corpus | **Reusable**, needs growth |
| Lean export | **Reusable** (`lean_pp.rs`), with the §6 caveat |
| `mk_*` term helpers | **Rewrite** — private, scattered, `alpha`-monomorphic |
| Metavariables | **Greenfield** — no `ExprNode::MVar`; every traversal assumes none |
| Goals / obligations | **Greenfield** — nothing exists |
| Tactic engine, unifier, elaborator | **Greenfield** |
| Fragment dispatch (`scan_proof_fragment`) | **Not reusable** — inverted control flow |

The last row is the deepest point. `scan_proof_fragment` (`:1839`) *recognizes* a
known shape and *replays* a known recipe. A prover *searches* an unknown space and
*discovers* a recipe. Reconstruction's control flow runs backward from the answer;
a prover's runs forward from the question. That is not an extension — it is the
opposite direction, and no amount of refactoring the 40-variant catalog produces
it.

---

## 6. `lean_pp.rs` — what it emits and how faithful

`render_lean_module(theorem_name, goal, proof)` (`lean_pp.rs:150`) emits a
self-contained Lean 4 module: every reachable declaration in dependency order via
`reachable_decl_order(&[goal, proof])` (`:284`), then
`theorem <name> : <goal> := <proof>`, then `#print axioms <name>` (`:353`).
Variants exist for compact/shared rendering (`:166`, `:195`, `:210`) with a
`compact_share_plan` (`:325`).

Fidelity, from its own doc (`:135-146`):

> The module opens with `prelude` (no `import Init`), so the re-declared logical
> constants (`True`/`False`/`And`/`Eq`/…) do not clash with Lean's core: it is
> checked against *axeyum's own* declarations, exactly the obligation the in-tree
> `Kernel` discharged. **Inductives, their constructors, and their generated
> recursors are emitted as `axiom`s carrying the kernel's stored types** (so Lean
> re-checks the proof term against those signatures)…

That emphasis is the honest limit, and it directly qualifies the
`PARITY-STATUS-AND-PATH.md:57-60` claim. Lean is **not** re-deriving the recursors
from an `inductive` command — it is being *handed* them as axioms and asked to
re-check the proof term against those signatures. `lean_pp.rs:125-128` concedes the
gap in a rendered comment:

```rust
"-- `{}` is regenerated by Lean's `inductive` command (export slice TODO)"
```

So `#print axioms` reporting "clean" means *no `sorryAx`* — not *no axioms*. The
recursors are axioms by construction. The claim at `PARITY-STATUS-AND-PATH.md:60`
("`#print axioms` clean, no…") is true in the `sorryAx` sense the test asserts
(`crates/axeyum-property/tests/property.rs:89`), and should not be read as
"axiom-free through Lean's own inductive kernel". Positivity is checked by
axeyum's `inductive.rs`, not re-checked by Lean.

### 6.1 CI validation — the emitted Lean is **not** checked by real Lean in CI

This is the finding that most qualifies §2's numbers.

`tests/lean_crosscheck.rs:1-12` states the intent plainly:

> These tests feed that module to a real `lean` binary: an external, Lean-grade
> kernel must accept it… The `lean` binary is **optional: each test skips**
> (prints a note, passes) when it is absent.

Four test files gate on `AXEYUM_LEAN_BIN`: `lean_crosscheck.rs`,
`diophantine_lean_reconstruct.rs`, `regex_emptiness_lean_reconstruct.rs`,
`int_inequality_lean_reconstruct.rs`. Each resolves the binary or skips
(`lean_crosscheck.rs:32-40`; e.g. `regex_emptiness_lean_reconstruct.rs:118`:
`eprintln!("[skip] regex-emptiness: lean binary not found; …")`).

Verified 2026-07-15:

```
$ grep -rn 'lean\|elan\|AXEYUM_LEAN_BIN' .github/    → no matches
$ ls .github/workflows/                              → ci.yml  docs-ci.yml
$ which lean elan                                    → NO LEAN BINARY INSTALLED LOCALLY
```

Neither CI workflow installs `elan` or a Lean toolchain, and no `lean` is on this
machine's PATH. **Every real-Lean cross-check therefore skips-and-passes in CI and
locally.** The "real-Lean-validated" claim at `PARITY-STATUS-AND-PATH.md:57-60`
rests on a run someone did by hand at some point, not on a standing gate — and a
skip is indistinguishable from a pass in the output.

Only the **in-tree** kernel check runs by default. That check is real and load-
bearing (`prove_unsat_to_lean_module` fails unless the term checks to `False`),
so the proofs are not unvalidated — but their validation is by axeyum's kernel
alone, which is the thing the cross-check was meant to corroborate
independently. Installing `elan` in `ci.yml` would close this; it is cheap and
should precede any new claim of Lean parity.

---

## What of this is reusable for a prover, and what is not

**Reusable — and genuinely valuable.** `axeyum-lean-kernel` (15 516 L) is the real
asset, and it is more than a prover track would otherwise get for free: a
locally-nameless term IR with interning and cached loose-bvar/fvar metadata
(`expr.rs:68-98`), the full constructor set including `app`/`lam`/`pi`/`let_`
(`lib.rs:812-858`), `instantiate`/`abstract_fvars`/`close_scoped_fvars`
(`lib.rs:928-1249`), a universe-level algebra with `level_leq` and simplification
(`lib.rs:424-751`), a caching type checker with a binder-stack `LocalContext`
(`tc.rs:234`), inductive/recursor generation (`inductive.rs`), four preludes, and
a Lean exporter (`lean_pp.rs`). Critically, this crate is **theory-neutral and
reconstruction-unaware** — it has no dependency on certificates, fragments, or
solver output. A prover can sit on it directly, today, without disentangling it
from anything. That is a large head start on the hardest-to-get-right layer, and
it is already exercised by ~5 000 lines of kernel tests.

**Not reusable — and this is the larger half.** Everything *above* the kernel is
shaped by having the answer in advance. Reconstruction is closed-term construction:
`fresh_local_fvar` (`reconstruct.rs:7921-7930`) admits reconstruction "otherwise
builds closed terms", and that single line explains the architecture. Because the
certificate dictates the proof, nothing ever needs to represent *not yet knowing*
— and so nothing does. There is no `ExprNode::MVar` (`expr.rs:80-98`), no goal
type, no obligation, no assignment table, no unifier, no elaborator, no tactic
state. The apparent counterexamples dissolve on inspection: `apply_func_with_hole`
(`:599`) takes a `usize` index and an already-built expression; `LocalContext`
(`tc.rs:234`) is a typing binder stack; `goal` in `lean_pp.rs:150` is a parameter
name for a finished proposition. The `mk_*` helpers exist but are private,
scattered from `:571` to `:11670`, and monomorphic in `self.alpha` — a prover
would rewrite them rather than lift them.

**The structural point.** `scan_proof_fragment` (`reconstruct.rs:1839`) matches a
formula against 40 shapes (`:1347`+) — including instance-specific ones like
`TwoByteMemcpy`, `BinarySearch16`, `FifoBc04` (`:1409-1428`) — and dispatches to a
bespoke recipe. That control flow runs *backward from the answer*. A prover runs
*forward from the question*. The 18 531 lines of `reconstruct.rs` are not a
proof-construction library with a certificate front-end bolted on; they are 40
certificate-replay recipes that happen to call kernel constructors. None of that
dispatch layer survives contact with a prover.

**Therefore: a prover is greenfield above the kernel, not an extension of
reconstruction.** The honest framing is that axeyum has built the *checker* half
of a proof assistant and none of the *elaborator* half. The correct reading of the
reconstruction stack is as **evidence the kernel is adequate** — 85 QF_ABV Lean
unsats (`DOMINANCE.md:39`) prove the kernel accepts nontrivial machine-generated
terms at scale, which de-risks the kernel as a prover foundation. That is real and
worth something. But it is evidence *about* the kernel, not machinery *for* a
prover.

Two caveats to carry into any prover plan. First, the trust ledger has **6 open
holes of 14** (`trust.rs:283-300`), two at pedantic 3 (`IntBlast`, `XorGaussian` —
"unsound with no recovery", `:197-199`); these bound what a reconstruction-fed
proof means today, though a prover that builds terms from tactics would bypass the
reduction ledger entirely rather than inherit it. Second, and more sharply: the
real-`lean` cross-check **does not run in CI** (§6.1 — no `elan` in `.github/`,
every gated test skips-and-passes). Before the prover track leans on "Lean parity"
as an established baseline, that gate should actually exist. Coverage is also
thinnest exactly where a prover would be aimed: QF_NIA 13% (2/15), QF_NRA 14%
(2/14), QF_S 29% (8/28) Lean unsat.
