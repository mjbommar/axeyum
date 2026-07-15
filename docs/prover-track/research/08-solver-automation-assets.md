# Solver Automation Assets — What a Prover Layer Inherits

> Bottom-up audit of the existing solver stack, asking one question throughout:
> **if we build a prover on `axeyum-lean-kernel`, what automation comes free?**
>
> Every claim below carries a `file:line`. Status date: 2026-07-15.
> Headline: the automation is real and strong; the **IR mismatch (§6) is the
> single biggest technical risk** and is currently un-addressed in either
> direction that a prover needs.

---

## 1. Decision procedures — what `check_auto` dispatch covers

`check_auto` ([`crates/axeyum-solver/src/auto.rs:435`](../../../crates/axeyum-solver/src/auto.rs)) is
the trusted entry point; `check_auto_explained` (`auto.rs:748`) adds a route
explanation. Specialized deciders sit beside it rather than inside it:

| Decider | Location |
| --- | --- |
| `decide_int_square_constraint` | `crates/axeyum-solver/src/nia_square.rs:322` |
| `decide_real_poly_constraint` | `crates/axeyum-solver/src/nra_real_root.rs:336` |
| `decide_forall_exists_by_witness` | `crates/axeyum-solver/src/quant_exists_witness.rs:99` |
| `decide_word_only_script` | `crates/axeyum-solver/src/smtlib.rs:699` |

### Measured per-fragment reality

From [`bench-results/SCOREBOARD.md`](../../../bench-results/SCOREBOARD.md)
(auto-generated; regenerate with `scripts/gen-scoreboard.py`). **35 division
baselines, 24 logic fragments, 992 files, 753 decided, DISAGREE = 0 across all
baselines** over 680 oracle-compared instances. Zero wrong verdicts is the
load-bearing claim and it holds.

The honest table — **including the weak rows**:

| Logic | Division | Files | Decided | Decide% | PAR-2 (s) | Line |
| --- | --- | --- | --- | --- | --- | --- |
| **LIA** | `lia-cvc5-regress-clean-quantified` | 12 | 0 | **0%** | **30.000** | `SCOREBOARD.md:29` |
| **UF** | `uf-cvc5-regress-clean-quantified` | 5 | 0 | **0%** | 0.000 | `SCOREBOARD.md:61` |
| QF_SLIA | `qf-slia-cvc5-regress-clean` | 50 | 18 | 36% | 3.650 | `SCOREBOARD.md:50` |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded` | 82 | 44 | 54% | 4.845 | `SCOREBOARD.md:52` |
| QF_UF | `…-bounded-uninterp-sorts` | 82 | 44 | 54% | 4.845 | `SCOREBOARD.md:53` |
| QF_S | `qf-s-cvc5-regress-clean` | 134 | 87 | 65% | 1.323 | `SCOREBOARD.md:48` |
| QF_UF | `…-overbound-uninterp-sorts` | 6 | 4 | 67% | 7.489 | `SCOREBOARD.md:51` |
| QF_SEQ | `qf-seq-cvc5-regress-clean` | 33 | 26 | 79% | 3.752 | `SCOREBOARD.md:49` |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 11 | 9 | 82% | 3.637 | `SCOREBOARD.md:42` |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 38 | 32 | 84% | 3.169 | `SCOREBOARD.md:47` |
| QF_NIA | `qf-nia-cvc5-regress-clean` | 39 | 33 | 85% | 2.730 | `SCOREBOARD.md:45` |
| QF_BVFP | `qf-bvfp-bitwuzla-regress-clean` | 8 | 7 | 88% | 0.005 | `SCOREBOARD.md:37` |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 11 | 10 | 91% | 1.819 | `SCOREBOARD.md:41` |
| QF_NRA | `qf-nra-synthetic-graduated` | 33 | 30 | 91% | 5.455 | `SCOREBOARD.md:46` |
| BV | `bv-cvc5-regress-clean-quantified` | 54 | 54 | 100% | 0.033 | `SCOREBOARD.md:28` |
| QF_AX / QF_DT / QF_FP / QF_UFBV / QF_UFLIA / QF_UFFF / QF_NIA(synth) | various | — | — | 100% | ≤6.772 | `SCOREBOARD.md:35–60` |

**Read this carefully for prover purposes.** The 100% rows are *finite-domain or
bounded* fragments — BV (including quantified BV: 54/54, `SCOREBOARD.md:28`),
arrays, datatypes, FP, and UF **over bounded/finite carrier sorts**. The 0% rows
are exactly the fragments a prover lives in: **quantified LIA over the infinite
integers (0/12, PAR-2 30.0 = every instance times out, `SCOREBOARD.md:29`) and
quantified UF over uninterpreted infinite carriers (0/5, `SCOREBOARD.md:61`)**.

Note the QF_UF rows are qualified `-bounded` / `-overbound-uninterp-sorts`
(`SCOREBOARD.md:51–53`) — the 54–67% decide rate is achieved *by bounding the
carrier*, i.e. by finitizing. `Sort::Uninterpreted` documents this directly:
"concrete models use deterministic finite class tokens for replay"
([`crates/axeyum-ir/src/sort.rs:140`](../../../crates/axeyum-ir/src/sort.rs)).

> **Honest summary:** axeyum decides finite/bounded domains superbly and infinite
> quantified domains not at all. A prover's goals (`∀ n : ℕ, …`) are the 0% column.
> The strength is a *complement* to an ITP, not a substitute for its tactics.

---

## 2. Unbounded / inductive machinery

Files: `pdr.rs`, `pdr_lia.rs`, `pdr_lra.rs`, `imc.rs`, `imc_lia.rs`,
`imc_lra.rs`, `horn.rs`, plus `bmc.rs` (BMC + k-induction).

### Inputs / outputs

Everything is keyed on the **`TransitionSystem` trait**
([`crates/axeyum-solver/src/bmc.rs:47`](../../../crates/axeyum-solver/src/bmc.rs)):

- `state_vars(&self, arena, step) -> Vec<SymbolId>` (`bmc.rs:57`) — "one symbol
  per state component… arity/sorts must not vary with `step`" (`bmc.rs:51–52`).
- `init(&self, arena, s0) -> TermId` (`bmc.rs:64`).
- `trans(&self, arena, pre, post) -> TermId` (`bmc.rs:71`).
- `bad(&self, arena, s) -> TermId`.

Outputs: `PdrOutcome::Safe { invariant }` / `Reachable` / `Unknown`
(`pdr.rs:29–35`). `Reachable` is itself gated — "confirmed only by
`bounded_model_check` returning a replay-checked `BmcOutcome::Reachable` trace"
(`pdr.rs:32–35`).

`horn.rs` generalizes to **CHC**, the format Z3's Spacer consumes
(`crates/axeyum-solver/src/horn.rs:1–6`). Crucially it adds **no new IR**: "a
predicate `P` is a `FuncId` declared with result `Sort::Bool`… a predicate
application `P(args)` is an `Op::Apply` term" (`horn.rs:8–14`). A `HornClause` is
`body ∧ constraint ⇒ head`, head `None` = query `false` (`horn.rs:15–20`). It is
*verify-guarded* and reduces to the PDR/IMC engines (`horn.rs:3–6`).

### The `verify_invariant` trusted gate

Six copies, one per engine: `pdr.rs:835`, `pdr_lia.rs:814`, `pdr_lra.rs:791`,
`imc.rs:437`, `imc_lia.rs:548`, `imc_lra.rs:530`.

This is the **architectural pattern most worth stealing for a prover.** The
IC3/PDR search is *entirely untrusted* — "its frames, proof obligations, cube
extraction, and generalization are all best-effort: a bug in any of them can only
ever cause an over-eager `PdrOutcome::Unknown`, never a wrong `Safe`"
(`pdr.rs:13–17`). The guarantee rests on one gate (`pdr.rs:835–876`) that
re-checks three classical conditions, each **independently decided by
`check_auto`**:

1. Initiation — `init(s) ∧ ¬Inv(s)` unsat (`pdr.rs:850`).
2. Consecution — `Inv(s) ∧ trans(s,s') ∧ ¬Inv(s')` unsat (`pdr.rs:859–866`).
3. Safety — `Inv(s) ∧ bad(s)` unsat (`pdr.rs:870–875`).

Any non-`Unsat` ⇒ decline to `Unknown` (`is_unsat`, `pdr.rs:883–895`, where both
`Ok(_)` and `Err(SolverError::Unsupported(_))` map to `false` — a conservative
decline). `prime_invariant` (`pdr.rs:899+`) does the `s[i] ↦ sp[i]` substitution.

This is *exactly* the untrusted-search / trusted-kernel-check shape a tactic
needs: search however you like, then hand a candidate to a small checker.

### Impedance mismatch — precise

**These engines are married to transition systems, and the marriage is
structural, not cosmetic.**

- The trait signature is *inherently stateful*: `state_vars(step)`, `init`,
  `trans(pre, post)`, `bad` (`bmc.rs:57–72`). A prover goal `∀ n, P n → P (n+1)`
  has no `init`, no `bad`, and no `s`/`s'` variable duplication. You would have
  to *invent* a transition system whose reachability encodes the induction —
  possible for the narrow shape "loop invariant", vacuous for the general case.
- The invariant `Inv` is "a conjunction of cube-clauses over the unprimed state
  vars" (`pdr.rs:896–898`) — a **quantifier-free propositional-over-theory-atoms
  formula**. Lean's induction hypotheses are arbitrary CIC props with binders.
  There is no cube representation of `∀ xs, Sorted xs → …`.
- Generalization is over a *finite vector of state symbols*. CIC induction is
  over an inductive **type's constructors**, with recursors and motives
  (`crates/axeyum-lean-kernel/src/inductive.rs`) — a different induction
  principle entirely. PDR does not know what a constructor is.
- The reachability framing fixes the *shape* of the theorem (safety of a
  transition relation). Nothing in `pdr.rs`/`imc.rs` is parameterized over "what
  is being inducted on".

**Verdict:** the *pattern* (untrusted search + one trusted re-check gate)
transfers cleanly and should be the prover's architecture. The *engines* do not
transfer — they are reachability solvers for `TransitionSystem`, and a prover's
induction automation over CIC inductive types would be a **new build**, not a
port. CHC (`horn.rs`) is the closest bridge (arbitrary predicates, not a single
state predicate), and is the only one worth prototyping against; but it still
requires the goal to be expressible as Horn clauses over `Sort::Bool` uninterpreted
functions in the **SMT IR** — which brings us to §6.

---

## 3. The e-graph — reusable as `simp`?

[`crates/axeyum-egraph/src/lib.rs:1`](../../../crates/axeyum-egraph/src/lib.rs):
"Incremental congruence-closure e-graph (Track 1, P1.4 — keystone)… the shared
**equality bus** for the reasoning stack".

### Used for what now

Only one consumer: `axeyum-solver`, and it is **optional**
(`crates/axeyum-solver/Cargo.toml:18`, feature-gated at `:43`). Intended
consumers per the header (`lib.rs:4–8`): "EUF, lazy arrays, datatypes, arithmetic
equality propagation, and all quantifier work".

Delivered (`lib.rs:10–16`): hash-consed e-node creation + union-find `find` and
the deferred-merge congruence cascade (T1.4.1/T1.4.2); a **Nieuwenhuis–Oliveras
proof forest with `explain`-to-LCA** (T1.4.3); backtrackable `push`/`pop`
(T1.4.4); an independent `check_congruence` re-validator (T1.4.5); per-class
theory-variable lists (T1.4.6).

### Does it explain itself? Yes.

- `Justification` — "The justification of one edge in the proof forest (T1.4.3)"
  (`lib.rs:116–124`): either an asserted equality (with the SAT literal that
  asserted it) or a congruence (premises recovered from argument explanations).
- `ProofStep` (`lib.rs:127–147`) — a **structured** explanation: "Unlike the flat
  reason set from `EGraph::explain`, the structured form exposes *how* — direct
  vs congruence — so a proof emitter (e.g. Alethe `eq_transitive`/`eq_congruent`)
  or an interpolator can consume it" (`lib.rs:128–133`).
- Proof-forest parent is maintained "independent of the union-find"
  (`lib.rs:158–173`).

**This is genuinely `simp`-shaped and genuinely proof-producing.** `ematch`
exists too — `Pattern` over pattern variables and function symbols (`lib.rs:59–71`),
`EGraph::ematch` "modulo congruence (P2.6)" (`lib.rs:392`), `Subst` (`lib.rs:81`),
and an indexed multi-pattern form `ematch_many_indexed` (`lib.rs:88`). A rewriter
driven by e-matching + `explain_steps` → Lean `Eq` terms is a *credible* `simp`
core. Caveat: e-nodes are `decl: u32` applied to e-nodes — untyped, first-order,
no binders (`lib.rs:19–27`). It closes congruence, not β/η.

### Is `axeyum-rewrite`'s canonicalizer close? **And does it produce proofs? — NO.**

This is a sharp finding. `crates/axeyum-rewrite/src/canonical.rs:1–5`:

> "Denotation-preserving canonicalization. The first canonicalizer is
> deliberately small and exact: **every enabled rule preserves term denotation
> under every assignment, so no model projection is needed.**"

The rules are named string constants — `bool.const_fold.v1`, `bool.double_not.v1`,
`array.select_store_same.v1`, `bv.eq_add_constant_cancel.v1`, … (`canonical.rs:18–36`).
A grep for `proof|justif|certificat` across `canonical.rs` + `lib.rs` returns
**only two hits, both aspirational**:

- `crates/axeyum-rewrite/src/lib.rs:49` — "Stable rewrite rule identifier used in
  logs and **future** certificates."
- `crates/axeyum-rewrite/src/lib.rs:118–119` — `Preservation::ProofObligation`:
  "**Future** proof obligation checked outside the rewriter."

(The only other hit, `canonical.rs:2697`, is the English word "justifies" in a
comment about `bvxnor` associativity.)

> **The canonicalizer's soundness argument is "every rule is denotation-preserving
> by construction," enforced by testing (`RewriteTestRoute`), not by emitting a
> checkable object.** For a solver that is defensible. **For a prover it is
> disqualifying**: a `simp` must justify itself to the kernel. The canonicalizer
> would need a proof-emitting rewrite of its rule application engine — the rule
> *ids* are already stable (`lib.rs:49`), which is the hook, but every one of the
> ~dozens of `*.v1` rules would need a corresponding Lean lemma and a term builder.
> The e-graph's `ProofStep` (`egraph/lib.rs:127`) is the better foundation: it
> already emits structure.

---

## 4. Quantifier machinery — what's real, what's measured

The surface area is large. 38 files in `crates/axeyum-solver/src/` match
`quant|mbp|mbqi|ematch|skolem`:

- **MBP**: `mbp.rs`. **MBQI**: `mbqi_model_finder.rs`. **E-matching instantiation**:
  `qinst_egraph.rs` (over the e-graph's `ematch`, `egraph/lib.rs:392`).
- **Skolemization certificates**: `skolem_alethe.rs`; quantifier Alethe glue in
  `quant_alethe.rs`.
- **Elimination**: `quant_fourier_motzkin.rs`, `quant_guarded_int.rs`,
  `quant_exists_witness.rs` (`decide_forall_exists_by_witness`, `:99`).
- **A large family of cert/search pairs** — the dominant design idiom. Each
  narrow shape gets a *search* (untrusted) and a *cert* (checkable):
  `quant_bv_alternation_{search,cert}.rs`, `quant_bv_conjunctive_{search,cert}.rs`,
  `quant_bv_paired_exists_{search,cert}.rs`, `quant_bv_model_sat_{search,cert}.rs`,
  `quant_closed_counterexample_{search,cert}.rs`, `quant_eq_partition_{search,cert}.rs`,
  `quant_guard_vacuity_{search,cert}.rs`, `quant_negated_exists_{search,cert}.rs`,
  `quant_vacuous_exists_counterexample_{search,cert}.rs`, plus
  `quant_bv_instance_set_cert.rs`, `quant_finite_cert.rs`, `quant_sat_cert.rs`,
  `quant_residue_cert.rs`, `quant_nested_xor_cert.rs`,
  `quant_affine_growth_cert.rs`, `quant_counterexample_cover.rs`,
  `quant_unsat_universal.rs`, `quant_vacuous_universal.rs`,
  `quant_valid_universal.rs`.

### What's *measured* — the honest read

Cross-referencing §1: the quantified rows that work are **BV**
(`bv-cvc5-regress-clean-quantified` 54/54 = 100%, PAR-2 0.033, `SCOREBOARD.md:28`;
`bv-bitwuzla-regress-clean-quantified` 5/5, `SCOREBOARD.md:27`). The quantified
rows that don't are **LIA** (0/12, `SCOREBOARD.md:29`) and **UF** (0/5,
`SCOREBOARD.md:61`).

That pattern is not an accident and it is the key insight of this section: **the
quantifier machinery that is measured-good is the machinery that can finitize.**
Quantified BV works because `∀ x : BitVec 32` has 2^32 instances and the BV
fragment bit-blasts; the cert families above are overwhelmingly `quant_bv_*`.
Quantified LIA/UF over infinite domains is where MBQI/MBP/CEGQI would have to
carry the weight, and the measured decide rate there is **zero**.

**How much transfers to a prover?** A prover handles binders constantly, and:

- The **cert/search split idiom transfers as an architecture** — it is the same
  untrusted-search/trusted-check shape as `verify_invariant` (§2), and it is the
  right one.
- The **BV-specialized certs do not transfer** — a prover's binders range over
  `ℕ`, `ℤ`, `List α`, arbitrary types, not `BitVec 32`.
- **Skolem certificates** (`skolem_alethe.rs`) are conceptually the most
  transferable — Skolemization is a real prover need — but note CIC Skolemization
  needs choice/`Classical.choice`, which is a kernel-axiom question, not a
  translation question.
- **E-matching** (`qinst_egraph.rs` + `egraph/lib.rs:392`) transfers *if and only
  if* §6 is solved, since patterns are over IR `Op`/`decl`, not CIC `Expr`.

---

## 5. Models / counterexamples — the differentiator

`Model` lives at [`crates/axeyum-solver/src/model.rs:30`](../../../crates/axeyum-solver/src/model.rs).
The project Hard Rule is unambiguous (`CLAUDE.md`): "Every `sat` result must be
checkable by evaluating the original term against the lifted model; never drop
lowering/lift maps after solving."

Sorts a model can range over ([`crates/axeyum-ir/src/sort.rs:121–149`](../../../crates/axeyum-ir/src/sort.rs)):
`Bool` (`:123`), `BitVec(u32)` (`:125`), `Array{index, element}` (`:127`, ADR-0010),
`Int` (`:134`, ADR-0014), `Real` (`:136`, ADR-0015, exact rationals via
`Rational`, `term.rs:360`), `Datatype(DatatypeId)` (`:139`, ADR-0022, recursive),
`Uninterpreted(SortId)` (`:143` — "pure equality/congruence; concrete models use
deterministic finite class tokens for replay"), and IEEE-754 `Float` (`:144`,
ADR-0026, lowering structurally to `BitVec(exp+sig)`).

Validation is by **replay**, and it's real: the scoreboard's DISAGREE = 0 across
680 oracle-compared instances (`SCOREBOARD.md`, Headline) is backed by model
replay in `axeyum-bench` ("backend selection, PAR-2 scoring, **model replay**, and
JSON artifacts", `CLAUDE.md` layout section). `BmcOutcome::Reachable` traces are
"replay-checked" before PDR will report `Reachable` (`pdr.rs:32–35`).

**How good really?** This is the strongest prover-facing asset after the
finite-domain deciders, and the framing is right — ITPs are notoriously bad at
counterexamples (Lean has `#eval`/`decide` and `slim_check`-style testing;
neither is a model-finder). A `axeyum_find_counterexample` tactic that says
"your lemma is false, here is `n = 7, xs = [3,1]`" would be a genuine
differentiator. **But** the honest caveats:

1. Counterexamples come from **`sat`**, and `sat` on quantified infinite-domain
   goals is the 0% column (`SCOREBOARD.md:29,61`). The differentiator lands for
   goals that finitize — concrete `BitVec`, bounded `Int`, finite datatypes,
   bounded carriers.
2. `Uninterpreted` models are *finite class tokens* (`sort.rs:140–143`) — for a
   prover, mapping a class token back to an inhabitant of a Lean type is
   §6's problem again.
3. A counterexample is only *useful* to a prover if it can be **exhibited in
   CIC** — i.e. lifted back to Lean values. That direction does not exist today.

---

## 6. THE IR MISMATCH — the critical risk

> **Bottom line up front:** `axeyum-ir` and `axeyum-lean-kernel` are two
> unrelated term languages that share nothing but a design idiom. Translation
> exists in **exactly one direction — SMT-IR → Lean — and only for
> reconstructing proof certificates over an axiomatized first-order model that
> the reconstructor invents.** There is **no CIC → SMT-IR path anywhere in the
> tree**, and that is precisely the direction a prover needs. This is the single
> biggest technical risk in the plan and it is not a matter of writing glue.

### 6.1 The two term languages, side by side

| | `axeyum-ir` | `axeyum-lean-kernel` |
| --- | --- | --- |
| Node type | `TermNode` ([`ir/src/term.rs:344`](../../../crates/axeyum-ir/src/term.rs)) | `ExprNode` ([`lean-kernel/src/expr.rs:80`](../../../crates/axeyum-lean-kernel/src/expr.rs)) |
| Variables | `Symbol(SymbolId)` (`term.rs:362`) — free, named, sorted | `BVar(u32)` de Bruijn (`expr.rs:82`) + `FVar(u64)` (`expr.rs:84`) |
| Application | `App { op: Op, args: Box<[TermId]> }` (`term.rs:364–369`) — **fixed operator set, n-ary** | `App(ExprId, ExprId)` (`expr.rs:90`) — **curried, head can be any term** |
| Binders | **none in `TermNode`** | `Lam(NameId, ExprId, ExprId, BinderInfo)` (`expr.rs:92`), `Pi(…)` (`expr.rs:94`), `Let(…)` (`expr.rs:96`) |
| Types | `Sort` enum, 8 closed cases (`sort.rs:121–149`) | `Sort(LevelId)` (`expr.rs:86`) — types are *terms*; universes |
| Constants | `BoolConst`/`BvConst`/`WideBvConst`/`IntConst`/`RealConst` (`term.rs:346–360`) | `Const(NameId, Vec<LevelId>)` (`expr.rs:88`) + `Lit` (`expr.rs:98`) |
| Universes | — | `LevelId`, with `simplify`/`subst`/antisymmetric `leq` (`lean-kernel/src/lib.rs:21–22`) |
| Handles | `Copy` ids, lifetime-free | `Copy` ids, lifetime-free — **deliberately mirrored** |

The mirroring is explicit and intentional: the kernel replaces nanoda's
lifetime-tagged arena "with a `Vec`-backed hash-consing interner returning
lifetime-free `Copy` ids (`NameId`/`LevelId`/`ExprId`), **mirroring `axeyum-ir`**"
([`lean-kernel/src/lib.rs:11–15`](../../../crates/axeyum-lean-kernel/src/lib.rs)).

**This shared idiom is a trap for the reader.** Both crates intern to `Copy` u32-ish
handles; both forbid lifetimes in public APIs; both are deterministic. It *looks*
like they were designed to interoperate. They were not — the idiom is a house
style (a Hard Rule in `CLAUDE.md`), not a bridge. `TermId` and `ExprId` are
indices into unrelated arenas with disjoint node types.

Note the depth of the gap: `axeyum-ir`'s `Op` is a **closed enum** of ~100+
concrete operators (`term.rs:78–340`: `BoolNot`, `BvAdd`, `BvUdiv`, …). Lean's
`ExprNode` has **no operators at all** — `Nat.add` is a `Const` resolved in an
`Environment` (`lean-kernel/src/env.rs:4`: "A Lean kernel checks terms relative to
an *environment*: a set of global declarations"). One language hard-codes its
semantics in a Rust enum; the other defers everything to a mutable global context
of declarations, definitions, and inductives.

### 6.2 What translation exists today — precisely

**Direction: SMT-IR/Alethe → Lean `ExprId`. Purpose: proof reconstruction. That's all.**

The dependency edge is one-way and optional:
`crates/axeyum-solver/Cargo.toml:21` — `axeyum-lean-kernel = { path = "../axeyum-lean-kernel", optional = true }`,
enabled by a feature at `:45`. **`axeyum-lean-kernel/Cargo.toml` has an empty
`[dependencies]` section — the kernel does not know `axeyum-ir` exists.** Nothing
else in the workspace depends on the kernel (`grep axeyum-lean-kernel --include=Cargo.toml`
returns only the workspace member list, the crate itself, and `axeyum-solver`).

The reconstruction modules that import the kernel:

| File | Import site |
| --- | --- |
| `crates/axeyum-solver/src/reconstruct.rs` | `:68` (and `:13608` for `ArithPrelude`) |
| `crates/axeyum-solver/src/int_reconstruct.rs` | `:41` |
| `crates/axeyum-solver/src/word_reconstruct.rs` | `:46` |
| `crates/axeyum-solver/src/regex_reconstruct.rs` | `:66` |
| `crates/axeyum-solver/src/lex_reconstruct.rs` | `:42` |
| `crates/axeyum-solver/src/reconstruct/quant_bv_instance_set_lean.rs` | `:17` |

Also touching the Lean side: `evidence.rs`, `solver.rs`, `capabilities.rs`,
`smtlib.rs`, `interpolant.rs`, `lia_interpolant.rs`, `uflia_interpolant.rs`,
`euf_interpolant.rs`.

`reconstruct.rs:66–73` imports **both** term languages into one module — this is
the *only* place they meet:

```rust
use axeyum_ir::{ConstructorId, DatatypeId, FuncId, Op as IrOp, Rational, Sort as IrSort,
                TermArena, TermId, TermNode as IrTermNode};
use axeyum_lean_kernel::{BinderInfo, DatatypeFamily, DatatypeInductive, Declaration, ExprId,
                         ExprNode, Kernel, LevelId, LocalContext, LocalDecl, LogicPrelude,
                         NameId, RecField, RecursiveDatatypeFamily, ...};
```

Note `Op as IrOp` / `Sort as IrSort` — the aliasing exists because the names
*collide* with the kernel's, which is a small but telling sign of two worlds.

The header states the purpose (`reconstruct.rs:1–8`): "**Alethe → Lean proof
reconstruction over the EUF / equality fragment** (Track 3, phase P3.7 — the first
slice)… an Alethe `eq_reflexive`/`eq_symmetric`/`eq_transitive` step is translated
into a Lean `ExprId` proof term whose type the trusted `Kernel` `infer`s to the
corresponding `Eq` proposition."

Entry points: `prove_unsat_to_lean` (`reconstruct.rs:2162`), `render_ctx_module`
(`:2174`), and ~20 `reconstruct_*_to_lean_module` functions (`:2392`–`:3231`+),
e.g. `reconstruct_finite_domain_pigeonhole_to_lean_module` (`:2392`),
`reconstruct_lra_dpll_to_lean_module` (`:3051`),
`reconstruct_bounded_int_blast_to_lean_module` (`:3162`),
`reconstruct_array_axiom_to_lean_module` (`:3231`), plus the quantified-BV family
re-exported at `reconstruct.rs:54–62`.

**The soundness story is excellent and worth stating** (`reconstruct.rs:29–35`):
"A reconstructed step is accepted **only** when the kernel `infer`s its proof term
and that inferred type is `Kernel::def_eq` to the expected conclusion… The trusted
small checker validates the reconstruction; **this module is untrusted glue**."
The kernel really does check: `assert_infers_false` (`reconstruct/tests.rs:301`),
and `lia_interpolant.rs:384` notes the in-tree `Kernel` (`infer` + `def_eq False`)
"is the REAL gate".

### 6.3 The finding that matters: the reconstructor *invents* its model

This is the crux, and it is easy to miss. The translation is **not** "Lean type
`X` ↔ SMT sort `X`". Read `reconstruct.rs:10–21`:

> "Reconstruction runs in a **fixed first-order model**:
> - a single carrier sort `α : Type` (i.e. `Sort 1`), **declared as an axiom**;
> - each uninterpreted Alethe atom (`a`, `b`, …) is a distinct constant of type
>   `α`, **declared as an axiom of type `α` on first use**;
> - each uninterpreted unary function symbol `f` is a constant of type `α → α`,
>   **declared as an axiom on first use**;
> - an Alethe equality `(= s t)` translates to `Eq.{1} α ⟦s⟧ ⟦t⟧`."

So the flow is: **SMT problem → SMT proof → a freshly-axiomatized Lean context
built to receive that proof.** The Lean side is *generated output*, an
`α : Type` axiom with constants hung off it. It is not connected to any
pre-existing Lean development, any Mathlib type, or any user goal. The `Kernel`
checks the proof against the axioms the reconstructor just wrote down.

**A prover needs the inverse and it is a different problem.** A prover has a
goal that *already exists* in CIC — `∀ (l : List ℕ), l.length = l.reverse.length`
— living in an `Environment` of real declarations (`env.rs:4`), typed by real
inductives (`lean-kernel/src/inductive.rs`), over `Nat`/`List` from a real
prelude (`prelude.rs`, `arith_prelude.rs`, `int_prelude.rs`, `string_prelude.rs`).
It must go **down** to `axeyum_ir::TermNode` to be solved. Nothing does that.

**Grep confirms the absence.** Searching for any function consuming an `ExprId`
and producing a `TermId`:

```
grep -rE "fn [a-z_]+\([^)]*ExprId[^)]*\)[^{]*-> *(Result<)?TermId" --include="*.rs" crates/
→ (no matches)
```

There is no `Expr → Term` function, no CIC-goal ingestion, no reflection
procedure, no `Decidable` instance discharge. The prover's *entire front half* is
missing, and it is the hard half.

### 6.4 Why CIC → SMT-IR is fundamentally hard

Not glue. Each item below is a research-grade obstacle, and each maps to a
concrete absence in `axeyum-ir`.

**(a) Dependent types.** CIC's `Pi(NameId, ExprId, ExprId, BinderInfo)`
(`expr.rs:94`) lets the codomain *mention the bound variable*: `Vec α n → Vec α (n+1)`.
`axeyum_ir::Sort` (`sort.rs:121–149`) is a **closed, non-dependent enum** — a sort
cannot mention a term. There is no `Sort` case that could hold a `TermId`, and
adding one would break `Sort: Copy` and the entire sort-checking discipline. **A
dependent goal has no image in `Sort` at all.** The tractable subset is goals
whose types are non-dependent — real, but it is a *subset*, and determining
membership is itself work.

**(b) Higher-order.** `TermNode::App` carries `op: Op` — a **closed enum variant**
(`term.rs:364–369`). The head of an application is *not a term*; it cannot be a
variable. Lean's `App(ExprId, ExprId)` (`expr.rs:90`) has an arbitrary term head,
and `Lam` (`expr.rs:92`) makes functions first-class values. **`axeyum-ir` cannot
represent `f x` where `f` is bound, nor any λ.** A goal like
`∀ (f : ℕ → ℕ), Monotone f → …` is not expressible. Options — defunctionalize,
λ-lift, or Ackermann-style encode into `Op::Apply`/`FuncId` (the trick `horn.rs:8–14`
uses for predicates) — are all *lossy and partial*, and higher-order unification
is undecidable in general.

**(c) Typeclasses.** Mathlib goals are saturated with instance arguments —
`BinderInfo` (`expr.rs:92,94`) is exactly where `instImplicit` lives. `@HAdd.hAdd ℕ ℕ ℕ inst a b`
must become `Op::IntAdd` (`term.rs`, the `Op` enum) — but only after resolving
that `inst` is *the standard* `Nat` instance and not some exotic one. That is
δ-unfolding + `def_eq` against a whole instance graph (`tc.rs:14–20` has the
machinery: δ-unfolding of `Definition`/`Theorem`, lazy-delta, universe
instantiation) — and getting it *wrong* silently means translating a goal about a
non-standard structure into one about `ℤ`. **This is a soundness surface, not
just an engineering surface** — though note it's a soundness surface for
*claiming to have proved the goal*, which the kernel would catch at proof-check
time. The real cost is unsoundness-of-*claim* → wasted work, plus wrong
counterexamples reported to the user (a `sat` on a mistranslated goal is a
**false counterexample**, and the kernel never sees `sat` results — §5's
differentiator has no kernel backstop).

**(d) `Prop` vs `Bool`.** The deepest structural mismatch. Lean `Sort(LevelId)`
(`expr.rs:86`) makes `Prop = Sort 0` a *universe of types*; a proposition's
inhabitants are proofs. `axeyum_ir::Sort::Bool` (`sort.rs:123`) is a two-element
value sort. `p : Prop` is **not** a Boolean — it needs `Decidable p` to become
one, and `decide`/`Decidable.decide` is itself a typeclass problem (see (c)).
Worse, the kernel implements **proof irrelevance** (`tc.rs:17`: "eta-expansion,
**proof irrelevance**, type inference") — two proofs of the same prop are
definitionally equal, an equivalence with no counterpart in the SMT IR. Going the
other way, the reconstructor sidesteps this entirely by *declaring its own*
`α : Type` (`reconstruct.rs:12`) rather than reflecting a real one.

**(e) Decidability.** `axeyum-ir` operators are **total by construction** —
`bvudiv x 0` = all-ones, per SMT-LIB verbatim (`CLAUDE.md` Hard Rules;
`docs/research/01-foundations/bv-semantics-and-partial-operations.md`). Lean's
`Nat.div` is a *definition* with its own convention, and `x / 0 = 0` in Lean. Any
translation must prove — or assume — that the conventions agree, per operator.
Silent divergence here is exactly the `a946f925` wrong-unsat class the project
already learned about (`CLAUDE.md` Hard Rules), now re-introduced at the
translation boundary where no fuzzer currently looks.

**(f) The environment gap.** Lean terms are meaningless without their
`Environment` (`env.rs:4`). A translator must interpret `Const(NameId, levels)`
(`expr.rs:88`) — resolving `Nat.succ`, `List.length`, `Finset.sum` — into IR ops.
The kernel's own preludes (`prelude.rs`, `arith_prelude.rs`, `int_prelude.rs`,
`string_prelude.rs`, `inductive.rs`) show the scale of what must be recognized,
and those are *toy* preludes relative to Mathlib. Any real prover faces a
**potentially unbounded recognition problem**: an open-ended map from Lean
constant names to IR semantics, where every unrecognized constant is a bailout.
This is `hammer`-style premise selection and it is the known-hard part of every
ITP–ATP bridge (Sledgehammer, CoqHammer, `lean-smt`).

**(g) Literal typing is deferred in the kernel.** `tc.rs:23–24`: "**Deferred to a
later slice** (and erroring cleanly if reached): literal typing/reduction (`Lit` →
`KernelError::UnsupportedLit`), inductive/recursor (ι) reduction, structure
projections, and `Quotient` reduction." So even the *Lean* side is not yet ready
to typecheck the numerals and recursors a translated arithmetic goal would
produce. `ExprNode::Lit` exists (`expr.rs:98`) but the typechecker rejects it.
**ι-reduction being absent means the kernel cannot yet compute with inductive
types — the prover's bread and butter.**

### 6.5 Risk assessment

| | |
| --- | --- |
| **Exists today** | SMT-IR/Alethe → Lean, proof-certificate reconstruction only, into a self-declared axiom context (`reconstruct.rs:1–21`, `:2162`+). Feature-gated (`axeyum-solver/Cargo.toml:21,45`). |
| **Needed for a prover** | CIC `Expr` → `axeyum_ir::TermNode` (goal ingestion), **and** SMT model → CIC (counterexample exhibition). |
| **Built** | Neither. Zero matches for `ExprId → TermId`. |
| **Fundamental blockers** | Dependent types have no `Sort` image (`sort.rs:121` is closed, non-dependent). Higher-order has no `App` image (`term.rs:364`, `op: Op` is a closed enum). `Prop`/proof-irrelevance (`tc.rs:17`) has no IR counterpart. |
| **Unbounded blockers** | Typeclass-instance resolution; the constant-recognition (premise-selection) map. |
| **Kernel-side gaps** | `Lit` typing, ι-reduction, projections, `Quotient` all deferred (`tc.rs:23–27`). |
| **Prior art says** | Every ITP–ATP bridge (Sledgehammer, CoqHammer, `lean-smt`, SMTCoq) spends most of its complexity here, and all of them are *partial and heuristic* by design. |

**The risk is not that translation is impossible — it is that translation is a
partial, heuristic, open-ended component with no crisp exit criterion**, which
sits badly with this project's culture of exact fragments and DISAGREE = 0. The
project's instinct — "conservative slicing + soundness-negative tests" — is the
right medicine, and the mitigation shape is already proven in-tree twice
(`verify_invariant`, `pdr.rs:835`; the cert/search families, §4): **let the
translator be untrusted and make the kernel the gate.** A mistranslated goal that
yields `unsat` produces a proof term the kernel rejects → decline, never a wrong
theorem. That handles the `unsat` side cleanly.

**The `sat` side has no such backstop and this is the sharpest unmitigated
risk in the plan.** A mistranslated goal that yields `sat` produces a
**counterexample that is wrong about the user's actual theorem** — and §5's
differentiator is precisely the `sat` side. There is no kernel check for "this
model refutes this CIC goal," because exhibiting an SMT model as CIC inhabitants
is itself the unbuilt reverse direction. Recommended mitigation: a counterexample
must be **replayed in CIC** (lift the model to Lean terms, `#eval`/`decide` the
instantiated goal to `False`) before it is shown to a user — which means the
model→CIC lifter is not optional polish, it is a soundness requirement for the
one feature that most differentiates the product.

---

## What automation a prover inherits free, what needs building, and the IR-mismatch risk

### Free (real, measured, no new work)

- **Finite/bounded-domain decision power with zero wrong verdicts.** 753/992
  decided, DISAGREE = 0 over 680 oracle-compared instances (`SCOREBOARD.md`).
  100% on quantified BV (54/54, PAR-2 0.033, `SCOREBOARD.md:28`), QF_AX, QF_DT,
  QF_FP, QF_UFBV, QF_UFLIA (`SCOREBOARD.md:35–60`). If a goal finitizes, axeyum
  crushes it.
- **A proof-producing congruence closure.** `axeyum-egraph` with a
  Nieuwenhuis–Oliveras proof forest, `explain`-to-LCA, structured `ProofStep`
  (`egraph/lib.rs:127–147`), `push`/`pop` (T1.4.4), an independent
  `check_congruence` re-validator, and e-matching modulo congruence
  (`egraph/lib.rs:392`). This is the best `simp`-core foundation in the tree.
- **A kernel that actually checks.** `infer` + `def_eq` gate reconstruction
  (`reconstruct.rs:29–35`, `reconstruct/tests.rs:301`, `lia_interpolant.rs:384`).
- **~20 SMT→Lean proof emitters** (`reconstruct.rs:2162`–`3231`+) — reusable the
  moment a goal can be *phrased* in the SMT IR.
- **The architectural pattern, which is the most valuable inheritance of all:**
  untrusted search + one small trusted gate. Proven twice — `verify_invariant`
  (`pdr.rs:835–876`, where search bugs can only cause `Unknown`) and the ~19
  quant `*_search`/`*_cert` pairs (§4). Adopt this wholesale.

### Needs building

- **CIC → SMT-IR goal ingestion. Does not exist. This is the prover's front half.**
- **SMT model → CIC lifting**, without which counterexamples cannot be trusted or
  exhibited (§6.5).
- **A proof-emitting `simp`.** `axeyum-rewrite`'s canonicalizer is
  denotation-preserving *by construction and by testing*, and emits **nothing** —
  its certificate story is two `Future`-tagged doc comments
  (`rewrite/src/lib.rs:49`, `:118–119`). Rebuild on the e-graph's `ProofStep`.
- **Induction over CIC inductive types.** PDR/IMC/CHC are married to
  `TransitionSystem` (`bmc.rs:47–72`): `state_vars`/`init`/`trans`/`bad`, cube
  invariants over a finite symbol vector (`pdr.rs:896–898`). No `init`, no `bad`,
  no cubes, and no constructors in a Lean goal. `horn.rs` is the closest bridge
  (arbitrary predicates as `Bool`-result `FuncId`s, `horn.rs:8–14`) and the only
  one worth prototyping — but it still needs §6 solved first.
- **Infinite-domain quantifier reasoning.** MBQI/MBP/CEGQI files exist
  (`mbp.rs`, `mbqi_model_finder.rs`, `qinst_egraph.rs`) but the measured decide
  rate on quantified LIA is **0/12 with PAR-2 30.0 — every instance times out**
  (`SCOREBOARD.md:29`) and quantified UF is **0/5** (`SCOREBOARD.md:61`). The
  quantifier machinery that works is the machinery that finitizes.
- **Kernel gaps:** `Lit` typing, ι-reduction, projections, `Quotient`
  (`tc.rs:23–27`) — the kernel cannot yet compute with inductives.

### The IR-mismatch risk — treat as the plan's #1

`axeyum-ir` (`TermNode`, `term.rs:344`; closed `Op` enum, `term.rs:78`; closed
non-dependent `Sort`, `sort.rs:121`; no binders) and `axeyum-lean-kernel`
(`ExprNode`, `expr.rs:80`; `Lam`/`Pi`/`Let`; `Sort(LevelId)`; de Bruijn) are
**different term languages that share only a house style** — the mirrored `Copy`-id
interner (`lean-kernel/src/lib.rs:11–15`) makes them *look* interoperable and they
are not. The kernel has an **empty `[dependencies]`**; it has never heard of the IR.

Today's only bridge is **one-way and points away from the prover**: SMT proofs →
Lean, into a first-order model the reconstructor **declares as axioms on the fly**
(`α : Type` + per-atom axioms, `reconstruct.rs:10–21`). It never reads a
pre-existing Lean goal. `grep -rE "fn .*\(.*ExprId.*\).*-> (Result<)?TermId"`
returns **nothing** — the direction a prover needs is unwritten.

The obstacles are structural, not clerical: dependent types have no image in a
`Copy`, term-free `Sort` (`sort.rs:121`); higher-order terms have no image in
`App { op: Op, .. }` where the head is an enum variant (`term.rs:364`); `Prop` +
proof irrelevance (`tc.rs:17`) have no IR counterpart; typeclass resolution and
Mathlib constant-recognition are open-ended heuristic problems that every
comparable bridge (Sledgehammer, CoqHammer, `lean-smt`) solves only partially;
and totality conventions differ per-operator (SMT `bvudiv x 0` = all-ones vs Lean
`x / 0 = 0`) — the same class as the `a946f925` wrong-unsat, re-introduced at a
boundary no fuzzer watches.

**Mitigation, in the project's own idiom:** make the translator untrusted and the
kernel the gate — a mistranslated `unsat` yields a proof term the kernel rejects,
so it declines rather than lies. That covers `unsat`. **It does not cover `sat`,
and `sat` is the differentiator (§5).** A wrong translation that returns `sat`
hands the user a confident, wrong counterexample with nothing checking it. So the
model→CIC lifter is **not polish — it is the soundness gate for the flagship
feature**, and it should be scoped in from day one alongside goal ingestion, with
a `:status`-style oracle-free corpus of CIC goals with known verdicts as the
pre-merge gate.

**Recommended sequencing:** pick a deliberately tiny, non-dependent,
typeclass-free CIC fragment (closed `Nat`/`BitVec` goals, no binders over
functions), build ingestion **and** model-lifting for exactly that, wire both
gates, measure it — then widen one obstacle at a time. Do not let the translator's
coverage grow ahead of its two gates.
