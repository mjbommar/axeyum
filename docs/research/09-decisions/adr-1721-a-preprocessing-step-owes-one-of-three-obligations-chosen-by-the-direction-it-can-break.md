# ADR-1721: A preprocessing step owes ONE of three obligations, chosen by the direction it can break

Status: accepted
Index-summary: What a preprocessing step owes as evidence is decided by what it does to the model set — **replacement** owes a denotation equality, **relaxation** owes nothing in the `unsat` direction, **strengthening** owes a per-constraint discharge — and an obligation is legally discharged by a certificate, by a structural check, or by the route declining to conclude in that direction. Measured correction to the family page: preprocessing is **not** evidence-free. `ArrayElimUnsatCertificate` and `AckermannUnsatCertificate` already discharge the *strengthening* half of the two eager eliminations, and they **re-derive** the replacement half, which `trust.rs:89-95` already names as proving determinism and not faithfulness. So the hole is narrower and sharper than "no evidence": the replacement obligation has no producer anywhere, the crate's one runtime semantic check (the ADR-0408 denotation guard, 4 samples, BV/Bool only) is structurally blind to it, and that check's refusal is swallowed at `auto.rs:1744` as an ordinary decline. First slice: an independent faithfulness witness for read-over-write, copying the `fpa2bv_faithfulness.rs` pattern that already caught this exact defect class.
Index-status: accepted
Date: 2026-09-06

## Context

The certificate chain is whole at bit-blasting, propositional search and model
lifting, and
[ADR-1704](adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
gave the theory layer a contract. Preprocessing — `axeyum-rewrite` — is the
stage between the input we were given and the formula we actually refuted, and
the question this ADR closes is what a step there owes.

**First, a correction to the premise.** The family page states preprocessing
"produces no checkable artifact". Measured, that is wrong in a way that matters:

- `TrustId` has 14 variants (`crates/axeyum-solver/src/trust.rs:124-139`) and
  four of them are preprocessing steps — `ArrayElim`, `Ackermann`, `IntBlast`,
  `DatatypeElim`.
- `ArrayElimUnsatCertificate::recheck`
  (`crates/axeyum-solver/src/abv/array_elim_certificate.rs:133`) and
  `AckermannUnsatCertificate::recheck` (`crates/axeyum-solver/src/euf.rs:1903`)
  are real, re-checkable artifacts for the eager-elimination `unsat` sub-case.
- All four ids are `is_certified() == false` (`trust.rs:284-300`), and the
  ledger says why.

So the hole is not absence. It is **which half is checked**, and the tree
already says so in its own words, at `trust.rs:89-95`:

> those re-blast the same circuit and re-check its CNF, which proves
> *determinism* but not *faithfulness* — a stably-wrong circuit (exactly the
> `af6c8bf` ±0 wrong-`unsat`) survives re-derivation.

That sentence is about `Fpa2Bv` and it names `ArrayElim`/`Ackermann`/`IntBlast`
in the same breath. It is the correct diagnosis and it has never been turned
into a rule about what a preprocessing step must produce. This ADR is that rule.

Five further measurements, all read from the tree:

1. **The placeholders have no producer.** `RewriteRuleId` is documented for
   "logs and future certificates" (`crates/axeyum-rewrite/src/lib.rs:68`) and
   `RewriteTestRoute::ProofObligation` as a "future proof obligation checked
   outside the rewriter" (`:138-139`). `grep -rn "ProofObligation" crates/
   --include=*.rs` returns **one** line — its own declaration.
   [ADR-0408](adr-0408-executable-rewrite-preconditions.md) says the same:
   "`RewriteTestRoute::ProofObligation` still has no consumer."

2. **A real semantic check already runs on every default query, and its verdict
   is thrown away.** ADR-0408's denotation guard
   (`PreconditionPolicy::Denotational`, the `Default`,
   `crates/axeyum-rewrite/src/canonical.rs:326-348`) evaluates each committed
   local rewrite before and after on `DENOTATION_GUARD_SAMPLES = 4` fixed
   assignments (`canonical.rs:312`, `:1064-1096`) and **refuses** the pass on
   disagreement (`RewriteError::PreconditionViolated`, `canonical.rs:474-483`).
   `SolverConfig::preprocess` defaults `true` (`backend.rs:377`), so every
   quantifier-free query runs it. `RewriteReport` and `PreconditionAudit` —
   including the deliberately honest `denotation_unavailable` hole counter,
   documented at `canonical.rs:443-450` as "a coverage hole, not a pass … so it
   can be measured instead of assumed away" — are read by **`axeyum-bench` and
   nothing else**. Every solver call site takes `.terms` / `.term`
   (`auto.rs:1895`, `preprocess.rs:85`, `incremental.rs:1213`).

3. **And the refusal is swallowed.** When the guard refuses,
   `auto.rs:1739-1751` records `record_declined("preprocess",
   DeclineReason::Incomplete(...))` and re-dispatches the original query. A
   rewriter that has just detected it cannot justify its own output is reported
   the same way as a timeout. That is a check whose exit status does not depend
   on its finding, in production, on the default path.

4. **The `unsat` direction is unchecked where the `sat` direction is
   hard-ruled.** `dispatch_reduced` reconstructs the model and replays it
   against the **original** assertions (`auto.rs:2043-2051`), and
   `replay_preprocessed_model` does the same (`preprocess.rs:189-195`). The
   `unsat` side is one line of prose in the same function's doc comment: "`unsat`
   of the reduced (equisatisfiable) problem transfers directly"
   (`auto.rs:1885`). `EvidenceReport.trusted_steps` is `Vec::new()` for every
   `sat` (`evidence.rs:2140, 2395, 2445, 3637`), and `evidence.rs`'s entire
   preprocessing footprint is a hand-bumped version string,
   `LayerVersions { rewrite: "1" }` (`evidence.rs:153-175`).

5. **What ADR-0005 asked for is a receipt, not a certificate.**
   [ADR-0005](adr-0005-phase3-query-evidence-rewrite-contracts.md)'s envelope
   requires "rewrite rule-set version and applied rule IDs". There is no input
   on which a list of rules that fired can be wrong. It is the shape the
   discipline names directly: *an operation registry where every entry names one
   target is a dispatch table, not a producer, and cannot fail to "produce"*.

**The literature does not hand us the answer.** eDRAT — the published form of
ADR-1704's own contract, cited there — states its main limitation is that it
starts from CNF and "is not adequate for representing proofs of preprocessing
and conversion of formulas to clauses"; it names three candidate bridges and
commits to none. cvc5, the one mature system that justifies its rewrites, needs
a whole DSL (**RARE**, FMCAD 2022) plus `--proof-granularity=dsl-rewrite` (now
its default), and **IsaRare** (TACAS 2024) verifying 338 of those rules in
Isabelle/HOL **found 6 faulty ones**, with a separate Eunoia→SMT-LIB translation
over 571 rules "instrumental in discovering several soundness bugs"
([survey](../02-ecosystems/competition-landscape-2026-09/adjacent-reasoning-arenas.md)
§5.6). Rewrite justification is where a from-scratch producer's coverage goes
holey first, and it is where real faults are found.

## Decision

**A preprocessing step owes exactly one of three obligations, and which one is
decided by what the step does to the model set — not by which crate it lives in
or which entry point it is reached through. An obligation is legally discharged
three ways: by a certificate the producer carries, by a structural check on the
artifact, or by the route declining to conclude in that direction. A decline is
a discharge. A re-derivation is not. Every default-enabled step on a route that
can report `unsat` must discharge its `unsat`-direction obligation by one of the
three, and the number that do not is a counted metric derived from the
artifact.**

### 1. The three obligations

Write `M(φ)` for the models of assertion set `φ`, and `φ ⟶ φ'` for one step.

| Shape | Effect on `M` | Obligation | Direction it can break |
|---|---|---|---|
| **Replacement** (denotation-preserving) | `M(φ') = M(φ)` | `⟦before⟧ = ⟦after⟧` under every assignment | both |
| **Relaxation** (drops or abstracts constraints) | `M(φ') ⊇ M(φ)` | "only constraints were removed" — a structural claim about the artifact | `sat` only |
| **Strengthening** (adds constraints) | `M(φ') ⊆ M(φ)` | every added constraint is a consequence of `φ` | `unsat` only |

Two things fall out, and both are already true in the tree:

- **A relaxation's `unsat` is free**, and the code already argues it:
  `check_qf_abv_lazy`'s doc comment (`abv.rs`) — "The abstraction is a
  relaxation (strictly fewer constraints), so an UNSAT abstraction soundly
  witnesses UNSAT of the original" — and `abstract_functions`
  (`functions.rs:87-97`) verbatim. That is a complete discharge with no
  artifact.
- **A strengthening's `sat` is free**, and its `unsat` is not. This is the half
  that already has certificates.

### 2. A re-derivation is not a discharge

`ArrayElimUnsatCertificate::recheck` re-runs `eliminate_arrays` on a scratch
clone of the originals (`array_elim_certificate.rs:137-138`), structurally
re-derives the select-congruence set from `elim.selects()`
(`rederive_select_congruence`, `:207`), asserts `eliminated == abstraction ++
rederived` (`:154-161`), re-bit-blasts and compares DIMACS byte-for-byte
(`:172-180`), and re-checks the DRAT (`:186`). Split against §1:

- **The strengthening half is genuinely discharged.** The re-derivation of the
  congruence set is a second implementation of one schema, and the equality
  `eliminated == abstraction ++ rederived` witnesses that no *spurious* extra
  assertion was appended — which is exactly the failure that can turn a
  satisfiable formula `unsat`. The file's own header says so: the witness
  "confirms each appended constraint is a real, valid congruence, never a
  spurious extra assertion". This is what the obligation asks for and it is
  done.
- **The replacement half is re-derived, not checked.** Read-over-write —
  `select(store(a,i,e),j) ⟶ ite(i=j, e, select(a,j))` and the `ite` case
  (`arrays.rs:364-379`) — is recomputed by the same `resolve_select` on the same
  input. A wrong branch order reproduces identically at step 1, so steps 2, 3
  and 4 compare wrong to wrong. That is `trust.rs:89-95`'s "determinism, not
  faithfulness", stated for the transform it applies to, and it is why the
  ledger keeps `TrustId::ArrayElim` at `is_certified() == false`.

  **Status of this claim.** It is derived from the four `recheck` steps and from
  the ledger's own general statement about these certificates; the specific
  mutation run — swap the `ite` branches at `arrays.rs:364-373` and confirm
  `recheck` still returns `Ok(true)` over a query that is genuinely satisfiable
  — is §7's first exit criterion and is **not** yet measured here. It is stated
  as a derivation, not as a measurement, and §7 exists to turn it into one.
- **`rederive_select_congruence` consumes the producer's own `selects()`.** If
  `record_select` (`arrays.rs:494-505`) recorded a wrong `(array, index, fresh)`
  triple, both sides agree. So even the checked half is checked *relative to*
  the producer's read record.

The general rule, stated so a violation is a test failure and not a matter of
taste: **a check that re-runs the producer discharges the obligation only for
the properties on which the two implementations are independent.** For an
elimination that appends constraints to an abstraction, that is the appended set
and nothing else.

### 3. The manifest has a slot for one direction and none for the other

`RewriteRule` (`crates/axeyum-rewrite/src/lib.rs:196-214`) carries
`preservation` and `projection: ModelProjection`. `ModelProjection` describes
how a model of the rewritten query maps back — the `sat` direction — and
`validate_projection` (`:288`) enforces it seriously: an equisatisfiable rule
may not be default-enabled without an `Implemented` projection *and* a
`ModelProjectionReplay` test route.

**There is no field for the other direction.** So
`Preservation::Equisatisfiable` reads as one class when it is two — a relaxation
and a strengthening are both "equisatisfiable" and they fail in opposite
directions. `RewriteRule` gains a field parallel to `projection`:

```rust
/// Why an `unsat` of the rewritten query is an `unsat` of the original.
///
/// The dual of [`ModelProjection`], which covers only the `sat` direction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsatObligation {
    /// Denotation is preserved, so `unsat` transfers with the equality.
    /// Legal only for `Preservation::Denotation`.
    Denotation,
    /// `M(after) ⊇ M(before)`: the step only weakens, so an `unsat` of the
    /// output is an `unsat` of the input for free.
    Relaxation { justification: String },
    /// The step adds constraints; the named checker reads the artifact,
    /// is independent of the producer on the added set, and can fail.
    Certified { checker: &'static str },
    /// The route does not conclude `unsat` from this step's output at all.
    Declined { reason: String },
    /// Nothing discharges it. Counted, and illegal on a default-enabled rule
    /// reachable from a route that reports `unsat`.
    Undischarged,
}
```

Validation mirrors `validate_projection`, so the failure is a `ManifestError` at
`RewriteManifest::new`: `Preservation::Denotation` with anything but
`UnsatObligation::Denotation` is `UnexpectedUnsatObligation` (the mirror of
`UnexpectedProjection`); `Preservation::Equisatisfiable` with
`UnsatObligation::Denotation` is `MissingUnsatObligation`; and
`enabled_by_default` with `Undischarged` is
`DefaultRuleWithUndischargedUnsat`.

All 59 rules `default_rules()` registers (`canonical.rs:547`, pinned at
`canonical.rs:5287`) are `Preservation::Denotation` with
`ModelProjection::Identity`, so all 59 take `UnsatObligation::Denotation` and
the field costs the manifest nothing today. Its value is that the ~20
non-manifest entry points now have a vocabulary to be classified in, and a
default (`Undischarged`) that counts rather than passes.

### 4. Every step, classified from the code

| Entry point | Shape | Obligation, and what it costs |
|---|---|---|
| `canonicalize` (59 manifest rules) | replacement | **Denotation.** Guard already runs per committed rewrite and refuses on mismatch. Two real gaps: the verdict is discarded (§Context 2) and the refusal is swallowed as a decline (§Context 3). Fixing both is plumbing, not proof theory. |
| `simplify_datatypes`, `lower_derived_bv` | replacement | **Denotation**, argued in doc comments (`datatypes.rs:10-11`, `lower_bv.rs:24-26`), nothing retained, no runtime guard. |
| `propagate_values` | replacement in effect | The only pass claiming both directions: "the substituted constant is literally the variable's only possible value, so this is also satisfiability-preserving for `unsat`" (`propagate_values.rs:12-18`). Trail retained. |
| `solve_eqs`, `elim_unconstrained` | equisatisfiable + model-sound | `ModelReconstructionTrail` retained — the `sat` direction. The `unsat` direction is unstated. `solve_eqs` drops the defining equality (`solve_eqs.rs:196-198`) after an occurs-check, which is a replacement; `elim_unconstrained` substitutes an inverse term. Both are cheap `Denotation`/`Relaxation` rows once someone writes the argument down. |
| `eliminate_arrays` | **mixed — and it already separates itself** | Read-over-write is replacement; Ackermann is strengthening; `assertions = abstraction ++ ackermann_constraints` (`arrays.rs:279-289`) makes the added set a suffix. `Certified` for the strengthening half (§2), **`Undischarged` for the replacement half**. |
| `eliminate_functions` | same shape (`functions.rs:389-390`) | Identical split. Note its fresh symbols are source-derived (`!fn_app_{TermId}`, `functions.rs:467-478`) and stable, where arrays uses a counter (`!arr_sel_{n}`, `arrays.rs:489`) — a determinism difference a serialized certificate would trip over. |
| `abstract_arrays`, `abstract_functions` | relaxation | **`Relaxation`**, free, argument already written. `abstract_arrays` has no caller outside its own unit test — dead surface worth deleting or wiring. |
| `instantiate_universals`, `instantiate_with_triggers` | relaxation (weakening) | **`Relaxation`.** Each conjunct is `body[x := t]` and the `∀` is replaced by the conjunction, so the result is *weaker*: `unsat` transfers, `sat` says nothing (`quantifiers.rs:282-288`). `Instantiation.instantiated` already flags it. Free. |
| `expand_quantifiers` | replacement on a complete finite domain | Denotation on the domain, and explicitly untrusted: "the caller replays the *original* quantified formula through the enumerating ground evaluator" (`quantifiers.rs:9-10`). That replay is the discharge — a `Declined`-adjacent route that works because the original is re-evaluated, not the expansion re-derived. |
| `blast_integers` | bounded; neither | **`Declined`, already.** "A bit-vector `unsat` means only 'no model in the bounded range', which is `unknown` for the integer problem, never `unsat`" (`int_blast.rs:18-21`), and it already carries `restricting_constraints: usize` (`int_blast.rs:106-113`), the count of no-overflow guards, precisely so an `unsat`-emitting consumer knows to decline. **The crate already contains a decline and a counted restriction; this ADR names the pattern rather than inventing it.** |
| `eliminate_int_divmod` | exact for `c ≠ 0`, relaxation for `c = 0` | **`Undischarged`, and the sharpest remaining gap.** It returns a bare `Vec<TermId>` with no split index, no fresh-variable map, and no record of which `div`/`mod` term became which variable (`int_divmod.rs:34-37`). Its `c = 0` congruence closure is bounded by `MAX_CONGRUENCE_GROUPS = 48` (`int_divmod.rs:199`), above which the pass changes soundness mode — and **the crossing is not reported to the caller in any form**. It feeds live `unsat` refuters (`auto.rs:2455`, `auto.rs:2497`). The documented direction is that `unsat` transfers at every size (`int_divmod.rs:197-198`), so this is a reporting gap rather than a known wrong-`unsat` — but an unreported soundness-mode change is exactly what a counted obligation exists to surface. |

The point of the table: the expensive cases are the minority. One step already
declines, four are relaxations whose argument is already written, most of the
rest are replacements, and the concentrated work is the replacement half of the
two eager eliminations plus `eliminate_int_divmod`'s missing metadata.

### 5. How this composes with ADR-1704

The two contracts are the same shape, so one artifact covers input-to-CNF
without a new format:

```
source assertions
   │  replacement steps: each a denotation equality
   ▼
abstraction   ++  added_constraints        ← ADR-1721; count is a subtraction
   │  bit-blast (lowering/lift maps retained by hard rule)
   ▼
cnf           ++  theory_lemmas            ← ADR-1704; count is a subtraction
   │  boolean stream
   ▼
   ⊥
```

The left column is not an analogy. `arrays.rs:281`, `functions.rs:389` and
`int_blast.rs:214` all snapshot the pre-append vector and then `extend` it, so
in all three the added set is literally a contiguous tail slice and its count is
`len(after) - len(before)` — the same subtraction discipline ADR-1704 §1
imposes, already implemented three times before either ADR was written.

Three rules make this one artifact instead of two:

1. **Same subtraction discipline**, with the same failure mode: ADR-1704's mode
   4 (a lemma hidden among the input clauses) has an exact analogue here — an
   added constraint smuggled into the rewritten body rather than appended. It is
   caught the same way, by the equality `eliminated[..n] == abstraction`, which
   `ArrayElimUnsatCertificate::recheck` already asserts.
2. **Two counts, never one.** The report carries `added_constraints` /
   `added_constraints_unchecked` beside ADR-1704's `theory_lemmas` /
   `theory_lemmas_unchecked`. Merging them would let progress on one layer hide
   a regression on the other.
3. **The reported assurance is the minimum over the layers.**
   `added_constraints_unchecked > 0` must never produce
   `EvidenceCheck::Verified`, and must never co-occur with a trust id whose
   meaning is a refutation of the *original* query. This is ADR-1704 §5.2
   restated one layer up.

**The trusted base does not grow.** As in ADR-1704, the checker for the
strengthening half is a structural match against a fixed schema — no solver, no
decision procedure. That is the reason to prefer per-step obligations over one
global "the preprocessed query is equisatisfiable to the source", which could
only be discharged by another solve.

### 6. What a certificate cannot express — the impossibilities, measured

Three, each a distinction the producer makes and the artifact cannot carry:

1. **A canonicalization certificate can carry the steps but not the
   derivation.** `RuleApplication` (`canonical.rs:295-303`) carries
   `rule_id`, `before`, `after` — and the arena is hash-consed, so `before`
   identifies the subterm exactly and the *local* obligation `⟦before⟧ =
   ⟦after⟧` is independently checkable. What is absent is the **position and
   the order**: no path, no parent, no argument index, and `RewriteReport` is a
   flat `Vec` across all roots (`canonical.rs:184-192`). Under DAG sharing a
   given `before` may occur at many positions. So a checker can verify every
   step and still cannot verify that those steps *compose* to the reported
   output term; only re-running the canonicalizer reproduces that, and a
   re-derivation shares every bug with the producer (§2). This is why
   canonicalization is not the first slice despite being the most-used step.

2. **The denotation guard's verdict is a sample and must be named as one.** Four
   fixed assignments (`canonical.rs:312`) with `DENOTATION_GUARD_MAX_BV_WIDTH =
   128` (`:319`); arrays, reals, datatypes, uninterpreted sorts and wider BVs
   fall through to `denotation_unavailable`. A certificate may record "guarded
   at N samples, M unavailable" and must not record "denotation preserved". The
   crate already got this right internally — `denotation_unavailable` is
   documented as "a coverage hole, not a pass" — and the honest form is still a
   strict gain over discarding it.

   **And this is why the replacement half of `eliminate_arrays` is unchecked:**
   the one runtime semantic check in the crate is structurally blind to
   array-sorted terms, which is exactly the sort read-over-write rewrites.

3. **Two manifest rules carry no witness at all.**
   `eq.alpha_equivalent.v1` and `quant.negation_duality.v1` are backed by
   `alpha_equivalent` / `alpha_equivalent_to_negation` (`alpha.rs:101`, `:132`),
   which return a bare `bool` and discard the binder correspondence
   (`Scope.pairs`, `alpha.rs:143-145`). Their `RuleApplication` therefore
   carries no renaming, so the certificate cannot say *why* those two rewrites
   were sound — only that the predicate said yes. The predicate is one-sided
   sound by construction (budget exhaustion returns `false`, "a decline, never
   an accept", `alpha.rs:62-64`), which is what makes the gap tolerable rather
   than urgent, but it is a distinction the producer makes and the artifact
   loses.

### 7. The smallest end-to-end slice, named concretely

**An independent faithfulness witness for read-over-write**, copying the pattern
this repository has already proved on the same defect class.

The precedent is exact. `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs` checks
the FP→BV circuits for `FP8_E5M2` over **every** input bit pattern against
`rustc_apfloat`'s native reference — an independent oracle, not a re-derivation
— and `trust.rs:80-95` records that it "has demonstrated teeth (it rejects a
swapped-selection `fp.min`/`fp.max` mutation)", against a real shipped
wrong-`unsat` (`af6c8bf`). Read-over-write's analogous mutation is swapping the
`ite` branches at `arrays.rs:364-373`.

The demonstration query is small and must be **satisfiable**, so that the
mutation produces a wrong `unsat` rather than merely a different formula:

```
i ≠ j  ∧  select(store(a, i, e), j) ≠ e
```

Correct read-over-write gives `ite(i=j, e, select(a,j))`, which under `i ≠ j` is
`select(a, j)`, so the query asserts `select(a,j) ≠ e` — satisfiable. With the
branches swapped it becomes `e`, so the query asserts `e ≠ e` — `unsat`. If
`certify_array_elim_unsat` then produces a certificate whose `recheck` returns
`Ok(true)`, that is a wrong `unsat` carrying a passing certificate, which is the
finding §2 predicts and this slice must either confirm or refute.

The slice:

1. `check_read_over_write_faithful(arena, assertions, &elim, samples) -> bool`.
   For each sampled assignment: give every array symbol a concrete finite map
   (the evaluator already has array values, ADR-0010), give every other free
   symbol a value, then derive each fresh select symbol's value as
   `a^M[idx^M]` from `elim.selects()` — the exact model extension the
   certificate header argues abstractly — and require
   `⟦original assertion⟧ = ⟦abstraction assertion⟧` for every assertion.
   The reference is the ground evaluator on the **original** array term, which
   is independent of `resolve_select`.
2. Call it from `ArrayElimUnsatCertificate::recheck` as a step (1b), so the
   existing artifact's replacement half stops being re-derived.
3. **Mutation control:** swap the read-over-write `ite` branches on a snapshot
   (never the shared worktree) and require that exactly one test dies — the new
   faithfulness test — while the existing
   `crates/axeyum-solver/tests/array_elim_unsat_proofs.rs` suite, whose
   soundness-negative anchors today cover a fabricated certificate but not a
   wrong producer, is unaffected. Whichever way that run comes out is the
   finding, and it settles §2's derivation.

Why this and not something bigger: it upgrades an artifact that already exists
and is already in the trust ledger, it closes the half §2 measures as open, it
needs no new semantics, and its negative control is a wrong rewrite over a
**satisfiable** query — so the test fails because the certificate is wrong, not
merely because it is absent.

The second slice, when this lands, is `eliminate_int_divmod`'s missing metadata
(§4), because it is the only `unsat`-feeding transform with no artifact of any
kind and a soundness-mode change nobody is told about.

## Evidence

Measured in this tree, not asserted:

- `grep -rn "ProofObligation" crates/ --include=*.rs` → one line,
  `crates/axeyum-rewrite/src/lib.rs:139`.
- `TrustId` has 14 variants (`trust.rs:124-139`); `ArrayElim`, `Ackermann`,
  `IntBlast`, `DatatypeElim` are all `is_certified() == false`
  (`trust.rs:284-300`), and `trust.rs:89-95` states the reason: re-derivation
  proves determinism, not faithfulness.
- `array_elim_certificate.rs:137-186` — the four `recheck` steps; step (1)
  re-runs `eliminate_arrays` on the originals, and
  `rederive_select_congruence` (`:207`) consumes `elim.selects()`, the
  producer's own record. The module's own doc says the rebuild "mirrors
  `Eliminator::ackermann_constraints` verbatim".
- `arrays.rs:281-286`, `functions.rs:389-390`, `int_blast.rs:214-215` — three
  independent implementations of "snapshot, then extend", so the added set is a
  tail slice in all three.
- `canonical.rs:326-348` (`Denotational` is `Default`), `:312` (4 samples),
  `:1030-1039` (refuse), `:443-450` (`denotation_unavailable` is a hole, not a
  pass); `auto.rs:1739-1751` (the refusal becomes `record_declined`).
- `canonical.rs:547` + the pin at `canonical.rs:5287-5288` — **59** default
  rules, all `Preservation::Denotation` / `ModelProjection::Identity`. ADR-0408
  said 57; the count has drifted and this ADR uses the pinned number.
- `evidence.rs:153-175` — `LayerVersions { rewrite: "1" }` is the whole
  preprocessing footprint of the evidence envelope.
- `int_blast.rs:18-21` (the decline) and `:106-113`
  (`restricting_constraints`); `int_divmod.rs:34-37` (bare `Vec`) and `:190-199`
  (`MAX_CONGRUENCE_GROUPS = 48`).
- `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs` and `trust.rs:80-95` — the
  precedent for §7, including its demonstrated teeth and the wrong-`unsat`
  (`af6c8bf`) it corresponds to.

External, from the in-tree survey (sourced there):

- **RARE** (Nötzli et al., FMCAD 2022,
  `10.34727/2022/ISBN.978-3-85448-053-2_12`) and
  `--proof-granularity=dsl-rewrite`, now cvc5's default; **IsaRare** (TACAS
  2024) verified 338 rules and found **6 faulty**; a Eunoia→SMT-LIB translation
  over 571 rules was "instrumental in discovering several soundness bugs".
- **eDRAT** (FMCAD 2024, cited in
  [ADR-1704](adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)'s
  Prior art): does not cover preprocessing; three unresolved bridges. Their
  measurement worth carrying: ALF and LFSC proofs do include preprocessing
  steps, and the size difference is "significant mostly on easy problems" — on
  hard problems resolution and theory lemmas dominate. **Preprocessing evidence
  is a correctness gap, not a scale problem.**

## Alternatives

### (1) Record the applied rule IDs and call it evidence — rejected

ADR-0005's envelope field, and the obvious cheap move. There is no input on
which it can be wrong: it reports what the producer did, from the producer. The
field stays as provenance; it is not a discharge and this ADR does not let it
count as one.

### (2) Keep re-derivation as the discharge — rejected, with the reason already in the tree

It is what the two existing certificates do for their replacement half, so
adopting it is not a regression. Rejected because `trust.rs:89-95` already
records the failure — a stably-wrong transform survives re-derivation — and
because the repository has already paid for that lesson once, in `af6c8bf`. §2
turns the observation into a rule so the next certificate cannot re-make the
choice silently.

### (3) Adopt cvc5's route (a rewrite-rule DSL plus a granularity flag) — rejected as the *first* step

RARE is the field's answer and the right long-run shape for the **replacement**
obligation. Rejected as the entry point because: it addresses only replacement,
and our replacement steps in the manifest are the ones ADR-0408 already guards;
it is a language plus a catalogue plus an elaborator, and cvc5 needed a
granularity flag precisely because full elaboration is expensive; and IsaRare's
6 faults in 338 rules say the DSL is where the correctness *effort* lands, not
where it starts. Revisit when the non-manifest replacements are the residual.

### (4) CPF/CeTA's shape — the long-run target, not this slice

The survey's own conclusion: *"if axeyum wants a rewriting-certificate arena,
CPF/CeTA is the pattern to copy, not RARE/IsaRare"* — an untrusted prover emits
a certificate, a trusted small checker extracted from a machine-checked
formalization re-verifies it, and only re-verified answers score. That is this
project's architecture, running for twenty years in termCOMP, with a measured
trusted-base gap (AProVE's certified configuration recovers ~92% of its own
uncertified YES answers) of exactly the kind we report. It is the destination;
§7 is the step that produces something worth serializing into it.

### (5) One global claim: "the preprocessed query is equisatisfiable to the source" — rejected

The only discharge is another solve, which is the inverted cost
[ADR-0613](adr-0613-unsat-is-certified-by-following-hints-not-by-searching-for-them.md)
was written against; and it collapses the three obligations into one
undifferentiated claim, losing exactly the distinctions — a relaxation's free
`unsat`, a decline's free everything — that make most of this work unnecessary.

### (6) A provably correct preprocessor — deferred, with the reason

eDRAT's third option, which they call "most effort … most benefit". Their
objection is ours: maintaining a verified preprocessor as theories and
simplifications are added. Deferred rather than rejected — this project has a
kernel, so it is reachable later in a way it is not for most solvers.

### (7) Translation validation over the whole pipeline — this *is* the decision, restricted

eDRAT's second option: treat preprocessing as a compilation and validate per
run. That is §1, with one restriction that makes it affordable — validation is
**per step and per shape**, not over the composed pipeline. Their noted
difficulty ("this may require the solver to produce hints") is answered as
ADR-1704 answered it: the producer carries what it already has, and
`ArrayElimination` already has it.

## Consequences

**Easier.**

- A step's evidence duty becomes a question with a mechanical answer — "what
  does it do to the model set?" — instead of a judgement call, and the answer is
  a manifest field a validator refuses.
- Most steps cost nothing: one already declines, four are relaxations whose
  argument is written, the manifest's 59 rules are all replacements.
- One artifact from input to CNF, because ADR-1721 and ADR-1704 are the same
  subtraction shape and three passes already implement it.
- The residual becomes a number that goes down
  (`added_constraints_unchecked`), visible per query.

**Harder.**

- `RewriteRule` grows a field, so every rule must be classified before the
  manifest builds — deliberate and loud, as ADR-0408 made the guard.
- The ~20 non-manifest entry points are outside the manifest, so the field alone
  does not reach them; until the ADR-0408 successor slice pulls them in, their
  honest value is `Undischarged` and the count says so.
- Two counts where one would read better in a report. That is the point; they
  are not merged.
- §7's witness costs sampled evaluation over array values inside a `recheck`
  that today is pure re-derivation, so certificate re-checking gets slower. It
  is the cheap half of the cost model — the measured external number is a median
  **6.9%** for kernel checking against a median **8.7x** for proof-producing
  search — so this is the right half to spend in.

**Revisited when.**

- `RuleApplication` gains a position and an order: §6 item 1 stops being an
  impossibility and canonicalization becomes independently replayable rather
  than only re-derivable.
- `eliminate_int_divmod` gains metadata: its row moves off `Undischarged` and
  the 48-group mode change becomes reportable.
- The non-manifest replacements are the residual: that is when alternative (3),
  a RARE-shaped rule language, is worth its cost.
- An external referee is wanted: alternative (4), CPF/CeTA's shape, which
  supersedes the artifact's *serialization* without changing what must be
  recorded.
