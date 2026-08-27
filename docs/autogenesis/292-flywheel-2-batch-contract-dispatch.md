# 292 — Batching the second turn: all 26 admissible facts, one s5 session

Date: 2026-08-27
Lane: flywheel-2

## Task

Turn one (doc 290, lane `flywheel-1`) ran the contract-dispatch flywheel
end to end for exactly one fact and recorded an honest decline. This task's
job was to amortize the per-dispatch setup (s5 session, pin verification,
adapter boilerplate) across **every** fact `scripts/fact-frontier.py --json`
currently reports admissible, rather than repeating turn one's procedure 26
times.

## Before state

`python3 scripts/fact-frontier.py --json`, verified against the merged tree
carrying `scripts/validate-producer-contract-declines.py` and doc 291:

```
admissible_count: 26
admissible_via_contract_count: 26
admissible_via_operation_count: 0
declined_count: 1  (producer-contract-int-modeq-family-v1)
selected_fact_id: F:ml430-int-add-modeq-right-e58108ee
```

(The brief cited `F:ml730-int-add-modeq-right-e58108ee`; the real id, verified
directly from `selection.selected_fact_id`, is `F:ml430-…` — the brief's `730`
was a typo, caught by checking rather than trusting it.)

**11 facts** match `producer-contract-int-modeq-family-v1` (`fragment: Int`,
`statement_contains: "[ZMOD "`). **15 facts** match
`producer-contract-nat-coprime-family-v1` (`fragment: Nat`,
`statement_contains: "Coprime"`). 11 + 15 = 26, the full admissible
population.

## Partition check (done first, per brief)

Cross-referenced all 26 admissible fact ids against
`artifacts/autogenesis/nursery-v1.json`:

- 11 int-modeq facts: partition `train`.
- 15 nat-coprime facts: partition `development`.

**Zero held-out.** No selector-bug stop condition triggered; safe to proceed
under ADR-0542.

## Pins verified once

```
mathlib4    HEAD = c5ea00351c28e24afc9f0f84379aa41082b1188f  (matches manifest)
lean4export HEAD = a3e35a584f59b390667db7269cd37fca8575e4bf  (matches manifest)
```

One `ssh s5` round trip, not 26.

## Batching the adapter authoring: mixed strategy, reported honestly

The brief asked which of two batching strategies was used. Both, because s5
already had partial batches from prior episodes:

1. **int-modeq family (11 facts): reused an existing compiled batch file,
   wrote none.** `AxeyumGeneratedModEqBatchV1.lean` (created 2026-08-25,
   already compiled: `.lake/build/lib/lean/AxeyumGeneratedModEqBatchV1.olean`
   dated the same day) already contained one `def` per fact for **all 11**
   target statements, verified line-by-line against this task's own read of
   the fact ledger's `formal.statement` fields before use. No new file, no
   recompile — this batch's entire int-modeq cost was 11 `lean4export`
   invocations against an already-built `.olean`.
2. **nat-coprime family (15 facts): one new file for 13, reused an existing
   batch file for 2.** `Nat.Coprime.symmetric` and `Nat.not_coprime_zero_zero`
   were already present (as `natCoprimeSymmetric`, `natNotCoprimeZeroZero`) in
   a second pre-existing compiled batch file,
   `AxeyumAutogenesisOpenArrowFreeV1.lean` (2026-08-26). The other 13 had no
   existing adapter anywhere on s5 (`grep -il coprime
   /home/mjbommar/lean-import-scale/mathlib4/Axeyum*.lean` found only these
   two files), so this task authored one new standalone file,
   `AxeyumAutogenesisNatCoprimeFamilyV1.lean` (13 `def`s, one namespace,
   `import Mathlib`), matching the binder shapes verified against the pinned
   Mathlib source for every one of the 13 (`Mathlib/Data/Nat/GCD/Basic.lean`,
   `Mathlib/Data/Nat/Prime/Basic.lean` — exact `variable` blocks read and
   matched, not assumed). One `lake env lean` compile for that file.

Total s5 compiles for this entire batch: **one** (the 13-def coprime file;
the two 11-def int/coprime batch files were already built by earlier
episodes and needed no rebuild). Total `lean4export` invocations: **26**, one
per fact, each against whichever already-built `.olean` held that fact's
`def`, run from a single shell script
(`flywheel-2-export-batch.sh`) so the whole export pass was one `ssh`
session. All 26 exports: exit 0, **zero-byte stderr**, records ranging
6,024–232,222 (the outlier, `coprimeOfLtMinFac`, pulls in `minFac`'s
well-founded recursion machinery — large but still a clean, complete export).

## Predict-then-check

Before running the batch, each fact's expected outcome was classified from
reading `crates/axeyum-lean-import/src/producers/modeq_family.rs`'s search
algorithm (peel leading `Pi`/hypothesis binders; at the terminal, `whnf`, then
close an `Eq`-headed goal by refl/symm/trans over retained hypotheses, or an
`Iff`-headed goal by two nested closures) against each fact's
`formal.statement`.

### int-modeq family: predictions matched actuals, 11/11

| fact | predicted | actual |
|---|---|---|
| `int-add-modeq-right` | decline, `TerminalNotClosed` (unconditional identity, no hypothesis to combine) | `TerminalNotClosed` |
| `int-mod-modeq` | decline, `TerminalNotClosed` (unconditional; `(a%n)%n = a%n` is not `def_eq` for symbolic `a,n`) | `TerminalNotClosed` |
| `int-modeq-add-left` | decline, `TerminalNotClosed` (hypothesis is `a%n=b%n`, goal is `(c+a)%n=(c+b)%n` — different subterms, no congruence step in this schema) | `TerminalNotClosed` |
| `int-modeq-add-left-cancel'` | decline, `TerminalNotClosed` (same mismatch, reversed) | `TerminalNotClosed` |
| `int-modeq-dvd-iff` | decline, `TerminalNotClosed` (`n∣a`/`n∣b` unfold to something other than `Eq`/`Iff` at the point the nested closure needs one) | `TerminalNotClosed` |
| `int-modeq-neg` | decline, `TerminalNotClosed` (hypothesis `a%n=b%n` vs goal `(-a)%n=(-b)%n`) | `TerminalNotClosed` |
| `int-modeq-of-dvd` | decline, `TerminalNotClosed` (hypothesis over modulus `n`, goal over modulus `m`) | `TerminalNotClosed` |
| `int-modeq-of-mul-left` | decline, `TerminalNotClosed` (hypothesis over `m*n`, goal over `n`) | `TerminalNotClosed` |
| `int-modeq-sub` | decline, `TerminalNotClosed` (unconditional, two fresh variables, no hypothesis) | `TerminalNotClosed` |
| `int-modulus-modeq-zero` | decline, `TerminalNotClosed` (unconditional; `n%n` vs `0%n` not `def_eq` for symbolic `n`) | `TerminalNotClosed` |
| `int-neg-modeq-neg` | decline, `TerminalNotClosed` (`Iff`, `mp` direction already mismatches like `modeq-neg`) | `TerminalNotClosed` |

All 11 imports were **clean** (0 axioms, 205–233 declarations each) — this
independently reconfirms turn one's finding that the `Nat.div_rec_lemma`
cascade (docs 241/242) stays bridged for every member of this family, not
just the one turn one tried. All 11 producer runs declined with exactly the
mechanism turn one found for the sibling `add_modEq_left`: an unconditional
identity, or a hypothesis whose sides don't syntactically match the goal's
sides after `whnf` — this schema has no congruence/rewriting step, only
refl/symm/trans over already-`def_eq` subterms.

### nat-coprime family: predictions were WRONG for all 15 — the interesting result

Predicted (from reading only `propose_modeq_family`'s search over an
already-imported goal): mostly `TerminalNotClosed`, for reasons like "`Coprime
a b` unfolds to `Eq (gcd a b) 1`, but `gcd a b` and `gcd b a` (or `gcd (m+n)
n` and `gcd m n`, etc.) are different terms with no congruence step available"
— plus two predicted `TerminalNotClosed` for a structurally different reason
(`Symmetric Nat.Coprime` and `¬Nat.Coprime 0 0` are headed by `Symmetric`/`Not`
applications, not raw `Pi`, so this schema's binder-peeling — which only fires
on a goal that is *syntactically* a `Pi` before any unfolding — never re-enters
after `whnf` reveals the `Pi` underneath).

**Actual: all 15 failed at IMPORT, before the producer ever ran, with
`StatementImportError::TrustedDeclaration`.**

| fact | predicted reason | actual stage | actual reason |
|---|---|---|---|
| `nat-coprime-add-self-left` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-add-self-right` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-iff-isrelprime` | `TerminalNotClosed` | **import** | `TrustedDeclaration("eq_self", Theorem)` |
| `nat-coprime-of-dvd'` | `TerminalNotClosed` | **import** | `TrustedDeclaration("eq_self", Theorem)` |
| `nat-coprime-of-dvd-left` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-of-dvd-right` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-of-lt-minFac` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Quot", Quotient)` |
| `nat-coprime-one-left-iff` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-one-right-iff` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-primes` | `TerminalNotClosed` | **import** | `TrustedDeclaration("eq_self", Theorem)` |
| `nat-coprime-self-add-left` | `TerminalNotClosed` | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `Coprime.symmetric` | `TerminalNotClosed` (never re-peels a `Pi` hidden behind `Symmetric`) | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `nat-coprime-two-left` | `TerminalNotClosed` | **import** | `TrustedDeclaration("eq_self", Theorem)` |
| `not_coprime_zero_zero` | `TerminalNotClosed` (never re-peels a `Pi` hidden behind `Not`) | **import** | `TrustedDeclaration("Nat.mod_lt", Theorem)` |
| `Prime.dvd_iff_not_coprime` | `TerminalNotClosed` | **import** | `TrustedDeclaration("eq_self", Theorem)` |

`TrustedDeclaration` (`crates/axeyum-lean-import/src/lib.rs:336`) is not a
producer decline reason at all — it is the v1 statement-adapter import
policy's own guard: *"a proof-bearing or trusted declaration entered the
statement stream."* Elaborating `Nat.Coprime`/`Nat.gcd`/`Nat.minFac` as a bare
`Prop` — before any proof is attempted — pulls in, transitively, either an
already-proved Mathlib `Theorem` (`Nat.mod_lt`, or `eq_self`, most likely
reached through a `Decidable`/well-founded-recursion equation-compiler
byproduct rather than anything in the surface statement) or the `Quot`
primitive itself (for `coprime_of_lt_minFac`, whose `minFac` unfolds through
machinery that reaches `Quot` directly). The import tool's fail-closed policy
refuses to admit any such declaration into a "proof-free" statement stream by
design, so **`propose_modeq_family` never got a chance to run for a single
one of these 15 facts** — the identical error line under `-- import --` and
`-- producer --` in the raw run output is not a coincidence; `modeq_family_
operation`'s `main()` calls the same import step first and fails at the same
point.

**This is the real finding this batch adds over turn one.** My own
prediction, built from reading the producer's search logic in isolation, was
wrong for all 15 nat-coprime facts because the producer's own decline space
(`BinderBudgetExceeded`, `RequiredDeclarationUnavailable`,
`UnsupportedRecursorShape`, `UnsupportedIffShape`, `TerminalNotClosed`) is not
the only place a "combinator-over-hypotheses" contract can fail — the
*import* stage has its own, structurally earlier gate, and
`nat-coprime-family-v1`'s shape predicate (`fragment: Nat`,
`statement_contains: "Coprime"`) says nothing about whether the STATEMENT
itself elaborates without touching a proof-bearing declaration. int-modeq
statements happen to elaborate through pure, proof-free `def`s
(`Int.ModEq`, `%`, `+`, `Dvd.dvd`); nat-coprime statements apparently do not,
because `Nat.gcd`/`Nat.minFac`'s well-founded-recursion compilation embeds
theorem-kind byproducts (`Nat.mod_lt`, the termination proof; `eq_self`,
likely from an auto-generated equation lemma or `Decidable` derivation) or
(for `minFac`) reaches `Quot` outright. **15 for 15**, with no exception —
this is not a corner case of the contract, it is the contract's entire
population.

## Falsifiability: is `TrustedDeclaration` real, or convenient?

Checked directly against the importer's own source rather than trusted from
the error text: `crates/axeyum-lean-import/src/lib.rs:336`
(`StatementImportError::TrustedDeclaration { name, kind }`, `Display` at
line 390: `"statement stream contains trusted declaration {name:?}
({kind:?})"`), raised at two call sites (`src/lib.rs:2065`, `:2163`). Both
call sites are inside the statement-adapter import path
(`import_statement_ndjson`), gating what may enter the stream **before** any
producer is invoked — exactly the "trusted assumption reached before a proof
is even attempted" check the v1 statement-adapter scheme (doc 290's
"encoding: transparent-definition-of-prop") exists to enforce. Not a
convenient relabeling; a pre-existing, already-typed enum variant this batch
merely exercised at scale.

## Disposition: 26 declines, 0 proofs

**Every one of the 26 admissible facts stays `epistemic_status: open`.** No
evidence attached, no operation registered — ADR-0602 and doc 288's
"admission precedes registration" apply identically to a batch of 26 as to
one. Recording a `proved` status or an operation receipt from a shape match
with no completed proof is exactly the checker-that-cannot-fail defect this
project rejects everywhere else; a 100% decline rate over the full admissible
population is a fine, honest result, not a failure of this task.

26 new decline artifacts, one per fact, in the established
`<name>-decline-v1.json` shape (doc 291's convention: top-level `contract` +
`fact_id`, `producer.result: "declined"`, a bare typed `decline_reason`,
`contract_sha256` of the current contract content):

- 11 × `artifacts/autogenesis/mathlib-int-*-decline-v1.json`
  (`decline_reason: TerminalNotClosed`, `contract_sha256` matches
  `int-modeq-family-v1.json`'s current content — identical to turn one's
  seed artifact's `contract_sha256`, confirming the contract has not changed).
- 15 × `artifacts/autogenesis/mathlib-nat-*-decline-v1.json`
  (`decline_reason: TrustedDeclaration`, `contract_sha256` matches
  `nat-coprime-family-v1.json`'s current content).

## After state

```
admissible_count: 0
admissible_via_contract_count: 0
declined_count: 27  (12 producer-contract-int-modeq-family-v1, 15 producer-contract-nat-coprime-family-v1)
selected_fact_id: null
outcome: refused-no-admissible-candidate
```

Every fact that matched either seed contract now carries a live decline
against that exact contract version. The selector has nothing left to
dispatch via either contract until: (a) a genuinely new fact matches one of
their shapes, (b) a contract's `recipe`/`shape` changes (a real capability
change re-opens every fact it previously declined — doc 291's re-dispatch
policy), or (c) a new, third contract is written for a different shape.

## Before/after table

| metric | before | after |
|---|---|---|
| `admissible_count` | 26 | 0 |
| `admissible_via_contract_count` | 26 | 0 |
| `declined_count` | 1 | 27 |
| `declined_by_contract[int-modeq-family-v1]` | 1 | 12 |
| `declined_by_contract[nat-coprime-family-v1]` | 0 | 15 |
| proved this batch | — | 0 |
| `selected_fact_id` | `F:ml430-int-add-modeq-right-e58108ee` | `null` |
| `outcome` | `selected` | `refused-no-admissible-candidate` |

## What this batch did NOT do

Per the brief: **no weakening of any gate, no extending the checker, no
engineering around a decline.** `propose_modeq_family` was not touched.
`crates/axeyum-lean-import/src/lib.rs`'s `TrustedDeclaration` guard was not
touched. Neither producer contract instance was touched. No operation was
registered. No fact's `epistemic_status`, `external_status`, or `evidence`
changed — this batch also did not touch any fact's `notes` field (unlike
turn one), because this lane's scope is `artifacts/facts/` evidence/status
*for facts proved*, and zero facts were proved.

## The manual-judgment accounting, against turn one's six items

Turn one itemized six places a human supplied judgment a machine could not
have. Re-running the same accounting for a 26-fact batch, to measure whether
the automation fraction improved:

1. **Recognizing which family member is which shape, per fact.** Still
   entirely manual — 26 times, not once. The `statement_contains` predicate
   still cannot distinguish "combinator over an already-given hypothesis"
   from "derive a new arithmetic identity" from "hypothesis's subterms don't
   match the goal's". Reading `formal.statement` and predicting the
   producer's behavior before running it was this task's own predict-then-
   check exercise, and it was reusable batch INFRASTRUCTURE (one script) but
   NOT reusable JUDGMENT — each of the 26 predictions required reading that
   fact's specific statement shape. Not reduced by batching.
2. **Locating and authoring s5 adapters.** **Substantially reduced.** Turn
   one's item 2 (finding the pinned Mathlib source, matching implicit/
   explicit binder shape exactly) was needed for only 13 of 26 facts this
   time — 11 int-modeq facts and 2 nat-coprime facts already had
   adapters from prior episodes' batch files, found by `grep`/`ls` on s5
   before authoring anything new. This is the clearest place the "one file,
   many `def`s" pattern (evidently already discovered by at least one prior
   episode, independently of this task) pays off across dispatches: the
   marginal cost of a NEW fact whose statement fits an EXISTING batch
   file's namespace is zero adapter-authoring, only one `lean4export`
   call.
3. **The `-o` flag / build mechanics.** **Fully eliminated this run** —
   every `.olean` needed already existed except the one new 13-def file,
   which needed exactly one `lake env lean … -o …` (documented once, reused
   13 times).
4. **Interpreting a decline as genuine rather than a bug to route around.**
   Still entirely manual, and arguably HARDER at scale: recognizing that 15
   of 15 nat-coprime facts failing identically is not evidence of a broken
   tool but evidence that the WHOLE nat-coprime contract shape has an import-
   stage gate the contract's shape predicate cannot see, required reading the
   importer's own source (`StatementImportError::TrustedDeclaration` and its
   two call sites) rather than accepting the batch-run error text at face
   value — the same discipline CLAUDE.md's "tools have lied" entry demands,
   applied to 15 identical-looking failures instead of one.
5. **Connecting the finding to a load-bearing prior gap.** For int-modeq,
   turn one's `0 < n` gap in `int_prelude/modeq.rs` applies identically to
   several of this batch's 11 (`add-left`, `neg`, `of-dvd`, `of-mul-left` all
   need a hypothesis-derived identity this kernel's own conditional
   `ModEq.add_left`/`add_right` cannot supply either) — recognizing that
   re-usability required re-reading turn one's finding, not re-deriving it,
   which this doc does by cross-reference rather than repeating the
   derivation. For nat-coprime, THIS batch is the first to surface the
   `TrustedDeclaration` gap at all; there is no prior finding to connect to,
   and finding it required going one level deeper than turn one had to
   (import-stage source, not just producer-stage source).
6. **The scoping decision not to fix anything.** Unchanged in kind, but now
   applies to a bigger, more precise negative: this batch does not attempt to
   weaken `TrustedDeclaration`'s guard (which would be a straightforward but
   dangerous "delete a check until the decline goes away") or extend
   `propose_modeq_family` with a congruence/rewriting step (which the brief
   explicitly named as future shape-predicate-refinement work, out of scope
   here).

**Net measurement:** batching removed real, mechanical setup cost (build
mechanics eliminated entirely for 25 of 26 facts, adapter-authoring reduced
for 13 of 26), but did not reduce the judgment calls that determine whether a
decline is honest — if anything, batch scale made judgment call 4
*more* load-bearing, because a human had to resist reading "15 identical
failures" as "the tool is broken" and instead trace it to a real, structural
gate one layer below where turn one looked.

## Verification run

```
python3 scripts/validate-facts.py
  776 facts checked, 0 errors (unchanged distribution: open=176, proved=591, ...)
python3 scripts/validate-autogenesis-operations.py
  AUTOGENESIS_OPERATIONS_OK|operations=27|registry=... (unchanged: no operation added)
python3 scripts/validate-producer-contract-declines.py
  PRODUCER_CONTRACT_DECLINES_OK|declines=27|registry=... (26 new + turn one's seed)
python3 scripts/check-autogenesis-holdout-isolation.py
  AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1100|settled=0|references=0|verdict=PASS
python3 scripts/fact-frontier.py --json
  admissible_count: 0, declined_count: 27, selected_fact_id: null,
  outcome: refused-no-admissible-candidate
```

No file under `crates/`, `scripts/`, either producer contract instance,
`artifacts/import-backlog.json`, `artifacts/facts/`, or `python/axeyum/agent/`
was touched by this task.
