# 294 — Statement-only import: the goal-record layer, and why `TrustedDeclaration` is (mostly) essential, not an artifact

Date: 2026-08-27
Lane: statement-import

## Task

ADR-0604 §2 names statement-only import as the missing segment of "properly
use axeyum": Lean statement in → contract dispatch → engine → kernel
admission → ledger fact → Lean export. This task's brief asked for that mode
plus a design answer to a specific question: doc 292 measured that 15 of 26
admissible facts (all `Nat.Coprime` family members) fail at IMPORT with
`StatementImportError::TrustedDeclaration`, before any producer runs. Is that
refusal essential, or an artifact of how the importer is built?

## Finding 0: the mode already exists; the missing piece was narrower

`crates/axeyum-lean-import::import_statement_ndjson` (added 2026-08-18,
`161adde83`) already does exactly what ADR-0604 §2 asks: translates a
declaration's TYPE through the fail-closed wire-import path, admits nothing
of its own beyond definition dependencies, and publishes the result as a
`CompletedStatementImport` goal. `import_candidate_statement_ndjson` is its
theorem-composition counterpart. This was confirmed by reading the source,
not assumed — `src/lib.rs:2040-2075` is the whole gate.

What did NOT exist: a typed bridge from a `CompletedStatementImport` to the
exact shape `artifacts/facts/`'s schema needs, with `formal.statement` being
the KERNEL's own rendering (never hand-transcribed surface syntax, which is
what every currently-committed `F-ml430-nat-coprime-*` fact does today —
`formal.language: "lean4-surface"`, statement read from source text). That
bridge is this task's actual code contribution:
`crates/axeyum-lean-import/src/statement_goal_record.rs`
(`build_statement_goal_record`) plus a worked-example CLI,
`examples/statement_goal_record.rs`.

## The design question, answered from the source

**Options on the table** (per the brief): (a) admit nothing at all, register
an open goal; (b) admit dependency types recursively as opaque/axiomatized
carriers; (c) some closures genuinely cannot be imported statement-only, a
typed decline.

**Evidence gathered before deciding:**

1. `import_statement_ndjson` scans `report.declaration_identities` — the
   WHOLE admitted stream, not a reachability closure computed from the goal
   expression — and refuses if ANY entry is `Axiom`/`Theorem`/`Opaque`/
   `Quotient` kind, unless the name is in the reviewed, independently
   reconstructed `trusted_substitution::SUBSTITUTABLE_THEOREMS` allowlist.
   `tests/statement_adapter.rs::unrelated_axiom_is_rejected` already proves
   this empirically: an `Axiom` with NO syntactic connection to the target's
   own Prop still poisons the whole import. This task added
   `a_theorem_reachable_only_through_an_auxiliary_definition_still_poisons_the_stream`
   to `tests/statement_goal_record.rs`, reproducing the SAME behavior for a
   `Theorem` reached only through an admitted auxiliary `Definition`'s
   VALUE — the exact shape of the real `Nat.gcd → Nat.mod_lt` blocker, at
   minimal scale, entirely inside the kernel's own term builder (no s5
   round-trip needed to demonstrate the mechanism).

2. Why is this check whole-stream rather than reachability-scoped? Two
   reasons, both load-bearing, read from the crate's own doc comments and
   confirmed structurally:
   - `Kernel::add_declaration` for `Declaration::Definition`/`Theorem`/
     `Opaque` type-checks the VALUE against the TYPE — always. There is no
     "admit the type, skip the value" declaration kind except `Axiom`
     (`crates/axeyum-lean-kernel/src/env.rs:128-176`: `Axiom` is "an asserted
     constant with no definitional value"; `Opaque`'s value IS "checked, but
     never unfolded" — checked is the operative word). So admitting
     `Nat.gcd` (a `Definition`, itself not directly trusted) at all requires
     the kernel to type-check its VALUE, and that value's well-founded
     recursion compilation embeds `Nat.mod_lt`'s proof BY NAME as a subterm
     — not optionally, not for computation only, but because it is literally
     part of the term being checked. There is no way to admit the real,
     computable `Nat.gcd` without the kernel seeing `Nat.mod_lt`.
   - The alternative — admit `Nat.gcd` (or `Nat.mod_lt`) as a bare `Axiom`
     (type only, no value check) — is mechanically possible but not sound
     for what a statement-only import promises. `Nat.Coprime`'s statement IS
     about the real, computable `gcd`; axiomatizing `gcd` away makes the
     "goal" a statement about an arbitrary function of the right TYPE, not
     the real Mathlib proposition, and any later "proof" of it would not be
     a proof of `Nat.Coprime.add_self_left` at all. Worse,
     `import_candidate_statement_ndjson`'s own doc comment says a producer
     "never scans the imported environment" for the CANDIDATE path, but the
     ordinary statement path makes no such promise — a permissive producer
     over `import_statement_ndjson`'s environment could exploit ANY admitted
     assumption, related or not. Axiomatizing `Nat.gcd` would inject exactly
     that kind of exploitable, un-derived assumption. This is why
     `unrelated_axiom_is_rejected` exists as a control at all: the
     whole-stream check is a deliberate anti-smuggling boundary, not an
     accident of implementation.

**Conclusion: option (b) is unsound for the population that needs it** (a
definition whose real recursive content the goal is actually about), so it
is not a live option here. The only sound path for a `TrustedDeclaration`
name is option (a)'s stronger cousin already built into this crate:
INDEPENDENTLY RECONSTRUCT the exact proof from kernel primitives
(`trusted_substitution`, `nat_order_substitution`) and admit the
self-derived term — nothing is then "trusted from the wire" at all. Where
that reconstruction does not exist (or, for `Quotient`, structurally
CANNOT exist — `is_exempted_trusted_declaration` never exempts `Quotient`,
by hard rule, verified in `src/lib.rs:1940-1956`), the refusal is option (c):
a genuine, typed, honest decline.

**So `TrustedDeclaration` is mostly essential, with one real artifact
identified along the way**: the check is *appropriately* whole-stream (an
anti-smuggling property, not a bug), but *which* names are refused is not
fixed by any inherent limit — it is exactly the size of
`SUBSTITUTABLE_THEOREMS`/`SUBSTITUTABLE_NAT_ORDER_THEOREMS` today. Both
`Nat.mod_lt` and `eq_self` are real, provable, `Nat`-only arithmetic facts
that are NOT yet in that reviewed set — extending it would be legitimate
strengthening (matching the existing pattern precisely: `Nat.div_rec_lemma`
and `Nat.div_rec_fuel_lemma`, needed for `Nat.div`'s own well-founded
recursion, are already there), not weakening the fail-closed gate. This is
real, separate, sizeable engineering (matching or exceeding the existing
28-name `nat_order_substitution` module in scope) and was correctly judged
out of scope for this task — it is the honest "what remains" answer, not a
shortcut taken.

## Empirical confirmation, both directions, from real Mathlib exports

Doc 292's exports were still present on s5
(`/home/mjbommar/lean-import-scale/flywheel-2-exports/*.ndjson`, from the
already-pinned checkout: mathlib4 `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
lean4export `a3e35a584f59b390667db7269cd37fca8575e4bf`, both reverified this
session by `ssh s5 git rev-parse HEAD` in both repos). Pulled two files
directly rather than re-exporting:

**The failing case, reproduced exactly** —
`nat-coprime-add-self-left.ndjson` against
`Axeyum.Autogenesis.Statement.NatCoprimeFamily.coprimeAddSelfLeft`:

```
$ statement_goal_record nat-coprime-add-self-left.ndjson \
    Axeyum.Autogenesis.Statement.NatCoprimeFamily.coprimeAddSelfLeft ...
{
  "decline_display": "statement stream contains trusted declaration \"Nat.mod_lt\" (Theorem)",
  "decline_reason": "TrustedDeclaration { name: \"Nat.mod_lt\", kind: Theorem }",
  "outcome": "declined-at-import",
  ...
}
```
Exit code 1 — matches doc 292's table exactly, independently re-derived.

**A successful worked example** —
`int-add-modeq-right.ndjson` against
`Axeyum.Autogenesis.Statement.Generated.intAddModeqRight` (one of the 11
int-modeq facts doc 292 reported as importing clean): succeeded, and its
`provenance.statement_goal_record.substituted_theorems` field lists **32
names** — `congrArg`, `Eq.symm`, `eq_of_heq`, all of
`SUBSTITUTABLE_NAT_ORDER_THEOREMS` including `Nat.div_rec_lemma`/
`Nat.div_rec_fuel_lemma`. **This is the finding that ties the two families
together**: the int-modeq facts do NOT import clean because their closure
avoids trusted declarations — it does not — they import clean because every
trusted declaration their closure reaches is ALREADY in the reviewed
substitution set. `Nat.Coprime`'s closure reaches exactly two names
(`Nat.mod_lt`, `eq_self`) that are not, plus one (`Quot`, via `minFac`) that
structurally never can be. The two families are the same mechanism at
different coverage.

The full worked-example fact JSON (id
`F:ml430-int-add-modeq-right-worked-example`, NOT committed under
`artifacts/facts/` per the brief) validated cleanly:

```
$ python3 -c 'import json,jsonschema; jsonschema.validate(
    json.load(open("worked-example-fact.json")),
    json.load(open("artifacts/ontology/fact.schema.json")))'
VALID against fact.schema.json
```

## What was built

- `crates/axeyum-lean-import/src/statement_goal_record.rs` —
  `StatementGoalRecord`/`build_statement_goal_record`: reads a completed
  statement import's kernel-rendered goal (`Kernel::render_lean`), its
  ADR-0350 structural content identity, dependency/declaration counts, and
  which trusted names (if any) were exempted via independent reconstruction.
  Admits nothing; it is a pure read of already-checked state (proved by a
  test calling it twice on the same import and asserting equality).
- `crates/axeyum-lean-import/examples/statement_goal_record.rs` — CLI
  demonstrating the round-trip into `artifacts/facts/`'s exact JSON shape,
  on either outcome (success prints a fact-shaped object; decline prints a
  typed refusal and exits nonzero — never forced into a fact shape it did
  not earn).
- `crates/axeyum-lean-import/tests/statement_goal_record.rs` — three
  integration tests: malformed-stream fail-closed (type-level: there is no
  `CompletedStatementImport` to build a record from), valid-statement
  round-trip, and the new auxiliary-definition `TrustedDeclaration` shape.
- Mutation-tested by hand this session (not committed as a permanent
  harness — this crate's existing convention for admission-gate proofs is a
  synthetic-stream integration test, not a scripted mutation suite):
  temporarily replaced `import_statement_ndjson`'s
  `matches!(identity.kind, Axiom | Theorem | Opaque | Quotient)` condition
  with `false && matches!(...)`, confirmed exactly three tests turned red
  (`a_theorem_reachable_only_through_an_auxiliary_definition_still_poisons_the_stream`,
  `proof_bearing_target_is_rejected`, `unrelated_axiom_is_rejected`), then
  restored via `git checkout -- src/lib.rs` (verified clean diff before
  committing anything).

## What remains before a Lean-authored statement can be posed as an axeyum goal end-to-end

1. **Extend `trusted_substitution`/`nat_order_substitution` with `Nat.mod_lt`
   and `eq_self`.** This is the one concrete, sizeable remaining task named
   by this investigation — real mathematical engineering (an independent
   kernel construction of `Nat.mod_lt`'s proof, mirroring Lean 4 core's own,
   likely needing the same well-founded-recursion machinery
   `Nat.div_rec_lemma` already bridges), not a policy change. It would
   unblock 14 of doc 292's 15 nat-coprime facts (every one except
   `coprime_of_lt_minFac`, whose `Quot` blocker is permanent for this
   statement shape).
2. **`coprime_of_lt_minFac`'s `Quot` blocker has no remedy within statement-only
   import as designed** — `Quotient`-kind declarations are never exempted,
   by hard rule (`src/lib.rs`'s `is_exempted_trusted_declaration` doc
   comment: "never `Axiom`, `Opaque`, or `Quotient` — those can never be
   exempted, no matter what `substituted_theorems` claims"). Posing that
   specific fact statement-only would require a differently-worded
   statement that avoids `Nat.minFac`'s `Quot`-reaching machinery, which is
   a mathematical restatement question, not an import-policy one.
3. **This lane did not wire the goal record into contract dispatch or the
   fact ledger** — out of scope per the brief. `build_statement_goal_record`
   plus the example's JSON-wrapping convention is the handoff point for
   whichever lane owns turning an admissible import into a committed
   `artifacts/facts/` entry.

## Verified this session

- `cargo build -p axeyum-lean-import` and `--examples`: clean.
- `cargo test -p axeyum-lean-import --lib`: 106 passed, 0 failed, 4 ignored
  (unrelated, pre-existing `#[ignore]`s).
- `cargo test -p axeyum-lean-import --test statement_adapter --test
  statement_goal_record`: 8 + 3 passed, 0 failed.
- Mutation test above: exactly 3 of the combined 11 tests failed with the
  guard neutered; all 11 pass with it restored (confirmed via `git diff`
  showing an empty `src/lib.rs` diff before every commit in this task).
- `python3 -m jsonschema`-style validation of the worked-example fact JSON
  against `artifacts/ontology/fact.schema.json`: valid.
- `git status --porcelain -- artifacts/facts/`: empty throughout — no fact
  was written.
- `cargo clippy -p axeyum-lean-import --all-targets --all-features -- -D
  warnings`: **could not run to completion** — `axeyum-lean-kernel`
  (a dependency this lane may not edit) currently fails
  `clippy::doc_lazy_continuation` in `src/creal/uniform_convergence.rs`,
  landed by an unrelated WIP commit (`7e6378b31`, "power series", not
  produced by this lane) merged in via `main`. Reported here rather than
  worked around; `cargo build`/`cargo test` for this crate are unaffected
  since that lint is clippy-only.

## Did not touch

`crates/axeyum-lean-kernel/src/`, `crates/axeyum-cas/`, `artifacts/facts/`,
`artifacts/autogenesis/`, `scripts/`, `python/axeyum/agent/`, producer
contracts (ADR-0602), or `lean_pp`/export-direction code — all out of scope
per the brief. Did not extend `trusted_substitution`'s allowlist (named
above as the real remaining work, correctly sized as its own task). Did not
weaken `TrustedDeclaration`'s guard to force any case to pass.
