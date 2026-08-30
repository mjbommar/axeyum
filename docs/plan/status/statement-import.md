# Lane: statement-import — statement-only import, ADR-0604 §2

<!-- plan-section: lane-status -->

**`DONE` (2026-08-27).** Brief: build the statement-only import mode ADR-0604
§2 names as the missing segment of "properly use axeyum", and answer whether
doc 292's 15 `Nat.Coprime` `TrustedDeclaration` refusals are essential or an
implementation artifact.

**Finding 0:** the mode itself (`import_statement_ndjson`,
`import_candidate_statement_ndjson`) already existed, added 2026-08-18
(`161adde83`). The missing piece was narrower: a typed bridge from a
completed statement import to the exact `artifacts/facts/` shape, with
`formal.statement` being the KERNEL's own rendering rather than
hand-transcribed surface syntax (which every currently-committed
`F-ml430-nat-coprime-*` fact uses today). Built that bridge:
`crates/axeyum-lean-import/src/statement_goal_record.rs`
(`build_statement_goal_record`) plus `examples/statement_goal_record.rs`
(worked-example CLI, prints a fact-schema-shaped JSON on success or a typed
decline on refusal, never writes under `artifacts/facts/`).

Detail moved to [`../notes/statement-import.md`](../notes/statement-import.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `abb9cb9d9` | `statement_goal_record` module: typed bridge from a completed statement-only import to the ledger-shaped fields (kernel-rendered goal, ADR-0350 content identity, substituted-theorem list). Admits nothing to any kernel. |
| 2026-08-27 | `ec8e0f5ec` | Worked-example CLI + integration tests, including a new `TrustedDeclaration` shape (theorem reached only through an auxiliary admitted `Definition`, mirroring the real `Nat.gcd -> Nat.mod_lt` blocker) and a by-hand mutation test on the fail-closed guard. |
