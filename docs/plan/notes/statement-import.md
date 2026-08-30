# Notes: statement-import

Detail moved out of [`../status/statement-import.md`](../status/statement-import.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Design answer:** `TrustedDeclaration`'s whole-stream check (not merely a
reachability closure) is a deliberate anti-smuggling boundary — proven by
`unrelated_axiom_is_rejected` (pre-existing) and a new equivalent test this
lane added for the auxiliary-`Definition`-embeds-a-`Theorem` shape (the real
`Nat.gcd → Nat.mod_lt` mechanism, reproduced at minimal scale purely via
kernel term construction). Admitting a trusted dependency as a bare `Axiom`
(the only kernel declaration kind that skips value-checking) would silently
corrupt the STATEMENT itself — `Nat.gcd`'s real recursive content is what the
`Coprime` facts are about, so axiomatizing it away makes the goal a
statement about an unrelated uninterpreted function. So: essential, given
the current mechanism, EXCEPT for one real artifact — which names are
refused is bounded only by the size of the reviewed
`trusted_substitution`/`nat_order_substitution` allowlist today, not by any
inherent limit. `Nat.mod_lt`/`eq_self` are absent from that allowlist (real,
sizeable engineering, correctly out of scope here); `Quot` (via `minFac`)
can never be exempted by hard rule.

**Empirical confirmation, both directions**, using doc 292's own s5 exports
(pins reverified: mathlib4 `c5ea0035…`, lean4export `a3e35a58…`): reproduced
the `Nat.mod_lt` `TrustedDeclaration` decline on `coprimeAddSelfLeft` exactly,
and produced a genuine successful goal record for `intAddModeqRight` whose
`substituted_theorems` field names 32 independently-reconstructed names
(including `Nat.div_rec_lemma`) — showing int-modeq imports clean not because
its closure avoids trusted declarations, but because every one it reaches is
already covered by the reviewed substitution set. Full detail, evidence, and
the "what remains" list:
[`../../autogenesis/294-statement-only-import-goal-record.md`](../../autogenesis/294-statement-only-import-goal-record.md).

**Verified:** `cargo test -p axeyum-lean-import --lib` (106 passed, 4 ignored
pre-existing), `--test statement_adapter --test statement_goal_record` (8+3
passed). Mutation test by hand: neutering `import_statement_ndjson`'s
`TrustedDeclaration` guard turned exactly 3 tests red across two test files;
restored and reverified clean before every commit. Worked-example fact JSON
validated against `artifacts/ontology/fact.schema.json` with `jsonschema`
(offline, not committed). `cargo clippy -p axeyum-lean-import` could not
complete — pre-existing `clippy::doc_lazy_continuation` failure in
`axeyum-lean-kernel/src/creal/uniform_convergence.rs` from an unrelated WIP
commit (`7e6378b31`) merged in via `main`; out of this lane's scope
(`crates/axeyum-lean-kernel/src/` is off-limits), `cargo build`/`cargo test`
for this crate unaffected.

**Did not touch:** `crates/axeyum-lean-kernel/src/`, `crates/axeyum-cas/`,
`artifacts/facts/`, `artifacts/autogenesis/`, `scripts/`,
`python/axeyum/agent/`, producer contracts, or `lean_pp`/export-direction
code. Did not extend `trusted_substitution`'s allowlist (named as the real
remaining work). Did not weaken `TrustedDeclaration` to force a pass.
