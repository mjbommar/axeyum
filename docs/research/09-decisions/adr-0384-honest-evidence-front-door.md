# ADR-0384: An honest evidence front door — three-valued checking, bounded proof production, retained subjects

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

Three defects in `crates/axeyum-solver/src/evidence.rs`, found during the
2026-08-12 Rado campaign (findings A3, A4, A5 in
[the findings register](../../plan/findings-register-2026-08-12.md)),
shared one theme: the evidence front door could *look* checked, bounded,
or checkable without being so.

1. **A3 — a green gate over nothing.** `Evidence::check` returned
   `Ok(true)` for `Evidence::Unsat(None)` and `Evidence::Unknown(_)`. A
   bare, uncertified verdict "passed the check" because there was nothing
   to check — exactly the silently-inert-gate failure class CLAUDE.md
   documents, sitting in the product's own API.
2. **A4 — an unbounded second search.** `produce_qf_bv_evidence` timed the
   *decision* with `config.timeout` but ran *proof production* — a second,
   independent SAT search that on a hard `unsat` costs as much as the
   decision or more — with no deadline at all.
3. **A5 — a report without a subject.** `produce_evidence_smtlib` parsed
   the input internally and dropped the arena, so a consumer holding only
   the report could not re-check it without re-parsing the text and hoping
   the second parse assigned the same `SymbolId`s.

## Decision

1. **Three-valued checking.** `Evidence::check_outcome` returns an
   `EvidenceCheck`: `Verified` (a certificate was present and re-derived
   this run), `NothingToCheck(NoCheckReason)` (bare `unsat`, `unknown`, or
   a `sat` model against an empty subject), or `Failed` (a certificate was
   present and did not hold up). `Evidence::check` remains as the boolean
   collapse — `Verified` and only `Verified` is `true` — so every existing
   `if evidence.check(..)? { … }` gate becomes sound rather than vacuous.
   "Nothing to check" is never a pass.
2. **Deadline threading.** `produce_qf_bv_evidence` fixes one deadline
   from `config.timeout` at entry; proof production spends whatever the
   decision left and no more. An expired deadline still returns the
   *decided* verdict as an honest bare `Unsat(None)` with `SatRefutation`
   recorded uncertified — losing a proof must not lose a verdict, and it
   is never an `Err` or a downgraded `Unknown`.
3. **Retained subjects.** `produce_evidence_smtlib_with_script` returns
   `EvidenceWithScript` — the report together with the parsed `Script` it
   was produced from — whose `check_outcome` re-validates against the
   *same* arena. `produce_evidence_smtlib` delegates to it and keeps its
   signature. String-gated scripts, whose flat view is not a faithful
   checking subject (ADR-0061), report `NothingToCheck` rather than
   pretending.

## Consequences

Callers that need to distinguish "uncertified but sound" from "certificate
failed" use `check_outcome`; boolean `check` callers get strictly fewer
false positives. Uncertified verdicts are now visible as such at every
call site, which is what the claim-ledger epistemics (ADR-0380) require of
the producing system. Unit tests cover each face: bare-`unsat`/`unknown`
never verify, a tampered certificate `Fail`s rather than reading as
unchecked, an expired deadline yields a decided uncertified `unsat`, an
ample one still produces the proof, and the with-script route re-checks
without re-parsing.
