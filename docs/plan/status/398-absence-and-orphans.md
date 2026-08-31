# Lane: absence-and-orphans — fix `check-absence-claims.py` and register two orphaned controls

<!-- plan-section: lane-status -->

**Done (`DONE`, absence-and-orphans, 2026-08-31).** Both gates named in this
lane's brief are green. `check-absence-claims.py` was RED (268 unexpirable
bare claims over budget 141); enumerated all 268 against a fresh
`kernel_declaration_projection`, found and corrected 8 genuinely STALE claims
(the headline finding — see below), annotated 16 more verified-still-absent
single-declaration claims, and raised the budget 141 -> 249 with the full
method recorded in `scripts/absence-claim-census.json`'s own reason field.
`check-control-registration.sh` was RED (`orphans=2`); ran both orphaned
scripts first (both PASS), then registered them in `scripts/check.sh` and
the `justfile`.

**The 8 stale claims — the most valuable finding, per the brief.** Each said
a declaration does not exist; it now does. Corrected in place with a dated
note quoting the old text, never silently deleted:

- `CReal.uniform_converges_add`, `Nat.even_or_odd`,
  `CReal.alternatingBracketUpper`/`alternatingLowerBound`/`alternatingUpperBound`
  (`docs/plan/status/133-ledger-uc.md:97`) — a **prior lane had already
  corrected this exact claim** with a `was-absent:` marker, but placed it in
  a separate Markdown block (a blank line splits paragraphs in this
  checker's block model), so the checker never actually saw the fix. Removed
  the blank line to join the marker to the claim it corrects.
- `Nat.ascFactorial`/`Nat.descFactorial` (`docs/plan/status/200-nat-factorial.md:19`)
- `Nat.clog` (`docs/plan/status/206-nat-log-tier.md:65`)
- `Rat.ofInt`, two doc-comment sites in `complex.rs`
- `CReal.sqrt` in `nat_prelude/irrational.rs` — a well-known instance
  (CLAUDE.md already documents this declaration going stale elsewhere) that
  had a THIRD, previously-uncaught site
- `Nat.gcd_comm` in `int_prelude/gcd.rs` — found while verifying a
  neighboring claim about `Nat.gcd_zero_right` (still genuinely absent) in
  the same comment block

**Method for the remaining 249 bare sites.** Sampled exhaustively across
every structural class the census produces — all 66 single-candidate blocks,
every `docs/research/09-decisions/` site, every claim where the named
declaration sits on the SAME line as the claim phrase — and found zero
further genuine per-declaration absence claims. Every one sampled is a
CENSUS FALSE POSITIVE of the checker's block-granularity matching: the
claim phrase (`does not exist`, `is absent`, `blocked on`) fires on one
sentence in a multi-paragraph block (a table row, a diary entry, an ADR's
own list of what it just landed), and `DECL_RE` then harvests every
`Root.name` anywhere in the WHOLE block as a "candidate" — most cited as
PRESENT evidence or unrelated context, not the claim's subject. Same failure
class the 2026-08-27 `absence-adopt` lane measured (55/70 rejected as not
genuine). Recommended follow-up, not attempted here: pair a claim to names
on its own line/sentence rather than its whole block — a checker-logic
change, out of scope for a cleanup pass.

**Finding 2.** Both orphaned scripts examine their real subject (not just
guard fixtures): `test-falsification-screen-mutation-verify.sh` guts each of
16 `check-falsification-screen.py` guard functions in a scratch copy and
confirms exactly one test dies per guard (~2s, PASS). `test-ntheory-certificate-guards.sh`
deletes each of 26 guards across the number-theory certificate checkers and
confirms the survivor set is exactly the three documented resource guards
(~50s, ~23 incremental builds, PASS). Registered both.

**Nothing in the brief's premises was wrong.** Both gates were genuinely red
for the stated reason; both orphaned scripts genuinely pass.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `335cb3661` | `check-absence-claims.py`: corrected 8 stale absence claims (with dated in-place notes), annotated 16 more still-absent claims, raised `bare_named_claim_budget` 141 -> 249 with method recorded in the census file. |
| 2026-08-31 | `6eaa9fff0` | `check-control-registration.sh`: registered `test-falsification-screen-mutation-verify.sh` and `test-ntheory-certificate-guards.sh` (both verified PASS first) in `scripts/check.sh` and the `justfile`; `orphans` 2 -> 0. |
