# ADR-8000: Python SAT replay binds restored clausal text to source terms

Status: accepted; bounded source/evidence contract adopted, final integration gates remain open
Date: 2026-10-11

## Decision

Expose the existing `UnsatProof::recheck_for_bool_terms` checker through the
Python proof object. Boolean assertion roots may contain the supported pure
Boolean/BV operators. Resolve handles through the arena epoch check, rebuild
term-to-AIG-to-CNF deterministically, require exact DIMACS equality, then verify
the clausal refutation. Never run SAT search to replay an exported certificate.

Add `UnsatProof(dimacs, drat, lrat=None)` for restoring saved text. Construction
only stores data and supplies no accepted verdict. Borrowed text is checked
before copying: each component at most 8 MiB, total at most 16 MiB. Oversized
transport raises an explicit resource-limit ValueError. Proof rejection or CNF
mismatch returns False; malformed text or unsupported source raises AxeyumError;
foreign handles raise EpochError. An absent LRAT remains None and uses the
existing DRAT checker; a present invalid LRAT never falls back to success.

Replay follows the existing unlimited Rust checker contract and exposes no
fictitious timeout. This does not change solver search budgeting. Expanding the
checker to timed replay requires one deadline across encoding and both proof
formats, rather than a Python-only timeout that leaves Rust checking running.

## Trust and coverage

Encoding is the existing explicit trusted bit-blasting/Tseitin reduction, not
an independently proved translation. Reconstructed DIMACS and verified LRAT
bind the refutation to the supplied term query within that trust boundary.
Equivalent queries with identical deterministic encodings need not be rejected;
this method checks the supplied proposition, not provenance of original bytes.
Renaming symbols is not an authentication protocol.

Array/UF/datatype elimination and finite-width LIA certificates remain distinct
routes; this method does not pretend their reductions are pure BV encodings.
Their representative source exports and clausal checks do not establish a
source-to-CNF map or independently checked theory reduction. No new backend,
proof artifact class, or kernel-admission credit is created by this API.

## Validation

Export Boolean and BV certificates, reconstruct frozen proof objects from saved
text, and replay against original terms and independently rebuilt term queries. This Python API accepts arena terms,
not SMT-LIB text; the text parser owns a distinct Script arena.
Changing assertions to a satisfiable query, tampering with hints or CNF, or
removing the empty clause must not succeed. Cover optional LRAT, unsupported
source sorts, foreign handles, malformed text, and both transport caps.
Run a child process which only restores and checks saved artifacts; delete or
replace the producer API in that child so replay cannot quietly use search.
Private mutation of the exact-DIMACS guard must kill exactly one targeted test.
Keep external clausal checks and source-bound replay results separate.

## Adoption and evidence scope

The bounded source/evidence contract is adopted. See the
[current receipts](../../plan/notes/28-wide-real-smtlib-writer.md) and
[completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
The implementation retains unsupported-route declines and source identity;
source-bound replay never substitutes search for checking. Parser/solver gates,
fresh native public-route tests and private source-binding controls supply the
recorded evidence. SAT clausal checking, checked source correspondence, external
proof checking and kernel admission remain separate claims. External reference
checks retain the pinned guard patches documented in
[scripts/patches](../../../scripts/patches/README.md); no unmodified-checker
credit or hole acceptance is inferred. Integer-only `lia_generic` proofs remain
internal-only; scopes/macros and broader portable theory reconstruction remain
explicit open coverage. This adoption does not declare the final workspace or
main integration gates complete.
