# ADR-1295: the header-exemption budget goes to zero, so a fact with no persistent declaration must not be given a header

Date: 2026-08-31
Status: Accepted
Lane: `statement-headers`

Index-summary: `check-settled-fact-statements.py`'s `max_header_exempt` is lowered 67 -> 0, not raised 67 -> 79, by giving 79 settled lean4 statements the `theorem <name> :` header their claimed declaration already renders. 78 are a pure prefix, proved safe by byte-identity against `Kernel::render_lean`; one hand-written paraphrase was replaced by hand and its text preserved. The consequence that binds other lanes: with the budget at zero there is no slot for a headerless statement, so a fact whose subject is a proof-isolated import must resolve its `formal.kernel_theorem`, not acquire a fabricated header.
Index-status: Accepted

## Context

`scripts/check-settled-fact-statements.py` carries a structural bind that no
content hash can express: a `lean4` statement rendered by `Kernel::render_lean`
opens `theorem <name> :`, and that name must be the fact's
`formal.kernel_theorem`. It catches a statement replaced by a *different*
declaration's rendering — a hash says "changed", this says "changed into
something about another declaration".

A statement with no header escapes that bind entirely. The escape is budgeted
(`coverage_floor.max_header_exempt`) so a new one cannot appear quietly, but the
budget only sees a fact once it NAMES a declaration.

On 2026-08-31 lane `resolve-kernel-subjects` annotated 28 facts with the
`formal.kernel_theorem` they had been missing (commit `366f11a91`), taking
`check-trust-closure.py`'s `unresolved` from 90 to 62. Twelve of those carried
headerless statements. They had always been headerless; naming a declaration is
what made them countable. `header_exempt` went 67 -> 79, the L0 gate reddened,
and every push behind it stopped.

**The count rose because the ledger got more honest, not less.** 79 − 12 = 67
exactly, verified by re-deriving both populations.

## Decision

**Lower the budget to 0. Do not raise it.**

Every settled `lean4` fact that names a `formal.kernel_theorem` now carries the
header for that declaration, so the structural bind applies to all of them and
there is no exemption slot left.

The transformation for 78 of the 79 is a **pure prefix**, and what licenses it
is byte-identity, not judgement: each fact's `formal.statement` was already,
byte for byte, the kernel's own `canonical_type` for the declaration it named
(read from `kernel_declaration_projection --release`, 2,729 declarations, fresh
build — a stale prebuilt copy answers about an older environment and would
report a present declaration as absent). Prefixing `<keyword> <name> : ` leaves
the proposition untouched. The keyword follows the declaration's kind
(`theorem`, `def`, `inductive`); `theorem` is not a safe default, because a
definition headed `theorem` claims a proof where there is only a body.

`scripts/header-settled-fact-statements.py` performs exactly that and **refuses
everything else by name**: ABSENT, DIVERGENT, AMBIGUOUS, UNKNOWN-KIND. The
refusals are the safety property, so its nine registered mutations delete
refusals rather than the happy path.

The 79th, `F:complex-admits-no-compatible-order`, the tool refused as DIVERGENT:
its `formal.statement` was a hand-written Lean-ish paraphrase no tool produced
and none could check. It was replaced **by hand**, with the kernel's rendering of
the same declaration, after checking the two agree hypothesis for hypothesis
(le_refl, lt_irrefl, lt_of_le_of_lt, add_le_add, le_congr, sq_nonneg,
zero_lt_one, then False); the superseded text is preserved verbatim in the fact's
`notes`, and the amendment says it was a hand edit rather than letting a content
change wear a mechanical tool's clothes.

## What this binds on other lanes

**A fact whose subject has no persistent declaration must not acquire a header.**
Lane `resolve-kernel-subjects` established that roughly 36 `ml430` facts are
checked through an ephemeral `Kernel::add_declaration` that is created per
receipt and never merged into the environment. There is no declaration to
render, so any header written for one would be a rendering of nothing — the
exact failure the bind exists to catch, arriving through the door marked
"satisfy the gate".

With the budget at zero, a lane that annotates such a fact with a
`formal.kernel_theorem` will red this gate and has exactly two honest moves:
resolve the subject to a declaration that really is in the environment, or leave
`formal.kernel_theorem` unset until `proof-isolated-subjects` decides how those
facts should be expressed. **Raising the budget back is a third move and it is
not available** — that ceiling has been raised once already (30 -> 67), so it has
no fixed direction, and a bump is an act needing its own ADR arguing why a
statement should stop being checkable against the declaration it claims.

## Consequences

* The gate passes at `header_exempt=0`, `floor_header_exempt=0`, `drifted=0`,
  `amendments=84` (5 + 79, one per fact, each with both digests and a reason —
  `--write` refuses to re-pin a changed statement without one, deliberately, so
  that running it after a drift cannot launder the change).
* **ADR-1275's trap was avoided by ordering.** Running `--write` BEFORE the
  headers exist pins the headerless form, which then reads as unamended drift.
  The order here was: dump the rendered types from the kernel, set the
  statements, then pin.
* No reader-facing `statement` changed. Every prose digest is byte-identical, so
  no amendment records one.
* **Proof the gate still fires**, in a `scripts/lane-snapshot.sh` scratch copy,
  never the shared tree: stripping the header back off
  `F:wilson-theorem-over-constructed-integers` takes `header_exempt` 0 -> 1,
  names that fact in the violation, and exits 1. It fires twice, in fact — the
  pin's digest guard catches the same edit independently.
* `gen-safety-matrix.py --check` and `check-absence-claims.py` are red and were
  red on this same tree **before** this change (measured both ways). Neither
  reads statement text: the matrix reads pin MEMBERSHIP, which did not move.
  They belong to other lanes.

## Alternatives rejected

**Raise `max_header_exempt` to 79.** This is the move the failure invites and it
is the one the gate exists to refuse. It would buy a green push by making twelve
statements permanently uncheckable against the declarations they name — and the
ledger IS the product, so a check that cannot fail is worse than no check.

**Fix only the twelve and leave the floor at 67.** Enough to unblock the push,
and it leaves 67 exemption slots for the next annotation lane to land in
quietly. The other 67 needed the same one-line change and the same byte-identity
argument; stopping at the blocking twelve would have been scope discipline
purchased with a standing blind spot.

**Re-dump each fact through `json.dumps(..., indent=2)`.** The obvious way to
write the change, and it reformats every compact array another tool wrote
(`check-fact-depends-derived.py` keeps `depends_on` on one line), turning 79
one-line edits into a 958-line diff in which the edit this lane is accountable
for is invisible. The tool rewrites the one encoded string in place instead, and
refuses if that string is not uniquely locatable in the file.
