# ADR-1005: Extraction-resolved fact subjects verified against the live kernel and bound; two were wrong, three previously-passing guards now correctly reject

Status: accepted
Date: 2026-08-31
Index-summary: 660 kernel-lean settled facts whose subject came from
`theorem_of`'s dotted-name extraction (`scripts/check-fact-depends-derived.py`)
were independently re-verified against `kernel_declaration_projection` and
bound to `formal.kernel_theorem` — 658 confirmed correct, 1 corrected
(`F:nat-bitwise-bit`: extraction found `Nat.bitwise_bit`, no such
declaration; the real subject is `Nat.bitwise_bit'`), 1 marked the deliberate
`null` (`F:farkas-refutation-over-constructed-reals`: a package-level result,
previously silently resolved to the Definition `CReal.Equiv`). The two
corrections tripped `validate-facts.py` and `check-trust-closure.py`, which
had both been passing on the wrong subject for these two facts; the
`Index-status` records those as findings, not regressions.
Index-status: accepted; 3 downstream gates left correctly red (see below)

## Context

A five-risk audit (referenced by the dispatching brief as ADR-1000 /
`docs/research/11-design-review/2026-08-31-five-risk-coverage-audit.md`,
neither present in this worktree at dispatch time — pushes from other lanes
lag this worktree's `origin/main`) measured that the trust-closure gate's
four guards, and the dependency-derivation guard `validate-facts.py` runs,
both identify a kernel-route fact's subject via `theorem_of`
(`scripts/check-fact-depends-derived.py`). That function resolves in two
tiers: `formal.kernel_theorem` when the key is present (authoritative,
including a deliberate `null` meaning "not about exactly one theorem"), else
the first dotted theorem-shaped name matched anywhere in the fact's own
`checker_command` text. The audit measured 1,320 authoritative, 664
extraction-resolved, 185 with no subject, of 2,169 settled facts — and the
function's own docstring already names two failures: `Int.sub` extracted for
`F:cassini-identity-over-constructed-integers` (the real subject,
`Int.fib_cassini`, appears only as a bare CLI argument, never as a dotted
name) and `Complex.mul_assoc` extracted identically for two unrelated facts
(since resolved: `F:complex-ring-constructed-axiom-free` now carries
`kernel_theorem: null`).

The risk: a wrong subject makes all four trust-closure guards, and the
dependency-derivation guard, evaluate the wrong declaration's closure and
report a clean result about something else entirely — silently, because none
of those guards can distinguish "this fact has no problems" from "this fact
was never actually checked."

## What was verified, and how

Re-measured the split in this tree: identical to the audit (1,320 / 664 /
185 over all settled facts). Restricted to `proof_route == kernel-lean`
(2,087 settled — the population both `check-fact-depends-derived.py` and
`check-trust-closure.py` actually enforce; `KERNEL_ROUTES = {"kernel-lean"}`
in both): 1,306 / 660 / 121. The remaining 4 extraction-resolved facts are
`proof_route == imported-kernel-lean` — real Lean4export/Mathlib identifiers
(`Bool.and_comm`, `List.nil_append`, `Nat.le_refl`, `Nat.le_succ`) checked
through a different route entirely (`axeyum-lean-import`, not
`axeyum-lean-kernel`); `kernel_declaration_projection` cannot verify them
(it projects only `axeyum-lean-kernel`'s own preludes) and neither gate
consults them. Left unbound, explicitly out of scope rather than silently
skipped.

Built `crates/axeyum-lean-kernel/examples/kernel_declaration_projection`
once (`--release`; it builds `creal`/`complex`/`cpoint` and recurses past a
debug stack) to get every declaration's kind and canonical `Kernel::render_lean`
type — 2,542 declarations. Every one of the 660 kernel-lean extracted
subjects was checked two ways, never by trusting the extraction itself:

1. **Exact type match.** When `formal.statement` (language `lean4`) or
   `formal.kernel_statement` is the kernel-rendered type verbatim (allowing
   for the `"theorem <Name> : "` header some facts carry and others don't),
   compare it against the projection's canonical type for the extracted
   name. 449 facts confirmed this way — the strongest evidence available,
   since it independently re-derives the exact same string the fact already
   asserts.
2. **Anchored name-filter match**, for the remainder (mostly `lean4-surface`
   ml430-mirror facts, whose `formal.statement` is informal math notation
   with no embeddable kernel type). Re-derived which `checker_command` and
   which regex span `theorem_of` actually matched, then required the
   character immediately following the matched name to be a hard boundary
   (a literal `[[:space:]]` grep marker, a closing quote, a shell redirect,
   end-of-string) rather than a space-then-identifier or space-then-`(` —
   the shape that means the name is the HEAD of an applied term embedded in
   a larger rendered type, which is exactly the cassini failure mode. 209
   facts confirmed this way.

Every one of the 658 was independently confirmed to be a
`Declaration::Theorem` in the projection (never a `Definition`, `Axiom`, or
other kind) as part of both checks.

## What was wrong

- **`F:nat-bitwise-bit`** extracted `Nat.bitwise_bit` (no apostrophe) — no
  declaration by that name exists; the extraction regex deliberately
  excludes apostrophes (a checker command's closing quote would otherwise
  absorb into the name). The real subject, `Nat.bitwise_bit'`, was already
  independently recorded in `evidence[].kernel_declaration` on both its
  evidence rows (the tier `check-trust-closure.py`'s `subject_of` checks
  before falling back to extraction, but `check-fact-depends-derived.py`'s
  `theorem_of` does not have that tier) — and its rendered type matches
  `formal.statement` byte-for-byte. Bound to the corrected name.
- **`F:farkas-refutation-over-constructed-reals`** extracted `CReal.Equiv` —
  a real declaration, but a `Definition`, not a theorem. Reading the fact:
  it measures a Farkas-refutation reconstruction pipeline across 5 fixtures,
  a package-level claim about axiom-footprint measurement, not one theorem
  — exactly the documented deliberate-`null` shape ("this fact is not about
  exactly one kernel theorem"). Bound `formal.kernel_theorem: null`.

No other wrong extractions found among the 660. 10 extracted names collide
across 2 facts each — every one a native fact paired with its `ml430-*`
mirror asserting the same underlying theorem, which is the intended shape
(a mirror fact's whole content is "this Mathlib-shaped statement corresponds
to our theorem X"), not contamination. (The audit measured 6 collisions
across 12 facts; the ledger grew between the audit and this lane.)

## Consequence: three guards started rejecting, correctly

Binding the two corrections caused `validate-facts.py` and
`check-trust-closure.py` to fail where they previously passed; binding the
37 legitimately-headerless facts among the 658 caused
`check-settled-fact-statements.py` to fail independently. None of the three
were repaired — CLAUDE.md's own standing rule applies directly: *a guard
that starts rejecting after a correct binding is a finding that it was
previously passing on the wrong theorem, and is reported rather than
repaired away.* This lane's declared scope (`artifacts/facts/`,
`formal.kernel_theorem` only) also structurally excludes touching any of
the three files below.

1. **`validate-facts.py`** (`scripts/check-fact-depends-derived.py`): exit
   1. Before this ADR, `F:nat-bitwise-bit` resolved to nothing (the
      extracted name is absent from the theorem dependency graph) and was
      silently excluded from this guard's enforced population — not a
      pass, an absence the guard cannot distinguish from a pass. Now that
      it resolves correctly, the guard can see its real proof term's
      dependency closure and reports 4 real, previously-invisible missing
      `depends_on` edges: `Nat.le_add_right`, `Nat.le_trans`,
      `Nat.one_mul`, `Nat.succ_mul`. Adding those edges is out of this
      lane's scope (`depends_on` is not `formal.kernel_theorem`).
2. **`check-trust-closure.py`**: exit 1, `guard_population`'s
   `COVERAGE-BELOW-FLOOR`. Measured before/after with the SAME
   `kernel_declaration_projection` snapshot pinned via `--projection`, so
   only the fact content varies: before, `subjects=2000 unresolved=87`,
   `failures=0`, every guard 0 hits; after, `subjects=1999 unresolved=88`,
   `population: hits=1` (`0.9578` against a recorded floor of `0.9583`), the
   other three guards (`self_occurrence`, `alias_occurrence`,
   `forbidden_trust`) unchanged at 0 hits both times. Mechanism:
   `collect_subjects` does not filter by declaration kind, so
   `F:farkas-refutation-over-constructed-reals` was silently counted as
   RESOLVED against `CReal.Equiv` before this ADR — fed into the
   self/alias/forbidden-trust closure guards under a subject that was
   never its real one, and counted toward the population ratio the floor
   in `artifacts/trust-closure/population.json` was calibrated against.
   Correctly marking it `null` removes it from the resolved population,
   which is the guard doing its job — and proves the floor (`min_ratio:
   0.9583`) was resting on at least one wrongly-resolved subject. `--write`
   would recompute the floor but this lane did not run it: raising a floor
   is a deliberate maintainer decision, not a byproduct of a metadata fix.
3. **`check-settled-fact-statements.py`**: exit 1. `max_header_exempt` is
   pinned at 30 in `artifacts/ontology/settled-fact-statement-pins.json`'s
   `coverage_floor`, and is designed as a ratchet that only auto-tightens
   (`--write` takes `min(old, new)`). Binding 37 additional bare-type
   `lean4` facts (no `theorem NAME :` header — the identical shape as the
   30 pre-existing exemptions, e.g.
   `F:cassini-identity-over-constructed-integers`) pushed the count to 67.
   This is not new risk introduced by this ADR — every one of the 37 was
   independently type-verified against the live kernel by the exact-match
   check above, stronger evidence than the header check itself provides —
   but the floor needs a maintainer to review and deliberately raise it;
   this lane's scope does not include `artifacts/ontology/`.

## What this does not claim

The 4 imported-kernel-lean extraction-resolved facts are unverified by this
ADR, honestly — not "probably fine." `kernel_declaration_projection`
projects only `axeyum-lean-kernel`'s own preludes; these facts' subjects are
Lean4export-imported Mathlib identifiers in a different formal system this
lane's tooling cannot check. The 121 kernel-lean facts with no extractable
subject at all are untouched; this ADR only converts facts extraction
*could* resolve, verified, never facts it could not resolve at all.

`artifacts/autogenesis/` was not touched —
`scripts/check-autogenesis-holdout-isolation.py` reports PASS
(`held_out=146`) identically before and after, and `git status --porcelain`
is empty for that path throughout.

## Method note for the next lane touching subject resolution

The distinguishing signal between "extraction happens to be right" and
"extraction is structurally guaranteed right here" is whether the matched
name sits at a hard text boundary (an anchored grep/awk name filter) versus
being embedded as the head of an applied term inside a larger rendered type
string (a `-F`/fixed-string grep of the whole type, as cassini's checker
command was). The first is safe by construction; the second is exactly how
`Int.sub` beat `Int.fib_cassini` to the match. When auditing a checker
command for what it actually pins down, check the character immediately
after the candidate name, not just whether the name appears.
