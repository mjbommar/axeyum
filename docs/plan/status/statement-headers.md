# Lane: statement-headers — the header-exemption budget goes to zero

<!-- plan-section: lane-status -->

**Done (`statement-headers`, 2026-08-31).** `check-settled-fact-statements.py`
was failing at `header_exempt=79` against `floor_header_exempt=67` and blocking
every push. It now **passes at 0 against a floor of 0**. The ceiling was
**lowered 67 -> 0**, not raised. [ADR-1295](../../research/09-decisions/adr-1295-the-header-exemption-budget-goes-to-zero.md).

```
SETTLED_FACT_STATEMENTS|settled=2271|pinned=2271|unpinned=0|identity_bound=2076
  |header_exempt=0|drifted=0|amendments=84|retracted=0
  |floor_unpinned=0|floor_identity=2076|floor_header_exempt=0
SETTLED_FACT_STATEMENTS|PASS
```

## The brief's premise, verified rather than inherited

`366f11a91` (lane `resolve-kernel-subjects`) added `formal.kernel_theorem` to
**28** facts — counted from the diff, `grep -c '^+.*"kernel_theorem"'`. Exactly
**12** of those 28 carry a headerless `formal.statement`, and the brief's list of
twelve is correct, name for name. 79 − 12 = **67**, the standing floor. So the
count rose because the ledger got more honest: those statements had always been
headerless, and naming a declaration is what made them countable.

## What was done, and why 79 rather than 12

All twelve were checked against the kernel, not against source text: a fresh
`--release` `kernel_declaration_projection` (2,729 declarations) has every one of
them present, `theorem`-kind, with exactly one `canonical_type` across all
preludes — and each fact's `formal.statement` was **byte-for-byte that canonical
type**. So the fix is a pure prefix, and byte-identity is what proves the
proposition is untouched.

The same held for **78 of the 79**, so fixing only the blocking twelve would have
left 67 exemption slots for the next annotation lane to land in quietly. All 79
were headed instead.

| bucket | count | what happened |
| --- | --- | --- |
| `EXACT`, theorem-kind | 71 | `theorem <name> : ` prefixed |
| `EXACT`, definition-kind | 6 | `def <name> : ` — the keyword follows the KIND; `theorem` on a definition would claim a proof where there is only a body |
| `EXACT`, inductive-kind | 1 | `inductive <name> : ` (`CReal.UniformConvergesOn`) |
| `DIVERGENT` | 1 | `F:complex-admits-no-compatible-order`, replaced BY HAND — see below |
| `ABSENT` (proof-isolated import) | **0** | none of the 79 is in that class |

**No fact was left for the `proof-isolated-subjects` lane.** The ~36 `ml430`
facts admitted through an ephemeral kernel do not appear here at all, because
they never had a `formal.kernel_theorem` to make them countable. Checked from the
projection with a positive control, not from a grep of one source file.

## The one that was not mechanical

`scripts/header-settled-fact-statements.py` **refused**
`F:complex-admits-no-compatible-order` as `DIVERGENT`: its `formal.statement` was
a hand-written Lean-ish paraphrase that no tool produced and none could check
against the declaration. Replaced by hand with `render_lean`'s rendering of the
same declaration, after checking the two agree hypothesis for hypothesis
(le_refl, lt_irrefl, lt_of_le_of_lt, add_le_add, le_congr, sq_nonneg,
zero_lt_one, then False). The superseded text is preserved verbatim in the fact's
`notes`, and its amendment says it was a hand edit — a content change must not
wear a mechanical tool's clothes.

## Amendment mechanism

`artifacts/ontology/settled-fact-statement-pins.json` `amendments`, one row per
fact: `fact_id`, `date`, `from_sha256`, `to_sha256`, `reason`, `recorded_by`.
5 -> **84**. No prose digests, because no reader-facing `statement` changed —
every one is byte-identical. `--write` refuses to re-pin a changed statement
without an amendment, deliberately, so that running it after a drift cannot
launder the change.

**ADR-1275's trap was avoided by ordering**: dump the rendered types from the
kernel, set the statements, THEN `--write`. Pinning first would have pinned the
headerless form, which then reads as unamended drift.

## Proof the gate still fires

In a `scripts/lane-snapshot.sh` scratch copy, never the shared tree. Stripping
the header back off `F:wilson-theorem-over-constructed-integers`:

```
baseline  header_exempt=0  PASS                              exit 0
mutant    header_exempt=1  VIOLATION ... above the allowance of 0:
                           F:wilson-theorem-over-constructed-integers   exit 1
```

It fires twice, in fact — the pin's digest guard catches the same edit
independently, which is the intended overlap.

## Two gates red, and they were red before this lane

`gen-safety-matrix.py --check` (stale generated artifact) and
`check-absence-claims.py` (BARE declaration mentions in `rat_prelude`) both exit
1 — **measured on this same tree with this lane's changes stashed, and they were
red then too.** Neither reads statement text: the safety matrix reads pin
MEMBERSHIP, which did not move (all 2,271 facts were already pinned).
Regenerating the matrix here would sweep ~2,000 lines of other lanes' state, so
it is left to its owner.

<!-- plan-section: landed-changes -->

| 2026-08-31 | | `scripts/header-settled-fact-statements.py` (`--check`/`--apply`) — heads a settled statement with the declaration it already renders, byte-identity licensed; refuses ABSENT / DIVERGENT / AMBIGUOUS / UNKNOWN-KIND |
| 2026-08-31 | | `scripts/tests/test_header_settled_fact_statements.py` — 14 controls, 9 mutations registered in `mutation_controls.py`, each killing exactly one |
| 2026-08-31 | | 79 settled `formal.statement`s headed, 79 amendments recorded, `coverage_floor.max_header_exempt` **lowered 67 -> 0**; `check-settled-fact-statements.py` PASS |
| 2026-08-31 | | [ADR-1295](../../research/09-decisions/adr-1295-the-header-exemption-budget-goes-to-zero.md) — with the budget at zero, a fact whose subject is a proof-isolated import must resolve its subject or leave `kernel_theorem` unset; it must not acquire a fabricated header |
