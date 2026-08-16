# Lane: ledger-integrity — a checker that cannot fail is not a checker

<!-- plan-section: lane-status -->

**Landed the claim dashboard's gate, and the type check whose absence hid the
bug** (`WIP`, ledger-integrity, 2026-08-16). Strand item
[`04-gates-and-truth.md`](../../refactor-2026-08/04-gates-and-truth.md) T1
("every gate reports its own scope"), and finding 8's shape one level down: the
defect was not a wrong number, it was three layers each trusting the one below.

**What was actually wrong — three defects, not one.**

1. `artifacts/claims/rado/rado-r4-a6-b5-frontier/claim.json` wrote `would_settle`
   as a one-element **list**; `claim.schema.json` declares `"type": "string"`.
2. `validate-claims.py` checked which frontier keys were *present* and never what
   they *held*, so the ledger reported **104 claims, 0 errors** over a claim that
   violated its own schema. The file already carries a `schema_drift()` check
   whose comment says "a schema no code reads is decoration" — that argument
   applied to field names but had never been extended to their types.
3. `gen-claims-dashboard.py` therefore crashed on `fr['would_settle'].strip()`,
   and **was wired into no gate at all** — not `check.sh`, not the `justfile`.

So the committed `DASHBOARD.md`, headed *"Auto-generated. Do not edit by hand"*,
reported **38 claims across 1 family** against an actual **104 across 3**, and
listed the campaign's flagship result `R_4(5(x-y)=4z)` as `open` at `> 740` when
the ledger had it `computed` at exactly **741**. Nobody edited it wrongly. Nobody
ran it.

**Both negative controls exercised, not asserted.**

- The new type check was run *before* the data was fixed and rejected the real
  claim with exit 1 — `frontier.would_settle must be a string, got list`.
- `--check` was run against a deliberately dirtied `DASHBOARD.md` and exited 1,
  then against the restored file and exited 0.

**Gated in both aggregates, deliberately.** `--check` joins `generated-trackers`
in the `justfile` (beside `gen-plan.py` and `gen-adr-index.py`, the other two
generated views) and `check.sh` gains `claims-validate` and `claims-dashboard`.
The claim ledger's structural gates previously ran only from `just claims`, which
is not part of `just check`; both are seconds long and need nothing external, so
the no-`just` fallback had no reason to be blind to them. The certificate pass
stays out of both — it needs the gitignored `drat-trim` clone.

**Next for this lane.** The larger half of finding 8: **40 of 162 checker runs
across 36 settled facts exit 0 on completion alone**, including
`nat_axiom_inventory`, which prints its number and exits 0 whatever it is — so
`axiom_footprint: []` on 31 kernel-lean facts, this project's headline
axiom-freedom metric, is asserted by nothing. Re-measure the count first
(`b94b56425` already fixed one example), then make each checker's exit status
depend on its finding, one exercised negative control per fix.

**Returned `main` to green: PLAN.md 225,019 -> 47,409 bytes** (`WIP`,
ledger-integrity, 2026-08-16). `just check` could not pass — `plan-authority`
failed at 233,888 bytes against a 52,000 ceiling, and had failed since
`69d32216b`, the commit that split PLAN.md into per-lane sources. The ceiling and
that design could not both stand: `docs/plan/global/` alone is 43,348 bytes of
the budget, so even a 500-byte cap across 43 lanes would not have fit. Resolved
by taking CLAUDE.md's framing literally — PLAN.md is an **active work queue** —
and archiving finished and cut-off lanes to
[`docs/plan/archive/`](../archive/README.md), which is not a PLAN source. Nothing
is lost: every file moves verbatim by `git mv`, 26 of the 43 duplicate a fuller
committed diary, and the archive README indexes all 43 with the next action each
lane left behind, so the queue keeps its work items. Restoring a lane is a `git
mv` back plus `gen-plan.py`.

<!-- plan-section: landed-changes -->

| 2026-08-16 | `pending` | Claim dashboard regenerated and gated: `gen-claims-dashboard.py --check` added and wired into `generated-trackers` (justfile) and `check.sh`; `validate-claims.py` now type-checks `frontier.known` / `would_settle` / `attack_notes` against `claim.schema.json`; the one schema-violating claim normalised. DASHBOARD.md goes from a stale 38 claims / 1 family / 81 rows to the actual 104 / 3 / 266. Both negative controls exercised. |
