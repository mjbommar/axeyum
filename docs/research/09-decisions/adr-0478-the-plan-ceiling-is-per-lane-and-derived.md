# ADR-0478: The PLAN.md ceiling is per-lane and derived, not one number every lane shares

Status: accepted
Index-summary: `check-plan-authority.py`'s flat 52,000-byte ceiling was a shared budget over per-lane files, so no single edit caused the failure and no single edit repaired it — it stood 3.4x over for days. The bound is now a per-lane cap (3,000 bytes, violations named by lane), a total for the genuinely shared `docs/plan/global/`, and an overall ceiling DERIVED from the two, so adding a lane cannot red the gate by itself.
Index-status: accepted

Date: 2026-08-18

Related: [ADR-0465](adr-0465-the-axiom-ledger-is-derived-not-transcribed.md).

## Context

`PLAN.md` is generated from `docs/plan/global/` and `docs/plan/status/`. Those
directories were split per lane because `PLAN.md` was a shared append point —
67 touches in 24 hours on 2026-08-13/14 and four clobbering incidents in one
day. The split worked. The gate that bounds it did not.

`scripts/check-plan-authority.py` bounded the sources with one number, 52,000
bytes. Measured 2026-08-18 they stood at **177,878** — 3.4x over — and the
gate's own comment records the growth: *0 → 54,398 → 98,180 → 233,888 in two
days*. `just check` had therefore been failing on this for days, and every lane
had learned to scroll past it. A gate in that state is worse than no gate: it
teaches people that red is normal.

Two things were wrong, and the second is the interesting one.

**The remediation text pointed at the wrong bytes.** "Move journal/detail to a
result note" names the landed-changes journal. The journal was 25,893 bytes
across 61 rows. The *lane-status* blocks — "what is true now, what is next, what
is blocked" — were **119,818 bytes across 25 lanes**, averaging 4,800 each.
Archiving the entire journal would have recovered a fifth of the overage.

**The budget was shared even though the files were not.** With 25 lanes drawing
on one 52,000-byte total, no individual edit causes the failure and no
individual edit repairs it. A lane that trims its own file by half still sees a
red gate and correctly concludes its work made no difference. That is the same
shared-append-point defect the per-lane split was created to remove, reappearing
one level up — in the *budget* rather than in the file. CLAUDE.md states the
general rule: per-lane state belongs in per-lane paths, never in one file or one
config key that every lane writes. A single shared ceiling is that key.

The flat number also punished growth in lane *count*. It was set when there were
nine lanes ("+744 for nine lane headings and sixteen section markers"). At 26
lanes, 52,000 leaves roughly 800 bytes per lane after `docs/plan/global/` — a
budget no honest status block can meet, so the gate was not merely broken but
unmeetable.

## Decision

The bound is attributable and derived:

- **Per lane:** each `docs/plan/status/<lane>.md` ≤ **3,000 bytes**. A violation
  names the lane and the number, so its owner can fix it and see the gate move.
- **Shared surface:** `docs/plan/global/` ≤ **32,000 bytes** in total, because
  that directory genuinely is shared.
- **Overall:** `32,000 + 3,000 x <lane count>`, derived from the two above.
  Adding a 27th lane cannot red the gate by itself, which the flat number did.

Overflow has somewhere to go: `docs/plan/notes/<lane>.md`, read by neither
`gen-plan.py` nor this gate. A per-lane cap without that directory would just be
an instruction to delete findings.

`scripts/archive-plan-status.py` performs the move mechanically: it splits on
paragraph boundaries rather than bytes, keeps the journal by byte budget rather
than by row count (rows are not comparable — one lane's nine rows run 1,434 /
1,145 / 651 bytes, so "keep the newest three" still blew a 3,000-byte cap),
never deletes, is idempotent, and **skips any file with uncommitted changes** so
it cannot sweep a lane's work-in-progress.

## Consequences

Measured on the first application: sources **146,636 → 59,655** bytes in
`status/`, total **177,878 → 90,897** against a derived ceiling of 110,000, and
`PLAN.md` **171,383 → 87,527** bytes. Every lane is now under its own cap and
`check-plan-authority.py` exits 0.

Nothing was lost: comparing every non-empty line of every status file before and
after gives **0 lost lines** (1,708 → 1,810; the growth is headers and pointers).
That check is the one that matters — a script that "reduced" these files by
deleting would report the same byte numbers.

The cost is one more indirection: the reader of a status block follows a link
for the reasoning. That is the right trade for a file every session loads, and
the reverse of what was happening, where the reasoning was in the file every
session loads and nothing else was.

What this does **not** fix: `PLAN.md` still grows linearly in lane count, at
~3 KB per lane plus the shared sections. At 26 lanes that is ~88 KB in every
session's context. If lane count keeps rising, the next decision is whether
`PLAN.md` should emit every lane's block at all, or only the active ones — a
different question from this one, and deliberately left open.
