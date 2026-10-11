# ADR-3400: Statute time template carries calendar and applicability inputs

Status: proposed
Date: 2026-10-11

The first statute template models positive day periods under the 2025 edition
of Minnesota §645.15. §§645.13 (successive-week publication) and 645.14 (month
periods) are explicit exclusions. The caller must supply applicability and both
exclusion facts, plus a sourced holiday classification complete within an
inclusive date window. Missing facts are never treated as false. §645.44 subd.5
contains branch-specific holiday distinctions; this template does not guess them.

Nominal endpoint is start plus a positive day count; weekend/holiday endpoints
roll forward to the first admitted date. This is a stated modeling interpretation
of omitting a last day, not an independent legal applicability finding. Dates
outside calendar coverage or Gregorian range and exhausted rollover budgets
decline with no returned deadline. Periods cap at 36600 days; rollover caps at
366 days (default 32). Output records nominal date, skipped endpoints and source.

Source edition/text identity/retrieval date are pinned separately. Retrieval is
not an effective date. Initial outcomes are computed, not proof-certified;
independent reference and native constraints now validate bounded cases.
Verification reconstructs three obligations without calling the producer and
records verdict, check status, reason, serialized source and evidence separately.
checked-native requires verified evidence and certified reductions for every
obligation; otherwise decided agreement is only validated. Wrong decided verdicts
reject; unknown/missing coverage stays inconclusive. Checked UNSAT routes remain
required before proof credit.
The new statute-template manifest is outside the seven example-pack validator
until its unknown effective-interval evidence can be represented explicitly.
No fabricated from date is introduced merely to satisfy the current schema.
