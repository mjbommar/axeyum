# Lane notes — the detail behind a status block

One file per lane, mirroring [`../status/`](../status/README.md). Nothing here
is read by `scripts/gen-plan.py` or counted by `scripts/check-plan-authority.py`,
so this is where a finding goes when it is worth keeping but does not belong in
"what is true now, what is next, what is blocked".

## Why this exists

The per-lane ceiling in `check-plan-authority.py` is only fair if there is
somewhere for the overflow to go. Before this directory there was not, so
findings went into the status block — which is how the sources reached **177,878
bytes against a 52,000 ceiling** on 2026-08-18, with the gate red long enough
that every lane had learned to scroll past it.

The bytes were not where the gate's remediation text said. "Move journal/detail
to a result note" points at the landed-changes journal, which was 25,893 bytes
across 61 rows; the lane-status blocks were **119,818 bytes across 25 lanes**.
Archiving the whole journal would have recovered a fifth of the overage. Nobody
wrote an essay on purpose — the status block was simply the only place to write.

## How content gets here

`python3 scripts/archive-plan-status.py --apply`, which splits on paragraph
boundaries, never deletes, is idempotent, and **skips any file with uncommitted
changes** so it cannot take a lane's work-in-progress with it. The first run
moved 86,981 bytes out of 20 lanes with **zero lines lost** (checked by
comparing every non-empty line before and after) and took `PLAN.md` from 171,383
to 87,527 bytes.

Writing here by hand is fine too. Link back to the status file, and keep the
status block pointing here.
