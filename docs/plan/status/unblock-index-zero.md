# Lane: unblock-index-zero

Status: in progress (started 2026-08-31)

## Goal

Fill cycle **index 0** for draw 16. ADR-1220 measured that index 0 is the
binding slot (index 3 now has three viable candidates) and recommended
`Mathlib.Computability.Primrec.Basic` (11 rows, 0 boundary rows, no churn, no
stale review), needing `Nat.Primrec` and `Nat.casesOn` — `Nat.unpaired` landed
in ADR-1220.

Construction only (ADR-0653). No draw is authored.

## Open caveat

`Nat.Primrec` is an inductive `Prop`, so it admits **no evaluation test**. The
substitute safeguard has to be designed and stated explicitly.

## Landed changes

(none yet)
