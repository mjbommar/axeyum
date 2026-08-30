# Lane 340 — vocabulary drift (S4)

<!-- plan-section: lane-status -->

## Status

IN PROGRESS (early commit, incomplete).

`python3 scripts/check-dispatchable-frontier.py` fails S4: 9 settled `ml430`
mirrors have no row in `artifacts/autogenesis/mathlib-statable-vocabulary-v1.json`.

Established so far:

- The artifact is NOT a per-row boolean `settled` flag, despite the gate
  docstring's wording. It is `{"bridge": [const], "settled": [{source_name,
  constants}]}`. Membership of `settled` is what promotes a row's constants
  into `bridge`.
- The 9 missing rows are all `proved`, all `Nat.clog_*` / `Nat.log_*`. Zero
  rows are listed-but-not-settled, so nothing needs a *corrected* flag —
  the drift is entirely one-directional.
- The pinned statement inventory the `constants` are derived from
  (`mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson`,
  sha256 `4285e551…`) IS reachable on this host under
  `/nas3/data/axeyum/autogenesis/sources/`, so a generator is feasible.

Next: confirm the whole artifact is derivable, then generate it.
