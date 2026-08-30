# Lane: parity-finish — closing the parity cluster's three named blockers

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this dispatch`, parity-finish, 2026-08-30).**
All three facts handed off by `nat-parity-div` (see
`docs/plan/status/369-nat-parity-div.md`) are closed. All three sizings from
the handoff were WRONG in the optimistic direction (the two "no missing
lemma, just a doubled case split" facts needed real new infrastructure; the
one sized as "more substantial... needs a new arithmetic identity" turned out
to need none) — see below for what each cost.

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
221 passed, 0 failed (was 218 before this lane's first commit; +3 net over
the two new files plus one shared test/coverage-list registration per
declaration). `clippy -D warnings` clean on `-p axeyum-lean-kernel
--all-targets --all-features`. `rustfmt --edition 2024 --check` clean on
every touched file. `python3 scripts/validate-facts.py` — 2270 facts, 0
errors. `python3 scripts/check-mirror-statement-fidelity.py` —
verdict=PASS. `python3 scripts/check-autogenesis-holdout-isolation.py` —
settled=0, references=0, verdict=PASS.

**Closed:**

Detail moved to [`../notes/376-parity-finish.md`](../notes/376-parity-finish.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | parity-finish | 3 axiom-free Nat kernel theorems closing the parity/division-by-two cluster's last blockers (`Nat.even_add`, `Nat.even_add'`, `Nat.even_div`); all 3 dispatched facts proved; two of three handoff sizings were wrong (one undersold, one — `even_div` — badly oversold: an existing unconditional lemma closed it in ~75 lines) |
