# Lane: producer-measurements — W1-12 (exact-real cost) and W1-13 (cas-internal residue)

<!-- plan-section: lane-status -->

**Status: LANDED (`DONE`, producer-measurements, 2026-09-04).** Both
deliverables measured and published, ADR-1617 accepted. No kernel
declarations added (measurement-only lane, as scoped).

**W1-12.** `examples/creal_eval_cost.rs` (new, `axeyum-lean-kernel`): builds
`CReal.seq x n` for `x` in `{pi, e, sqrt 2, exp 1}` plus trivial
`{zero, one, two}` controls, two ways to encode `n` (kernel-accelerated
`Lit::Nat` literal vs. genuine unary `Nat.succ` chain, matching this
codebase's own numeral idiom), and fully normalizes with a hand-rolled
`deep_nf` built only from public `Kernel::whnf`/`Kernel::expr_node` calls —
no new declaration, everything transient. Finding: the controls are
sub-5ms at every `n` and either encoding (the caller's index encoding does
not matter); `e` and `pi` at `n = 0` — the loosest possible request — **did
not complete** within a 400s/480s compute budget respectively, even though
the outer `Kernel::whnf` alone (exposing the head redex) resolves in
30-40ms. The cost lives inside the series' own internal `Nat.rec` recursion
(built unary regardless of the caller's `n`), which the library's own bound
theorems (`threeLePi`, `piLeFour`, ...) never force — they stay symbolic.
Reported as "did not complete", not extrapolated. Full method, raw
transcripts, and load readings: `artifacts/measurements/creal-eval-cost-2026-09-04.md`.

**W1-13.** `scripts/check-cas-internal-residue.py` (new): reuses
`validate-facts.py`'s own `classify_cas_certificate_fact` over every
`cas-certificate` fact and ratchets a floor — a fact recorded
`kernel-reconstructed` must stay one; a new `cas-internal` fact is not
refused. Measured: 60 total, 14 kernel-reconstructed, 46 cas-internal
(76.7% residue), 0 unrecognized — matches `validate-facts.py`'s own summary
line exactly. Per-`formal.fragment` breakdown shows the residue concentrated
in number theory, hypergeometric/binomial identities, GF(2), and SOS
families with no kernel bridge yet. Registered in `scripts/check.sh` and
`justfile`; companion suite `scripts/tests/test_check_cas_internal_residue.py`
(10 tests) registered under `scripts/tests/mutation_controls.py`'s
`cas-internal-residue` entry, mutation-verified 2026-09-04 on a scratch copy
(never the shared worktree) — all four guards each kill exactly one test.
Full breakdown: `artifacts/measurements/cas-internal-residue-2026-09-04.md`.

**Gates run and green**: `rustfmt --edition 2024` + `cargo clippy -D warnings`
on the example; `cargo fmt --all --check`; `cargo check --release -p
axeyum-lean-kernel --examples`; `python3 -m py_compile` on every touched
Python file; `python3 -m unittest scripts.tests.test_check_cas_internal_residue`
(10/10); `python3 scripts/tests/mutation_controls.py cas-internal-residue`
(4/4 guards, each kills exactly 1); `python3 scripts/check-cas-internal-residue.py
--report`; `python3 scripts/validate-facts.py`; `python3 scripts/gen-adr-index.py`;
`python3 scripts/gen-plan.py`.

<!-- plan-section: landed-changes -->

| 2026-09-04 | producer-measurements | lane started: W1-12/W1-13, ADR-1617 reserved |
| 2026-09-04 | producer-measurements | W1-12 landed: `examples/creal_eval_cost.rs`, ADR-1617, `artifacts/measurements/creal-eval-cost-2026-09-04.md` — controls fast, `e`/`pi` at n=0 did not complete within budget |
| 2026-09-04 | producer-measurements | W1-13 landed: `scripts/check-cas-internal-residue.py` + ratchet + tests, registered in `scripts/check.sh`/`justfile`/`mutation_controls.py`, `artifacts/measurements/cas-internal-residue-2026-09-04.md` — 60 total, 14 kernel-reconstructed, 46 cas-internal (76.7%), 0 unrecognized |
