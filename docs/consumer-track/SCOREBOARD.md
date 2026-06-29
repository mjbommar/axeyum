# Consumer-track scoreboard — aggregate (App D measurement backbone)

A single honest view of the consumer apps' measured state. Each app commits its
own construction-known scoreboard + machine-readable `corpus.json`; this page
aggregates them. **The soundness floor across the whole track is `DISAGREE = 0`.**

Regenerate the per-app numbers:
`cargo run -p axeyum-evm --example measure_evm` ·
`cargo run -p axeyum-verify --example measure_verify` · (property: the crate's
generated corpus test).

| App | Crate | Cases | Bugs found | Proved safe | Unknown | DISAGREE | Lean-cert | Scoreboard |
|---|---|---:|---:|---:|---:|---:|---|---|
| Bounded-property SDK | `axeyum-property` | 16 | 11 | 5 | 0 | **0** | 1/1 required | [property/](property/SCOREBOARD.md) |
| EVM bug-hunter | `axeyum-evm` | 18 | 13 | 5 | 0 | **0** | (needs core accessor) | [evm/](evm/SCOREBOARD.md) |
| Rust verifier | `axeyum-verify` | 14 | 7 | 7 | 0 | **0** | 4/7 verified | [verify/](verify/SCOREBOARD.md) |
| **Total** | — | **48** | **31** | **17** | **0** | **0** | — | — |

## Soundness hardening (beyond the construction-known corpora)

Adversarial **differential fuzzes** with independent concrete oracles back the
`DISAGREE = 0` claim over *random* inputs, and have earned their keep — each found
a real wrong-safe that was fixed:

- **EVM** (`axeyum-evm/tests/differential_fuzz.rs`): random bytecode + calldata; a
  concretely-reachable `REVERT`/`INVALID` is never reported `SafeUpToBound`
  (single-tx + multi-tx + totality, over arith/mem/storage/env/call, with
  `BYTE`/`SIGNEXTEND`/`EXP`/`LOG`/`BLOCKHASH`/`MSIZE`/`CALLDATACOPY`/CALL-return-
  data in the opcode pool). *Found & fixed:* a bad jump destination treated as a
  safe path end.
- **verify** (`axeyum-verify/tests/differential_fuzz.rs`): random `a op b` (unsigned
  + signed + array index) with a trivially-correct evaluator; a reachable panic is
  never `Verified`. *Found & fixed:* the `iN::MIN / -1` signed division overflow.
  Also value-checks the widened fragment (C5) against std oracles — `wrapping_*`
  modular result, `saturating_*` clamp (both signednesses), `min`/`max` selection,
  `abs` (MIN-overflow edge + value), and the `match`-on-int dispatch desugar
  (per-branch panic folding): an always-false assertion over each computed value
  must stay reachable, so a wrong value surfaces as a wrong-safe.

## Honest scope

- These are **construction-known** corpora (the label is the oracle) +
  cross-checks (concrete re-execution for EVM; warm-vs-unroll agreement + original-fn
  `catch_unwind` for verify). They prove *no wrong verdict on a known set*, not a
  decide-rate vs a competitor.
- **vs-SOTA decide-rate scoreboards are install-gated** (hevm/halmos/Kani not
  installed, network offline). The `ExternalOracle` seam exists; the numbers will
  be added when the tools are available.
- The consumer track is **demand-pull**: it does not move the core SMT decide-rate
  (see [the decide-rate frontier](../plan/decide-rate-frontier-2026-06-28.md)); its
  jobs are certifying user-facing value and surfacing core gaps (it has filed
  `UPSTREAM-FEEDBACK.md` U6/U7/U8).
