# Glaurung authoritative finding parity — 2026-07-17

This artifact compares Glaurung with Z3 and Axeyum separately compiled as the
sole exploration authority. Across three order-balanced repetitions per
backend and driver, all four drivers emit byte-identical raw finding lists.

| Driver | Roots analyzed | Z3 solves | Axeyum solves | Raw findings | Canonical SHA-256 |
|---|---:|---:|---:|---:|---|
| DptfDevGen | 6/8 | 561 | 561 | 17 | `4f23929cadbb7ec47c6cc64706cc6e20ff6025a721ac13375a4649f9112e6f5c` |
| vwififlt | 13/14 | 4,742 | 4,734 | 104 | `32be08d3f36b95f473f30337592012033ea8f138df98b634f70dad43ddcac204` |
| IntcSST | 18/34 | 1,672 | 1,668 | 116 | `2c30994aaf26a10f408c187724d94ec9cc85aa9a102af56019f17f5931cb2fbc` |
| SurfacePen | 31/35 | 2,551 | 2,551 | 65 | `876b5c20a34154795179fc475dc0d2c7c98c7d73844972f174adf1ee6216d0cb` |

The result covers 24 clean processes and 302 canonical raw sinks. Counting
every repetition and authority population, all 1,812 emitted sink rows are
stable. `IOCTLANCE_ALL=1` makes the comparison cover Glaurung's raw sink
output rather than only its displayed high-confidence subset. No process hit
the 300-second deadline, 100,000-function analysis cap, 20,000-solve budget,
or 60-second per-solve bound.

## Exact identities

- Axeyum: `d495cc7ce18b00531b3bef5a8bc62b89eff954bb`, clean tracked tree.
- Glaurung: `4fce79fccd167c898fa5acad24f4b8b947ba7daa`, clean tracked tree.
- Z3-authority binary SHA-256:
  `f88bb52754c73a271c7db85ef95a1fa8247cf12a7dc497eec35b21bcc33561a0`.
- Axeyum-authority binary SHA-256:
  `613c3fd83ad9ec2b08490486030864ceb58fda69a5bff680ad3b4af95568f40d`.
- [`report.json`](report.json) SHA-256:
  `2afe3abc0fafb5acd9069e148faf3d405112f5d7a3976c39c92ba3bd49c2b944`.

The two authority binaries were built independently from the same Glaurung
revision:

```sh
cargo build --release --example ioctlance --no-default-features \
  --features solver-z3
cargo build --release --example ioctlance --no-default-features \
  --features solver-axeyum
```

The committed runner is
[`scripts/measure-glaurung-authoritative-findings.py`](../../scripts/measure-glaurung-authoritative-findings.py).
It alternates backend order, rejects nonzero exits and coverage-bound hits,
requires stable per-backend output and work summaries, and computes both
ordered-list parity and set differences. The complete configuration, input and
binary hashes, timing/RSS arrays, solve counts, and empty backend-only sets are
in `report.json`. The four `*.findings.txt` files are the canonical Z3 output;
their hashes equal every Axeyum output hash as well.

## Claim boundary

This establishes exact raw finding-output parity for these four current,
bounded drivers when either backend controls exploration. It is stronger than
verdict parity and requires no canonical model-selection policy on this tier.

It does not establish identical exploration. vwififlt uses eight fewer solve
calls and IntcSST four fewer solve calls under Axeyum authority, despite ending
with identical findings and root coverage. The artifact therefore does not
claim an identical query stream, model stream, or concretization path.

It also does not cover timeout-sensitive or wider driver families. Glaurung's
warm lifecycle footer is compiled only when both backend features are present,
so the Axeyum-only binary cannot supply warm hit/fallback telemetry; ADR-0228
provides that separate fixed-work evidence. Finally, the standalone authority
timers are not the fair four-cell solver comparison and must not replace
ADR-0215/0217 in performance claims.
