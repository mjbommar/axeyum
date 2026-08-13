# CAS/SMT arithmetic capability corpus

A small, self-contained corpus of arithmetic queries that isolates **where
axeyum's nonlinear-integer reasoning fails today**, plus a harness that reports
per query: the verdict, the **deciding route**, and the wall time.

It exists to judge a capability change, not to advertise one. A corpus that its
own subject can quietly satisfy is worthless, so three properties are built in:

1. **Ground truth is independent of axeyum.** Every expected verdict is
   established in [`ground_truth.py`](ground_truth.py), which imports nothing
   from this repository. Justification is one of: a Python-verified witness, an
   exhaustive scan of an explicitly stated box, a hand proof written out in the
   entry, or a cited classical theorem.
2. **Every `unsat` entry has a minimally-different `sat` control.** A route that
   answers `unsat` to everything scores zero here, not full marks. Every `sat`
   verdict also gets its model replayed against the original goal.
3. **Some entries must NOT decide.** Two are Diophantine equations believed
   unresolved by mathematics; several are satisfiable queries whose only
   witnesses are astronomically large. Making those decide, or flipping one to
   the opposite verdict, is a soundness alarm — not a capability win.

Route provenance uses `check_auto_explained`, never `check_auto`: a verdict
without a route is not evidence about which machinery did the work.
`explain_corpus` is not used anywhere (CLAUDE.md documents it as capable of
printing a wrong verdict).

## Files

| file | what it is |
|---|---|
| [`ground_truth.py`](ground_truth.py) | independent verification of all 91 checkable expected verdicts; declares the 2 open ones |
| [`ground_truth.out`](ground_truth.out) | its output (`91 claims, 0 failed`) |
| [`harness/`](harness/) | the measurement harness (standalone crate, **not** a workspace member) |
| [`baseline-9f0f4ed.md`](baseline-9f0f4ed.md) | the baseline result at commit `9f0f4ed`, before the CAS wiring landed |
| [`baseline-9f0f4ed.out`](baseline-9f0f4ed.out) | verbatim harness output for that run |
| [`baseline-9f0f4ed.json`](baseline-9f0f4ed.json) | the same, machine-readable, with full route traces |
| [`gaps-6x-9f0f4ed.out`](gaps-6x-9f0f4ed.out) | the 13 gaps re-run at 6× budget (still 13 gaps) |

## Running it

```sh
export CARGO_BUILD_JOBS=1              # shared box
cd docs/plan/cas-smt-capability-2026-08-12/harness
cargo build --release
./target/release/cas-capability-corpus --selftest        # alarm paths must fire
./target/release/cas-capability-corpus --json result.json
python3 ../ground_truth.py                               # must exit 0
```

Flags: `--only <A|B|C|D|F|G|H>` one axis; `--ids a,b,c` named entries;
`--budget-scale N` multiply every budget; `--json <path>` machine-readable output.

`harness/` carries an empty `[workspace]` table, so `cargo test --workspace`,
`cargo deny`, and `scripts/check.sh` never build it. The repository root's
`members` list enumerates `crates/*` explicitly, so nothing sweeps it in either.
**It is not a workspace member and adding one was not necessary.**

## Axes

| axis | n | what it isolates |
|---:|---:|---|
| A | 15 | units (`a·p = 1`) and **variable-divisor** divisibility, in both phrasings |
| B | 10 | the same fact with an **opaque symbol** versus **instantiated** |
| C | 14 | **monolithic** hypothesis set versus the same content **decomposed** into lemmas |
| D | 20 | polynomial identities of degree 2–4 in 2–3 variables, each with a `+1` near-miss |
| F | 14 | **nonzero-polynomial-but-unsat traps**: integrality beats zero-testing |
| G | 15 | tripwires — huge witnesses, deep theorems, and two **open** problems |
| H | 5 | anchors that must not regress |
| | **93** | |

Axis F is the sharpest trap for a CAS-backed route. `x·x = 2` is `unsat` over ℤ
while `x² − 2` is emphatically *not* the zero polynomial. Any route that reasons
"the difference does not normalise to zero, therefore satisfiable" produces a
**wrong `sat`** on F1, F3, F5, F7, F9, F11 and F14. Their `sat` controls (F2, F4,
F6, F8, F10, F12, F13) differ by one constant, so a route cannot pass the traps
by refusing to answer `sat` at all.

## Tiers — how each entry is judged on a re-run

| tier | meaning | `unknown` is… | opposite verdict is… |
|---|---|---|---|
| `core` | elementary; deciding it is the point | a capability gap | a wrong answer |
| `hard` | expected verdict known only via deep mathematics | the **honest** answer | a wrong answer |
| `tripwire` | satisfiable, but only with an astronomical witness | acceptable | a **wrong answer** |
| `open` | believed unresolved by mathematics | **required** | an alarm: bug or research result |
| `anchor` | decided at the baseline | a **regression** | a wrong answer |

A decisive verdict on a `hard` entry is only a win if it carries a proof. `unsat`
on `G5-flt-4` means the tool claims Fermat's Last Theorem for n = 4; that is
believable only with a certificate, and must be re-checked before being counted.

The two `open` entries are `x³ + y³ + z³ = 114` and `= 390`, which as of 2026 are
unresolved. If a change makes either decide: a `sat` model must be verified in
plain Python before it is believed (if it verifies, it is a genuine new result;
if it does not, it is a soundness bug), and an `unsat` is a theorem nobody has
proved.

## Honesty caveats

- **Every wall time in the results is an upper bound, not a timing.** The
  measurements were taken on a 4-core box with load average above 4 (another
  agent building Rust, plus a remote solver job). Do not quote them as
  performance numbers; use them only as "decided quickly" versus "did not
  decide".
- The `sat` model replay uses axeyum's own ground evaluator, so it is a
  self-consistency check, not an independent one. The independent check is
  copying the printed witness into `ground_truth.py`.
- Bounded enumeration corroborates an `unsat` only *within the stated box*. Every
  `unsat` justified by a scan also carries a proof or a cited theorem.
