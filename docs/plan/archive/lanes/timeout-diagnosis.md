# Lane: timeout-diagnosis — the give-up variant that could not tell its gates apart

<!-- plan-section: lane-status -->

**Lane block (`DONE`, timeout-diagnosis, 2026-09-14).** [ADR-2060] fixes the
defect [ADR-2045] found and deliberately did not fix: `lra.rs`'s
`Decision::TimedOut` was a unit variant whose **own doc comment** claimed the
Fourier–Motzkin elimination had exhausted its budget, and the rendered string
said the same for every producer — on 34 of 34 measured `QF_LRA` rows carrying
it, `cube_matrices=0`, i.e. the elimination had never built a matrix. ADR-2045
declined because it is **two** changes: give the variant a detail, *and* stop
routing an `i128` overflow through a timeout variant. Both are here. This is a
**correctness-of-diagnosis** fix on a soundness-adjacent path; **no capability
lever is attached** and the lane is not measured in files decided.

**The enumeration, three ways.** A name scan gives **six** `Decision::TimedOut`
constructions — ADR-2045's count, and correct at that level. The compiler
confirms exactly those six, and also that **exactly one test in the entire
workspace** referenced the variant, which asserted only *that* the decision gave
up. The transitive closure over the cause-erasing returns **below** them gives
**28 program points** (27 distinct; one is a funnel) carrying **15 distinct
causes**, of which **one** is the elimination running out of wall clock:
`eliminate` returned a bare `None` for **eleven** bail points including **eight
`?`-on-`Option` `i128` overflows**; `simplex_fallback` one `Ok(None)` for five,
two of which — **a `sat` model that did not replay** and **an `unsat`
certificate that failed its self-check** — are this route's own trust anchors
and had no way to be counted at all; `collect_constraints` one `Ok(None)` the
caller re-read the clock afterwards to *guess* about. Reproducible with
`bench-results/timeout-diagnosis-20260914/scripts/enumerate-producers.py`.

**The shape.** `Decision::GaveUp(GaveUp)`, five gates, two carrying a nested
`(FmDecline, SimplexDecline)` pair because reaching the simplex *means* the
elimination already declined and the honest answer is two facts. `ctx.overflow`
leaves the timeout variant entirely for `Decision::Incomplete` /
`UnknownKind::Incomplete` — the **one** `UnknownKind` this change moves. Every
routing decision is unchanged by construction, watchdog precedence included.

**Verdict neutrality, measured** (200-file board, two binaries interleaved per
file, four pinned pairs `s5 0,8` / `s5 1,9` / `s6 0,8` / `s7 0,8`, 24 s,
`ulimit -v 8G`, all four shards complete at 50 rows each): **0 gains, 0 losses**
out of 200, **0 flips** out of 159 comparable, **0** exit-status moves out of
200, **0** soundness disagreements out of 185 annotated rows. `base decided
107/200, arm decided 107/200` — reproducing ADR-2045's 107 exactly. Wilson 95 %
upper bounds: gains `[0, 0.0189]`, flips `[0, 0.0236]`, soundness `[0, 0.0203]`.

**The finding inside the non-vacuity check.** A verdict-neutral A/B proves
nothing unless the binaries differ, so the give-up detail is a channel that
**must** move, attributed rather than counted: **35 board rows carried the old
sentence, 0 still do**, and the gate the solver now names on them is the
multiplier-matrix loop (**18**), the entry poll (**13** — the conjunctive
decider had not run at all) or collection (**2**). **Not one is the
elimination.** ADR-2045 inferred exactly this from the engines' own counters;
the solver now says it in its own words, through a channel sharing nothing with
those counters.

**Pinning.** Four tests of deliberately different kinds — one derives its
population from the file's own source text, with a negative control that
**panics** rather than returning an empty list. Coverage 5/5 `GaveUp`, 5/5
`FmDecline`, 4/6 `SimplexDecline` (the two undrivable ones named with reasons).
The requested guard deletion — `decide_within`'s entry deadline poll — goes from
**0 tests killed to 2**; the old test's own doc said deleting it left all 1,705
unit tests green. Seven mutations kill five different tests between them, so the
guards do not share a rejection path.

**Two things found on the way.** `rustfmt` rejoins a backslash-continued string
literal and leaves the continuation's indentation **inside** it: every detail
this lane added shipped briefly with runs of 14 spaces, and all four new tests
passed, because a run of spaces breaks nothing a `contains` looks for. And
`cargo doc --workspace --all-features` with `-D warnings` is **red on `main`** —
6 rustdoc errors in `axeyum-ir`/`axeyum-cnf`, measured on the base tree at
`91c721f8e`, neither caused nor fixed here.

**Next.** `SimplexDecline::ModelDidNotReplay` and
`SimplexDecline::CertificateFailedSelfCheck` are countable for the first time;
either above zero on a real board is a finding about a **trust anchor**, not
about a budget. And `past_deadline` is `stop_requested() || clock_expired`, so
"deadline" still covers a portfolio cancellation — separating them doubles the
enum and wants its own measurement first.

**Gates.** `cargo fmt --all --check` clean; `cargo check --workspace
--all-targets` 0 errors; `check-clippy-complete.sh` **887 of 887** targets, 0
diagnostics; `-p axeyum-solver --lib --features full` **1763 passed**;
`corpus_regression` 2 passed; `progress_frontier --features full` 12 passed;
the three mandatory z3 differential fuzzes **5 / 1 / 1 passed**, all nonzero;
`check-suite-gating.py` PASS (the pins are unit tests already inside
`hooks/pre-push:513`, so no new suite needs registering).

<!-- plan-section: landed-changes -->

| 2026-09-14 | `f6303ee7a` | timeout-diagnosis: the give-up variant cannot lie any more — and the overflow was never a timeout |
| 2026-09-14 | `0e7057f4f` | timeout-diagnosis: pin every give-up reason to the producer that makes it |
| 2026-09-14 | `2d6a78135` | timeout-diagnosis: rustfmt rejoined my continued literals and kept the indentation inside them |
| 2026-09-14 | `3f587710a` | timeout-diagnosis: pre-registered the A/B rules before the binaries were built |
| 2026-09-14 | `7c93daf52` | timeout-diagnosis: lane state, the A/B runner, the producer enumerator |
| 2026-09-14 | `ac43d6031` | timeout-diagnosis: clippy `unnecessary_wraps` on the test's expired-deadline helper |
| 2026-09-14 | `3d0fa24a3` | timeout-diagnosis: the last stale intra-doc link, on `Collector::timed_out` |
