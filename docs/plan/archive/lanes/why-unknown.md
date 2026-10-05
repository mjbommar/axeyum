# Lane: why-unknown — an `unknown` that declines must say why

<!-- plan-section: lane-status -->

**Reason coverage on the addressable gap (`done`, why-unknown, 2026-09-12).**
When we return `unknown` we frequently did not say why, and an unattributed gap
is a gap nobody can work on. Measured over **two whole populations** from
`bench-results/parity-details/` — the 313-file addressable gap across all
eleven divisions, and a 233-file decided control — at `--timeout-ms 8000`, both
arms at comparable machine load: a `; give-up` line on **93 of 260 `unknown`s
(35.8%) → 260 of 260 (100%)**, with **0 verdict changes and 0 exit-status
changes over all 546 files**. On `QF_DT` alone, **11 of 81 → 81 of 81**, and
the route trail on the 70 newly-explained files went from one attempt to five.

The reason was never absent — it was discarded at four layers, each of which
had it in hand. `check_auto_explained` reached the dispatch through `?`, so an
`Err` destroyed the `RouteTrace` it had just filled in, and `check_auto`
absorbed that trace with `Result::inspect`, which does not run on `Err` either.
Twelve `auto.rs` sites bound a `SolverError::Unsupported` message to `_` and
recorded the payload-free `DeclineReason::Unsupported`. Five rungs
(`q:egraph` — roadmap item 1.8's one deliberately-out-of-scope line — plus
`q:finite-expansion`, `q:uf-fmf-full`, `q:mbqi-quick`, `preprocess`) recorded a
placeholder for a route that had RUN. And `smtcomp_cli` discarded both its
front-door `Err` and its watchdog reason.

**The diagnosis is worth more than the instrumentation.** 70 of the 81-file
`QF_DT` gap give ONE sentence from ONE function (`datatype_native.rs:432`,
`expect_dt_symbol`): an `is`/`select` whose operand is neither a free variable
nor a constructor. Parsing all 70 files and classifying that operand: a
datatype-sorted `ite` (28 files), a constructor application (43), a nested
selector (17), 13 unresolved by a scan that does not substitute `let`. Three
repairs are implied and none is a new decision procedure. Separately, the
newly-carried `preprocess` detail exposed a **second** `QF_DT` defect nobody
could see: on **74 of 81** files the preprocessed path fails with `canonicalize
failed: IR error during rewrite: sort mismatch: expected Bool or BitVec, found
(Datatype n)` — the canonicalizer does not admit a datatype-sorted term at all,
so every one of those files loses its whole preprocessing pass.

**Two inert-gate findings.** `cargo test -p axeyum-bench` ran **zero** of
`smtcomp_cli`'s six existing tests (cargo defaults an example to `test = false`)
and no gate used the `--example smtcomp_cli` form that does; every guard on the
competition CLI's trace output was inert in every gate this repository runs.
And `UnknownReason` is `#[non_exhaustive]` with no constructor, which is *why*
the CLI's give-up formatting had no test.

**Next, for whoever picks up `QF_DT`.** The three `expect_dt_symbol` repairs
above, and the canonicalizer's datatype sort admission, are now named with
per-file counts. Neither is claimed to be worth N verdicts — that is the next
measurement, not this one. The largest remaining reasonless bucket is the
**watchdog**: 91 of 260 say *that* they ran out and not *where*, because a kill
leaves no route trail. Fixing that is cross-thread state, not a discarded
string. Full note:
`docs/research/03-measurements/why-unknown-says-nothing-2026-09-11.md`.

<!-- plan-section: landed-changes -->

| 2026-09-11 | `ff2f39a34` | An `unknown` that declines now says why. `check_auto_explained_parts` hands the trace back on the error path (it was destroyed by `?`, and `check_auto`'s `Result::inspect` absorb never ran on `Err`); new `DeclineReason::UnsupportedDetail` carries the twelve discarded `auto.rs` messages; `smtcomp_cli` prints `; give-up kind=Error detail=<error>`; `q:egraph` records the loop's own reason (roadmap 1.8's open line). Plus `[[example]] test = true` for `smtcomp_cli` (six guards were inert in every gate) and `UnknownReason::new`. |
| 2026-09-12 | `849df360d` | Five more placeholder sites: `q:finite-expansion`, `q:uf-fmf-full`, `q:mbqi-quick` (three cases in one arm, one of them a `VerifierRejected`), `preprocess` (which then exposed the `QF_DT` canonicalizer sort mismatch on 74 of 81 files), and the watchdog's own `; give-up kind=Watchdog`. Measured 93/260 → 260/260 reason coverage over the 313-file addressable gap, 0 verdict changes over 546 files. Six mutation controls, one of which first reported zero kills because the killing test was in a target I had trimmed from the command. |
