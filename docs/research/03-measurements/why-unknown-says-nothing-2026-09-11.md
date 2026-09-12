# Why an `unknown` said nothing — and what the newly-visible reasons say about `QF_DT`

Lane `why-unknown`, 2026-09-11/12. Commits `ff2f39a34` and its follow-up.

## The question

When we return `unknown` we frequently do not say **why**, and an unattributed
gap is a gap nobody can work on. `QF_DT` scores 114/200 against the reference's
192 — an **81-file** addressable gap — and a sampled read said most of those
files printed no reason at all.

## Method

Two populations, both taken whole rather than sampled, from
`bench-results/parity-details/`:

- **the addressable gap** — every file recorded as `unsolved` for axeyum and
  decided by the reference, across all eleven divisions: **313 files** (81 of
  them `QF_DT`);
- **a decided control** — every sixth file recorded as `sat`/`unsat` for
  axeyum: **233 files**, whose verdicts must not move.

Run as `smtcomp_cli <file> --timeout-ms 8000 --trace`, six at a time, under
`ulimit -v 8388608`, on s4.

Both arms are release builds from this lane's worktree with a private
`CARGO_TARGET_DIR`, differing only in the instrumentation: the "before" binary
is `1446a809c`'s content of the touched files, the "after" binary is the same
tree with the change applied. The *main checkout's* prebuilt `smtcomp_cli` was
**not** used as the baseline — it was built at 12:56 and `1446a809c` was
committed at 16:39, so it describes an older tree.

**The arms are compared at comparable machine load**, and that matters: a first
pass ran while another lane held the box at load 25 and produced 13 verdict
differences across the two populations. Re-running those 13 files with the two
binaries *interleaved back to back*, four times each, showed 10 of 13 agreeing
in every run and the other 3 flipping **within a single binary** across repeats
(`pb_real_40_80_60_00`: base gives `sat, unknown, unknown, sat`). Those were
wall-clock flips at an 8 s budget, not an effect of the change. The numbers
below are from arms run at load 3–6.

## Result

| | before | after |
|---|---|---|
| **addressable gap** — files | 313 | 313 |
| verdict `unknown` | 260 | 260 |
| printed a `; give-up` line | **93 (35.8%)** | **260 (100%)** |
| route trail contained a reasoned `declined` entry | 93 | 168 |
| **decided control** — files | 233 | 233 |
| verdict `unknown` | 16 | 16 |
| printed a `; give-up` line | 9 | 16 |
| **verdict changes, per file, both populations** | — | **0 of 546** |
| **process exit-status changes** | — | **0 of 546** |

On the `QF_DT` sub-population alone: **11 of 81 → 81 of 81**, route-trail depth
on the 70 newly-explained files **1 attempt → 5**.

The structured trail stays at 168/260 while the human line reaches 260/260
because a watchdog kill leaves no trail to publish — the worker thread never
returned. That gap is real and is named below, not papered over.

## Why the reason was missing — four places, none of them "we do not know"

The reason was never absent. Every silent file had one in hand:

1. **`check_auto_explained` reached the dispatch through `?`.** On an `Err` that
   destroyed the `RouteTrace` it had just filled in, and `check_auto` absorbed
   that trace with `Result::inspect`, which does not run on `Err` either — so an
   errored dispatch published *nothing at all*. Split out
   `check_auto_explained_parts`, which hands the trace back on both paths, plus
   a terminal `dispatch-error` entry carrying the error's own `Display`.
2. **Eleven `auto.rs` sites matched `Err(SolverError::Unsupported(_))`** —
   binding the message to `_` — and recorded the payload-free
   `DeclineReason::Unsupported`. A twelfth (`milp`) discarded the whole error.
   New `DeclineReason::UnsupportedDetail(String)` carries it under the same
   `"unsupported"` JSON reason token plus a `detail` field, so a consumer
   grouping by reason is unaffected.
3. **Four quantified/arithmetic rungs recorded `NotApplicable`** — "the probe
   said this route does not match" — for routes that had *run* and returned
   their own classified `UnknownReason`: `q:egraph` (roadmap item 1.8's one
   deliberately-out-of-scope line), `q:finite-expansion`, `q:uf-fmf-full`,
   `q:mbqi-quick`. A fifth, `preprocess`, said a path "errored" without saying
   what it hit.
4. **`smtcomp_cli` threw two of its three `unknown` sources away**: the
   `Err(_) => "unknown"` arm discarded the front-door error, and the watchdog
   path had no `CheckResult` at all, so it printed the reason in a `; partial …`
   header and nowhere a `; give-up` grep could find it.

`kind=Error` and `kind=Watchdog` are deliberately **not**
`axeyum_solver::UnknownKind` members. That vocabulary classifies a *solver*
give-up; an ingest refusal and a thread that never returned are not among them,
and labelling either `Timeout` or `Other` would make it indistinguishable from a
route that noticed its own deadline and declined in good order. Those have
different remedies.

## What the newly-visible reasons SAY

### `QF_DT`: 70 of the 81-file gap is one refusal

All 70 give the same sentence, from one function
(`crates/axeyum-solver/src/datatype_native.rs:432`, `expect_dt_symbol`):

```
unsupported by backend: `is`/`select` over a non-variable datatype term
(constructors should fold first) (ADR-0022)
```

So 86% of the `QF_DT` gap is **not** 70 problems. The eager tag/field expansion
requires a tester's or selector's operand to be a free variable or a constructor
application, and these files apply them to something else.

Parsing all 70 files' s-expressions and classifying the operand head of every
tester and selector application (a real reader, not a regex over the surface):

| operand of the `is`/selector application | occurrences | files containing it |
|---|---|---|
| `ite` | 293 | 28 (tester) / 21 (selector) |
| a constructor application | 342 | 43 |
| another selector application | 30 | 17 |

Classes overlap. Counting each file by the set of classes it contains:
constructor + `ite` 18, constructor + selector 13, **none resolved by this
scan 13**, constructor only 12, `ite` only 10, selector only 4.

**Caveat, stated because it bounds the claim:** the scan is source-level and
does not substitute `let`, so the 13 unresolved files are ones this method could
not attribute — not files with no refused operand. The per-class counts are a
lower bound.

Three repairs are implied, in descending file count, and none is a new decision
procedure:

- **Fold a selector/tester over a constructor application** (43 files). The
  error message itself blames this on ADR-0022 step A not folding first, so the
  intended architecture already covers it. A *mis-applied* selector
  (`(pred zero)` — `pred` belongs to `succ`) is the SMT-LIB **underspecified**
  case and needs an unconstrained value of the field sort: this repository's
  Hard-Rule class for partial operators, fuzz seed included.
- **Push a tester/selector through a datatype-sorted `ite`** (28 files):
  `((_ is c) (ite b x y))` ≡ `(ite b ((_ is c) x) ((_ is c) y))`.
- **Name intermediate field variables for nested selectors** (17 files).

### `QF_DT`: a second defect the `preprocess` detail exposed

Carrying the preprocess error instead of the words "errored" named something
nobody could see before. The `preprocess` decline appears on **74 of the 81**
`QF_DT` addressable-gap files, and on **73** of those it now reads:

```
preprocessed path errored; degraded to the original query: backend failure:
canonicalize failed: IR error during rewrite: sort mismatch:
expected Bool or BitVec, found (Datatype 0)
```

The canonicalizer does not admit a datatype-sorted term at all, so every one of
those files silently loses its whole preprocessing pass before any datatype
route runs. This is independent of the `expect_dt_symbol` refusal above — it
happens earlier and on more files — and it was invisible because the one line
that could have said so said only that a path "errored". Across all eleven
divisions the same entry appears on 80 files, 73 of them this sort mismatch.

Whether fixing it decides anything is not measured here and is not claimed. What
is measured is that a stage 74 of 81 files depend on is failing for a reason
nothing recorded.

The other 11 of the 81 already said why, and say something different: the
`datatype-elim` route's own `Incomplete` — *"datatype unfolding produced a
candidate that does not satisfy assertion #N; the traversed-field relaxation is
incomplete here"*. That is a genuine incompleteness in the relaxation, separate
work from the 70.

### Across all eleven divisions

Of the 260 `unknown`s in the addressable gap, after the change:

| reason kind | files | the largest single detail |
|---|---|---|
| `Watchdog` | 91 | the worker thread did not return before the internal deadline |
| `Error` | 76 | 70 of them the `QF_DT` sentence above; 3 `re.allchar` outside the wired bounded subset (ADR-0029); 2 an uninterpreted sort the pure-Rust BV backend cannot bit-blast |
| `Incomplete` | 46 | e-matching did not refute within the round budget; wide integer constants outside i128 (ADR-1702); the bounded-string encoding-bound artifact |
| `Timeout` | 30 | `preprocessed dispatch timeout after reduced solve` |
| `ResourceLimit` | 17 | `quantified solve time budget exhausted after e-matching`; the lazy-arithmetic joint resource boundary, which states its own atom/CNF numbers |

The `Watchdog` bucket is now the largest, and it is the one that carries the
least information: a kill leaves no route trail, so 91 files say *that* they ran
out and not *where*. That is the next thing to fix, and it is a different fix —
cross-thread state, not a discarded string.

## Two findings that fell out of building the guards

- **`cargo test -p axeyum-bench` ran ZERO of `smtcomp_cli`'s six existing
  tests.** Cargo's default for an example target is `test = false`, and no gate
  in `scripts/` or the `justfile` used the `--example smtcomp_cli` form that
  does run them. Every guard on the competition CLI's trace output was inert in
  every gate this repository runs. Fixed with `[[example]] test = true`, which
  puts them under `cargo test --workspace` and therefore under
  `scripts/check-workspace-tests.sh`.
- **`UnknownReason` is `#[non_exhaustive]` with no constructor**, so a consumer
  could read one and never build one — which is *why* the CLI's give-up
  formatting had no test. Added `UnknownReason::new`.

## Mutation controls

Six mutations, each applied alone in this lane's private worktree and reverted
with a byte-comparison afterwards:

| mutation | tests killed |
|---|---|
| drop the `dispatch-error` record | 1 — `an_errored_dispatch_publishes_the_routes_that_ran_and_the_error_text` |
| `datatype-elim` records the placeholder again | 1 — `an_unsupported_decline_carries_the_refusing_calls_message` |
| the JSON render drops the new `detail` | 1 — `route_trace::json_tests::an_unsupported_decline_with_a_message_renders_the_message` |
| the CLI's error line goes silent | 2 — both CLI give-up tests |
| the CLI's error line claims `kind=Other` | 1 — `a_front_door_error_yields_a_give_up_line_carrying_the_error_text` |
| absorb the dispatch trace only on `Ok` | 2 — the two guards on that path |

**The JSON mutation first reported ZERO kills**, and that was my command, not a
missing guard: the killing test lives in the `--lib` target and I had trimmed
`--lib` out of the mutation command to make it faster. Re-run with `--lib`, it
kills exactly one. An empty result from a command that never pointed at the
subject is not a finding.

## What this does not claim

- It does not claim a verdict improved. Nothing here is a solver change; the
  measured **0 verdict changes over 546 files** is the point, not a footnote.
- It does not claim the three `QF_DT` repairs are worth 70 files. It claims 70
  files stop at one named refusal and names what that refusal is applied to.
- The `--timeout-ms 8000` budget is shorter than the 24 s the parity board uses.
  It is the same in both arms, so the coverage comparison holds; the *file set*
  would be the board's only at the board's budget.
- 100% is coverage of the `; give-up` **line**, not of the route trail. A
  watchdog kill still publishes no trail (168 of 260 carry a reasoned decline).
