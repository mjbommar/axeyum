# QUANT-PREPROCESS: both premises reversed, and the macro finder is net negative

ADR-2127. The lane question came from
`bench-results/dt-ground-probe-20260916/README.md`, which established that
ADR-2114's `GROUND` attribution is **z3's preprocessing of the quantified
assertions** — stripping every quantified assertion from those 83 files and
asking plain z3 gives 83 of 83 `sat` — and named two mechanisms: Skolemizing an
existential at positive polarity, and folding definitional `forall`-equalities
into ground macros. Build both, measure both.

**Both premises reversed.** The first mechanism already ships and already fires
on 90 of 90 files. The second was built, and measured to be worth **−1 file**
across all 525.

## 1. Skolemization already ships, and already fires

`crates/axeyum-solver/src/quant_skolemize.rs` is a polarity-aware
NNF + Skolemize + prenex pass over the **whole assertion set**, emitting Skolem
*functions* over enclosing universals, wired into the ladder inside
`prove_unsat_by_ematching`. The brief's first item describes code already on
main.

"Already ships" is not "already fires", so `skolem-reach-probe.sh` measures the
difference using the pass's own `AXEYUM_QPROBE` instrumentation — never
inferred from verdicts. 90 undecided files, 30 each from AUFDTLIRA, UFLIA, UF:

| | count |
|---|---:|
| `QPROBE skolem-bail` (abandoned an assertion at the mixed-polarity corner) | **0 of 90** |
| `skolemize-unchanged` (ran and changed nothing) | **0 of 90** |
| reached the e-matching retry | 86 of 90 |
| **residual quantifier survived skolemization** | **86 of 86** |

Loop exit afterwards: 59 `timeout-mid-round`, 2 `timeout-round-head`, 23
`CLOCK`. Per-file rows in `skolem-reach/`.

So the block is downstream of skolemization, and the census's
414-of-525 "has a skolemizable position" describes the corpus rather than
naming headroom.

## 2. Census — the shapes, with denominators (`census/`)

`scripts/quant-preprocess-census.py` over 1200 files (200 per division), 525
undecided by our ladder. Files carrying each shape; undecided in parentheses.

| division | files | undec. | top-level skolem pos. | deep | needs Skolem *fn* | ANY skolem | definitional macro | quasi-macro |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 81 | 159 (65) | 137 (51) | 10 (2) | 184 (74) | 22 (14) | 0 (0) |
| UFDTLIRA | 200 | 56 | 147 (43) | 88 (20) | 0 (0) | 162 (44) | 51 (7) | 0 (0) |
| UFLIA | 200 | 114 | 26 (22) | 81 (65) | 62 (51) | 83 (67) | 70 (44) | 6 (6) |
| AUFLIRA | 200 | 22 | 21 (6) | 160 (14) | 14 (4) | 164 (17) | 2 (2) | 184 (16) |
| UFNIA | 200 | 146 | 132 (93) | 47 (38) | 43 (34) | 166 (119) | 9 (8) | 1 (0) |
| UF | 200 | 106 | 42 (25) | 167 (93) | 156 (90) | 167 (93) | 87 (51) | 36 (21) |
| **total** | **1200** | **525** | (254) | (281) | (181) | **(414, 78%)** | **(126, 24%)** | (43) |

The census transcribes z3's criteria with `file:line` and is deliberately
conservative: polarity is *proven*, never assumed, and a quantifier reachable
only through a `let` binding value gets its own column rather than being
counted as skolemizable.

Two readings worth carrying: **`sk_conj` is 0 in all six divisions** — no
assertion in this corpus puts a negated universal under a top-level `and`, the
goal is always directly `(assert (not (forall ...)))`. And
`macro_reject_occurs` is 0 in five of six divisions (120 in UF alone), so on
this corpus the occurs check is almost never the condition that refuses a
macro candidate; coverage is.

## 3. The first ablation was VACUOUS, and printed a clean-looking answer

`z3 smt.macro_finder=false` against plain `z3` reported `same` on **297 of 297
rows**. That is exactly what a working ablation with no effect prints, which is
the only reason it was checked instead of reported.

It measured nothing. `smt_params::setup_AUFLIRA()` assigns
`m_macro_finder = true` **unconditionally**
(`references/z3/src/params/smt_params.cpp:420`), and the logic setup runs
*after* the command line is parsed. Every division here reaches that
assignment: `AUFLIRA` by name (`src/smt/smt_setup.cpp:188`), and
`AUFDTLIRA`/`UFDTLIRA` through `setup_unknown(static_features&)`
(`smt_setup.cpp:210`), whose quantified-and-contains-real branch calls
`setup_AUFLIRA(false)` (`smt_setup.cpp:845-847`). Both arms ran with macros
**ON**. On UFLIA/UFNIA/UF the mirror image held — `setup_UFNIA` delegates to
`setup_AUFLIA`, which leaves the flag false because the assignment is commented
out at `smt_params.cpp:399-401` with the reason *"It destroys the existing
patterns"* — so both arms ran with macros **OFF**.

The obvious check passes and is worthless: z3 **does** validate option names
and errors on an unknown one, so "the flag was accepted" was true all along.

`auto_config=false` fixes it, routing to `setup::setup_default()`
(`smt_setup.cpp:69`) whose unmatched-logic branch is the static-feature-free
`setup_unknown()` (`smt_setup.cpp:805`), which never touches the flag.

`control/macro-finder-positive-dt.smt2` pins the discrimination: under those
flags with both quantifier engines off it is `unsat` with `macro_finder=true`
and `unknown` with `macro_finder=false`. **`z3-macro-ablation.sh` now RUNS that
control and exits 4 before writing a single row if the arms agree**, so this
cannot recur silently.

## 4. Corrected ablation — macro finding is NET NEGATIVE here (`ablation/`)

One binary, two arms (`auto_config=false smt.macro_finder=true|false`), back to
back on the same file on the same pinned core, arm order alternating per file,
12 s / 8 GiB, s7 cores `1,9` and `3,11`. Population: the files **our** ladder
leaves undecided.

| division | n | unsat (macro on) | sat (macro on) | LOST without macro | GAINED without macro | sat/unsat disagreement |
|---|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 81 | 57 | 0 | 0 | 0 | 0 |
| AUFLIRA | 22 | 18 | 0 | 0 | 0 | 0 |
| UFDTLIRA | 56 | 14 | 25 | 1 | 0 | 0 |
| UFLIA | 114 | 52 | 1 | 1 | 0 | 0 |
| UFNIA | 146 | 59 | 2 | 0 | **3** | 0 |
| UF | 106 | 13 | 0 | 0 | 0 | 0 |
| **total** | **525** | 213 | 28 | **2** | **3** | **0** |

**520 of 525 rows are identical between the arms. Macro finding decides 2 files
that are lost without it and LOSES 3 that turning it off recovers. Net −1.**
Zero sat/unsat disagreements in either arm: no soundness incident.

All three GAINED-without-macro files are in **UFNIA** — precisely the division
z3's own authors disabled the flag for, with the stated reason *"It destroys
the existing patterns"*. The measurement reproduces their reason independently,
on a population they never ran.

This is the COMPLETE undecided population -- all 525 files, all six divisions,
no prefix. The denominator this is a ceiling *for*: z3 decides **241 of the 525**
that our ladder does not. Macro finding accounts for 2 of them, and costs 3
elsewhere.

## 5. What was shipped anyway, and why it stays off

`crates/axeyum-solver/src/quant_macro_inline.rs` implements definitional macro
finding and inlining with every z3 condition transcribed at `file:line`
(`is_macro_head` `macro_util.cpp:139-165`, the occurs check `:182`/`:222` and
`occurs.cpp:76-85`, acyclicity `macro_manager.cpp:130-134`, twice-defined
refusal `:120-123`). Behind `AXEYUM_MACRO_INLINE`, **OFF**, wired as a PREFIX
so shipped behaviour is a floor even when armed. `unsat` transfers; `sat` does
not, and the producer reports that rather than the call site restating it.

It is landed rather than deleted because the measurement is the deliverable and
re-running it needs the code.

### Mutation controls

Run in a `scripts/lane-snapshot.sh` copy, in the ARMED arm.

| mutation | tests that die |
|---|---|
| drop the ACYCLICITY check (`if !acyclic(...)`) | **exactly one**: `mutually_recursive_definitions_are_refused_by_the_cycle_check` |
| drop the ARITY `== binder size` check | **exactly one**: `a_binder_variable_missing_from_the_head_is_refused` |
| weaken DISTINCTNESS (`\|\|` → `&&`) | 9 unit + 3 route — a blunt mutation that also breaks the positive path, so it kills loudly rather than cleanly |
| drop the OCCURS CHECK | **ZERO** — including the test that was named for it |

The second row is the finding. **The acyclicity check subsumes the occurs
check**: `f` occurring in its own body is a self-loop in the dependency graph,
so the graph check refuses it first. No fixture can separate them in this IR,
because a function can only occur as an application. The occurs check is kept
for parity with z3 and because it rejects locally before a graph is built — but
it is recorded in the code as subsumed, rather than left looking like
protection it does not provide. This is the pattern CLAUDE.md names: six of
seven guards in one suite were removable because they all rejected through one
shared check.

## Artifacts

- `census/*.tsv` — per-file counts, all 1200 files, six divisions.
- `lists/*.list` — the `all` and `undecided` populations per division.
- `ablation/abl-*.tsv` — per-file two-arm z3 rows.
- `skolem-reach/*.tsv` — per-file `AXEYUM_QPROBE` readings.
- `control/macro-finder-positive*.smt2` — the discriminating control.
- `z3-macro-ablation.sh`, `skolem-reach-probe.sh` — the harnesses; both exit
  non-zero rather than write a vacuous row.
- `scripts/quant-preprocess-census.py` + 33 tests.
