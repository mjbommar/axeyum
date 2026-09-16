# Lane: quant-preprocess — goal skolemization and definitional macro inlining, the two mechanisms DT-GROUND-PROBE named

<!-- plan-section: lane-status -->

**Both premises reversed by measurement; the pass is built, measured, and stays
off** (`DONE`, quant-preprocess, 2026-09-16, ADR-2127,
`bench-results/quant-preprocess-20260916/`).

DT-GROUND-PROBE established that ADR-2114's `GROUND` attribution is z3's
*preprocessing* of the quantified assertions, and named two mechanisms:
Skolemizing a negated-universal goal, and folding definitional
`forall`-equalities into ground macros. This lane was to build both behind one
lever and measure them.

**1. Goal skolemization already ships, and already fires on every file this
question is about.** `crates/axeyum-solver/src/quant_skolemize.rs` is a
polarity-aware NNF + Skolemize + prenex pass over the WHOLE assertion set,
emitting Skolem *functions* over enclosing universals, wired into
`prove_unsat_by_ematching`. Measured with the pass's own `AXEYUM_QPROBE`
instrumentation over 90 undecided files (30 each AUFDTLIRA/UFLIA/UF):
**0 of 90 `skolem-bail`, 0 of 90 `skolemize-unchanged`, and a residual
quantifier survives on 86 of 86** where the rung was reached. The instantiation
loop then dies on the clock (59 `timeout-mid-round`, 2 `timeout-round-head`,
23 `CLOCK`). Building a second skolemizer would have bought nothing, and the
census's 414-of-525 "has a skolemizable position" is a description of the
corpus, not headroom.

**2. The first macro ablation was vacuous and printed a clean answer.**
`z3 smt.macro_finder=false` vs plain `z3` gave `same` on **297 of 297 rows** —
exactly what a working ablation with no effect prints.
`smt_params::setup_AUFLIRA()` assigns `m_macro_finder = true` unconditionally
(`smt_params.cpp:420`) and the logic setup runs AFTER the command line, so the
flag was overwritten and both arms ran with macros ON for
AUFDTLIRA/UFDTLIRA/AUFLIRA and OFF for UFLIA/UFNIA/UF. The obvious check is
useless here: z3 DOES reject unknown option names, so "the flag was accepted"
was true throughout. Fixed with `auto_config=false`; a positive control
(`unsat` with macros on, `unknown` with them off) is now RUN BY the ablation
script, which exits 4 before writing a row if the arms agree.

**3. Corrected ablation: macro finding is net NEGATIVE on this population.**
One binary, two arms, interleaved per file, 12 s / 8 GiB, s7 `1,9`/`3,11`, over
the files our ladder leaves undecided. **All 525 undecided files, all six divisions,
no prefix: 520 identical, 2 LOST without macros, 3 GAINED without macros, 0
sat/unsat disagreements. Net −1.**
All three GAINED files are in UFNIA — the division z3's own authors commented
the flag out for, giving the reason "It destroys the existing patterns"
(`smt_params.cpp:399-401`). The measurement reproduces their stated reason on a
population they never ran. For scale: z3 decides 241 of these 525 files our
ladder does not; macro finding accounts for 2 of them.

**Census (criterion 1), 1200 files, 525 undecided.** Undecided files carrying:
a top-level skolemizable position 254, a deep one 281, one needing a Skolem
FUNCTION 181, ANY skolemizable position **414 (78%)**, a definitional macro
**126 (24%)**, a quasi-macro 43. `sk_conj` is 0 in all six divisions — no
assertion puts a negated universal under a top-level `and`; the goal is always
directly `(assert (not (forall ...)))`.

**Shipped:** `crates/axeyum-solver/src/quant_macro_inline.rs` behind
`AXEYUM_MACRO_INLINE` (armed only by exactly `"1"`), **OFF**, wired as a PREFIX
in `prove_unsat_by_ematching` so shipped behaviour is a floor even when armed.
`unsat` transfers; `sat` does not, and the producer says so
(`MacroInlining::sat_transfers`) rather than the call site restating it. 14
unit tests + `tests/quant_macro_inline_route.rs` (5), gated in `hooks/pre-push`
**twice** — the default arm and `AXEYUM_MACRO_INLINE=1` — because the lever
ships off and gating only the default arm would register a suite that cannot
fail for the reason it exists.

**Mutation finding worth carrying:** dropping the OCCURS CHECK kills **zero**
tests, including the one named for it. The acyclicity check over the definition
set subsumes it — a self-occurrence is a self-loop — and dropping acyclicity
instead kills **exactly one** named test. No fixture can separate them in this
IR, so the check is kept for parity with z3 and the redundancy is recorded at
the code rather than left to look like protection.

**Left undone:** quasi-macros (not implemented; the simple-macro ceiling
removes the reason), model reconstruction that would let `sat` transfer through
inlining, and an our-own-binary A/B of the lever over the six divisions — the
z3 ablation already answers the ship question in the negative, and the pass is
off.

**The open question this lane surfaced** is not preprocessing at all: a
universal survives skolemization on 86 of 86 files and the instantiation loop
then exhausts its budget. That is where this population is lost.
