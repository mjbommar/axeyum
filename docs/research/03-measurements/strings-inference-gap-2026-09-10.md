# Strings inference depth — is the gap an inference gap? (roadmap 3.6)

**Lane M3-6, 2026-09-10. Base `474423c8d`.**
Item **3.6** of [`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md):

> **Strings inference depth** — 87 cvc5 inference ids vs our 4; loop detection;
> four disequality procedures.
> *Measurement gate:* "After 2.5, count `unknown` on the vendored `QF_SLIA` set
> by missing inference kind."

## Recommendation

**DO NOT BUILD** the cvc5 `STRINGS_*` inference machinery — not now, and not on
this evidence.

**Zero of the 43 `unknown`s on the vendored corpus is caused by a missing
strings inference.** 39 of 43 never reach a strings solver at all: they are
declined at *ingest* by the ADR-0029 admission test. The remaining 4 reach the
solver and are declined by the **bounded-encoding completeness gate** (packed
sequences / int-blast width), not by an unresolved lemma.

Building inference kinds would move **0** of these 66 files. The work that would
move them is, in rank order, front-end and encoding work (§5).

There is one exception worth landing on its own: a **one-cause, one-file fix**
that is a constant fold, not an inference (§4.2).

## 1. The question, as a number

On how many of the 66 committed cvc5 string/seq benchmarks does a *missing
inference kind* cost us a verdict we would otherwise get?

**Answer: 0 of 66.** The denominator of undecided files is 43; every one of them
is attributable to a named front-end or encoding cause, and each cause is listed
per file in §3.

## 2. The measurement

### 2.1 Instrument

The shipped competition front door, `axeyum-bench`'s `smtcomp_cli`, with
`--trace` for route attribution. Nothing else — no probe code was needed for the
headline numbers, and none is left in the tree.

```sh
cargo build -p axeyum-bench --example smtcomp_cli --release   # via scripts/cargo-serialized.sh
# per file:
smtcomp_cli <file>.smt2 --trace --timeout-ms 60000
```

The sweep script is reproduced in §7. It walks
`corpus/regression/cvc5/qf_slia/*.smt2` (36 files) and
`corpus/regression/cvc5/seq/*.smt2` (30 files), extracts each file's
`(set-info :status …)`, and records the verdict line plus the
`; route decided_by=… bound_by=… last=… attempts=N` line.

### 2.2 Coverage and controls

- **Files examined: 66 of 66.** Every vendored file has a
  `(set-info :status sat|unsat)`; none was skipped.
- **Positive control (the instrument can decide):** 23 of the 66 are decided,
  and the same binary with the same `:status` extraction decides
  `corpus/regression/qf_bv/sat_wraparound.smt2` (`sat`, expected `sat`) and
  `corpus/regression/qf_bv/unsat_eq_conflict.smt2` (`unsat`, expected `unsat`).
- **Positive control (the route trace can distinguish an ingest decline):** the
  `attempts=1 … last=fd:parse` signature fires on 39 files and does **not** fire
  on the 4 solver-reached ones, which show `attempts=48/92/128/144` and
  `last=fd:bounded-completeness-unsat`. A per-cause parse-error message was
  independently captured for all 39 with a throwaway probe (now deleted); the
  two instruments agree file-for-file.
- **Second instrument, disagreeing about nothing:** a replay of
  `corpus_regression`'s own routing (`solve_capped`,
  `crates/axeyum-solver/tests/corpus_regression.rs:71-119`) decides 20 of 66 and
  never contradicts the front door — it is strictly weaker, deciding 3 fewer
  files (§6).

### 2.3 Real output

```
rows: 66
--- verdict tally ---
     12 sat
     43 unknown
     11 unsat
--- unknown rows: declined at ingest (attempts=1, last=fd:parse) ---
39
--- unknown rows that reached the solver ---
qf_slia/cvc5__cli__regress0__seq__seq-nemp.smt2	sat	; route decided_by=qf-bv bound_by=dl-online last=fd:bounded-completeness-unsat bound_ms=0 total_ms=5 attempts=92
qf_slia/cvc5__cli__regress0__strings__proj-issue409-re-loop-none.smt2	unsat	; route decided_by=qf-bv bound_by=fd:parse last=fd:bounded-completeness-unsat bound_ms=0 total_ms=1 attempts=48
seq/cvc5__cli__regress0__seq__seq-types.smt2	unsat	; route decided_by=int-blast-ladder bound_by=int-blast-ladder last=fd:bounded-completeness-unsat bound_ms=2 total_ms=19 attempts=144
seq/cvc5__cli__regress1__seq__issue8936-nth-eager-red.smt2	unsat	; route decided_by=qf-bv bound_by=int-blast-ladder last=fd:bounded-completeness-unsat bound_ms=3 total_ms=19 attempts=128
```

Per directory:

| directory | files | decided | `unknown` | wrong |
|---|---|---|---|---|
| `corpus/regression/cvc5/qf_slia` | 36 | 18 | 18 | 0 |
| `corpus/regression/cvc5/seq` | 30 | 5 | 25 | 0 |
| **total** | **66** | **23** | **43** | **0** |

## 3. Where the 43 `unknown`s actually come from

**39 declined at ingest**, by cause:

| # | cause | files |
|---|---|---|
| 10 | `(Seq E)` element sort has no sound fixed-width packing | `(Seq Real)` ×3, `(Seq (Seq (Seq Bool)))` ×2, `(Seq (Seq Int))` ×2, `(Seq E)` ×2, `(Seq String)` ×1 |
| 6 | packed-sequence **length/width bound** exceeded (`seq.++`, `seq.replace`, `seq.unit` element width) | `issue5547-seq-len-unit`, `seq-ex5`, `issue5547-small-seq-len-unit`, `proj-issue747-cmi-len-split`, `proj-issue733-mbqi-w`, `proj-issue708-explain` |
| 6 | content the front end does not model **at all** (`real.pi`, `(Bag String)`, `set.choose`, the `seq.empty` identifier, the `-1` identifier, a string op on `BitVec(115)`) | `proj-issue384-subtypes`, `proj-issue586-nth-update-no-fact`, `proj-issue653`, `issue8148-const-mv`, `seq-eval-extract`, `update-eq-unsat` |
| 4 | regex built from a **symbolic** string (`str.to_re` of a non-literal) | `issue6057-replace-re`, `issue6057-replace-re-all-jiwonparc`, `issue9269-rei-nconst`, `issue6639-replace-re-all` |
| 3 | `seq.unit` reaches the generic string-operator table (script declares no `Seq` symbol, so the sequence path is never entered) | `proj-issue586-nth-update-no-fact-2`, `seq-eval-bug`, `seq-eval-contains` |
| 3 | `str.replace_re` / `str.replace_re_all` over a symbolic string | `issue6203-6-replace-re`, `issue6636-replace-re-all`, `issue6637-replace-re-all` |
| 2 | `str.from_code` over a **symbolic** code point | `simple-nth-fail`, `issue8944-sygus-inst` |
| 2 | `str.indexof_re` — a cvc5 extension, declined unconditionally (`parse.rs:7581-7590`, ADR-0029) | `indexof_re-start-index`, `issue10195` |
| 2 | `str.to_upper` / `str.rev` outside the wired bounded subset | `to_upper_12`, `issue8926-sygus-inst` |
| 1 | `str.replace_all` over a symbolic operand | `repl-all-non-const-range` |

Rolled up by *theory*: **22 of 43 are `Seq`** (19 ingest + 3 solver-reached),
**12 are strings/regex over symbolic operands**, **6 are other theories entirely**
(`Bag`, `Set`, transcendental reals), **2 are a cvc5 extension**, **1 is the
`re.loop` fold in §4.2**.

## 4. The four that reach the solver, file by file

For each: the shape, where we decline, and what cvc5 uses. cvc5 line references
are against clone commit `1689f13331f7543801f82d9dcbcaac2f70a26781`
(`references/cvc5`, gitignored).

### 4.1 `seq/…seq-types.smt2` (`unsat`) — the one genuine inference analogue

```smt2
(declare-fun s () (Seq Int)) (declare-fun n () Int)
(assert (= 5 (seq.nth s n)))  (assert (< n (seq.len s)))  (assert (> n 0))
(assert (= (seq.unit 6) (seq.at s n)))
```

`seq.at s n = seq.unit (seq.nth s n)` in range, so unit injectivity gives `6 = 5`.
cvc5: `STRINGS_ARRAY_NTH_UNIT` (`src/theory/inference_id.h:828`) plus
`STRINGS_UNIT_INJ` (`:661`), in `src/theory/strings/array_core_solver.cpp`.
We decline with `int-blast-ladder` — "no model within the bounded integer width
32" — because `n` is an unbounded `Int` index. **This is the only file in the
corpus whose gap has a cvc5 inference id as its natural fix**, and even here the
proximate cause is the bounded `Int` encoding, not the absence of the lemma.

### 4.2 `qf_slia/…proj-issue409-re-loop-none.smt2` (`unsat`) — a constant fold, and it is a one-line finding

```smt2
(assert (str.in_re (str.from_code 0) ((_ re.loop 2 1) re.all)))
```

`(_ re.loop 2 1)` with lower > upper is the empty language. cvc5 rewrites it with
the RARE rule `re-loop-neg` (`src/theory/strings/rewrites:649-652`,
`Rewrite::RE_LOOP_NONE` at `sequences_rewriter.cpp:1219`).

**We already have that rewrite** — `crates/axeyum-smtlib/src/regex.rs:741-743`,
`if lo > hi { return Ok(Regex::None) }`. The file still comes back `unknown`.
Three variants isolate the cause exactly:

| query | verdict | route |
|---|---|---|
| `(str.in_re "a" ((_ re.loop 2 1) re.all))` | **unsat** | `fd:source-string`, 0 ms |
| `(str.in_re x ((_ re.loop 2 1) re.all))`, `x` a declared `String` | **unsat** | `fd:source-string`, 0 ms |
| `(str.in_re (str.from_code 97) ((_ re.loop 2 1) re.all))` | `unknown` | `qf-bv`, `last=fd:bounded-completeness-unsat` |

A *constant-numeral* `str.from_code` is not folded to a literal, so the query
falls off the source-string route into the bounded encoding, where the P2.7 A.2
completeness gate refuses to promote the bounded `unsat`. The value is
irrelevant (0 and 97 behave identically). **Constant-folding
`(str.from_code <numeral>)` at ingest converts this file from `unknown` to
`unsat`** and touches nothing else. That is not an inference; it is a fold.

### 4.3 `seq/…issue8936-nth-eager-red.smt2` (`unsat`)

```smt2
(declare-fun a () (Seq Int)) (declare-fun b () (Seq Int)) (declare-fun c () Int)
(assert (= a b))  (assert (not (= (seq.nth a c) (seq.nth b c))))
```

Congruence on `seq.nth`. **We already emit the semantic Ackermann constraint**
`(seq_eq ∧ idx_eq) → val_eq` at `crates/axeyum-smtlib/src/parse.rs:16859-16882`,
so the congruence is not the gap. The decline is again the unbounded `Int` index
`c` against the 32-bit int-blast width. cvc5 gets it from its equality engine
plus the `STRINGS_ARRAY_NTH_*` family (12 ids, `inference_id.h:828-844`).

### 4.4 `qf_slia/…seq-nemp.smt2` (`sat`)

```smt2
(declare-fun x () (Seq Int))
(assert (not (= x (as seq.empty (Seq Int)))))  (assert (= (seq.len x) 16))
```

A 16-element `(Seq Int)` does not fit the packed fixed-width representation, so
no model is found inside the bound. cvc5 builds the witness in
`model_cons_default.cpp` after a length split (`STRINGS_LEN_SPLIT`,
`inference_id.h:740`; cardinality `STRINGS_CARD_SP`, `:670`). This is encoding
**capacity**, not inference.

## 5. The four zero-coverage operators — parse or decide?

The P2.5 READMEs report `re.all`, `re.comp`, `re.inter` and `str.is_digit` as
having zero decided coverage. Measured through the shipped front door, **that is
no longer true of three of them, and the fourth is a corpus artefact**. None is
in `str.indexof_re`'s class (recognized syntax, declined unconditionally at
parse).

| operator | carriers in this corpus | measured |
|---|---|---|
| `re.all` | `re.all.smt2`, `proj-issue409-re-loop-none.smt2` (+ `qf_s/issue9784.smt2`) | `re.all.smt2` → **unsat**, decided by `fd:source-string` in 0 ms; `qf_s/issue9784.smt2` → **sat** (expected `sat`). Decided coverage exists. |
| `re.comp` | `re-in-rewrite.smt2`, `issue6639-replace-re-all.smt2` (+ `qf_s/issue4674-recomp-nf.smt2`) | `re-in-rewrite.smt2` → **unsat**, `fd:source-string`, 0 ms. `issue6639` declines on `str.to_re` of a symbolic string — not on `re.comp`. |
| `re.inter` | `re-in-rewrite.smt2` only | same file → **unsat**. Decided. |
| `str.is_digit` | `issue8944-sygus-inst.smt2` only | wired (`parse.rs:1825`; inventory row `07-strings-and-regex.md:299` says "Bounded, yes"). Its one carrier declines on `str.from_code` of a symbolic code point — an unrelated operator. |

So the answer to the brief's question is **neither**: we can parse all four and
we have routes for all four. The reported zero was an artefact of measuring
`check_auto` rather than the front door, plus a corpus of one file for
`str.is_digit`.

## 6. A correction the P2.5 READMEs need

`corpus/regression/cvc5/qf_slia/README.md` and `.../seq/README.md` state:

> Run: `cargo test -p axeyum-solver --features full --test corpus_regression`.
> Of these 36 files: **30 decided correctly** … **6 returned `unknown`** … 0 wrong.
> Of these 30 files: **27 decided correctly** … **3 returned `unknown`** … 0 wrong.

The `unknown` sets are right (all 9 reproduce exactly). The **decided** counts
are not. Measured here: **18 of 36** and **5 of 30**, front door; **16 of 36**
and **4 of 30** through the cited test's own routing.

The mechanism is a label, not a solver change. `corpus_regression::evaluate_file`
returns `Eval::Skip` when `parse_script` fails
(`crates/axeyum-solver/tests/corpus_regression.rs:158`) and the summary counts
`Eval::Skip` into `parse_skipped`, a **different** bucket from `Eval::Agree`
(`:219`, `:221`). The READMEs' per-file tables mark 37 parse-skipped files as
"decided (agrees)". Those 37 files return `unknown` from the shipped binary.

Nothing about soundness changes: **0 wrong verdicts** on all 66 under both
instruments, which is what the P2.5 exit criterion actually asserted. What
changes is the coverage headline, and it changes a lot: the corpus was reported
at 86 % decided and measures at 35 %.

I did not re-run the full `corpus_regression` gate (it walks all 218 files and
its summary is not per-directory), so this is stated as a discrepancy between
the READMEs' per-file rows and two direct measurements, not as a gate failure.

## 7. Reproduction

```sh
W=$(pwd)
CLI=$W/target/release/examples/smtcomp_cli
for f in "$W"/corpus/regression/cvc5/qf_slia/*.smt2 "$W"/corpus/regression/cvc5/seq/*.smt2; do
  exp=$(grep -oE '\(set-info :status (sat|unsat)\)' "$f" | head -1 | grep -oE '(sat|unsat)')
  out=$(timeout 120 "$CLI" "$f" --trace --timeout-ms 60000 2>&1)
  v=$(printf '%s' "$out" | grep -E '^(sat|unsat|unknown)$' | tail -1)
  r=$(printf '%s' "$out" | grep -E '^; route decided_by=' | tail -1)
  printf '%s\t%s\t%s\t%s\n' "$(basename "$f")" "$exp" "$v" "$r"
done
```

An ingest decline is `last=fd:parse … attempts=1`; anything else reached the
solver.

## 8. If the decision is later revisited, this is the rank order

Not "build 87 inferences". By files moved on this corpus:

| rank | work | files | what it is |
|---|---|---|---|
| 1 | `Seq` element sorts beyond the packed fixed-width set (`Real`, `String`, uninterpreted, nested `Seq`) | 10 | encoding |
| 2 | `Seq` length/width beyond the packed bound | 6 | encoding |
| 3 | unbounded-`Int` index/length into a sequence (the int-blast ceiling) | 3 | encoding |
| 4 | regex/replace over a **symbolic** string (`str.to_re` non-literal, `str.replace_re(_all)`, `str.replace_all`) | 8 | front end; cvc5 does it with `regexp_elim.cpp` + `STRINGS_EXTF`/`STRINGS_REDUCTION` (`inference_id.h:886-928`) |
| 5 | ground `seq.*` in a script that declares no `Seq` symbol | 3 | front end (sort inference) |
| 6 | `str.from_code` over a symbolic code point | 2 | front end; cvc5 `code_point_solver.cpp`, `STRINGS_CODE_PROXY`/`_INJ` (`:817`, `:819`) |
| 7 | `str.to_upper` / `str.rev` | 2 | front end |
| 8 | `str.indexof_re` (cvc5 extension) | 2 | policy — ADR-0029 declines it on purpose |
| 9 | **constant-fold `(str.from_code <numeral>)`** | 1 | a fold; §4.2 |
| — | other theories (`Bag`, `Set`, transcendental) | 6 | out of scope for strings |

Ranks 1–3 are one coherent piece of work (a real `Seq` theory rather than a
packed bit-vector) worth **22 files**. Rank 4 is worth **8**. Everything the
roadmap item names — inference ids, loop detection, the four disequality
procedures, `arith_entail.cpp`, cardinality, strings-FMF — is worth **1**
(§4.1), and that one is gated on rank 3 anyway.

Rank 9 is the only item I would land unconditionally: it is a fold, it is
independent of every other row, and it is 1 file for near-zero work.

## 9. What I did not measure

- **Anything outside these 66 files.** No off-tree corpus (`/nas3` not consulted),
  no SMT-LIB `QF_S`/`QF_SLIA` benchmark suite, no cvc5 head-to-head timing.
- **Whether cvc5 actually decides these 66.** The `:status` values are cvc5's own
  declared expectations, which is why "cvc5 would decide it" is stated only where
  I can name the rule or inference id in its source.
- **The pre-existing `corpus/regression/cvc5/qf_s/` directory** beyond the two
  files carrying `re.all` / `re.comp` (§5).
- **Whether widening the int-blast width would decide §4.1/4.3/4.4.**
  `SolverConfig` exposes no int-width knob (`backend.rs:99-143`), so this was not
  testable without changing solver behaviour, which the Phase 3 brief forbids.
- **The full `corpus_regression` gate** (§6).
- **Any `push`/`pop` script.** P2.5 excluded scoped scripts from vendoring, so
  the incremental string routes are untouched by this measurement.

## 10. How small the denominator is

**66 files. Say it out loud before quoting any number here.**

cvc5's own `test/regress/cli` carries **602** unique `.smt2` files under a
`strings` or `seq` path (`find test/regress/cli \( -path '*strings*' -o -path
'*seq*' \) -name '*.smt2' | sort -u | wc -l`, clone commit
`1689f1333…`). We vendored **11.0 %** of it, and P2.5's selection filter
excluded scoped scripts, multi-`check-sat` scripts, quantified scripts and
ambiguous-status scripts — so the sample is not random within that 11 %.

What that means for this recommendation:

- The **DO NOT BUILD** call is robust, because it does not rest on a rate. It
  rests on a structural fact: 39 of 43 files never reach a strings solver, so no
  amount of solver work can move them. Adding files cannot lower 39 below 39;
  it can only add more of both kinds.
- The **rank order in §8 is not robust.** It is 43 observations spread over ten
  buckets, several with 1–3 members. Do not schedule work off those counts.

**What would make §8 solid:** the same sweep over ~250+ files — either the rest
of cvc5's 602 (relaxing P2.5's scoped/quantified exclusions, which the
incremental corpus path can now absorb) or the SMT-LIB `QF_S`/`QF_SLIA`
divisions. The instrument in §7 scales unchanged; the cost is vendoring and
licence review, not measurement. Re-run the §3 taxonomy at that size before
committing to rank 1 over rank 4.

## 11. Scaffolding

None left. A throwaway `axeyum-bench` example was used to capture the per-file
parse-error strings and was deleted; §7 reproduces the split from committed
tooling alone.
