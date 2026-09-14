# ADR-2040: the reach half is worth two, and the whole remaining shape is the ground checker

Status: accepted
Index-summary: [ADR-2025]'s skeleton rung left four `UFNIA` rows `RUNG-NEVER-REACHED` at `fd:parse`, and asked where else the shape is. Both are answered, and the second answer relocates the problem. **The `fd:parse` label is TWO causes**: over 200 `UFNIA` files with verdicts re-derived in the same run, 7 of 147 undecided rows stop there — **5 `ResourceLimit`** (`distinct` over the pairwise cap, whose linear encoding [ADR-2000] built and shipped `Off`) and **2 `Error`**, a **name-capture bug**: `apply_op` tries every theory-operator arm before consulting `arena.find_function`, so `(declare-fun fp (Int Int Int) Int)` in a `UFNIA` script is read as an IEEE literal constructor and dies at ingest in 25 ms of a 24 s budget, though `UFNIA` has no FloatingPoint theory and both z3 and cvc5 accept it — **180 files corpus-wide, all `UFNIA`, zero elsewhere**, and two independent methods agree on the 7. A static instrument over **all 655 undecided Tier 1 rows** (no axeyum binary: abstract offline, ask cvc5 **and** z3, **0 disagreements at 514 comparable rows**) finds the shape on **13**, and **six are `AUFLIRA`**, a division on nobody's list — against `UFNIA` 5, `UF` 1, `UFLIA` 1, `AUFDTLIRA` 0, `UFDTLIRA` 0, and `QF_NIA` **116/116 absent** (quantifier-free: the abstractor's negative control), with 6 of 6 known positives reproduced as the positive one. It also splits [ADR-2025]'s single `ABSTRACT-FAIL` bucket into a genuine ABSENT (116) and NOT MEASURED (25, quantifiers inside `define-fun` bodies). The reach fix is [ADR-2000]'s existing lever plus this bug fix in front of [ADR-2025]'s existing rung — a composition untestable until yesterday, because a file refused at INGEST reaches neither the ladder [ADR-2000] blamed nor the rung that skips it. Measured interleaved, **one binary two env values**, 8 pinned pairs: **`UFNIA` +2 of 200, 0 losses, 0 flips, both gains EXPLAINED with `q:bool-skeleton` `decided`**, 2/2 STABLE-GAIN over three passes per arm, **0 authority disagreements at a full 2/2 comparable denominator** on `:status`/z3/cvc5, against a same-arm noise floor of **0 of 200**. **All seven rows lose the ingest refusal and reach the ladder**; five then spend the budget elsewhere. The decisive number is the follow-up: with reach fixed, all 13 rows reach the rung and split **11 CAPABILITY-LIMIT / 2 CONVERTED / 0 BUDGET-LIMIT / 0 RUNG-NEVER-REACHED** at 24 s **and** at 5x — so the reach question is CLOSED and was worth exactly 2, a budget lever buys nothing, and **the entire remaining shape is the ground checker refusing a quantifier-free query two independent solvers refute**, the component [ADR-2020] left open. Pre-registered R9 was ≥ 5 net; **+2 does not meet it, so the lever ships `Off`** — and the ADR separates that from the correctness question it does not decide, since the `fp` capture rejects 180 legal scripts. The control is reported **WEAK**: its only candidate row is a `let`-binding site [ADR-2000]'s polarity walk declines (the remaining 47 of 356). Three instruments were wrong and each was caught by a control rather than by reading: the operator-name extraction swept `apply_parameterized` and reported 59 shadowed files when 57 were `is`, which shadows nothing; the mutation suite's arity guard **SURVIVED** because the fixture tested too FEW arguments and `zip` stops at the shorter side; and `EXPLAINED` matched a base `Timeout`, labelling the control's own timing gain as the lever's.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2025] shipped the one lever that worked this week — a `q:bool-skeleton`
rung that abstracts every maximal quantified subformula to one opaque Boolean
atom and refutes the quantifier-free remainder, worth **+12 on `UFLIA`** on
merged `main`. It left two questions open, and this lane takes both rather than
opening an eleventh hypothesis about the quantified gap.

1. **Why does the ladder stop at `fd:parse` on `UFNIA`?** Four of [ADR-2025]'s
   fifteen skeleton-unsat rows were `RUNG-NEVER-REACHED`, all `UFNIA`, which is
   now the largest remaining Tier 1 gap.
2. **Where else does the skeleton shape exist, and why did only `UFLIA` move?**
   Absent, present-but-not-reached, or present-and-reached-but-not-refutable —
   three different findings with three different follow-ups.

Branch base: `git merge-base main HEAD` is
`b32867a21b37dcb0f12c75d81557c8eabf6b25a4`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/skeleton-reach-20260914/PREREGISTRATION.md)
in their own commit (`3dda4bba8`) before any lever or any measurement existed.

## 1. `fd:parse` on `UFNIA` is 7 of 147, and the label is two causes

All 200 `UFNIA` files, run with the route trail on, verdicts **re-derived in
the same run** (R4 — [ADR-2035] found 8 of 22 censused "declining" files were
decided anyway). 147 undecided, matching the `tier1-current` sample exactly.

`bound_by` over the undecided:

| route | n |
|---|---:|
| `q:egraph` | 81 |
| `q:mbqi` | 41 |
| `NONE` (no route line at all — the watchdog fired before the worker returned) | 12 |
| **`fd:parse`** | **7** |
| `uf-arithmetic` | 6 |

The pre-registration forbids sizing a bucket by its label (R3), so the raw
give-up detail is carried verbatim per row and bucketed afterwards. It splits:

| kind | n | detail |
|---|---:|---|
| `ResourceLimit` | **5** | `` `distinct` with N arguments requires N pairwise expansions; deterministic limit is 65536 `` |
| `Error` | **2** | `parse error: syntax error: fp exponent field must be a bit-vector` |

**The second is a name-capture bug, and a legal SMT-LIB script is what it
rejects.** `apply_op` is one large `match op {…}` whose theory-operator arms
are all tried before the `_ =>` fall-through that consults
`arena.find_function(other)`. These benchmarks carry

    (declare-fun fp (Int Int Int) Int)

`fp` is a FloatingPoint theory symbol; the scripts' logic is `UFNIA`, which has
no FloatingPoint theory, so the name is a legal user symbol there and both z3
and cvc5 accept it. We read the application as an IEEE literal constructor and
die at ingest in 23–26 ms of a 24 s budget.

**Corpus-wide over the seven Tier 1 division directories: 180 files, all
`UFNIA`, zero elsewhere.** The scan's alternation is parsed out of `apply_op`'s
own source rather than typed, and the run asserts the pattern matches the file
that was read by hand before it reports anything — an empty result from a
pattern never shown to match is indistinguishable from a strong negative.

**Two independent methods agree on the 7.** The route-trail census says 5
`ResourceLimit` + 2 `Error`; a static cross-reference of the same 147 rows
against [ADR-2000]'s committed over-cap list and this lane's shadow scan says
5 over-cap + 2 shadowed. Neither derives from the other.

### The operator extraction was wrong the first time, and the control caught it

Reading match arms from `fn apply_op(` to end-of-file also swept
`apply_parameterized`'s INDEXED arms — `is`, `repeat`, `to_fp`, `divisible` —
which are only ever reached for an `((_ name …) x)` head and cannot capture a
bare `(name x)` application. That reported **59** shadowed files; **57 were
`is`, which shadows nothing**. Bounding the scan at
`arena.find_function(other)` — the line below which nothing is tried first —
gives 2. Two asserts now pin both bounds: `fp` must be in the set and `is` must
not.

## 2. The shape outside `UFLIA` is 13 of 655, and six of them are `AUFLIRA`

A static instrument over **all 655 undecided rows** of the seven Tier 1
divisions. No axeyum binary is involved: abstract every maximal quantified
subformula to one opaque atom offline and ask cvc5 **and** z3 whether the
remainder is already unsat. Abstraction only weakens, so `skeleton unsat`
entails `original unsat`, and that is the only direction claimed.

| division | n | ABSENT | NOT MEASURED | PRESENT | **skeleton-`unsat`** | Wilson 95 % |
|---|---:|---:|---:|---:|---:|---|
| `AUFLIRA` | 36 | 0 | 0 | 36 | **6** | `[7.9 %, 31.9 %]` |
| `UFNIA` | 147 | 0 | 25 | 122 | **5** | `[1.5 %, 7.7 %]` |
| `UF` | 106 | 0 | 0 | 106 | 1 | `[0.2 %, 5.2 %]` |
| `UFLIA` | 115 | 0 | 0 | 115 | 1 | `[0.2 %, 4.8 %]` |
| `AUFDTLIRA` | 79 | 0 | 0 | 79 | 0 | `[0.0 %, 4.6 %]` |
| `UFDTLIRA` | 56 | 0 | 0 | 56 | 0 | `[0.0 %, 6.4 %]` |
| `QF_NIA` | 116 | **116** | 0 | 0 | 0 | `[0.0 %, 3.2 %]` |
| **total** | **655** | 116 | 25 | 514 | **13** | |

**0 cvc5/z3 disagreements at 514 comparable rows.**

**R5's positive control**: the same sweep reproduces all six of [ADR-2025]'s
known skeleton-unsat rows that are still undecided, so the zeros on
`AUFDTLIRA` and `UFDTLIRA` are measured rather than an instrument that never
worked. `QF_NIA` at 116/116 `ABSENT` is the negative control: it is
quantifier-free, so every row must abstract nothing, and every row does.

**This splits a bucket [ADR-2025] reported unsplit.** Its instrument called
every `occ=0` row `ABSTRACT-FAIL`. That string covers two different findings:
`occ=0` with **no `forall`/`exists` token anywhere** is a genuine ABSENT, while
`occ=0` with the quantifiers inside `define-fun` **bodies** — which the
text-level tool refuses to abstract, because a fresh constant cannot track a
function *parameter* — is NOT MEASURED, and the limit there is the
diagnostic's, not the solver's. The two are 116 and 25 respectively and they
are not the same claim.

**`AUFLIRA` was on nobody's list.** It is the division `tier1-current` had just
corrected from 4 % to 82 %, and it holds the largest single concentration of
the shape.

## 3. The composition nobody could have measured before yesterday

Each half of the reach fix is worth ~nothing alone, and the only interesting
question is whether they compose with a rung that landed a day later.

* [ADR-2000] measured the linear `distinct` injection encoding on **2026-09-13**
  at **+1 of 356** and shipped it **Off**, concluding "the front-door refusal
  was never the binding constraint; the quantified ladder is, at any budget."
  That was true when it was measured.
* [ADR-2025]'s rung landed **2026-09-14** and **does not enter the quantified
  ladder at all** — it refutes before the first instantiation.
* A file refused at **ingest** reaches neither.

So the pair was untested by construction, and this is not a new lever: it is
[ADR-2000]'s existing one, plus one bug fix, in front of [ADR-2025]'s existing
rung.

The `fp` fix is `crates/axeyum-smtlib/src/parse.rs`: a user `declare-fun`
outranks the theory-operator arm of the same name **when the declared signature
matches the application exactly**. SMT-LIB forbids declaring a symbol already in
the current signature, so a *successful* `declare-fun` is itself the evidence
that the name is not a theory symbol in this script; requiring the parameter
sorts to match makes the redirect a no-op wherever the theory reading was the
applicable one, because an arity or sort mismatch falls straight through to the
arm it would have taken. **Polarity: ships `Off`**, armed by
`AXEYUM_DECLARED_NAME_WINS=on`.

Registered with `mutation_controls.py` as `smtlib-declared-name-wins`.
**Its first run found a real hole:**

| guard | first run | after |
|---|---|---|
| the lever's opt-in polarity | killed 2 | killed 2 |
| the arity half of the signature test | **SURVIVED** | killed 1 |
| the sort half of the signature test | killed 1 | killed 1 |

The arity guard survived because the fixture tested too **few** arguments, and
`zip` stops at the shorter side — so relaxing `==` to `<=` still rejected it.
Only the too-**many** case is load-bearing, because that is the one where a
prefix match silently redirects. The polarity guard kills 2, and both of those
tests legitimately depend on the shipped polarity.

## 4. The A/B

Interleaved per file, **one binary, two env values**, both arms back to back on
the same pinned core with the order alternating per row. **Shard configuration
held fixed across every phase**: s5 cores `{1,3,5,7}` and s6 cores `{1,3,5,7}`,
**eight pinned pairs and never more**, with both arms inside each shard so a
shard cannot move one arm relative to the other. Files go to shards
round-robin, never in contiguous blocks. 24 s budget.

**Polarity, stated because the three levers in play do not agree with each
other:** `AXEYUM_DECLARED_NAME_WINS` ships **Off** and `on` arms it;
`AXEYUM_DISTINCT_LINEAR` ships **Off** and `on` arms it;
`AXEYUM_ZERO_INST_SKELETON` ships **On** and `0` kills it, and it is left at
its shipped value **in both arms** — it is not a lever here, it is the thing
being reached.

`ab-preflight.sh` asserts the arms differ **by mechanism** before any
measuring, and fails if the base does not stop at `fd:parse` or if the arm
still does:

    arm base  bound_by=fd:parse        unknown  giveup=fp exponent field must be a bit-vector
    arm arm   bound_by=q:bool-skeleton unsat    103 ms

| run | rows | base decided | arm decided | net | GAIN | LOSS | FLIP | wall |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| **treatment** `UFNIA` | 200 | 53 | **55** | **+2** | 2 | **0** | **0** | 1.03x |
| **noise floor** (both arms base) | 200 | 53 | 53 | **0** | 0 | 0 | 0 | 1.00x |
| control `QF_NIA` | 200 | 84 | 84 | **0** | 1 | 1 | **0** | 1.01x |

Gain 2 of 200, Wilson 95 % `[0.3 %, 3.6 %]`, against a same-arm band of
**0 of 200**, `[0.0 %, 1.9 %]`. **Both gains carry `q:bool-skeleton` `decided`
in the arm's trail and lost the base's ingest give-up**, so the summarizer
labels them `EXPLAINED`; it labels a gain the lever cannot have caused
`UNEXPLAINED` and names it, and on the treatment there are none.

### The control's zero is honest, and the control is WEAK — here is which

`QF_NIA` was chosen because a static cross-reference says exactly one of its
116 undecided rows carries an over-cap `distinct`, so the lever has somewhere
to fire. It moves **0 net**: one gain and one loss, both `UNEXPLAINED` by
construction (the gain is `unknown → sat` at 23,962 ms of a 24 s budget with
the rung **absent** and a base give-up of `Timeout`; that is the machine, not
the lever).

**But the lever FIRED on 0 of its 200 rows, so the zero is a weak control and
this ADR says so rather than banking it.** Probing the one over-cap row
directly says which kind of weak:

    file   QF_NIA/20210219-Dartagnan/ReachSafety-Loops/array_3-1-O0.smt2
    base   bound_by=fd:parse  unknown  `distinct` with 16525 arguments …
    arm    bound_by=fd:parse  unknown  `distinct` with 16525 arguments …

The site **exists** and the lever **declines** on it. That is [ADR-2000]'s
polarity walk, which admits 309 of 356 over-cap sites; the `Dartagnan` family
sits in a `let` **binding**, where the polarity of the bound name's uses is not
resolved and a fresh symbol would not be sound. So the control is weak because
the lever's own scope excludes its only candidate — not because nothing was
there, and not because the measurement was never taken.

**That is also a finding of its own**: the remaining 47 of 356 over-cap sites
are `let`-binding-positioned, and nothing in this lane or [ADR-2000] resolves
them.

### The attribution label was wrong once, and the control is what caught it

`EXPLAINED` was first spelled `base_giveup != "none"`. The control's timing
gain — `Timeout` in the base, no give-up in the arm, rung **absent** — matched
it and was printed as `EXPLAINED`. A gain this lever cannot have caused was
wearing the lever's name. It now requires the base give-up to be an **ingest**
refusal (`ResourceLimit` or `Error`), which is the only thing the lever acts
on. The treatment's two gains are unaffected; the control's one is now
correctly `UNEXPLAINED`.

**The noise-floor runner is the same script under a `phase` switch**, and
`ab-verify-noise.sh` checks by reading the runner that the noise branch calls
the base runner and *returns* before the armed `env` is reachable. It is
**mutation-verified**: exit 0 on the real runner, exit 1 when the noise branch
is armed. [ADR-2025]'s first attempt to derive a noise floor by `sed` silently
failed to substitute one branch, which would have produced a second copy of the
real A/B still labelled a noise floor.

**R5 — three passes per arm on both moved rows: 2 of 2 STABLE-GAIN**, zero
UNSTABLE and zero FLIP. [ADR-2005] got +1 / −2 / +0 from three passes of
byte-identical code, so one pass would not have been evidence.

**R6 — the two new verdicts against three independent authorities: 0
disagreements at a comparable denominator of 2/2 on each** of declared
`:status`, z3 and cvc5. No authority abstained, so the zero is six agreements
rather than six no-opinions.

**R12 — the A/B binary is the committed tree.** Two lint-only edits landed
after the build (an `#[allow]` block that the new function had displaced, and
two missing doc backticks). A fresh build from the committed tree is
**byte-identical** to the binary the A/B ran, checked with `cmp`, so the
measurement did not need repeating and that is a measurement rather than an
assumption.

### Reporting only the +2 would hide that the mechanism fired seven times

| base cause | base | arm | arm rung | arm give-up |
|---|---|---|---|---|
| `Error` | unknown | **unsat** | **decided** | none |
| `ResourceLimit` | unknown | **unsat** | **decided** | none |
| `Error` | unknown | unknown | declined | `ResourceLimit` |
| `ResourceLimit` ×4 | unknown | unknown | declined | `Watchdog` |

**All seven lose the ingest refusal and reach the quantified ladder** — the
rung goes from `absent` to `declined` or `decided` on every one. Two convert in
60 ms and 130 ms. On the other five the budget then goes somewhere else.

## 5. With reach fixed, the entire remaining shape is CAPABILITY

The 13 skeleton-unsat rows, both reach levers armed, each run at the A/B budget
and at **5x** it — the pairing that separates a capability limit from a budget
one:

| | n | what it means |
|---|---:|---|
| **CAPABILITY-LIMIT** | **11** | declines at 24 s **and** at 120 s. Our ground checker cannot refute a skeleton that cvc5 **and** z3 both refute |
| CONVERTED | 2 | |
| **BUDGET-LIMIT** | **0** | |
| **RUNG-NEVER-REACHED** | **0** | |

**Both zeros are the useful part.** `RUNG-NEVER-REACHED` was 4 before this lane
and is 0 after it, so **the reach question is closed and it was worth exactly
2**. `BUDGET-LIMIT` at 0 says the rung's one-tenth budget share is not what
binds — the same shape [ADR-2025] measured, now confirmed at 5x on a wider
population, so a budget lever here buys nothing.

The 11 split `AUFLIRA` 6, `UFNIA` 3, `UF` 1, `UFLIA` 1. **This is the cleanest
possible statement of the ground-checker gap**: a quantifier-free query, no
instantiation, no admission bound, refuted by two independent solvers and not
by us — and it is the same component [ADR-2020] left open.

## 6. Decision

**R9 was pre-registered at ≥ 5 rows net with 0 losses, 0 flips, every moved row
STABLE-GAIN, and 0 authority disagreements. The measured value is +2.** It
meets every condition but the threshold, so **by the lane's own rule the
combination does not ship ON as a gain lever**, and `AXEYUM_DECLARED_NAME_WINS`
stays `Off` alongside `AXEYUM_DISTINCT_LINEAR`.

**Two things that rule does not decide, stated rather than folded in.** R9 was
written for a gain lever, and the `fp` capture is a *correctness* defect: we
reject 180 legal SMT-LIB scripts. Whether a rejection-of-a-legal-script bug
ships on a row count is a different question from whether a search heuristic
does, and this ADR does not answer it — the fix is landed, tested,
mutation-verified and measured, behind a lever, for whoever does. Second, the
+2 is on a **200-file sample**; the class is 180 files corpus-wide, so the
sample rate is not the corpus rate and R1 forbids transferring it.

**Predicted post-merge value: no division total moves.** Both levers ship
`Off`, so the shipped default is byte-for-byte the behaviour `tier1-current`
measured. That is a prediction about a no-op, and the reason it is worth
stating is that the *code* changed and the *behaviour* did not.

## 7. The rules that were pre-registered, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | no conversion RATE pre-registered or inherited | [ADR-2025]'s 8/9 and 15/129 were not transferred; §2's rates are measured on the population they are reported for, and §6 refuses to transfer the +2 to the corpus |
| R2 | every bucket with its denominator, zeros included, NOT-MEASURED separate | §1, §2 and §5, including 25 NOT MEASURED, 0 BUDGET-LIMIT and 0 RUNG-NEVER-REACHED |
| R3 | the `fd:parse` label is not trusted until split | split into 5 `ResourceLimit` + 2 `Error` by the raw detail, and cross-validated by an independent static scan |
| R4 | population re-derived on the current tree, in the same run | 147 of 200, matching `tier1-current` exactly |
| R5 | "shape absent" needs a positive control in the same sweep | 6 of 6 known positives reproduced; `QF_NIA` 116/116 is the negative control |
| R6 | three authorities, comparable denominator beside any zero | 0 disagreements at 2/2 on each |
| R7 | Wilson 95 % for every small-n proportion | §2 and §4 |
| R8 | interleaved, one binary two env values, polarity stated, 3x per arm, noise floor, non-vacuous control | §4 — except the control, which is **WEAK and reported as weak**: the lever's only candidate row on `QF_NIA` is a site [ADR-2000]'s polarity walk declines, so the zero is honest but not load-bearing. The noise checker is mutation-verified |
| R9 | ship ON only at ≥ 5 net, all STABLE-GAIN, 0 loss/flip/disagreement | **+2** → does **not** ship ON |
| R10 | unfinished checks reported as "did not run" | §8 |
| R11 | the A/B measures THIS BRANCH; post-merge value predicted with a reason | §6 |
| R12 | freshness licensed by `find -newer`, not exit status | both builds passed it, and the A/B binary is `cmp`-identical to a rebuild of the committed tree |
| R13 | the abstractor's liveness is a measured column | `occ`/`atoms` per row; `occ=0` split into ABSENT and NOT MEASURED |
| R14 | no waiter greps for a process by a pattern its own command line contains | every waiter watches an artifact |

**The pre-registered predictions, against what happened:**

| | predicted | measured |
|---|---|---|
| **P1** | the `fd:parse` bucket is not one cause | **right** — 5 `ResourceLimit` + 2 `Error`, and the larger part is not an ingest *failure* but a deliberate resource refusal |
| **P2** | between 5 and 60 of the 147 | **7** — inside, at the low end |
| **P3** | ≥ 1 skeleton-unsat row on at most two divisions besides `UFLIA`; absent on `QF_NIA` | **half wrong** — three (`AUFLIRA`, `UFNIA`, `UF`), and `AUFLIRA` holds the most of any division. `QF_NIA` absent, 116/116 |
| **P4** | `UFLIA`'s remaining undecided rows still contain skeleton-unsat files | **right** — 1, and it is a CAPABILITY-LIMIT |
| **P5** | under 15 additional convertible rows across the six non-`UFLIA` divisions | **12 skeleton-unsat, of which 1 converts.** Right on the number and wrong on what it buys: the shape being present is not the same as it being convertible, and §5 is why |

P1's second clause was wrong in the more useful direction: the predicted
"dispatch-level stop whose trail was never mirrored" is not what the larger
bucket is. It is a deliberate, correct resource refusal with a lever already in
the tree.

## 8. Not measured here, and reported as "did not run"

- **The 25 `NOT-MEASURED-DEFINE-FUN` `UFNIA` rows were never measured for
  skeleton satisfiability.** They are excluded from the 13, not counted against
  it. Inside axeyum the parser has already expanded such definitions, so a
  solver-side probe could measure them and this lane did not build one.
- **The 12 undecided `UFNIA` rows with `bound_by=NONE`** — no route line at
  all, because the watchdog fired before the worker thread returned — are
  **unsplit**. That is the second-largest unexplained bucket in §1 and nothing
  here touches it.
- **The corpus-wide value of the `fp` fix is not measured.** 180 files carry the
  shape; 2 are in the 200-file sample. The other 178 were not run.
- **The 11 CAPABILITY-LIMIT rows were not diagnosed further.** Why our ground
  checker declines a skeleton two other solvers refute is the next question and
  is not answered here.
- **`AUFLIRA`'s 6 were not re-run 3x**, because none of them moved; they are
  reported as declines, not as gains.

[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2005]: adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
[ADR-2020]: adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2025]: adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md
[ADR-2035]: adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
