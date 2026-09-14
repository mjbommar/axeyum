# Lane: inst-select — the instances are e-matchable, and we already build them

<!-- plan-section: lane-status -->

**Lane inst-select (`DONE`, inst-select, 2026-09-13).** [ADR-1995] closed the
budget question at 0 of 87 and handed over *"the vein is instance selection, not
clock."* This lane was briefed to test that, and specifically to test whether the
instances a `UFLIA`/`UFNIA` refutation needs are out of e-matching's reach at any
budget — the named suspicion being that enumerative or model-based instantiation
over small domains is the missing capability. **It is not, and the census says so
without depending on our own instrumentation at all.**

**The reference ablation.** cvc5 1.3.4 on all 129 winnable rows, 24 s / 8 GiB /
one pinned core, in four arms. **Of the 115 files cvc5 decides, e-matching alone
(`--no-enum-inst --no-cegqi`) decides 111 the same way — 97 %, Wilson 95 %
`[91 %, 99 %]`** (`UFLIA` 66/66, `UFNIA` 45/49). And **0 of 115 need the
combination**: every file is decided with e-matching alone or with e-matching
switched off entirely. The four `UFNIA` exceptions are all `2019-Zohar-ic` and
all refute under `--no-e-matching`.

Both levers are shown live by MECHANISM rather than by verdict counts, because
"5 of 129 moved" is equally what a silently ignored flag looks like: on
`int_check_bvsge_bvneg`, `default` emits 4 instantiation tuples and refutes while
`--no-enum-inst` emits **zero**. All 7 `NONE` rows were re-run and every one is
cvc5's own `--tlimit` firing, not a crash — so they sit outside the denominator
instead of inflating it.

**The brief's exemplar refutes the hypothesis on its own terms.** On
`f2_rw160.smt2` the whole cvc5 refutation runs through the **two** `pow2` lemmas
that carry **no** `:pattern`; every other lemma is fenced behind
`:pattern ((instantiate_me a))` and contributes nothing. And
`pow2_base_cases` writes `(pow2 0)`, `(pow2 1)`, `(pow2 2)`, `(pow2 3)` into the
file **as applications** — so the inferred multi-pattern `{(pow2 i),(pow2 j)}`
has a five-element match set and the "enumeration over small numerals" is a
two-variable join. Reduced to a minimal file with just that lemma and those
applications, **we refute it**; its negative control is refuted by neither us nor
cvc5.

**Where we actually go wrong.** Our own ground dump for that file holds every
application the winning instantiation needs — `(pow2 0)` 1,256 rows, `(pow2 1)`
1,174, `(pow2 2)` 1,174, `(pow2 3)` 1,254. So this is [Q2]'s case (ii), *"we
build it and rank it 1000th"*, and the **opposite** of Q2's `UF` finding where
the term was never built; the two need different fixes. The instances are there
too, instantiated at the wrong class member:

    GROUND 14 gen=1 ... (<= (pow2 (pow2 0)) (pow2 (pow2 1)))

    1,128 rows carrying a nested (pow2 (pow2 …))
        4 instances of the lemma at bare numerals

`InstBridge::repr_term` is `entry(root).or_insert(term)` — **first-inserted, not
smallest** — and it is keyed on the root *as it was at insertion time*, so a
later `merge` leaves one class's term unreachable as a witness. The base equation
`(= (pow2 0) 1)` merges the application with the numeral and we substitute the
application.

**`AXEYUM_QINST_SMALLEST_WITNESS` (ships OFF) fixes that, and decides nothing.**
Same file, both arms: nested `(pow2 (pow2 …))` **1,128 → 500**, lemma instances at
bare numerals **20 → 36**, verdict `unknown` → `unknown`. The mechanism works and
is not what stands between us and these refutations.

### The A/B, and why its one gain is not one

Interleaved per-file, **one binary and two env values**, both arms back to back
on the same file on the same pinned physical core with the order alternating,
24 s wall / 8 GiB `ulimit -v`, 6 shards on s5 and s6. Branch `1a9054710`;
`git merge-base main HEAD` is `2611e14b0`, which **is** `main`'s HEAD, so the
base arm is the shipped tree.

| division | n | base | arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| `UFNIA` | 200 | 53 | 53 | **+0** | 0 | 0 | 0 |
| `UFLIA` | 200 | 72 | 73 | **+1** | 1 | 0 | 0 |
| `UF` *(control)* | 200 | 89 | 89 | **+0** | 0 | 0 | 0 |

`UFNIA`'s base of 53 reproduces the pinned board and [ADR-1995]'s figure exactly.

**Soundness, with the comparable denominator on the same line ([ADR-1957]):**

    UFNIA  vs :status 14/14 base, 14/14 arm
    UFLIA  vs :status 72/72 base, 73/73 arm
    UF     vs :status 87/87 base, 87/87 arm
    DISAGREEMENTS: 0.  sat<->unsat flips: 0 in 1,200 solves.

**The control is not vacuous, and the number saying so is published rather than
asserted.** Of `UF`'s 110 undecided rows, `q:mbqi` — the rung this loop runs
under — binds **40**, and `q:egraph` another **13**; 16 of the 200 rows run the
instantiation loop far enough to dump a ground set. The route runs on the
control, and the control is flat.

**Then the `UFLIA` division was run three independent times, and the +1
evaporated.**

| pass | base | arm | net |
|---|---:|---:|---:|
| 1 | 72 | 73 | +1 |
| 2 | 75 | 73 | **−2** |
| 3 | 74 | 74 | +0 |

    base-arm totals 72 / 75 / 74   BAND 3 files
    arm totals      73 / 73 / 74   BAND 1 file
    files that disagree with THEMSELVES across passes: base 3, arm 2

Three rows move in at least one pass. **All three are UNSTABLE; there is not one
STABLE-GAIN and not one STABLE-LOSS**, and no row is ever decided differently by
the two arms:

| row | base ×3 | arm ×3 | verdict |
|---|---|---|---|
| `sledgehammer/…/smtlib.1057395` | unknown ×3 | unsat, unknown, unsat | **UNSTABLE** — this is pass 1's "+1" |
| `simplify/javafe.parser.TokenQueue.576` | unknown, unsat, unsat | unknown ×3 | **UNSTABLE** — one of pass 2's "losses" |
| `sledgehammer/FFT/smtlib.1015458` | unknown, unsat, unknown | unknown ×3 | **UNSTABLE** — the other |

A single pass would have reported `+1` on pass 1 and `−2` on pass 2 from the same
code. **The measured result is +0**, against a base band of 3 files that a
one-pass A/B cannot see.

**The cost is real and is reported whether or not it is convenient.** The arm
scans the witness pool per bound variable per joined substitution:

| division | median base ms | median arm ms | total base s | total arm s |
|---|---:|---:|---:|---:|
| `UFNIA` | 22,928 | 22,831 | 3,205.6 | 3,182.2 |
| `UFLIA` | 20,127 | 21,329 | 2,858.4 | 2,932.0 |
| `UF` | 12,719 | 13,925 | 2,605.3 | 2,735.8 |

On `UF` the arm is **+5.0 %** of total wall. That is the mechanism behind the
instability rather than an aside: `smtlib.1015458` decides in 2,112 ms under the
base arm in one pass and spends 21,926 ms under the arm, so a scan cost of this
shape converts near-boundary decisions into timeouts — which is exactly what a
row that churns looks like.

**Target-division gain rate 0/400 after re-checking, Wilson 95 % `[0.0 %, 0.9 %]`.**

**What the next lane should look at:** not reach, but what happens *after*
admission. The exemplar reports `ematch retried residual=true instantiated=false`
and prints no fixpoint line at all — killed at a round head — while the final
ground check is handed a set whose own code calls it a wall. This lane does not
claim to have sized that.

**Do not size a lane against enumerative instantiation on this population**: it
would be aimed at 4 files of 115, and cvc5's `--no-e-matching` arm decides those
four anyway.

## Method notes worth keeping

- The winnable list is a snapshot from `c281a4b22`; this base is 28 commits
  later, so it was **re-derived**: 127 of 129 still undecided here. One of the two
  that are not is `z3.885941`, [ADR-1995]'s only file that churns across
  same-arm noise runs.
- `--dump-instantiations` prints what cvc5 **produced**, not a minimised set it
  **needs**, so the bucket census measures a **superset**: a small N is strong
  evidence, a large one weak.
- **Bucket N is contaminated by arithmetic normal form** — cvc5 prints
  `(+ -1 (typeof S))` where the source writes `(- (typeof S) 1)`. 727 of 2,544 N
  terms (28.6 %) have an arithmetic head; the bucket is published both ways.
  On `2019-Preiner` the split is **Q = 32, G = 0, N = 0, S = 9** — N is empty on
  the family the hypothesis came from.
- A `${VAR:+NAME=value}` command prefix is **not** an assignment: bash decides
  that before it expands. It became the command name and all 61 `UFNIA` rows came
  back `rc=127` / `NONE` in a well-formed TSV that reads exactly like a hard
  division. `ours-run.sh` now probes one file for a verdict before the sweep.
- Explicit `:pattern` is a **per-family** property, not a division one: of the
  quantifiers cvc5 instantiates, `vcc-havoc` 279/375 and `spec_sharp` 199/224
  carry one, against **0 of 1,446** for `sledgehammer`/`simplify`/`grasshopper`.

## Branch point

Branched at `76f4f22c6`, fast-forwarded to local `main` `2611e14b0` before any
work. `git merge-base main HEAD` is `2611e14b0`, which **is** `main`'s HEAD, so
the base arm measures the tree that ships.

## Compute

s5 core pairs `1,9` `3,11` `5,13` and s6 `1,9` `3,11` `5,13` — 6 of the fleet's
12, the brief's cap. All of s7 and both `6,14` pairs left free.

<!-- plan-section: landed-changes -->

| 2026-09-13 | inst-select | [ADR-1995] closed the budget question at **0 of 87** and handed over *"the vein is instance selection, not clock"*. This lane tested the named suspicion behind it — that a refutation may need terms **pure e-matching structurally cannot generate**, so the missing capability is enumerative or model-based instantiation — and it **does not survive**. A **reference ablation** answers the capability question without our own instrumentation: of the **115** winnable `UFNIA`/`UFLIA` files cvc5 decides, `--no-enum-inst --no-cegqi` decides **111 the same way — 97 %, Wilson 95 % `[91 %, 99 %]`** (`UFLIA` 66/66, `UFNIA` 45/49), and **0 of 115 need the COMBINATION** — the four exceptions all refute under `--no-e-matching`. Both flags are shown live by MECHANISM (`default` emits 4 instantiation tuples and refutes where `--no-enum-inst` emits **zero**), because "5 of 129 verdicts moved" is equally what a silently ignored flag looks like. The brief's own exemplar refutes its hypothesis: `f2_rw160`'s refutation runs entirely through the **two `pow2` lemmas carrying NO `:pattern`** while the `:pattern ((instantiate_me a))` fence contributes nothing — and `pow2_base_cases` writes `(pow2 0)`, `(pow2 1)`, `(pow2 2)`, `(pow2 3)` into the file **as applications**, so "enumeration over small numerals" is a two-variable multi-pattern over a five-element match set. Reduced to a minimal file, **we refute it** (negative control refuted by neither us nor cvc5). Our own ground dump holds every application needed — `(pow2 0)` 1,256 rows, `(pow2 3)` 1,254 — so this is **[Q2]'s case (ii), "we build it and rank it 1000th", the OPPOSITE of Q2's `UF` finding**, and the two families need different fixes. The defect is located: `InstBridge::repr_term` is `entry(root).or_insert(term)` — **first-inserted, not smallest** — and is keyed on the root **as it was at insertion time**, never repaired when a later `merge` re-roots the class, so `(= (pow2 0) 1)` makes us substitute the application and build `(pow2 (pow2 0))`: **1,128 nested rows against 4 instances at bare numerals**, a ~280:1 dilution. `AXEYUM_QINST_SMALLEST_WITNESS` (**ships OFF**) fixes exactly that — nested rows **1,128 → 500**, useful instances **20 → 36** — and **decides nothing**: `UFNIA` +0, `UFLIA` +1, `UF` control +0 with the route binding **40 + 13** of its 110 undecided rows; three `UFLIA` passes give **+1 / −2 / +0**, base band **3 files**, and **all 3 moved rows are UNSTABLE — zero STABLE-GAIN, zero STABLE-LOSS**, 0 disagreements and 0 sat↔unsat flips in 1,200 solves. **Measured +0, Wilson `[0.0 %, 0.9 %]`**, and the arm costs **+5.0 %** wall on `UF`. So the vein is selection rather than clock, but **not because we cannot reach the instances** — we reach, build and admit them; **do not size a lane against enumerative instantiation on this population**, it would be aimed at 4 files of 115. Bucket N is published BOTH ways because it is contaminated: cvc5 prints `(+ -1 (typeof S))` where the source writes `(- (typeof S) 1)`, and **727 of 2,544 N terms (28.6 %) have an arithmetic head**; on `2019-Preiner` the split is **Q=32, G=0, N=0, S=9**. Numerals are only **12.7 %** of distinct instantiating terms, and the explicit-`:pattern` shape is a **per-family** property (`vcc-havoc` 279/375, `spec_sharp` 199/224 against **0 of 1,446** for `sledgehammer`/`simplify`/`grasshopper`), not a division one. ADR-2005 |

[ADR-1995]: ../../research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-1957]: ../../research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[Q2]: ../../research/03-measurements/does-the-required-instance-enter-our-egraph-2026-09-10.md
