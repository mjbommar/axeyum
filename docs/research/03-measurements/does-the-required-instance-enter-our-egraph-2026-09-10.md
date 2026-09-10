# Does the required instance ever enter our e-graph?

**Date:** 2026-09-10
**Lane:** Q2-groundset
**Population:** `bench-results/parity-losses-20260908/UF.txt` — the 32 declared-status
UF files we return `unknown` on and z3 refutes. NAS mount was live
(`/nas3/data/axeyum/corpus/`); nothing here reproduces without it.

## The question

`why-the-instantiation-loop-produces-nothing-2026-09-10.md` measures that
**41.1% of all universal-rounds (8,219 of 19,975) have a trigger pattern present
that matched NOTHING in the e-graph** — its category B — and names the decisive
follow-up it did not run. `why-z3-refutes-and-we-do-not-2026-09-10.md` says the
same thing in its own "What I did not measure": *whether the required term ever
enters our e-graph* is **not** separated for the S class, and doing so "needs a
dump of the loop's ground set and a structural match against the proof's
instance terms".

That splits two situations which need completely different fixes and are
otherwise indistinguishable:

- **(i) We never build it.** No ranking, budget or cap change could ever help.
- **(ii) We build it and rank it 1000th.** A selection problem, and fixable.

This note runs that experiment.

## The answer

**Of the 16 files where both sides can be attributed, the required term is
absent from our ground set on 10 and present on 6.** The majority answer is
**(i): we never build it.** Raising a cap, a budget or a ranking cannot reach
those 10, because the term being ranked does not exist.

But (i) here does **not** mean "far away". **66 of the 71 arguments (93%) of the
absent terms are already in our ground set.** We hold the arguments, and we hold
the Skolem function symbols. We never form the application. This is a term
**construction** gap, one function application wide — not a search-depth gap.

The 6 (ii) files sharpen the same point from the other side. On four of them
(`f14`, `f15`, `f22`, `f26`) **every required term is at generation 0 and within
the first 181 rows** of a 4,269–14,688-row ground set — available from
essentially the first instant — and we still return `unknown`. Where selection
*is* the whole story, selection is failing on terms that were never hard to find.

## Method

### Population and replication

`z3 -T:24` on all 32 reproduces the earlier split exactly: **18 `unsat`, 14
`timeout`**. Proofs (`(set-option :produce-proofs true)` first, every `(exit)`
stripped — the corpus files end with one, which silently swallows `(get-proof)`
— and `(get-proof)` appended, then `z3 -T:120`) come back for **17 of the 18**;
`f23` solves in 0.01 s without proofs and times out at 120 s with them, so it is
**unattributed** and excluded, exactly as before.

**Positive control on the extractor.** z3 shares proof structure aggressively
with nested `let`, and the proof STEPS themselves are let-bound, so a
quant-inst application is normally found inside a binding value rather than in
the body. The extractor walks bindings and body alike with the let environment
in scope and fully expands. Its per-file step counts — 2, 3, 10, 4, 2, 5, 93,
15, 9, 6, 4, 2, 4, 2, 9, 6, 4 — **match the earlier note's `z3 qinst` column on
all 17 files**, and it resolves terms that note left as unexpanded `?x` names
(e.g. `f27`'s `(f10 ?x66)` is `(f10 (f7 f8 (f9 f24)))`).

`f27` is now **decided `unsat` by our own CLI**, so it never reaches a give-up
point and produces no dump. That is reported as **did not run**, and it is also
a positive control that the routing fix (`318930806`) is live in this tree.

**16 attributed = 18 z3-refuted − `f23` (no proof) − `f27` (we now decide it).**

### Our side: the ground-set dump

`AXEYUM_QGROUNDDUMP=<path>` (added in `f87d0f649`, `qinst_egraph.rs`) writes the
accumulated ground set at **every** point `prove_quantified_unsat_via_egraph_impl`
gives up — both deadline exits, the ground-ceiling exit, and the fallthrough
covering every `break` including the fixpoint. Rows carry each formula's
generation and are emitted in `ground` insertion order, which is deterministic.

Run as `AXEYUM_QGROUNDDUMP=… target/release/examples/axeyum_cli <file>
--timeout-ms 24000`, four at a time, at the budget the loss list was produced at.
All 16 return `unknown`.

**Cross-tool control.** The earlier note measured its per-file ground counts
through `smtcomp_cli`; these dumps come from `axeyum_cli`, so the two front
doors could in principle take different routes. Three of its four sub-ceiling
counts reproduce here **exactly**, and all three land on the same block:
`f29` 273, `f31` 424, `f17` 24 — each is this run's **block 1**. That both
confirms the dump is measuring the same loop the earlier note measured and
identifies *which* rung it was reporting (the un-Skolemized one, see below).
Its fourth, `f22` at 2017, does **not** reproduce — this run's blocks are 1191 /
1253 / 1825 — and that discrepancy is unexplained.

**`ground` is the ground FORMULA partition, not a term set** — assertions plus
admitted instances. So the terms a proof instantiates on live in its
**subterms**, and the comparison is against the subterm closure of every dumped
formula, unioned over every give-up point in the run. "Ever enters" is the
question, so the union is the right population.

### How the symbol correspondence was established

Both solvers read the same SMT-LIB file and render uninterpreted applications
with the **source** function names (`f19`, `f28`, …), so every non-Skolem symbol
compares equal on the nose — no renaming is needed or allowed for them. Only the
Skolem symbols each solver invented for itself are matched modulo renaming:

| | |
|---|---|
| z3 | `?v<N>!<M>` — arity 0 from the negated goal, arity > 0 a Skolem **function** of the enclosing binders |
| ours | `!qsk_<n>` / `!qskf_<n>` — constant / function (`quant_skolemize.rs`) |

A z3 Skolem may match **only** a name matching our Skolem pattern. It may
**not** match an ordinary function symbol, and deliberately not the
alpha-renamed bound-variable placeholders `!q.<name>.<n>` or the hoisted
universal variables `!qu_<n>` — both are binders, not ground terms, and matching
them would turn "we still have an open quantifier here" into a false PRESENT.
The map must be well-defined (repeats become backreferences) and **injective**;
a global system-of-distinct-representatives check confirms one consistent
injective assignment exists per file, rather than relying on per-term matching
picking the same head twice.

**The argument-order convention, measured rather than assumed.** A first pass
matched Skolem-function arguments positionally and reported 39 absent terms.
Checking whether any *permutation* of the arguments was present found 11 hits —
and **all 11 are exact argument REVERSAL, zero are any other permutation**.
`quant_skolemize::fresh_skolem` emits the enclosing universal variables in the
opposite order to z3's Skolem applications. That is one systematic convention,
not a licence to permute, and it is applied in the authoritative run. It moved
**`f05` and `f07` from (i) to (ii)** — without this control the counts below
would have been wrong by two files in the direction of the headline.

### The matcher can fail

Thirteen controls, run against the shipped matcher: a ground subterm found; one
argument changed → ABSENT; a Skolem term matched modulo renaming, with the
renaming reported; a z3 Skolem against an ordinary symbol → ABSENT; a Skolem at
the wrong argument → ABSENT; injectivity enforced → ABSENT; an empty proof and
an empty dump each reported as **did not run** rather than a silent 0/0; the
reversed tuple ABSENT in default mode and PRESENT with the convention on;
reversal not rescuing a genuinely different tuple; and a forward tuple going
ABSENT under reversal, so the mode really reverses. **Nine of the thirteen are
negatives.** The first version of the fast matcher failed three of them on a
regex-stitching bug and was fixed before any result below was read.

## The (i) / (ii) split

| id | file | z3 qinst steps | our ground rows | required terms present | absent | answer |
|---|---|---:|---:|---:|---:|---|
| f01 | `bindag/…1094926` | 2 | 24576 | 6 | 1 | **(i) never built** |
| f05 | `coinductive_list/…2416479` | 3 | 15653 | 9 | 0 | (ii) built |
| f06 | `coinductive_list/…2500061` | 10 | 20662 | 4 | 4 | **(i) never built** |
| f07 | `coinductive_list/…2906170` | 4 | 17216 | 12 | 0 | (ii) built |
| f10 | `gram_lang/…1432776` | 2 | 14522 | 4 | 1 | **(i) never built** |
| f12 | `rbt_impl/…992499` | 5 | 24576 | 3 | 4 | **(i) never built** |
| f14 | `instantiated/dl_remove_postcondition_of_dl_remove_50_4` | 93 | 14580 | 10 | 0 | (ii) built |
| f15 | `uninstantiated/dl_copy_invariant_19_2` | 15 | 14688 | 9 | 0 | (ii) built |
| f17 | `Arrow_Order/smtlib.663965` | 9 | 992 | 9 | 3 | **(i) never built** |
| f18 | `Arrow_Order/uf.704291` | 6 | 11969 | 6 | 2 | **(i) never built** |
| f19 | `Arrow_Order/uf.813308` | 4 | 10801 | 3 | 2 | **(i) never built** |
| f22 | `FFT/uf.863296` | 2 | 4269 | 3 | 0 | (ii) built |
| f23 | `Fundamental_Theorem_Algebra/uf.1065126` | — | — | — | — | did not run (no proof) |
| f26 | `Fundamental_Theorem_Algebra/uf.974621` | 4 | 12952 | 5 | 0 | (ii) built |
| f27 | `Hoare/smtlib.1116374` | 2 | — | — | — | did not run (**we now decide it**) |
| f28 | `Hoare/uf.834137` | 9 | 17158 | 10 | 2 | **(i) never built** |
| f29 | `Hoare/uf.966336` | 6 | 3223 | 5 | 3 | **(i) never built** |
| f31 | `TypeSafe/smtlib.1098821` | 4 | 2326 | 10 | 3 | **(i) never built** |

**Counts: (i) 10, (ii) 6, did not run 2, of 18.**
**25 required terms are absent** across the 10 (i) files, out of 133 distinct
required terms across all 16.

Two facts hold with **zero exceptions** across all 16 files:

- **Every one of the 85 required terms containing no Skolem symbol is PRESENT.**
- **Every absent term contains a Skolem symbol.** Of the 25 absent, 22 are a
  Skolem function applied to a compound/ground argument and 3 to Skolem
  constants only.

So the gap is exactly at Skolem-function applications — and specifically at
*which arguments* they are applied to, since `f05` and `f07` show the same
construction succeeding.

### Where the required term sits on the (ii) files

| file | ground rows | deepest required term | its generation |
|---|---:|---:|---:|
| f22 | 4,269 | row **1** | 0 |
| f26 | 12,952 | row **2** | 0 |
| f15 | 14,688 | row **25** | 0 |
| f14 | 14,580 | row **181** | 0 |
| f07 | 17,216 | row 1,195 | 3 |
| f05 | 15,653 | row 4,796 | 1 |

On `f14`, `f15`, `f22` and `f26` **every** required term is generation 0 and
inside the first 1.2% of the ground set. Nothing was ranked 1000th. The terms
were there from the start and the loop still did not close the file — which
makes these four the cleanest possible targets for a selection fix, and says the
selection problem is not primarily one of reach.

## f29 in full — the sharpest reproducer

`Hoare/uf.966336`: 27 assertions, z3 refutes in 0.02 s with 6 quant-inst steps.
The dump is small enough to read completely.

z3's six steps use **8 distinct substitution terms**. Against our ground set:

| term | in ours? |
|---|---|
| `(f19 (f20 f29) f28)` | **PRESENT**, generation 0 |
| `?v1!5` | **PRESENT** as `!sk_0` |
| `f28` | **PRESENT**, generation 0 |
| `f29` | **PRESENT**, generation 0 |
| `(f38 f12)` | **PRESENT**, generation 0 |
| `(?v2!0 (f19 (f20 f29) f28))` | **ABSENT** |
| `(f18 f29 (?v2!0 (f19 (f20 f29) f28)))` | **ABSENT** |
| `(f8 (f13 (f18 f29 (?v2!0 (f19 (f20 f29) f28)))) f26)` | **ABSENT** |

The three absent terms are one chain built on one missing link:
`(?v2!0 (f19 (f20 f29) f28))`.

**What `?v2!0` is, established from the proof itself rather than guessed.**
Step 2's conclusion renders the instantiated universal in z3's own Skolemized
form:

```
(forall ((?v0 S12) (?v1 S6))
  (or (= (f16 ?v1 (f8 (f13 (f30 f31 ?v0)) f26)) f1)
      (not (= (f27 ?v0) f1))
      (not (or (not (= (f6 (?v2!0 ?v1) f28) f1))
               (= (f16 ?v1 (f8 (f13 (f18 f29 (?v2!0 ?v1))) f26)) f1)))))
```

so `?v2!0 : S6 → S2` is the Skolem function for the **inner, negative-position**
`(forall ((?v2 S2)) …)` of the source assertion at line 77, taking the enclosing
`?v1 : S6`. The declared sorts confirm it: `f19 : (S9 S3) → S6`,
`f18 : (S8 S2) → S5`, `f13 : S5 → S7`, `f8 : (S7 S6) → S6`.

**Why the chain is never formed.** The loop is entered three times on this file.
Our dump contains, in the whole run, exactly **one** application of `f18`:

```
GROUND 9 gen=1
(=> (= (f27 !sk_1) f1)
    (=> (forall ((!q.?v2.7 (Uninterpreted 1)))
          (=> (= (f6 !q.?v2.7 f28) f1)
              (= (f16 !sk_0 (f8 (f13 (f18 f29 !q.?v2.7)) f26)) f1)))
        (= (f16 !sk_0 (f8 (f13 (f30 f31 !sk_1)) f26)) f1)))
```

The **outer** universals are instantiated at exactly the right constants —
`!sk_1` is z3's `?v1!5`, and `!sk_0` is the goal's S6 Skolem, which the goal
asserts equal to `(f19 (f20 f29) f28)`, so it is z3's `?v1` up to congruence.
The **inner** universal is still a live `forall` whose binder `!q.?v2.7` is an
alpha-renamed bound variable, not a term. `f18`'s second argument slot never
holds a ground term at all.

Per block, `f18` applications are: **block 0 — 0, block 1 — 1 (the row above),
block 2 — 0.**

`quant_skolemize::walk` handles a negative-position `Forall` correctly (it falls
through to `fresh_skolem`), so the Skolemizer is not the defect. The block
census says what is:

| | block 0 | block 1 | block 2 |
|---|---:|---:|---:|
| rows | 1,172 | 273 | 1,778 |
| rows with `!qskf_` | 1,157 | **0** | 1,763 |
| rows with a live `forall` | 309 | 8 | 511 |
| distinct `!q.` bound variables | 0 | **5** | 0 |

**Block 1 is the UN-Skolemized assertion set**, and this holds on 15 of the 16
files: one of the loop's entries per file is handed assertions that still carry
their binders. That is the `f27` routing shape, still present as a rung on every
file in the slice. It is also expensive — **block 1 floods the full 8,192 ground
cap on 11 of the 16 files** (`f01`, `f05`, `f06`, `f07`, `f10`, `f12`, `f14`,
`f15`, `f18`, `f19`, `f26`), spending the entire ground budget on a set that
cannot contain a Skolem term because it has none.

Meanwhile the Skolemized blocks (0 and 2) admit almost nothing from that
assertion: 2 rows mentioning `f30` and 3 mentioning `f16`, against 231 and 112
in the un-Skolemized block. **Both routes fail, for different reasons, and
neither builds the term.**

## What a fix would have to do — and the number that moves

Not "the ranking should be better". The claim below is falsifiable and the
observation is a command.

**Claim.** The gap on the 10 (i) files is that we never apply a Skolem function
to arguments we already hold. A fix must make those applications exist.

**The number that moves — aggregate.** `25` — the count of required terms absent
from the ground dump across the 10 (i) files. Re-running the matcher after a fix
must move it toward 0. It is derived from the dump and the proof, not from a
literal, so it cannot be satisfied by editing an expectation.

**The number that moves — sharpest single observable (`f29`).** Today the dump
contains exactly **one** distinct `f18` application, `(f18 f29 !q.?v2.7)`, whose
second argument is a bound variable, and **zero** applications of any `!qskf_`
symbol to `(f19 (f20 f29) f28)`. A fix works iff **both**:

1. that second count goes from **0 to ≥ 1**, and
2. `axeyum_cli Hoare/uf.966336.smt2 --timeout-ms 24000` prints **`unsat`**
   instead of `unknown`.

**The two outcomes are separately informative, which is the point of stating
both.** If (1) moves and (2) does not, the term was built and selection still
failed — that would be the **first** evidence for (ii) on `f29`, and it would
move `f29` out of this note's (i) column. If neither moves, the construction
step is in the wrong place.

**A fix must not be accepted on (2) alone.** `f29` could flip via some unrelated
route and leave the measured gap untouched.

## If the answer is (i), what construction step is missing and where

The missing step is **not** in `quant_skolemize` — its polarity handling is
correct — and **not** a bigger cap. It is that the assertion set carrying the
open binder and the assertion set carrying the Skolem functions are **different
sets, handled on different rungs, and the required term needs both**: the outer
instantiation that only the un-Skolemized rung performs (`!sk_0`/`!sk_1` at
exactly z3's constants) and the inner Skolem function that only the Skolemized
rung has.

Two bounded places to put it, in the order the evidence supports:

1. **Stop running the loop on the un-Skolemized set** (`qinst_egraph.rs`, the
   entry that produces block 1). It cannot contain a Skolem term, it is where
   the 8,192 cap is spent on 11 of 16 files, and the earlier note already
   established for `f27` that handing the loop the Skolemized set is what
   decides the file. **Predicted observable:** block 1 disappears from the dump,
   and the per-file ground rows fall by roughly the block-1 count — on `f01`
   from 24,576 to 16,384. This is a **cost** fix; on its own it need not move a
   verdict, and it should not be sold as one.
2. **Seed the Skolem application directly.** `matcher.invent_starved_trigger_terms`
   / `invent_starved_universal_instances` (`qinst_egraph.rs`, the term-invention
   route that already exists for the starved fixpoint) is the natural home: for
   each Skolem function in the Skolemized set, form its application at ground
   arguments already in the set. **93% of the arguments are already present**, so
   this is a bounded product over terms we hold, not a search. Its ceiling is
   already gated by `invention_ceiling`, and this note supplies the reason to
   point it at Skolem heads specifically.

**What this note does not license.** It does not say item 2 will flip 10
verdicts. It says the term is absent, that its arguments are present, and that
`f05` and `f07` are the same construction succeeding — so the construction is
reachable. Whether the loop then *selects* it is a separate question this
measurement cannot answer, and the four generation-0 (ii) files are a standing
warning that having the term is not sufficient.

## What I did not measure

- **Whether building the missing term flips any verdict.** Not attempted. The
  falsifiable statement above is the test; it has not been run.
- **The 14 files z3 also times out on.** Untouched. Everything here is the
  18-file refutable subset.
- **`f23`.** z3 cannot produce a proof for it in 120 s, so nothing here says
  what it needs — unattributed, as before.
- **`f27`.** We decide it now, so it has no give-up point and no dump. Its
  absence from the table is not a negative result.
- **Congruence.** Matching is **structural**. A term absent as a syntactic
  subterm could still be present as an e-class representative under the
  congruence the ground facts force. `f29`'s `!sk_0` = `(f19 (f20 f29) f28)` is
  exactly such a case, and it is handled there by reading the correspondence
  from the goal — but no systematic congruence-aware match was run, so the (i)
  count is an upper bound on "never built" in the strict semantic sense and a
  lower bound on how close we are.
- **Whether the un-Skolemized rung is load-bearing anywhere.** Item 1 above
  assumes it is not. On this slice it decides nothing, but population B was not
  swept and `corpus/regression` was not run.
- **cvc5.** Still not installed.
- **`AXEYUM_NESTED_QUANT=0`.** Every arm ran the shipped `Nested` layout.

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench \
    --example axeyum_cli --features axeyum-solver/full
AXEYUM_QGROUNDDUMP=/tmp/f29.dump ./target/release/examples/axeyum_cli \
    /nas3/.../UF/sledgehammer/Hoare/uf.966336.smt2 --timeout-ms 24000

# z3 side: prepend (set-option :produce-proofs true), STRIP every (exit)
# -- the corpus files end with one and it swallows (get-proof) -- append
# (get-proof), then `z3 -T:120`, and expand the let-bound proof steps.
```

The proof extractor, the structural matcher, its thirteen controls and the
per-file dumps live in this session's scratchpad and are not committed; the
matcher is ~180 lines and its whole contract is in the module docstring quoted
above. The one committed artifact is the `AXEYUM_QGROUNDDUMP` probe itself
(`f87d0f649`), which is what a re-run needs.
