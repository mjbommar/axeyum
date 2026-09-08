# Bit-blasting and AIG: encoding quality upstream of the SAT solver

Lane: `research-bitblast-aig`. Read-only survey, 2026-09-08.

Every claim is tagged: **[C]** read from source code (cited `file:line`),
**[P]** from a paper, **[I]** inference by the author of this note. No
measurement in this document was produced by running anything — measurements
quoted from our own tree or from a reference solver are quoted from the comment
that already records them, and are attributed as such.

§1–§7 were written from source alone, before the paper survey arrived. **§8 is
the literature, and it revises two conclusions in §1 and §3** — it is flagged at
both sites, and §8.1 and §8.2 carry the corrections. Read §8 before acting on
§1.3 or on any adder recommendation.

Sibling lanes own the other files in this directory; this file covers the AIG
and bit-blasting layer only.

**Reading order.** §0 is the answer. **§6 is the actionable list** and is what a
lane should be briefed from; it forward-references the evidence sections. §1 is
the "already exists, do not rebuild" inventory — read it before writing any
brief that touches this area. §2–§5 and §7–§8 are the evidence.

### Source provenance

`references/` is gitignored, so a later reader cannot check what was read.
Every clone was verified as genuine upstream before citing — this matters
because upstream STP's comments are recent and specific enough that I initially
suspected a fork:

| clone | remote | HEAD |
|---|---|---|
| `references/stp` | `https://github.com/stp/stp` | `e4af105c0`, 2026-09-08 |
| `references/bitwuzla` | `https://github.com/bitwuzla/bitwuzla` | `a5e6e8a`, 2026-09-04 |
| `references/z3` | `https://github.com/Z3Prover/z3` | `e18d63b`, 2026-09-08 |
| `references/abc` | `https://github.com/berkeley-abc/abc` | `fbaae01`, 2026-09-05 |
| `references/boolector` | `https://github.com/Boolector/boolector` | `43dae91c1`, 2024-08-23 |

`abc`, `boolector`, `stp` and `aiger` were not in `scripts/fetch-references.sh`
and were cloned for this survey. **If ABC, Boolector or STP are to be cited by
future work, they should be added to that script** — it is the reproducible
record and it currently does not name them.

---

## 0. The one-paragraph answer

Our pipeline has three layers — term → AIG (`axeyum-bv`), AIG construction
(`axeyum-aig`), AIG → CNF (`axeyum-cnf`). Read against Bitwuzla, Boolector, STP,
Z3 and ABC:

- **The CNF layer is the strongest of the three** in gate fusion: we do XOR /
  ITE / OR / AND-tree fusion with fanout guards, where Bitwuzla's `aig_cnf.cpp`
  does ITE extraction plus plain Tseitin and carries `TODO`s for two things we
  have. **But our Plaisted–Greenbaum encoding is not the advantage it looks
  like.** Measured on 3,672 bit-blasted QF_BV benchmarks, PG saves 8 % of
  clauses and **zero** variables, and blocked-clause elimination on plain
  Tseitin beats it on both — and BCE subsumes PG as a theorem. No competitive
  eager BV solver uses PG. **We do not have BCE**, and it is an unusually good
  fit here: it only deletes, so a bug in it cannot produce a wrong `unsat` (§8.1).
- **The AIG layer is where the gap is.** We apply local rules at construction
  time only. There is no post-construction optimisation of any kind: no
  rewriting pass, no SAT sweeping, no cut enumeration, and no fanout, level or
  reference counts on the graph to build one with.
- **The circuit layer has specific, countable inefficiencies** — the shapes we
  emit for XOR, for the unsigned comparator, and for the divider — each a
  self-contained function body.

**The highest-value items are not the famous ones.** Restructuring `Aig::xor`
(one function, ~6 lines, no call sites) makes every half-adder in the system
share a node it currently allocates twice: 9 → 7 AND nodes per full-adder bit,
across all of QF_BV arithmetic. All three of Boolector, Bitwuzla and STP write
that half-adder three different ways and produce the *identical* AIG; we picked
the other factorisation. Reformulating `lower_unsigned_less` drops it from ~7 to
4 AND nodes per bit, and that saving is multiplied `width` times inside the
divider.

**And the loudest finding is a warning.** Three independent measurements — STP's
(a 2.2× smaller divider that solved **287 vs 289** of 311 queries and turned a
39 s refutation into minutes), our own Sage2 accumulator (a **half-size** CNF
that times out at 60 s where the larger one solves in **8.5 ms**), and our own
reverted Booth experiment — all say the same thing: **node count is not solve
time.** So the ranked list opens not with a build but with a measurement (Rank 0:
export our AIGs to ABC and find out how much redundancy is actually there),
because ranks 7–9 are multi-week builds whose payoff is currently unmeasured.

---

## 1. What we already have (do not rebuild these)

This section exists because the repository's most expensive recurring failure is
re-deriving something that is already in the tree. Each item below was read, not
inferred from a name.

### 1.1 The AIG (`crates/axeyum-aig/src/lib.rs`, 1046 lines)

- **Deterministic structural hashing.** Open-addressed unique table with linear
  probing, power-of-two capacity, 0.7 load factor, keyed on the *canonically
  ordered* `(lhs, rhs)` literal pair. `crates/axeyum-aig/src/lib.rs:136-197`.
  The hash is a splitmix-style finaliser over the two packed literals,
  `crates/axeyum-aig/src/lib.rs:199-217`. The table is documented as
  lookup-only, so slot order is never observed and node order stays driven by
  caller request order — this is what makes construction deterministic.
  **[C]**
- **Canonical fanin order.** `Aig::and` swaps so the smaller `AigLit` is first,
  `crates/axeyum-aig/src/lib.rs:479-481` (`if b < a { swap }`). `AigLit` derives
  `Ord` over `(node: AigNodeId, inverted: bool)`,
  `crates/axeyum-aig/src/lib.rs:49-54`, so the order is by node id then by
  complement bit. **[C]**
- **Trivial (level-1) folding at construction.** `simplify_and` folds
  `a∧0`, `a∧¬a`, `1∧a`, `a∧a`. `crates/axeyum-aig/src/lib.rs:732-744`. **[C]**
- **Two local level-2/3-ish rules**: OR-absorption (`a ∧ (a∨b) = a`, and the
  `¬a ∧ (a∨b) = ¬a ∧ b` substitution) at
  `crates/axeyum-aig/src/lib.rs:383-401`, and OR-consensus at
  `crates/axeyum-aig/src/lib.rs:403-418` with
  `crates/axeyum-aig/src/lib.rs:745-755`. **[C]**
- **A substantial MUX simplifier**, ~14 identity cases plus condition-directed
  and branch-absorption rewrites, `crates/axeyum-aig/src/lib.rs:450-598`. This
  is richer than anything in Bitwuzla's `AigManager`. **[C]**
- **Construction telemetry**: every `and` call is classified as trivial
  simplification / local simplification / structural-hash hit / new node,
  `crates/axeyum-aig/src/lib.rs:233-268`. **This is the A/B harness an encoding
  policy needs and it already exists.** **[C]**
- **ASCII AIGER export**, `crates/axeyum-aig/src/lib.rs:628`. **[C]**

### 1.2 The bit-blaster (`crates/axeyum-bv/src/lib.rs`, 5218 lines)

- **Ripple-carry adder**, `crates/axeyum-bv/src/lib.rs:2791-2818`
  (`lower_add_bits`), with an explicit carry-in parameter so subtraction reuses
  it (`lower_sub_op` passes the inverted rhs and carry-in `TRUE`,
  `crates/axeyum-bv/src/lib.rs:2262-2276`). **[C]**
- **Shift-and-add multiplier**, `crates/axeyum-bv/src/lib.rs:2278-2327`. **[C]**
- **Log/barrel shifter**, `⌈log2 w⌉ mux stages plus an out-of-range guard,
  `crates/axeyum-bv/src/lib.rs:2560-2609`. **[C]**
- **Restoring divider**, `crates/axeyum-bv/src/lib.rs:2355-2407`, with the
  SMT-LIB totality convention applied by a final mux
  (`bvudiv x 0 = ~0`, `bvurem x 0 = x`), `crates/axeyum-bv/src/lib.rs:2401-2406`.
  Signed division/remainder/modulo route through `signed_divrem_abs` and share
  the unsigned core by structural hashing,
  `crates/axeyum-bv/src/lib.rs:2457-2532`. **[C]**
- **A heavily constant-specialised unsigned comparator.** `lower_unsigned_less`
  has seven constant fast paths before the general chain, including
  "rhs is a power of two ⇒ all bits above the set bit must be clear" and
  "lhs+1 is a power of two ⇒ some bit above must be set",
  `crates/axeyum-bv/src/lib.rs:2833-2861`. Bitwuzla's `ult_helper` has none of
  these. **[C]**
- **Demand-driven lowering**: `lower_terms_demanded` and the admission-controlled
  `lower_terms_range_demanded` (ADR-0158) propagate half-open bit ranges and
  materialise only demanded term bits, with a policy struct and a six-valued
  admission decision, `crates/axeyum-bv/src/lib.rs:144-253`. **[C]**
- **Incremental lowering** (`IncrementalLowering`, ADR-0009 stage 2),
  `crates/axeyum-bv/src/lib.rs:899-1035`. **[C]**

### 1.3 The CNF encoder (`crates/axeyum-cnf/src/lib.rs`, 7021 lines)

This is the layer that is *ahead* of the reference solver.

> **Read §8.1 before treating the PG bullet below as a win.** Measured on 3,672
> bit-blasted QF_BV benchmarks, PG saves 8 % of clauses and **zero** variables,
> and blocked-clause elimination on plain Tseitin beats it on both axes. No
> competitive eager BV solver uses PG. Ours is sound, already built and free —
> but the upgrade path is BCE, which we do not have, not more polarity work.

- **Plaisted–Greenbaum polarity encoding, in both directions.** The one-shot
  `tseitin_encode` plans root polarities globally
  (`plan_root_polarities`, `crates/axeyum-cnf/src/lib.rs:3491`), and
  `IncrementalCnf` emits gate definitions **lazily by polarity of use**, adding
  the opposite half only if an opposite-polarity use later appears
  (`crates/axeyum-cnf/src/lib.rs:1145-1168`, `1562-1640`). The doc comment
  explicitly records the consequence — a node may be left
  polarity-underconstrained, so its CNF variable is not a faithful gate value —
  which is the correct statement of the PG caveat. **[C]**
- **Gate fusion**: XOR detection (`detect_xor_gate`,
  `crates/axeyum-cnf/src/lib.rs:4369`), not-ITE/mux detection
  (`detect_not_ite_gate`, `:4396`), not-AND / OR factoring
  (`detect_not_and_gate`, `:4438`), and positive AND-tree flattening
  (`plan_and_tree_gates`, `:3576`; `try_flatten_internal_positive_and`, `:1510`).
  **[C]**
- **Fanout-guarded extraction.** Every fusion is guarded by
  `use_counts[helper] == 1` so extraction never destroys sharing,
  `crates/axeyum-cnf/src/lib.rs:3528`, `:3540`, `:4488`, `:4587`. This is the
  same guard Bitwuzla uses (`l.parents() > 1`,
  `references/bitwuzla/src/lib/bitblast/aig/aig_cnf.cpp:182-198`) but applied to
  more gate families. **[C]**
- **Clause canonicalisation and dedup** with per-template origin attribution
  (`CnfClauseOriginTemplate`, `crates/axeyum-cnf/src/lib.rs:2100+`) and a full
  construction profile. **[C]**

### 1.4 Word-level passes (`crates/axeyum-rewrite/`)

- **Unconstrained-variable elimination** — Z3's `elim_unconstr`, over
  `bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg` and `bvmul` by an odd constant, with a
  model-reconstruction trail. `crates/axeyum-rewrite/src/elim_unconstrained.rs:1-32`.
  **[C]**
- **AC flattening + commutative operand ordering by ascending `TermId`**, with a
  width cap, `crates/axeyum-rewrite/src/canonical.rs:841-842` and `:19-45`. **[C]**
- **Value propagation, equation solving, array elimination, int-blasting**:
  `propagate_values.rs`, `solve_eqs.rs`, `arrays.rs`, `int_blast.rs`. **[C]**

### 1.5 Two things that make encoder experiments cheap and safe

These are the reason a configurable encoder is a *tractable* project here rather
than a risky one.

- **`reduction_shrinks_encoding`** (`crates/axeyum-solver/src/auto.rs:1975-2010`)
  already judges a preprocessing decision **by the AIG size it lowers to**, not
  by term count, and the comment records the measurement that forced it:
  `062-bench_2195`'s term DAG *shrank* 1375 → 1215 while its AIG *grew* 35 329 →
  51 724 (+46 %). Bitwuzla has the same idea as `AigScore`
  (`references/bitwuzla/src/preprocess/pass/normalize.cpp:48`, with
  `score() { return d_bitblaster.num_aig_ands(); }` at `:64`), used at `:1330-1349`
  to pick between *two* candidate normalisations by AND-count. **We
  independently converged on it and ours is wired into dispatch.** **[C]**

  One detail worth copying, and it is better than "lower both and compare".
  `AigScore` is **resumable and budgeted** — `process(limit = 100000)` builds at
  most `limit` AND gates and returns, with `done()` reporting whether the term
  set was exhausted (`references/bitwuzla/src/preprocess/pass/normalize.cpp:55-66`,
  `:91-100`). The caller then runs *three* scorers — original, pass 1, pass 2 —
  **in lockstep**, and breaks the moment any candidate is finished and already
  cheaper than the original, or the original finishes and neither beat it
  (`:1322-1346`). So a decisively better candidate is detected without ever
  fully lowering anything, and an inconclusive comparison costs a bounded
  prefix rather than two full lowerings. **[C]**

  Our `reduction_shrinks_encoding` lowers both sides fully; the comment records
  the cost as 0.36 ms on `021-bench_11651`
  (`crates/axeyum-solver/src/auto.rs:2002`), which is fine for two
  candidates but does not generalise. **[I]** If an `EncodingPolicy` ever has to
  choose among several topologies by predicted size, this interleaved-bounded-race
  shape is the one to build, not a full lowering per candidate.
- **`certify_bitblast_by_miter`** (`crates/axeyum-solver/src/bitblast_miter.rs:1-24`)
  proves by a DRAT-checked miter that production bit-blasting agrees with a
  separately coded reference bit-blaster **on every input**, across the whole
  supported QF_BV operator set. **This is exactly the acceptance test a new
  adder or multiplier topology needs**: implement the alternative, run the
  miter, get an exhaustive (not sampled) equivalence certificate. **[C]**
- **`lazy_bv`** (`crates/axeyum-solver/src/lazy_bv.rs:1-28`, ADR-0019) already
  implements abstraction–refinement for the heavy gadgets (`bvmul`, the whole
  div/rem family): abstract to fresh variables, solve, replay, refine only the
  operations the model violated. **[C]**

### 1.6 What is genuinely absent

Checked by pattern across `crates/**/*.rs` with a positive control on
`structural` (which hits, so the search reaches the right files):

| capability | occurrences | note |
|---|---|---|
| FRAIG / SAT sweeping | 0 | no functional reduction of any kind |
| cut enumeration | 0 | — |
| NPN canonical form | 0 | the one `npn` hit is a variable name in a Lean prelude |
| technology-mapped CNF | 0 | — |
| random simulation / simulation vectors | 0 | — |
| post-construction AIG rewrite pass | 0 | all AIG rules fire at construction only |

Structurally, `Aig` stores only `nodes`, `inputs`, `and_table`,
`construction_stats` (`crates/axeyum-aig/src/lib.rs:268-276`) — **no fanout
counts, no level array, no reference counts, no garbage collection**. Any
ABC-style rewriting needs at least fanout/refcounts (for MFFC) and levels (for
balancing), so that struct is the first thing an AIG-optimisation project
touches. **[C]** Note that the *CNF encoder* computes its own local
`use_counts` per encode (`crates/axeyum-cnf/src/lib.rs:4352`), so the fanout
information exists transiently but is not on the graph. **[C]**

---

## 2. Bitwuzla, read directly

`references/bitwuzla` is a shallow clone of `bitwuzla/bitwuzla`.

### 2.1 The AIG manager is a template parameter, not a class — copy this shape

`references/bitwuzla/src/lib/bitblast/bitblaster.h` defines
`BitblasterInterface<T>` with every BV operator written against an abstract
`BitInterface<T>` providing `mk_false/mk_true/mk_bit/mk_not/mk_and/mk_or/mk_iff/mk_ite`
(`:32-46`). `BitInterface<AigNode>` is one specialisation
(`references/bitwuzla/src/lib/bitblast/aig_bitblaster.h:20-59`). **[C]**

This is the reusable-encoder abstraction the brief asks for, and it is worth
noting what Bitwuzla got right and what it left on the table:

- **Right**: the *bit primitive* is the parameter. So the same circuit library
  runs over an AIG, over concrete bits (constant folding), over a different
  gate representation, or over an instrumented counter — no duplication.
- **Left on the table**: the *topology* is still hard-coded. `bv_add` always
  calls `add_helper`, which is always ripple-carry
  (`references/bitwuzla/src/lib/bitblast/bitblaster.h:423-437`). The methods are
  `virtual`, so a subclass can override one operator, but there is no policy
  object and no way to select a topology per call site or per operand width.

**[I]** The design to aim for is two orthogonal parameters, not one: a *bit
backend* (what a gate is) and an *encoding policy* (which circuit to build).
Bitwuzla parameterises the first only.

### 2.2 Two-level AIG rewriting: the complete rule set, implementable as read

`AigManager::rewrite_and`
(`references/bitwuzla/src/lib/bitblast/aig/aig_manager.cpp:177-408`) is a direct
implementation of Brummayer & Biere, *Local Two-Level And-Inverter Graph
Minimization without Blowup*, cited at
`references/bitwuzla/src/lib/bitblast/aig/aig_manager.h:106-110`. **[C]** The
rules are organised in four optimisation levels and the whole thing is a
`do { … } while(true)` loop where levels 3 and 4 *rewrite the operands and
`continue`* rather than returning — that is what makes it two-level without
blowup: it never allocates a node to explore a rewrite, it only ever narrows the
operand pair before the final `find_or_create_and`.

| level | rule | shape | result | line |
|---|---|---|---|---|
| 1 | neutrality / idempotence | `a∧1`, `a∧a` | `a` | `:196-203` |
| 1 | boundedness / contradiction | `a∧0`, `a∧¬a` | `0` | `:204-215` |
| 2 | contradiction, asymmetric | `(a∧b)∧c`, `a=¬c ∨ b=¬c` | `0` | `:226-237` |
| 2 | contradiction, symmetric | `(a∧b)∧(c∧d)`, any cross-negation | `0` | `:239-247` |
| 2 | subsumption, asymmetric | `¬(a∧b)∧c`, `a=¬c ∨ b=¬c` | `c` | `:249-260` |
| 2 | subsumption, symmetric | `¬(a∧b)∧(c∧d)`, cross-negation | `c∧d` | `:262-275` |
| 2 | idempotence | `(a∧b)∧c`, `a=c ∨ b=c` | `a∧b` | `:277-288` |
| 2 | resolution | `¬(a∧b)∧¬(c∧d)`, `a=d ∧ b=¬c` | `¬a` | `:290-304` |
| 3 | substitution, asymmetric | `¬(a∧b)∧c`, `b=c` | rewrite to `¬a∧c`, loop | `:308-339` |
| 3 | substitution, symmetric | `¬(a∧b)∧(c∧d)`, `b=c` | rewrite to `¬a∧(c∧d)`, loop | `:341-374` |
| 4 | idempotence, two ANDs | `(a∧b)∧(c∧d)`, `a=c` | drop the shared operand, loop | `:376-394` |

Only after the loop breaks does it normalise (`|left| > |right| ⇒ swap`,
`:399-403`) and hash-cons. **[C]**

Our `Aig::and` implements level 1 in full, plus OR-absorption and OR-consensus,
which cover parts of the level-2 subsumption and resolution families. It does
**not** implement the asymmetric/symmetric contradiction rules, the two-AND
idempotence rules, or either substitution rule — and in particular it has **no
operand-rewriting loop**, so it cannot chain. **[C]/[I]**

### 2.3 The unique table

Chained buckets, power-of-two count, resize doubling, hash
`547789289·|lid| + 786695309·|rid|` masked to the table size
(`references/bitwuzla/src/lib/bitblast/aig/aig_manager.cpp:92-124`). Note the
hash uses `abs(id)` — **it discards the complement bits** — and the bucket walk
then compares full signed ids (`:32-35`). Ours hashes the complement bits into
the key (`crates/axeyum-aig/src/lib.rs:199-206`), which is strictly better
collision behaviour for no extra cost. **[C]/[I]**

Bitwuzla also refcounts nodes (`d_refs`, `d_parents`) and garbage-collects
(`:433-494`). We do neither. **[C]**

### 2.4 The circuits Bitwuzla actually builds

All in `references/bitwuzla/src/lib/bitblast/bitblaster.h`:

| operator | topology | line |
|---|---|---|
| `bvadd` | ripple carry (half adder then full adders) | `:423-437` |
| `bvmul` | shift-and-add, with skip of constant-`false` multiplier bits and of full-adder calls where both addend and carry are constant `false` | `:438-477` |
| `bvmul` where both operands are the same term | **dedicated square circuit** | `:370-406`, dispatched at `src/solver/bv/aig_bitblaster.cpp:174-186` |
| `bvult` | ripple comparator, "less-or-not-greater" recurrence | `:478-500` |
| `bvslt` | sign split then unsigned compare of the remainder | `:302-333` |
| `bvshl`/`bvshr`/`bvashr` | log shifter, `⌈log2 w⌉` mux stages plus an `ult` overflow guard | `:126-258` |
| `bvudiv`/`bvurem` | **two-stage** restoring divider, no separate comparator | `:541-660` |

**No parallel-prefix adder. No Wallace/Dadda tree. No Booth recoding. No
carry-save.** The state of the art in a competition-winning QF_BV solver is
ripple-carry and shift-and-add. **[C]** That is a strong signal about where the
value is not.

### 2.5 The three places Bitwuzla's circuits beat ours

These are the concrete, countable findings. Node counts below are **[I]**,
derived by hand from the **[C]** sources on both sides, counting AND nodes
(inverters are free, they are edge bits).

**(a) XOR / half-adder sharing.** Bitwuzla's `mk_xor(a,b)` is
`and(or(a,b), ¬and(a,b))` (`:527-531`); its `half_adder` computes `and(a,b)`
*once* and uses it both as the carry and inside the sum (`:501-511`). Cost: 3
AND nodes for a half adder, carry included. Our `Aig::xor` is
`or(and(a,¬b), and(¬a,b))` (`crates/axeyum-aig/src/lib.rs:425-449`) — also 3
nodes standalone, but it shares **nothing** with the `and(a,b)` that
`lower_add_bits` builds separately for the carry
(`crates/axeyum-bv/src/lib.rs:2810-2814`). Counting one full-adder bit:

| | our `lower_add_bits` | Bitwuzla `full_adder` |
|---|---|---|
| AND nodes per bit | **9** | **7** |

The derivation, since this is the headline recommendation and an implementer
should check it rather than trust it. `lower_add_bits`
(`crates/axeyum-bv/src/lib.rs:2810-2814`) does, per bit:

```
pair_sum         = xor(lhs, rhs)
sum              = xor(pair_sum, carry)
carry_from_pair  = and(lhs, rhs)
carry_from_input = and(pair_sum, carry)
carry            = or(carry_from_pair, carry_from_input)
```

*Today* (`xor(a,b) = or(and(a,¬b), and(¬a,b))`): the two XORs allocate 3 nodes
each over the operand pairs `{lhs,rhs}` and `{pair_sum,carry}` — but neither
allocates `and(lhs,rhs)` or `and(pair_sum,carry)`, so `carry_from_pair` and
`carry_from_input` each allocate a fresh node, and `or` allocates one more.
**3 + 3 + 1 + 1 + 1 = 9.**

*After* (`xor(a,b) = and(or(a,b), ¬and(a,b))`): the first XOR allocates
`and(¬lhs,¬rhs)`, **`and(lhs,rhs)`**, and the combiner; the second allocates
`and(¬pair_sum,¬carry)`, **`and(pair_sum,carry)`**, and its combiner. Now
`carry_from_pair` and `carry_from_input` are **structural-hash hits and cost
nothing**, leaving only the final `or`. **3 + 3 + 0 + 0 + 1 = 7**, which is
exactly Bitwuzla's number. **[I]**

Because `lower_add_bits` is also the inner loop of the multiplier and (via the
subtract) of the divider, this is a ~22 % AND-node reduction across essentially
all of QF_BV arithmetic — **from changing one function body**, with no call-site
changes, because the sharing is recovered automatically by the existing
structural hash. **[I]**

*Caveat, stated plainly:* fewer AND nodes is not automatically faster CDCL (see
§4). This one is unusually safe because it does not change the circuit's
topology or its implication structure at all — it changes only which
sub-expression is named, so propagation behaviour is preserved and the CNF
shrinks. **[I]**

**(b) The unsigned comparator.** Ours maintains an explicit `equal` prefix
(`crates/axeyum-bv/src/lib.rs:2862-2877`): per bit it builds `and(¬l,r)`,
`and(equal, ·)`, `or(·)`, `xor(l,r)` (3 nodes) and `and(equal, ·)` — **7 AND
nodes per bit**. Bitwuzla's recurrence is
`res_i = (¬a_i ∧ b_i) ∨ (¬(a_i ∧ ¬b_i) ∧ res_{i-1})`
(`references/bitwuzla/src/lib/bitblast/bitblaster.h:478-500`) — **4 AND nodes
per bit**. Using "not greater" instead of "equal" absorbs the XOR entirely, and
the two are semantically identical. **[C]/[I]**

This one compounds: `lower_unsigned_less` is called once per bit position inside
the divider, over `width+1` bits.

**(c) The divider.** Ours, per bit position: a full `ult` chain over `width+1`
bits, *then* a full ripple subtract over `width+1` bits, *then* a `width+1`-wide
mux (`crates/axeyum-bv/src/lib.rs:2385-2400`). The comparator and the subtracter
compute the same carry chain twice, and the mux is a third pass. Bitwuzla's is
two stages over `width` bits with **no comparator and no mux**: stage one
computes only the carries of `rem + ¬d + 1` with a carry-only full adder
(`fa_div_carry`, `:541-546`) and reads `carry[size]` as the quotient bit — *the
comparison is the carry-out, for free*; stage two reuses those same carry bits
to produce the sum, gated by the quotient bit (`fa_div_sum`, `:559-563`), which
folds the restore-or-not mux into the adder. Loop at `:625-660`. **[C]**

Counting honestly, per inner bit (**[I]**, and note that structural hashing
shares some terms *between* our comparator and our adder, so our figure is an
upper bound rather than an exact count):

| | ours | Bitwuzla |
|---|---|---|
| comparator pass | ~7 nodes/bit | — (folded into the carry chain) |
| add/subtract pass | 9 nodes/bit | `fa_div_carry` = 4 nodes/bit |
| restore mux pass | 3 nodes/bit | `fa_div_sum` = 5 nodes/bit *(see below)* |
| width | `width+1` | `width` |
| upper bound per bit | **≤ 19** | **9** |

The `fa_div_sum` figure is the interesting one. Written out it is
`xor(and(xor(d,c), q), r)` — which looks like 7 nodes. But `xor(d,c)` in
Bitwuzla's spelling is `and(or(d,c), ¬and(d,c))`, and **both `or(d,c)` and
`and(d,c)` were already built by `fa_div_carry` on the same bit**
(`references/bitwuzla/src/lib/bitblast/bitblaster.h:541-546`), so the structural
hash returns them and `xor(d,c)` costs one new node. Total 5, not 7. **[C]/[I]**

**That sharing exists only because of the XOR spelling in finding (a).** With
our current XOR form the same circuit would cost 4 + 7 = 11 nodes per bit, not
9. So finding (a) is not merely additive with the divider work — **it is a
precondition for it**, and the same holds for the multiplier's inner adder. Fix
the XOR first and other improvements get cheaper; fix the divider first and part
of its benefit is left on the table.

The divider is quadratic, so this is the largest single-operator gap in the
table — but see §4.1 before acting on it: STP measured this exact swap and did
not take it as the default.

### 2.6 The CNF encoder: we are ahead

`references/bitwuzla/src/lib/bitblast/aig/aig_cnf.cpp` does:

- top-level AND flattening for asserted roots, emitting unit clauses for the
  leaves of the positive-AND tree (`:47-83`) — we do this too
  (`plan_direct_root_nodes` / `fused_positive_and_roots`);
- ITE extraction from the two-level `¬(c∧¬a) ∧ ¬(¬c∧¬b)` shape, guarded by
  `parents() > 1` to protect sharing (`:170-242`), emitting the 4-clause ITE
  definition (`:303-318`) — we do this too, and also XOR and OR/not-AND;
- otherwise the plain 3-clause AND definition (`:319-335`);
- and carries two `TODO`s: *"and optimization: collect all children and encode
  one big and"* and *"xor optimization: use native xor encoding"* (`:300-301`)
  — **both of which we already do**. **[C]**

Bitwuzla emits the **full two-sided** Tseitin definition for every gate; the
one-sided/polarity optimisation is not present in this file. We do
Plaisted–Greenbaum. **[C]/[I]**

**Conclusion for the CNF layer: there is no Bitwuzla feature here to port.** Any
further CNF-layer gain has to come from the *technology-mapping* route (§3), not
from gate-fusion tweaks.

### 2.7 Word-level: eliminate the divider instead of building it

`references/bitwuzla/src/preprocess/pass/elim_udiv.cpp:81-117` replaces every
`bvudiv`/`bvurem` node by fresh variables `q`, `r` and asserts the defining
relation instead of building the circuit. The full side-condition set, which is
the part that is easy to get wrong:

```
b ≠ 0 → q*b + r = a
b ≠ 0 → r < b
b = 0 → q = ~0            (SMT-LIB totality)
b = 0 → r = a             (SMT-LIB totality)
¬ bvumulo(q, b)           (no overflow in q*b)
¬ bvuaddo(q*b, r)         (no overflow in q*b + r)
```

**[C]** Note this trades a divider (quadratic, ~11 nodes per bit-pair) for a
multiplier (quadratic, ~1 AND + one adder row per bit-pair) plus a comparator
plus two overflow predicates. It is not obviously smaller; it is *differently
shaped*, and the multiplier is the shape SAT solvers and preprocessors have more
machinery for. Whether it wins is an empirical question on our corpora — but the
pass is ~120 lines and the correctness argument is fully written down above.
**[I]**

We do not have this pass. `crates/axeyum-rewrite/` has no udiv/urem elimination;
the closest thing is `lazy_bv`'s abstraction of the whole div/rem family, which
is a different mechanism (abstract-and-refine, not define-and-assert). **[C]**

### 2.8 Word-level: the Boolean skeleton pre-solve

`references/bitwuzla/src/preprocess/pass/skeleton_preproc.cpp:144-200`
bit-blasts *only the Boolean skeleton* of the assertions (an `AigBitblaster`
constructed with the "skeleton only" flag), CNF-encodes it, runs
`CaDiCaL::simplify()`, and harvests **fixed literals** through a
`connect_fixed_listener` callback; each fixed literal that maps back to a
word-level node becomes a top-level assertion or its negation. It is disabled
when unsat cores or interpolants are requested (`:100-105`) because the
attribution would be wrong. **[C]** This is a cheap way to let the SAT solver's
unit propagation do word-level constant propagation for you.

---

## 3. STP: the encoding menu already exists, and it has been measured

**This is the single most valuable source in the survey.** The clone was
verified as genuine upstream `stp/stp` — `git remote -v` gives
`https://github.com/stp/stp`, HEAD `e4af105c0` dated 2026-09-08 — because its
comments are recent enough and specific enough to look implausible. They are
real.

STP does exactly what the brief proposes: **the circuit topology is a runtime
policy**, with 19 multiplier variants, 2 adder spellings, 2 comparator
spellings, 5 divider variants plus 2 circuit-free encodings, all on the CLI.
Flags: `references/stp/include/stp/STPManager/UserDefinedFlags.h:877-994`; CLI
at `references/stp/tools/stp/main.cpp:619-698`. **[C]**

### 3.1 The policy axes STP actually parameterises

| axis | choices | where |
|---|---|---|
| full-adder spelling | shared-half-adder-carry (7 gates) / majority-carry (11 gates) | `lib/ToSat/BitBlaster.cpp:2364-2425` |
| n-ary add accumulation | pairwise ripple / column compression network | `:1538-1569` |
| partial-product generation | AND array / radix-2 Booth (constants) / radix-4 modified Booth (symbolic too) / radix-4 hard-triple | `:2921-3072`, `:3904-3935` |
| partial-product summation | per-row ripple / carry-save rows / greedy column network / **Dadda** / sorting networks | `:2766-2837`, `:3776-3902`, `:4242-4330` |
| divider | recursive long division / restoring+mux / restoring+comparator / two-stage borrow chain / **defining relation, no circuit** | `:4731-4998`, `:3417-3480` |
| comparator | ITE chain / OR-of-first-difference | `:5042-5127` |
| operand canonicalisation | by symbolic-bit profile (`cheaperAsMultiplier`) | `:3937-3975` |
| lemma augmentation | multiplication residue implicates / division order laws | `:3731-3774`, `:3560-3588` |

**[C]** Crucially, partial-product *generation* and *summation* are orthogonal
in STP, and that orthogonality is what produces a 19-entry table from a handful
of primitives. Any policy design we do should preserve that factoring rather
than enumerating whole multipliers.

### 3.2 The full-adder finding, independently confirmed

`references/stp/lib/ToSat/BitBlaster.cpp:2409-2413`, verified verbatim:

> `sum = a + b + cin over one bit. Two half adders: the first's carry is`
> `AND(a, b), which its sum -- xorWithSharing(a, b) -- already created, and`
> `likewise for the second, so the whole adder is seven gates where the`
> `majority-carry form is eleven. On a 226-bit significand product the`
> `difference between the two spellings is a third of the multiplier.`

`xorWithSharing` is `AND(OR(a,b), NOT(AND(a,b)))`
(`references/stp/lib/ToSat/BitBlaster.cpp:2394-2407`) — **the same construction
as Bitwuzla's `mk_xor`**, for the same reason. **[C]**

This is the §2.5(a) finding arriving from a second, independent codebase, with
STP's own gate count (7 vs 11) bracketing my hand count of our shape (9 — we
are between the two, because our XOR is the cheap 3-gate form but does not share
its conjunction with the carry).

**The sharpest form of this finding.** Three reference solvers write the
half-adder three different ways, and all three produce the *identical AIG*:

| solver | source | spelling |
|---|---|---|
| Boolector | `references/boolector/src/btoraigvec.c:221-234` | `¬( and(x,y) ∨ and(¬x,¬y) )` |
| Bitwuzla | `references/bitwuzla/src/lib/bitblast/bitblaster.h:501-511` | `and( or(x,y), ¬and(x,y) )` |
| STP | `references/stp/lib/ToSat/BitBlaster.cpp:2394-2407` | `and( or(a,b), ¬and(a,b) )` |

In an AIG, `or(x,y)` *is* the node `and(¬x,¬y)` read through a complemented
edge, so every one of these allocates exactly the node pair
`{ and(x,y), and(¬x,¬y) }` plus one combining node — **3 nodes, with the carry
`and(x,y)` already among them.** **[C]**

Ours allocates `{ and(x,¬y), and(¬x,y) }` plus a combining node for the XOR
(`crates/axeyum-aig/src/lib.rs:425-449`), and then a *fourth*, disjoint node
`and(x,y)` for the carry (`crates/axeyum-bv/src/lib.rs:2812`). **Four nodes
where all three reference solvers use three — because we picked the other
factorisation of XOR.** **[C]/[I]**

This is the cleanest single finding in the survey: a one-function change, no
call sites touched, no change to circuit topology or implication structure, and
the saving is recovered automatically by the structural hash we already have.

### 3.3 Division without a divider — better than Bitwuzla's version

`BBDivByMult` (`references/stp/lib/ToSat/BitBlaster.cpp:3417-3480`) is
circuit-free division, and its construction is materially better than
Bitwuzla's `elim_udiv` (§2.7). Read verbatim from the implementation:

- fresh `q`, `r` of width `w` (`:3443-3447`);
- a **magnitude ladder** `h[i] ⟺ y < 2^i`, one AND gate per rung (`:3451-3454`);
- one binary clause per quotient bit: `¬q[k] ∨ h[w-k]` (`:3456-3458`) — this is
  the entire "no partial product reaches column `w`" staircase;
- `y*q + r` accumulated at width `w+1` with rows truncated at column `w` and
  **every step's carry-out asserted false and pinned** (`:3460-3472`);
- `acc[0..w) = x` (`:3474-3475`);
- `y = 0 ∨ r < y` (`:3477-3479`).

**[C]** Compare Bitwuzla, which asserts `¬bvumulo(q,b)` and `¬bvuaddo(q*b,r)`
(`references/bitwuzla/src/preprocess/pass/elim_udiv.cpp:104-107`) — two
overflow *circuits*. STP replaces both with `w-1` binary clauses and `w` pinned
carry-out literals. **[I]** If we build this pass, build STP's version.

**A correctness note on reading STP**: the flag comment at
`references/stp/include/stp/STPManager/UserDefinedFlags.h:908-911` says the
product is "carried at double width so nothing wraps". The implementation says
the opposite — "made exact **not** by a double-width product but by a magnitude
ladder" — and the code confirms the implementation (`acc` is `w+1` wide, not
`2w`). **The header comment is stale; cite the implementation.** **[C]**

### 3.4 Two more STP measurements worth having

- **Constant-bit multiplication bounds are worthless on the Booth path.**
  `references/stp/lib/ToSat/BitBlaster.cpp:3373-3375`, verified verbatim:
  `Measured over 1276 multiplies: the bounds were live 0 times.` **[C]** A
  reminder that an optimisation can be structurally unreachable rather than
  merely unhelpful.
- **Radix-4 Booth is explicitly an open question, not a known win.**
  `:3023-3025`: `The trade is that halving the rows has to pay for a costlier`
  `row: a naive row is one AND per bit, a radix-4 row is a select plus an XOR.`
  `Whether that is worthwhile in CNF rather than in silicon is a question for`
  `measurement.` **[C]** This corroborates our own reverted Booth experiment
  (§4).

### 3.5 Boolector and Z3, briefly

Both have **one** topology per operator; neither parameterises anything. **[C]**

- **Boolector** (`references/boolector/src/btoraigvec.c`): ripple-carry
  (`:265-296`), shift-and-add multiplier with ripple rows and no square case
  (`:554-602`), non-restoring cellular divider with two gate types
  `SC_GATE_CO`/`SC_GATE_S` and no restore mux (`:604-723`), log barrel shifter
  with the amount split into `upper2`/`lower2` and an out-of-range ITE
  (`:331-474`), and the same "less-than-so-far" comparator recurrence Bitwuzla
  uses (`:150-177`). `bvashr` is **not** a bit-blasting primitive — it is
  rewritten away before blasting (`references/boolector/src/btorcore.c:2660-2693`).
  Operand canonicalisation for `add`/`mul` is an option, `BTOR_OPT_SORT_AIGVEC`
  (`:250-263`, `:279-283`, `:568-572`).
- **Z3** (`references/z3/src/ast/rewriter/bit_blaster/`): ripple-carry with a
  **majority carry** rather than the shared form
  (`bit_blaster_tpl_def.h:115-119`, `bit_blaster.cpp:116-121`) — the 11-gate
  spelling STP measures as worse; a half/full-adder diagonal array multiplier
  drawn in a comment at `bit_blaster_tpl_def.h:218-239`; restoring division
  with a **full `sz`-bit subtractor plus explicit restore multiplexers per row**
  (`:383-440`), which is the most expensive divider of the four; signed division
  that can build **four** unsigned dividers, with the comment
  `Otherwise, it will create 4 copies of the expensive sdiv/srem/smod`
  (`:486-487`). Options are `blast_add` / `blast_mul` / `blast_full` — *whether*
  to blast, not *how* (`bit_blaster_rewriter.cpp:136-139`,
  `tactic/bv/bit_blaster_tactic.cpp:132-135`). **[C]**
- Z3's one genuinely unusual idea: `mk_const_case_multiplier`
  (`bit_blaster_tpl_def.h:1120-1142`) replaces the array with a **balanced ITE
  tree over constant products**, guarded by `2^(#symbolic bits) < 5·sz²` and
  `sz < 100`. Verified. **[C]** Worth stealing for narrow, mostly-constant
  multiplies.
- Z3 declares and defines `mk_carry_save_adder`
  (`bit_blaster_tpl_def.h:1109-1118`) and **never calls it** — a repo-wide grep
  finds only the definition and the declaration. Abandoned Wallace-tree
  infrastructure. **[C]**

### 3.6 Nobody uses a parallel-prefix adder

A case-insensitive search for `kogge|sklansky|brent.kung|parallel.prefix|carry.look.ahead|wallace`
across `boolector/src`, `stp/lib`, `stp/include`, `z3/src` and `bitwuzla/src`
returns **zero hits**. Every adder in all four solvers is a ripple-carry
full-adder chain, and no source contains a comment explaining why not. **[C]**

STP has carry-*save* reduction (Dadda, CSA rows, column networks) for
multiplier partial products, but every one of them terminates in a **ripple
adder over the two surviving rows**
(`references/stp/lib/ToSat/BitBlaster.cpp:3890-3900`). **[C]**

**[I]** The reason is implicit in STP's full-adder comment: the metric these
solvers optimise is gate count and node sharing, not depth. A parallel-prefix
adder trades gates for depth, and there is no evidence in any of these
codebases that CDCL rewards circuit depth. **This is a strong negative result:
do not build a Sklansky or Kogge-Stone adder as a first move.** If we ever
build one, it must be as a measurement arm, and the burden of proof is on it.

## 4. The tension: fewer gates is not always easier for CDCL

The brief asks what the evidence says. There are now three independent
measurements, and they agree.

### 4.1 STP's divider measurement — the cleanest statement of the tension

`references/stp/include/stp/STPManager/UserDefinedFlags.h:878-891`, verified
verbatim. `division_variant_4` is a two-stage borrow-chain divider (the same
circuit as Bitwuzla's):

> `at 226 bits the same division falls from 1,015,894 AIG nodes to 458,106,`
> `which is what Bitwuzla's divider costs, and the two-copy fp.div micro query`
> `solves three times faster. It is nonetheless off by default: over 311 KLEE`
> `binary128 queries the smaller circuit solved 287 against 289 with the`
> `recursive one, and on an escalated 256-bit refutation it turns a 39 s proof`
> `into minutes -- the borrow chain hides the word-level slices a CDCL`
> `refutation of a whole division leans on. Fewer gates is not always an easier`
> `formula; the circuit stays selectable for the workloads it does win.`

**[C]** A **2.2× smaller circuit that is a net loss** on the corpus it was
built for, and catastrophically worse on refutations. The stated mechanism —
the borrow chain destroys word-level structure a refutation leans on — is the
same mechanism as our own Sage2 finding below.

This directly qualifies §2.5(c): our divider *is* more expensive than
Bitwuzla's, and porting Bitwuzla's is a change STP measured and then **declined
to make the default**. It belongs in the ranked list as a *policy option with a
measurement arm*, not as a fix.

### 4.2 Our own, in-tree

`crates/axeyum-rewrite/src/canonical.rs:19-45` records a measurement on
`QF_BV/Sage2/bench_6444.smt2` (a 200-term accumulator with 163 prefix bounds,
`unsat`):

`crates/axeyum-rewrite/src/canonical.rs:19-45` records a measurement on
`QF_BV/Sage2/bench_6444.smt2` (a 200-term accumulator with 163 prefix bounds,
`unsat`):

| form | CNF | outcome |
|---|---|---|
| AC-flattened and rebuilt as a balanced tree over sorted operands | 13 556 vars / 53 598 clauses | **unsolved at 60 s** (and CaDiCaL does not solve that same CNF in 120 s) |
| original left-associated chain preserved | 29 189 vars / 101 984 clauses | **8.5 ms** |

**The smaller CNF is nearly twice as small and does not solve.** The reason is
stated in the comment: the source emits `s1 = a+b`, `s2 = s1+c`, … and asserts
bounds on many prefixes; the chain means the whole family costs one adder chain
and the SAT solver propagates *along* it. Rebuilding gives each prefix its own
tree and destroys that. **[C]** The cap chosen was 64 operands, and the comment
records that a cap of 16 bought `bench_6444` but cost
`QF_BV/float/div3.c.50.smt2` (20.4 s `sat` → `unknown` past a 24 s budget),
while 64 keeps both and decides `div3.c.50` in 10.7 s. **[C]**

The same file also records the counter-direction from
`crates/axeyum-solver/src/auto.rs:1975-2010`: on `062-bench_2195` the term DAG
*shrank* (1375 → 1215) while the AIG *grew* 46 %. **Term count is not merely a
weak proxy for encoding size — on that file it points the wrong way.** **[C]**

### 4.3 Our own reverted Booth experiment

`crates/axeyum-bv/src/lib.rs:2305-2311` records that modified-Booth (radix-4)
recoding was implemented here, verified (exhaustive evaluator equality plus a
DRAT miter), and **reverted**: it halves the partial-product count but its
per-digit select/negate logic is ~4× heavier than a single AND, giving a net
AND-node change of **+6 % at width 8, −8 % at width 16, −14 % at width 24**.
The comment notes the public QF_BV frontier instances are 8-bit, where Booth is
a regression. **[C]**

This is our measurement of exactly the trade STP flags as "a question for
measurement" (§3.4), and it answers it for our corpus: **width-dependent, and
negative at the widths we are graded on.** It also demonstrates that the
`certify_bitblast_by_miter` route (§1.5) already works as the acceptance gate
for a topology change.

**[I]** The practical rule these three measurements support: *sharing and
implication-chain structure beat size*. A transformation that preserves both and
shrinks (the XOR restructuring in §2.5(a)) is safe. A transformation that
shrinks by destroying sharing or by flattening an implication chain is a
gamble, and must be gated by a measured cost model — which is precisely why
`reduction_shrinks_encoding` exists and why any encoding-policy work must be
A/B'd on corpora, not argued from node counts.

---

## 5. Design: what a configurable encoder should look like here

**[I]** throughout this section.

Bitwuzla parameterises one axis (the bit primitive). We should parameterise two,
because we have three consumers (QF_BV, QF_ABV via array elimination, QF_FP) and
they have different profiles.

### 5.1 The two separable decisions

```
trait BitSink                       // what a gate IS
    fn false_(), true_(), fresh_bit()
    fn not(a), and(a,b), or(a,b), xor(a,b), mux(c,a,b)
```

Implementations: the AIG (today's `Aig`), a constant-folding evaluator, a
gate-counting instrument (for the cost model), later a CNF-direct sink.

```
struct EncodingPolicy                // which CIRCUIT to build
    adder:      AdderTopology        // RippleCarry | Sklansky | KoggeStone | BrentKung
    multiplier: MultiplierTopology   // ShiftAdd | Wallace | Dadda | Booth4
    divider:    DividerTopology      // Restoring | TwoStage | DefineAndAssert
    shifter:    ShifterTopology      // LogShifter | ...
    comparator: ComparatorTopology   // EqualPrefix | NotGreaterRipple
```

`EncodingPolicy` must be selectable **per call site**, not only per query: the
right multiplier for an 8-bit operand differs from the right one for 64 bits
(see §5.3), and QF_FP's significand multiply is a different regime from a
symbolic-execution `bvmul`.

**Factor generation and summation separately.** STP's 19 multiplier variants are
not 19 hand-written multipliers — they are a small set of partial-product
*generators* (AND array, radix-2 Booth, radix-4 Booth, radix-4 hard-triple)
crossed with a small set of column *summation* strategies (per-row ripple,
carry-save rows, greedy column network, Dadda, sorting networks), §3.1. Writing
`MultiplierTopology` as a flat enum of whole multipliers throws that away and
guarantees the combinatorial blow-up lands in copy-pasted code.

**The multiplier's output range must be a parameter, not a convention.** **[P]**
Brain (SMT 2021): *"for bit-vector multiplication we only need the low n bits,
for floating-point we need the high n+1 bits."* Our `lower_mul_op` truncates to
the low `width` bits (`crates/axeyum-bv/src/lib.rs:2278-2327`) — right for
`bvmul`, wrong for an FP significand multiply, which wants the high half plus a
sticky OR of everything below. A `MultiplierTopology` that bakes "truncate low"
into its signature cannot serve QF_FP. See §8.6.

**And make the shifter configurable before the multiplier, if QF_FP matters.**
**[P]** SymFPU is parametric over a circuit back-end, and across all three of
its symbolic back-ends the *only* routines ever overridden are two shift
variants — never the multiplier, never the divider. FP needs shift forms plain
`bvshl`/`bvlshr` cannot express (sticky-fused, order-encode,
normalise-and-report-amount).

**Two constraints from our existing lowerer that a naive trait extraction will
break.** `lower_add_bits` and friends interleave `self.poll_deadline()?` on a
64-bit stride (`crates/axeyum-bv/src/lib.rs:2807-2809`,
`crates/axeyum-bv/src/lib.rs:2314-2320`), and every operator returns
`Result<_, BitLowerError>` carrying the `TermId` for width-mismatch reporting.
**[C]** A `BitSink` trait whose methods are infallible and deadline-free forces
either a wrapper that re-adds both or the silent loss of interruptibility on
exactly the operators (multiplier, divider) that need it most. Put the deadline
and the error type in the policy-facing signature from the start. **[I]**

### 5.2 Data structures the AIG needs before any of this matters

`Aig` currently has no fanout, level, or refcount arrays
(`crates/axeyum-aig/src/lib.rs:268-276`). Add, in this order:

1. `fanout_count: Vec<u32>` — needed by every sharing-preserving decision, and
   already computed transiently by the CNF encoder
   (`crates/axeyum-cnf/src/lib.rs:4352`). Making it a graph property removes a
   full pass and unlocks the Bitwuzla `parents() > 1` guard at *construction*
   time.
2. `level: Vec<u32>` — needed for balancing and for any depth-vs-size policy.
3. Reference counts + a free list — needed for MFFC computation, which is the
   cost model every ABC-style rewrite uses, and for garbage collection.

None of these change determinism: they are derived from the same
caller-request-ordered node vector.

### 5.3 Where the policy pays off beyond QF_BV

- **QF_FP.** `crates/axeyum-fp/Cargo.toml` shows the crate depends only on
  `axeyum-arith` and `axeyum-ir` — it builds **BV terms over the typed IR**, not
  circuits. The calls are `TermArena` constructors:
  `arena.bv_add(e, lead_idx)?` (`crates/axeyum-fp/src/lib.rs:694`),
  `arena.bv_shl(m, neg_drop)?` (`:751`), and so on, so an FP formula is an IR
  term graph that reaches `lower_terms` like any other. Counting spellings in
  `crates/axeyum-fp/src/lib.rs` (8257 lines):
  `bv_sub` ×37, `bv_or` ×27, `bv_shl` ×26, `bv_add` ×11, `bv_lshr` ×5,
  `bv_mul` ×2, `bv_udiv`/`bv_urem` ×2 each, plus comparisons. **[C]** So every
  QF_FP query flows through the *same* `lower_terms` circuit library, and the
  adder and shifter are the FP hot path (alignment/normalisation shifts and
  significand subtraction). **A configurable BV encoder is automatically a
  configurable FP encoder** — no separate work, and the adder improvement in
  §2.5(a) lands on QF_FP for free.
  **And we are already on the good side of the main FP encoding fork.** STP has
  a whole native-packed-operand FP family as an alternative to SymFPU's
  unpack/repack circuits, the first of which — `fp_native_cmp`, "bit-blast the
  floating-point predicates — comparisons, equalities and classifications — over
  already-packed operands natively (over the IEEE bits) instead of via the
  SymFPU unpacking circuits" — is **on by default**
  (`references/stp/include/stp/STPManager/UserDefinedFlags.h:924-927`). **[C]**
  Our classification predicates already do exactly that: `is_nan` is
  `exp_all_ones ∧ sig_nonzero` read straight off the packed BV
  (`crates/axeyum-fp/src/lib.rs:409-413`), and `is_infinite`, `is_zero`,
  `is_subnormal`, `is_normal` follow the same shape (`:417-448`). **[C]** So the
  SymFPU-unpacking cost that STP added a flag to avoid is a cost we never paid
  on predicates.

  STP's *unlanded* FP levers, for whoever works on QF_FP next, all in the same
  header: `fp_native_arith` (packed-operand `fp.mul`, experimental, off),
  `fp_native_add_iszero` (recognise `fp.isZero(fp.add …)` and encode the
  zero-result condition instead of constructing and packing every result bit),
  `fp_native_domain` (mine finite box bounds to omit impossible NaN/infinity
  cases), and a `fp_domain_*` prepass family (`:928-984`). **[C]** These are
  word-level, not circuit-level, and none of them is in our tree.

- **QF_ABV.** `eliminate_arrays` (ADR-0010) reduces to QF_BV, so the same
  library applies; the Ackermann congruence conditions are chains of
  equalities, which are comparator-shaped, so §2.5(b) helps there
  disproportionately.
- **QF_BVFP / QF_AUFBV** likewise, since all of them bottom out in
  `lower_terms`.
- **Anything int-blasted.** `crates/axeyum-rewrite/src/int_blast.rs` and the
  "int-blast ladder" route bounded integer problems through BV, so QF_LIA/QF_NIA
  instances that take that route inherit the adder and multiplier choice.
  PLAN.md records the int-blast ladder as decisive on 158 of 161 undecided
  QF_NIA files, which is a large blast radius for a multiplier change. **[C]**

### 5.4 The acceptance test already exists

Any new topology must be proved equivalent to the current one before it ships.
`certify_bitblast_by_miter` (`crates/axeyum-solver/src/bitblast_miter.rs`) does
exactly this with a DRAT-checked refutation over the whole operator set — an
exhaustive equivalence certificate, not a sample. Use it as the gate for every
`EncodingPolicy` variant; a `sat` miter is a bug with a witness.

---

## 6. Ranked findings

Ranked by expected solve-time improvement per unit of implementation effort.
"Beyond QF_BV" names the other divisions that inherit the gain — everything that
bottoms out in `lower_terms` does, which is QF_ABV (via `eliminate_arrays`),
QF_FP and QF_BVFP (the FP crate builds BV *terms*, §5.3), QF_AUFBV, and any
QF_LIA/QF_NIA instance taking the int-blast ladder.

**A standing caveat on every item below.** Three independent measurements (§4)
say node count is not solve time. Every item here must be A/B'd on corpora
before it becomes a default; `AigConstructionStats::and_nodes_created` with
`delta_since` (`crates/axeyum-aig/src/lib.rs:232-266`) gives the per-operator
attribution, and `certify_bitblast_by_miter` gives the correctness gate. Items
1–3 are the ones where the node-count argument is *also* a
propagation-preserving argument, which is why they rank where they do.

---

### Rank 0 — Measure the AIG-rewriting ceiling with ABC before building any of it

**Effort: a shell script and an afternoon. No Rust.**

Ranks 7–9 (technology-mapped CNF, SAT sweeping, DAG-aware rewriting) are the
large builds. **We can measure their combined ceiling on our own corpora first,
without implementing anything**, because the export half of the bridge already
exists.

`Aig::to_aiger_ascii` (`crates/axeyum-aig/src/lib.rs:628-669`) emits standard
ASCII AIGER (`aag`): dense node ids as variable indices, no latches, inputs in
order, ANDs in dense node order, named outputs. **[C]** So:

1. lower a corpus file, dump the AIG as `.aag`;
2. feed it to ABC — `read_aiger`, `print_stats`, a resynthesis script,
   `print_stats` — and read the AND-count before and after;
3. optionally have ABC write its CNF and compare clause counts against
   `tseitin_encode`'s.

That answers the only question that matters before committing to the expensive
tier: **how much redundancy is actually left in the AIGs we produce?** If
ABC's resynthesis removes 3 % of our AND nodes, ranks 7–9 are not worth
building and this survey's expensive half should be dropped. If it removes 30 %,
they are the main event. Either way the number is cheap and we currently do not
have it.

Two caveats. There is **no AIGER importer**
(searched `from_aiger`/`parse_aiger`/`read_aiger` across `crates/`, zero hits;
`aiger` appears only in the exporter and in unrelated files) **[C]**, so this
measures the ceiling — it does not let us *use* ABC's output. And there is no
`abc` binary on this host: `command -v abc` finds nothing and
`/nas3/data/axeyum/harness/bin/` holds `bitwuzla`, `cvc5`, `yices-smt2`,
`smtinterpol` and our own binaries but no ABC. **[C]** It would have to be built
first, and ABC is not on the fleet capability baseline
(`docs/contributor-guide/fleet-hosts.md`), so confirm the host before believing
any result. **[I]**

**[I]** This is ranked zeroth because every item in ranks 7–9 is a multi-week
build whose payoff is currently unmeasured, and the measurement costs
essentially nothing. Ranking a build above the measurement that would justify it
is how a lane spends a month on a 3 % win.

### Rank 1 — Re-factor `Aig::xor` to the shared-conjunction form

**Effort: one function body, ~6 lines. No call sites change.**

Change `xor(a,b)` from `or(and(a,¬b), and(¬a,b))` to
`and(or(a,b), ¬and(a,b))` (`crates/axeyum-aig/src/lib.rs:425-449`). Both are 3
AND nodes standalone; the second allocates `and(a,b)`, which every half adder
also needs as its carry, so the structural hash returns it instead of allocating
a fourth node.

- Full adder: **9 → 7 AND nodes per bit** (§2.5(a)).
- Confirmed identical in all three reference solvers, by three different
  spellings that produce one AIG (§3.2).
- Compounds: it is a *precondition* for the divider gain (§2.5(c)) and it is
  the inner loop of the multiplier.
- **Beyond QF_BV**: yes, everything. The FP significand path is adder-dominated
  (`bv_sub` ×37, `bv_add` ×11 in `crates/axeyum-fp/src/lib.rs`).
- Risk: essentially nil for correctness (`certify_bitblast_by_miter` proves it),
  but it moves CNF variable and clause counts, so any test pinning an absolute
  clause count downstream of bit-blasting will need re-pinning. The AIG
  node-count assertions in `crates/axeyum-bv` are *relative* comparisons
  (`:4767`, `:4789`, `:4926`), so those are safe.

### Rank 2 — Reformulate `lower_unsigned_less` to the "not-greater" recurrence

**Effort: one function body, the general-case loop only.**

Replace the `equal`-prefix accumulator
(`crates/axeyum-bv/src/lib.rs:2862-2877`) with
`less_i = (¬a_i ∧ b_i) ∨ (¬(a_i ∧ ¬b_i) ∧ less_{i-1})`. Using "not greater"
instead of "equal" absorbs the XOR entirely: **7 → 4 AND nodes per bit** (§2.5(b)).

- This is the recurrence Bitwuzla
  (`references/bitwuzla/src/lib/bitblast/bitblaster.h:478-500`) and Boolector
  (`references/boolector/src/btoraigvec.c:150-177`) both use.
- Keep all seven existing constant fast paths — they are ours alone and no
  reference solver has them.
- Compounds: the comparator is called once per bit position inside the divider,
  over `width+1` bits, so the divider gets a second-order saving for free.
- **Beyond QF_BV**: yes. QF_ABV's Ackermann congruence conditions are chains of
  equalities and comparisons; FP comparison predicates likewise.

### Rank 2a — Check whether our full adder and comparator are propagation complete

**Effort: a check, then possibly a gadget swap. Small.**

**[P]** CVC4's shipped full adder was 8 vars / 17 clauses and **not** propagation
complete; the generated PC one is **5 vars / 14 clauses** — smaller *and*
stronger. Its `ult` gadget went 5/10 → **4/6**. A 2016 audit found Boolector,
STP2, Yices2 and Z3 all ship non-PC addition (VMCAI 2016, §8.2).

This sits directly on top of Ranks 1 and 2 — all three are about the shape of
the same two gadgets — so **do the check first and decide the three together**,
rather than landing Rank 1 and then discovering the PC gadget wants a different
factorisation. We have not checked ours; this survey did not.

Temper expectations: the 25× in that literature is a *gadget-level* propagation
figure. The authors' own end-to-end result is +15 solved on 31,066 QF_BV
benchmarks, which they call "not dramatic… but consistent." **[P]**

### Rank 2b — Blocked clause elimination

**Effort: moderate, and it is the best-fitting item in this list for how this
project works.**

We do not have it (§8.1; the only `blocked_clause` hit in `crates/` is a DRAT
checker test asserting a blocked clause is RAT-not-RUP,
`crates/axeyum-cnf/src/drat.rs:1299-1307`). **[C]** Measured on 3,672
bit-blasted QF_BV instances, BCE on plain Tseitin reaches 420 M vars / 1 119 M
clauses where PG reaches 442 M / 1 153 M — better on both axes, and it subsumes
PG as a theorem, not just empirically. **[P]**

Why it fits here specifically:

- It only **deletes**, so DRAT reconstruction is `d` lines, and **a bug in the
  blocked-clause detector cannot produce a wrong `unsat`** — deleting a
  non-blocked clause only weakens the formula. That is a rare shape: an
  optimisation whose failure mode is "the proof stops going through", not
  "the answer is wrong".
- It is **confluent**, unlike variable elimination.
- Our model lift already recomputes node values from inputs, which is exactly
  the discipline BCE's non-model-preservation requires.

**The caveat is load-bearing**: the paper's QF_BV *solve-time* experiments were
run at 90 s and reported as **inconclusive**. Only the size wins are measured.
**[P]** So this is a build with a measured size case and an unmeasured speed
case — which is the same epistemic position as Rank 7, at a fraction of the
effort.

### Rank 3 — Put fanout counts on the `Aig`

**Effort: one `Vec<u32>` maintained in `and`/`push_node`; small.**

`Aig` has no fanout array (`crates/axeyum-aig/src/lib.rs:269-276`), yet the CNF
encoder computes one on every encode (`node_use_counts`,
`crates/axeyum-cnf/src/lib.rs:4352`). Making it a graph property:

- removes a full traversal per encode;
- lets the *construction-time* rules apply Bitwuzla's `parents() > 1`
  sharing guard, which today they cannot;
- is the prerequisite for MFFC computation, and hence for **every** item in the
  AIG-rewriting family below.

Ranked here rather than lower because it is cheap and unblocks the expensive
tier. No behaviour change on its own, so nothing to A/B.

### Rank 4 — Complete the Brummayer–Biere two-level rule set in `Aig::and`

**Effort: moderate. The full rule table is transcribed in §2.2 with line
citations, and the loop structure is the whole trick.**

We have level 1 plus OR-absorption and OR-consensus. Missing: the asymmetric
and symmetric contradiction rules, the two-AND idempotence rules, and — most
importantly — **the operand-rewriting `continue` loop** that lets levels 3 and 4
narrow the operand pair without allocating, so rules chain
(`references/bitwuzla/src/lib/bitblast/aig/aig_manager.cpp:177-408`).

- Cost is bounded and local: it is *two-level*, never traversing more than
  grandchildren, which is what "without blowup" means.
- Applies to every gate we ever build, so it reaches every division.
- Needs Rank 3 first if the sharing guards are to be honoured.

### Rank 5 — `bvudiv`/`bvurem` by defining relation, as a selectable policy

**Effort: ~150 lines, following STP's construction exactly (§3.3).**

Fresh `q`, `r`; magnitude ladder `h[i] ⟺ y < 2^i`; one binary clause `¬q[k] ∨ h[w-k]`
per quotient bit; `y*q + r` at width `w+1` with every carry-out pinned false;
`acc = x`; `y = 0 ∨ r < y`. Build **STP's version, not Bitwuzla's** — Bitwuzla
asserts `¬bvumulo` and `¬bvuaddo`, i.e. two extra overflow circuits, where STP
uses `w-1` binary clauses.

- Trades a quadratic divider for a quadratic multiplier plus a comparator. Not
  obviously smaller; *differently shaped*, and shaped like the thing
  preprocessors handle better.
- **Ship it behind a flag with a measurement arm**, never as a default. STP
  ships two circuit-free division encodings and neither is on by default.
- **Beyond QF_BV**: FP division and square-root paths use `bv_udiv`/`bv_urem`.

**⚠ The soundness caveat, added after the paper survey (§8.3).** Bitwuzla built
this exact pass and then **dead-coded it**:
`references/bitwuzla/src/preprocess/preprocessor.cpp:355-356` reads
`// Disabled until murxla-c598aa85aefc51a0.min.smt2 is fixed.` /
`if (false && options.pp_elim_bv_udiv())` — the option and the pass still exist,
only the call is disabled, and the named blocker is a **Murxla fuzzer**
minimisation. **[C]** The known failure mode of this technique is therefore a
fuzzer-found soundness bug on a corner case, which is exactly this repository's
`a946f925` class. **This pass must not land without a fuzz seed-class that
deliberately emits a zero divisor** — CLAUDE.md's hard rule applies to it
verbatim, and a corpus sweep plus a fuzz that avoids the corner is not a gate.

**Two sources do recommend the rewrite** (Brain, SMT 2021 fn. 6; POS 2026 §1),
and **no published comparison of division encodings exists at all** — three
solvers, three dividers, no cited justification for any. **[P]** So this is
also the cheapest genuinely novel experiment in the list.

### Rank 6 — The two-stage divider, as a selectable policy only

**Effort: one function; the algorithm is fully written out in §2.5(c).**

Our divider does three passes per bit position (comparator, subtract, restore
mux) over `width+1` bits where Bitwuzla does two over `width`, and the
comparison falls out of the carry chain for free.

**Ranked sixth, not second, because STP measured this exact change and declined
it as a default** (§4.1): 2.2× fewer AIG nodes, three times faster on a
micro-query, but **287 vs 289** solved over 311 KLEE binary128 queries and a 39 s
refutation turned into minutes. Implement it as an `EncodingPolicy` variant with
a measurement arm; do not ship it as the default on a node-count argument.

### Rank 7 — Technology-mapping-based CNF generation

**Effort: large — cut enumeration, a 64K min-SOP table, area-flow mapping.
Do Rank 0 first.**

ABC's mapper minimises the clause count *directly*: a cut's cost is
`|minSOP(f)| + |minSOP(¬f)|`, which is exactly the clauses it will emit
(`references/abc/src/sat/cnf/cnf.h:99`), and area flow amortises shared cuts
(§7.1). Nodes that fall inside a chosen cut get no variable at all.

**Ranked seventh, not higher, for one reason: our baseline is not plain
Tseitin.** ABC's large published wins are measured against 1 var / 3 clauses per
AND node (`cnfWrite.c:595-596`). We already fuse XOR, ITE, OR/not-AND and
positive AND-trees with fanout guards, which is a hand-written special case of
what the mapper generalises. **Nobody has measured the delta between a mapped
encoder and an encoder like ours**, and this survey cannot supply it. **[I]**

**The published numbers, now that §8.5 supplies them, argue both ways.** Eén,
Mishchenko & Sörensson (SAT 2007) measured 62 % fewer clauses and a **22.3×**
total speedup on Cadence BMC with the full pipeline — and **0.9× total, 0.3×
harmonic (a slowdown)** on SAT-Race `manol-pipe`, because the transformations
destroy the equivalent-point structure equivalence checking relies on. **[P]**
A pipeline with a 22× win on one family and a 3× loss on another is the exact
profile that must be measured on *our* corpora, which is Rank 0.

The cheap variant, `Cnf_DeriveFast` (supergate collection only,
`references/abc/src/sat/cnf/cnfFast.c:666+`), we already have.

### Rank 8 — SAT sweeping / functional reduction, with checkable evidence

**Effort: large. But it is the item that best fits this project's identity.**

Random simulation to form candidate equivalence classes, counterexample-driven
refinement, and bounded SAT calls to prove or refute each candidate (§7.4).
Nothing of this exists here (0 hits for `fraig`, `sweeping`, `random simulation`,
`simulation vector` across `crates/`).

Two reasons it ranks above rewriting despite being a bigger build:

1. **We already own the pieces.** A proof-producing CDCL core with DRAT output
   and an independent DRAT checker (`solve_with_drat_proof`, `check_drat`,
   ADR-0011/0012). A sweep could emit a **checked certificate per merge**
   instead of being a trusted transformation. No reference solver does this,
   and "untrusted fast search, trusted small checking" is the project's stated
   identity.
2. It subsumes work the CNF layer cannot do: two structurally different cones
   computing the same function are invisible to structural hashing and to any
   local rewrite.

Copy: the arena-based classes with in-place stable partition
(`references/abc/src/proof/dch/dchClass.c:443-491`), the two-call
solve-under-assumptions with learned blocking clauses (`dchSat.c:45-158`), and
**the soundness rule that timed-out candidates are excluded from all future
merges** (`references/abc/src/proof/fra/fraCore.c:266-270`, `:283-284`) — that
one is easy to get wrong and unsound if you do.

### Rank 9 — DAG-aware AIG rewriting (`rewrite` / `refactor`)

**Effort: largest. Needs Rank 3, plus cut enumeration, plus a subgraph library.**

The gain model is `Dec_GraphToNetworkCount`
(`references/abc/src/bool/dec/decAbc.c:167-226`): cost a candidate by asking the
strash table which of its nodes already exist and are not in the MFFC being
destroyed (§7.2). MFFC comes from deref/ref with traversal stamps
(`references/abc/src/base/abc/abcRefs.c:100-113`), which is why Rank 3 comes
first.

Ranked last of the build items because the expensive part — the subgraph library
— is **tuned to hardware benchmarks** (135 "practical" NPN classes taken from
IWLS/MCNC/ISCAS cuts, `references/abc/src/opt/rwr/rwrUtil.c:31-33`). Our AIGs
come from BV arithmetic, a different distribution. The library and its per-class
priorities would have to be re-derived from our corpora using ABC's own training
machinery (`darLib.c:648`, `:683`), which roughly doubles the project.

**`balance` is deliberately not in this list.** It is the pass that re-associates
AND chains for depth, and §4.2 is our own measurement of an association-chain
rebuild turning an 8.5 ms solve into a 60 s timeout. If it is ever tried, it must
be behind the same measurement discipline as Rank 6.

### Not recommended

- **Parallel-prefix adders (Sklansky, Kogge-Stone, Brent-Kung).** Zero of four
  reference solvers use one; a search across all four codebases returns no hits
  and no comment explaining the absence (§3.6). **Now measured, not just
  argued from absence**: POS 2026 reports that all five parallel-prefix networks
  produce *identical* learned-clause quality, Brent-Kung winning only on
  variable count. **[C]/[P]** The adder knob that does matter is propagation
  completeness of the carry gadget (Rank 2a), which is not a topology choice.
- **Booth recoding as a default.** Measured *here* at +6 % / −8 % / −14 % AND
  nodes at widths 8/16/24, and the QF_BV frontier instances are 8-bit
  (`crates/axeyum-bv/src/lib.rs:2305-2311`); upstream STP calls the CNF-side
  trade "a question for measurement"
  (`references/stp/lib/ToSat/BitBlaster.cpp:3023-3025`). It is a width-gated
  policy option at best. **[C]**
- **Chasing multiplier encodings to make *hard* multiplier instances tractable.**
  **[P]** Beame & Liew (JACM 2019) *refuted* the conjecture that this needs
  exponential resolution — polynomial regular-resolution proofs exist for
  degree-2 ring identities on array, diagonal and Booth multipliers. **The short
  proofs are in CDCL's own proof system and CDCL cannot find them**, so no
  encoding closes the gap; the working answer is algebraic (Kaufmann/Biere/Kauers
  verify 64-bit multipliers in seconds where SAT times out). A propagation-
  complete multiplier is separately unlikely to exist — it would factor in `n`
  propagation calls (Brain, SMT 2021).

  And on *ordinary* instances the encoding is measured neutral: POS 2026, on a
  stratified sample of 66 `bvmul`-carrying SMT-COMP 2024 QF_BV benchmarks,
  **34/66 solved either way, PAR-2 62.5 s vs 62.6 s** — *"most multiplications
  are small (BW ≤ 32) and the bottleneck is rarely the multiplier."* **[P]**
  That corroborates our own reverted Booth measurement
  (`crates/axeyum-bv/src/lib.rs:2305-2311`) and explains STP's 19-variant menu:
  no single multiplier encoding won. **[C]/[P]**

---

## 7. ABC

`references/abc`, verified as upstream `berkeley-abc/abc` at `fbaae01`
(2026-09-05). ABC contains three independent AIG packages; the one to copy for a
from-scratch Rust optimiser is **GIA** (`src/aig/gia/`), because it is
index-based rather than pointer-based.

### 7.1 Technology-mapped CNF — the one thing that could beat our encoder

`src/sat/cnf/`. This is the Eén/Mishchenko/Sörensson route, and the design is
strikingly simple once you see the cost function
(`references/abc/src/sat/cnf/cnf.h:99`, verified verbatim):

```c
static inline int Cnf_CutSopCost( Cnf_Man_t * p, Dar_Cut_t * pCut )
{ return p->pSopSizes[pCut->uTruth] + p->pSopSizes[0xFFFF & ~pCut->uTruth]; }
```

**The cost of a cut is `|minSOP(f)| + |minSOP(¬f)|` — which is exactly the number
of CNF clauses that cut will emit.** So the technology mapper's objective
function *is* the clause count, and the standard area-flow machinery
(`Cnf_CutAssignAreaFlow`, `references/abc/src/sat/cnf/cnfMap.c:45-60`, which
amortises a shared cut's cost by `/nRefs`) minimises clauses subject to sharing.
**[C]**

The pipeline (`Cnf_DeriveWithMan`, `references/abc/src/sat/cnf/cnfCore.c:144-179`):

1. enumerate ≤4-input cuts, ≤10 per node (`Dar_ManComputeCuts`);
2. one topological pass picking the min-area-flow cut per node, tie-broken
   toward more-referenced leaves (`Cnf_DeriveMapping`, `cnfMap.c:100-151`);
3. materialise the chosen cuts;
4. `Cnf_ManScanMapping` (`cnfUtil.c:327-394`) walks *only* the selected cuts and
   **recomputes `nRefs` over the mapped graph** — internal AND nodes that sit
   inside somebody's cut and are not themselves a cut root get `nRefs == 0` and
   **never receive a CNF variable at all**;
5. emit two covers per node: each cube of `f` becomes `(out ∨ ¬cube)`, each cube
   of `¬f` becomes `(¬out ∨ ¬cube)` (`cnfWrite.c:324-367`, cube decoding at
   `:82-104` and `:170-184`).

**The enabling data structure is small and self-verifying.**
`references/abc/src/sat/cnf/cnfData.c` stores the minimum SOP of *every*
4-variable function as base-3-packed cubes in an 81-character alphabet
(`cnfData.c:30`), decoded at load into `pSopSizes[65536]` and `pSops[65536]`
(`Cnf_ReadMsops`, `cnfData.c:4537-4605`). The loader then re-expands every entry
and asserts the truth table round-trips (`cnfData.c:4586-4604`). **[C]** So
"minimum CNF for any 4-input function" is a table lookup, and the table can be
regenerated rather than transcribed.

**The honest comparison.** ABC's own plain-Tseitin baseline is exact
(`Cnf_DeriveSimple`, `references/abc/src/sat/cnf/cnfWrite.c:595-596`, verified):

```c
nLiterals = 1 + 7 * Aig_ManNodeNum(p) + Aig_ManCoNum(p) + 3*nOutputs;
nClauses  = 1 + 3 * Aig_ManNodeNum(p) + Aig_ManCoNum(p) +   nOutputs;
```

— exactly 1 variable, 3 clauses and 7 literals per AND node. Against *that*
baseline the mapped encoder is a large win (an XOR built from 3 AND nodes goes
from 3 vars / 9 clauses to 1 var / 4 clauses; a 3-input XOR from 9 AND nodes to
1 var / 8 clauses). **[C]/[I]**

**But plain Tseitin is not our baseline.** `tseitin_encode` already fuses XOR,
not-ITE, not-AND/OR and positive AND-trees with fanout guards (§1.3), which is a
hand-written special case of exactly what the mapper does generically. **The
marginal gain of a mapped encoder over *our* encoder is therefore much smaller
than the against-plain-Tseitin figures suggest, and nothing in ABC measures that
particular delta.** **[I]** This is the single most important caveat in this
section, and it is why Rank 0 (measure the ceiling) exists.

Two further notes:

- `Cnf_DeriveFast` (`references/abc/src/sat/cnf/cnfFast.c:666+`) is a
  mapping-free variant that only collects multi-input AND supergates — "most of
  the benefit for a fraction of the code". **We already have this** as
  `plan_and_tree_gates`. **[C]/[I]**
- **A DIMACS-export hazard, recorded as a shape to know, not as a defect here.**
  `Cnf_DataWriteDanglingUnitClauses`
  (`references/abc/src/sat/cnf/cnfMan.c:36-67`) exists because a primary input
  wired straight to a primary output has no fanout into any AND, so its declared
  DIMACS variable appears in **no clause** — silently doubling a model count.
  ABC's fix is a unit clause per unreferenced declared variable. **[C]**

  I checked how far this applies to us and the answer is: **not demonstrated,
  and probably not analogous.** `crates/axeyum-cnf/src/weighted.rs` is
  weighted-at-most constraint composition, not model counting. The only
  counting-shaped route I found is one all-SAT test
  (`crates/axeyum-solver/tests/symbolic_execution.rs:1879`), which enumerates at
  the term level. And an unconstrained *symbol bit* in our encoding is a genuine
  free variable of the query, so its absence from every clause is correct, not a
  leak. **[C]/[I]** The one case where ABC's guard would matter is if we ever
  hand our DIMACS to an external #SAT or projected-counting tool — then the
  declared variable count must be justified clause-by-clause. **I did not find a
  defect and none should be reported on the strength of this note.**

### 7.2 DAG-aware rewriting — the gain model is the whole idea

The function to port is `Dec_GraphToNetworkCount`
(`references/abc/src/bool/dec/decAbc.c:167-226`). It walks a *candidate*
replacement subgraph bottom-up and, for each of its AND gates, asks the
**existing structural hash table** whether that AND already exists in the
network. If it does, and it is not inside the MFFC about to be destroyed, it
costs **zero** — the rewrite will reuse it. **[C]**

```
gain = MFFC size of the root (bounded by the cut) − nodes actually added
```

That is the entire "DAG-aware" claim: cost is measured against the whole rest of
the DAG, not against an isolated cone. The two halves:

- **MFFC by deref/ref with traversal stamps.** `Abc_NodeMffcLabelAig`
  (`references/abc/src/base/abc/abcRefs.c:100-113`, recursion at `:215-253`)
  decrements fanout counts recursively, stamping every node it could free with
  the current TravId, then restores. A node is in the MFFC iff dereferencing the
  root drives its fanout count to zero. **This needs reference counts on the
  graph — see Rank 3.** **[C]**
- **Boundary inflation.** Before computing the MFFC, the cut leaves' fanout
  counters are temporarily incremented so the MFFC computation stops at the cut
  boundary, then decremented (`references/abc/src/opt/rwr/rwrEva.c:139-147`).
  **[C]** A small trick that is easy to miss and load-bearing.

The subgraph library: `Extra_Truth4VarNPN`
(`references/abc/src/misc/extra/extraUtilMisc.c:643-731`) precomputes four 64K
tables — canonical form, input phases plus an output-complement bit, permutation
index, and class number — and asserts `nClasses == 222` (`:716`, verified). Of
those, **135 are "practical"**, hard-coded from cuts actually observed in IWLS,
MCNC and ISCAS benchmarks (`references/abc/src/opt/rwr/rwrUtil.c:31-33`,
verified verbatim). The `dar` library is 43 906 nodes over 24 772 subgraphs with
a **per-class priority array** learned from observed gains
(`references/abc/src/opt/dar/darData.c`; the training mode that produced it is
`darLib.c:648`, `:683`). Runtime keeps only the top `nSubgMax = 5` per class —
`"5 is a magic number"` (`references/abc/src/opt/dar/darCore.c:51-64`). **[C]**

**[I]** The library is the expensive part to reproduce, and it is *tuned to
hardware benchmarks*. Our AIGs come from BV arithmetic, which is a different
distribution — adders, comparators, muxes, barrel shifters. If we ever build
this, the practical-class list and the per-class priorities should be
**re-derived from our own corpora**, not transcribed from ABC's. That is what
`Rwr_ScoresReport` (`references/abc/src/opt/rwr/rwrEva.c:550-591`) and the
per-class gain breakdown in `Dar_ManPrintStats`
(`references/abc/src/opt/dar/darMan.c:113-121`) exist to produce.

### 7.3 `refactor`, `balance`, and the scripts

- **`refactor`** uses the *same* gain evaluator as rewrite; the only differences
  are cut size (10–16 inputs rather than 4) and how the candidate is produced —
  reconvergence-driven cut, truth table, Minato–Morreale ISOP with both
  polarities tried, algebraic factoring
  (`references/abc/src/base/abci/abcRefactor.c:191-215`;
  `references/abc/src/bool/kit/kitIsop.c:134-182`;
  `references/abc/src/bool/kit/kitGraph.c:356-371`). The cut-growth cost
  function (`abcReconv.c:126-144`) takes an expansion for free when **both**
  fanins are already in the cut — that is what "reconvergence-driven" means, and
  it is why the cuts land on exactly the regions where refactoring can win.
  **[C]**
- **`balance`** rebuilds the network from scratch rather than transforming in
  place (`references/abc/src/base/abci/abcBalance.c:53-89`). It collects maximal
  AND supergates (stopping at complemented edges and multi-fanout nodes,
  `:345-378`), sorts operands by decreasing level, and repeatedly pops the two
  **lowest-level** operands — Huffman-style height reduction. Layered on top:
  `Abc_NodeBalancePermute` (`:192-228`) searches within the set of
  depth-equivalent pairings for one whose AND **already exists in the hash
  table**, i.e. it buys sharing for free wherever depth does not care. **[C]**
  Node count can go either way: re-strashing from scratch and the permute
  heuristic shrink it, while re-association can destroy the sharing the original
  structure had, and `-d`/`-s` explicitly duplicate logic. **[C]/[I]** Given §4,
  balance is the ABC pass we should be *most* cautious about — it is precisely
  the "flatten an association chain" transformation our own Sage2 measurement
  says can turn an 8.5 ms solve into a timeout.
- **The scripts** (`references/abc/abc.rc`, verified):
  - `resyn2` = `b; rw; rf; b; rw; rwz; b; rfz; rwz; b`
  - `compress2rs` = `b -l; rs -K 6 -l; rw -l; rs -K 6 -N 2 -l; rf -l; rs -K 8 -l; b -l; …; rwz -l; b -l`
    (`-l` preserves level; `K` ramps 6 → 12 so expensive resubstitution only runs
    after the network has shrunk).
  The interleaving logic: `b` re-strashes and thereby **changes the cut space**
  the next `rw` sees, which is why it appears between every pair of transforms;
  `rwz`/`rfz` accept zero-gain moves purely to perturb structure and unlock the
  next pass. Zero-gain moves need a termination guard — ABC freezes the node
  budget at the start of a pass so newly created nodes are never revisited
  (`references/abc/src/base/abci/abcRewrite.c:109`, `:115-116`). **[C]**

### 7.4 SAT sweeping / FRAIG

Three generations exist; the two worth reading are `dch` (`src/proof/dch/`) and
`&fraig` (`src/proof/cec/`).

- **Equivalence classes in an arena, refined by stable in-place partition.**
  `Dch_Cla_t` (`references/abc/src/proof/dch/dchClass.c:36-57`) holds
  `pId2Class` indexed by representative id and `pMemClasses` as one contiguous
  arena. `Dch_ClassesRefineOneClass` (`:443-491`) splits a class by writing the
  two halves **back-to-back into the same arena slot**, so refinement allocates
  nothing. **[C]** That is the trick worth copying.
- **Two SAT calls per candidate pair, under assumptions, with learned blocking
  clauses.** `Dch_NodesAreEquiv` (`references/abc/src/proof/dch/dchSat.c:45-158`)
  splits `A ≠ B` into `A ∧ ¬B` and `¬A ∧ B`, each a solve-under-assumptions with
  a conflict budget (`nBTLimit = 1000`); on UNSAT it adds the negated assumption
  pair as a **permanent binary clause** so later calls benefit. Solver recycling
  is budgeted on *both* variable count and calls-since-recycle. **[C]**
- **Bottom-up sweeping makes most pairs free.** Because the FRAIG is rebuilt
  bottom-up through `Aig_And`, proving an equivalence low in the DAG makes the
  nodes above it merge *structurally*, with no SAT call
  (`references/abc/src/proof/fra/fraCore.c:249-253`). A merge is not a deletion:
  the node's image is redirected to the representative's image with the phase
  difference folded into a complement bit, and structural hashing does the rest
  (`fraCore.c:262-263`). **[C]**
- **A soundness detail we would get wrong.** Nodes whose equivalence proof timed
  out are excluded from all future merges (`fraCore.c:266-270`, with the reason
  at `:283-284`): otherwise a node could be merged with a representative whose
  own proof also timed out. **[C]** Likewise `dch` keeps a separate
  `pReprsProved` and installs it only at the end, so **only SAT-proved
  equivalences survive — never simulation candidates**
  (`references/abc/src/proof/dch/dchSweep.c:133-135`). **[C]**
- **`&fraig` is the scalable rewrite of the idea**: rather than one SAT call per
  pair against the full AIG, it builds a **speculative-reduction miter** in which
  every already-assumed equivalence is substituted, emits an XOR output per
  remaining candidate pair, and solves them together
  (`references/abc/src/proof/cec/cecSweep.c:45+`, driver at
  `references/abc/src/proof/cec/cecCore.c:356+`). **[C]**

**[I]** For us, SAT sweeping is the most *architecturally* interesting of the
three ABC families, because we already own a proof-producing CDCL core and a
DRAT checker — so a sweep could emit checkable evidence for each merge rather
than being a trusted transformation. That is a genuine differentiator, and it is
also a reason the work is larger than it looks: an unchecked sweep would be a
new trusted component, which this project's discipline does not want.

### 7.5 Data structures to copy verbatim

- **GIA node record**, 3 words / 12 bytes, fanins stored as backward **id
  differences** so the array is relocatable and always topologically ordered
  (`references/abc/src/aig/gia/gia.h:77-90`). **[C]**
- **Strash table**: `vHTable` of bucket heads plus a *parallel* `vHash` next-array,
  both `Vec_Int_t`; table size a **prime** (`Abc_PrimeCudd(2 * nAnds)`);
  resize amortised behind `(nObjs & 0xFF) == 0 && 2*tableSize < nAnds`
  (`references/abc/src/aig/gia/giaHash.c:45-190`, `:576-620`). **[C]** Ours is
  open-addressed with power-of-two capacity, which is fine and arguably better
  for cache behaviour; the part worth taking is the **amortised resize check**,
  since ours tests the load factor on every insert
  (`crates/axeyum-aig/src/lib.rs:156-160`).
- **Normalisation by literal, not by id.** GIA swaps on `iLit0 > iLit1` where a
  literal is `2*id + compl` (`giaHash.c:599-600`); the older AIG package orders
  by regular id only and lets the complement bits ride along
  (`references/abc/src/aig/aig/aig.h:346-364`). **We already do the literal
  form** (`crates/axeyum-aig/src/lib.rs:479-481`). **[C]**
- **Bounded cut store with eviction rather than rejection.** `Dar_CutFindFree`
  (`references/abc/src/opt/dar/darCut.c:142-177`) evicts the lowest-value cut
  when the per-node array is full, where value rewards leaves with high
  reference counts (`:106-129`) — DAG-awareness applied to cut *selection*, not
  just to gain. **[C]**

---

## 8. Literature — including two corrections to sections above

The paper survey arrived after §1–§7 were written from source. §8.0 answers the
Plaisted–Greenbaum question from our own code; §8.1 onward is the literature,
and §8.1 and §8.2 revise conclusions in §1.3 and §3.6.

### 8.0 Plaisted–Greenbaum: what it costs us, answered from our own code

The brief asks when the one-sided encoding is sound and profitable and what it
costs in proof terms. **We already use it**, so the most reliable answer is what
our own code does about it — that is [C] rather than [P], and it is the answer
an implementer actually needs.

**The soundness condition, as our code states it.** PG is satisfiability-
preserving, not equivalence-preserving: a gate defined in only one polarity
leaves its CNF variable free in the other direction. `IncrementalCnf`'s doc
comment states both the condition and why the incremental version is sound
(`crates/axeyum-cnf/src/lib.rs:1150-1155`, verified):

> `applied incrementally, which is sound because the encoder only ever *adds*`
> `clauses — never retracts — so a half emitted for an early use stays valid as`
> `the formula grows, and a new use simply triggers the missing half. Gate`
> `definitions are unconditional (only roots are selector-guarded), so push/pop`
> `scopes do not interact with the polarity bookkeeping.`

**[C]** That is the non-obvious part. The usual objection to PG under
*incremental* solving is that a later opposite-polarity use invalidates an
earlier one-sided definition; the resolution is that adding the missing half is
monotone, so nothing already learned becomes unsound.

**The model-extraction cost, and how we pay it.** This is the real price of PG
and it is easy to get wrong. Same comment, `:1157-1161`:

> `Because a node may be left polarity-underconstrained (its CNF variable can`
> `take an arbitrary value the gate definition does not pin), the model lift`
> `aig_node_values reconstructs every node value by forward evaluation from the`
> `input bits rather than reading internal node variables — the same`
> `recompute-from-inputs discipline the one-shot sparse path uses.`

**[C]** So: **under PG you may not read a gate's value out of the SAT model.**
You must recompute it from the input assignment. We do, on both the incremental
and the one-shot path. This is also why our `sat` results stay checkable — the
project's rule that every `sat` is verified by evaluating the *original* term
against the lifted model is exactly the discipline PG forces anyway.

**The proof cost.** The proof-producing route calls the *same* PG-applying
encoder (`tseitin_encode` at `crates/axeyum-solver/src/proof.rs:173` and `:376`),
so DRAT proofs are produced and checked against the PG CNF. **[C]** That is
sound because DRAT certifies "*this* CNF is unsatisfiable", and the separate
obligation — that the CNF faithfully reduces the query — is carried by a
different mechanism (`certify_bitblast_by_miter`, and the reduction trust ledger
of ADR-0031), not by the proof format. **[I]** The practical consequence is that
PG costs nothing on the UNSAT/proof side here: a one-sided encoding of an
unsatisfiable formula is still unsatisfiable, and the refutation is over the
formula actually handed to the solver.

**What PG would break, and does not here.** Model *enumeration* and model
*counting* are the operations that genuinely need the two-sided encoding, because
a polarity-underconstrained variable multiplies the model count. We do not count
models over this CNF (§7.1's last bullet), so this does not bite — but it is the
constraint to remember if a counting route is ever added. **[C]/[I]**

### 8.1 What the literature says, and where it contradicts §1.3

**[P]** Järvisalo, Biere & Heule, *Blocked Clause Elimination*, TACAS 2010,
LNCS 6015:129–144 (journal version *Simulating Circuit-Level Simplifications on
CNF*, JAR 49(4), 2012). Two results matter here.

- **Lemma 4**: `BCE(TST(C))` is at least as effective as `PG(C)` — BCE removes
  *exactly* the clauses Tseitin has and PG does not, working from the outputs
  with no knowledge of the circuit.
- **Strictly stronger**, by the paper's own counterexample: for
  `g := OR(g₁…gₙ)` where `g` has both polarities and one `gᵢ` is an input of
  fanout one, the clauses mentioning `gᵢ` are blocked. PG emits the full Tseitin
  set for any two-polarity gate, so nothing there is pure and PG cannot act.

**[P] And the measurement is on our exact workload.** Their benchmark family
"B" is **3,672 SMT-LIB QF_BV instances bit-blasted to AIGs by Boolector**:

| encoder | variables | clauses | after BCE |
|---|---|---|---|
| Tseitin | 442 M | 1 253 M | **420 M / 1 119 M** |
| Plaisted–Greenbaum | 442 M | 1 153 M | 420 M / 1 119 M |

So on bit-blasted QF_BV: **PG saves 8.0 % of clauses and zero variables, and
BCE on plain Tseitin beats PG on both axes.** The paper also notes that variable
elimination alone does *not* close the Tseitin/PG gap, while BCE does — so
whether the encoding choice is moot depends on *which* simplifier you run. **[P]**

**Why PG does so much less on QF_BV than on hardware** (17.6 % of clauses on
HWMCC BMC vs 8.0 % here): the validity condition for a polarity function
requires `pol(gᵢ) = {t,f}` for **both** operands of an XOR and for the condition
of an ITE. Bit-blasted arithmetic is XOR-dense — every full-adder sum bit is
`a ⊕ b ⊕ c` — so PG degenerates toward Tseitin through every adder. **[P]** for
the condition; **[I]** for the attribution of the 8-vs-17.6 gap to it.

**Consequences for this document.** §0 and §1.3 call our PG encoding a strength
relative to Bitwuzla. That framing needs qualifying, in two directions:

1. **The literature does not treat PG as the good option.** Eén, Mishchenko &
   Sörensson (SAT 2007) explicitly declined it: *"there is no special treatment
   of nodes that occur only positively or negatively."* Boolector, Bitwuzla and
   cvc5 all emit full bi-implications. **[P]/[C]** So "we have PG and Bitwuzla
   does not" is a difference, not automatically an advantage.
2. **But it is not a defect either, and it should not be ripped out.** It is
   already built, already sound (§8's opening), already paid for on the model
   side, and it costs nothing on the proof side. The measured 8 % is a real if
   modest saving. The actionable conclusion is **not** "remove PG" — it is
   "**BCE is the stronger move and we do not have it**" (see the new Rank 2b).

**We do not have BCE.** Searched `crates/` for `blocked.clause`, `blocked_clause`,
`is_blocked`, `BCE`: the only real hit is a *DRAT checker test*,
`blocked_clause_is_rat_but_not_rup` (`crates/axeyum-cnf/src/drat.rs:1299-1307`),
which asserts that a blocked clause is RAT and not RUP. **[C]** (Every other
`bce` hit is a Lean prelude variable named for `b+c+e` — an unmasked-grep false
positive, checked.) So our DRAT checker already understands the rule BCE needs,
and the elimination itself is absent.

**BCE is an unusually good fit for this project's discipline. [P]/[I]**

- It only **deletes**, so on the UNSAT side it is DRAT-reconstructible by
  emitting `d` lines. Deletion lines are unchecked by the checker and do not
  need to be checked: **a bug in a blocked-clause detector cannot produce a
  wrong `unsat`**, because deleting a non-blocked clause only weakens the
  formula and the worst outcome is that the proof stops going through.
- It is **confluent** (their Prop. 4), unlike variable elimination.
- Blocked-clause *addition* is exactly DRAT's RAT rule and is **not**
  resolution-derivable (Järvisalo, Heule & Biere, *Inprocessing Rules*,
  IJCAR 2012: the "resolution tautology" property is the same as "blocked").
  This is the reason DRAT p-simulates extended resolution — relevant to us
  because a kernel that only understands resolution cannot replay it.

**The honest caveat, from the paper itself**: on the structural families —
*including* the bit-blasted QF_BV one — they ran only preliminary 90-second
experiments and report the results as **inconclusive**. **The CNF-size wins on
QF_BV are measured; the solve-time wins on QF_BV are not.** **[P]**

The model-side price is the one §8 already describes, and it is the same price
PG charges: BCE does not preserve models, only satisfiability. Lagniez, Marquis
& Biere (SAT 2024) give both the failure and the repair — BCE is sound for
counting **projected onto** the variables whose blocking literals were not used,
which for a Tseitin encoding means projection onto the symbol bits. **[P]** Our
recompute-from-inputs model lift is already the right shape for this.

### 8.2 The adder finding the code survey missed: propagation completeness

**[P]** Brain, Hadarean, Kroening & Martins, *Automatic Generation of
Propagation Complete SAT Encodings*, VMCAI 2016, LNCS 9583:536–556.

§3.6 concluded, from four codebases and no counterexample, that adder
**topology** does not matter. The literature agrees and sharpens it — POS 2026
(Biere, Brain, Kroening, Manthey, Tautschnig) reports that **all five
parallel-prefix networks (Brent-Kung, Kogge-Stone, Sklansky, Han-Carlson,
Ladner-Fischer) produce identical learned-clause quality**, with Brent-Kung
winning only on variable count. **[P]** That is a measured confirmation of a
"not recommended" I had only argued from absence.

**But it identifies a different adder knob that I missed entirely, and this one
is not topology.** CVC4's shipped full adder was **8 variables / 17 clauses and
not propagation complete**; their generated one is **5 variables / 14 clauses
and propagation complete** — *smaller and stronger at once*. The `ult` gadget
went 5 vars / 10 clauses → **4 / 6**, also PC. A ripple chain of PC full adders
is itself PC. Their 2016 source audit states that **Boolector, STP2, Yices2 and
Z3 all ship non-propagation-complete addition**. **[P]**

**[I]** We have not checked ours, and this survey did not. It is a cheap check
and it sits directly on top of Rank 1 — both are about the *shape* of the
full-adder gadget, and they may or may not be compatible, which is exactly the
question to answer before doing either.

**Do not oversell it.** The 25× figure in that literature is a *gadget-level*
propagation measurement. The authors' own end-to-end result on 31,066 QF_BV
benchmarks is 2287 → 2302 solved (+15), which they describe as *"not
dramatic… but consistent enough to show that propagation strength is an
important characteristic."* **[P]**

### 8.3 Division: the recommendation, and the reason to be careful

Two independent sources recommend the `a = b·q + r` rewrite over a divider
circuit (Brain, SMT 2021, fn. 6; POS 2026 §1). That is Rank 5. **[P]**

**But Bitwuzla built exactly this pass and then disabled it.**
`references/bitwuzla/src/preprocess/preprocessor.cpp:355-356`, verified verbatim:

```cpp
// Disabled until murxla-c598aa85aefc51a0.min.smt2 is fixed.
if (false && options.pp_elim_bv_udiv())
```

**[C]** The pass, its option, and its option registration all still exist
(`src/option/option.h:637`, `src/option/option.cpp:513`); only the call is
dead-coded, and the named blocker is a **Murxla fuzzer** minimisation. So the
divider-elimination rewrite is a technique whose *known* failure mode is a
fuzzer-found soundness bug on a corner case — which is precisely this
repository's `a946f925` hazard class, and precisely why CLAUDE.md requires that
every underspecified operator carry a fuzz seed-class generating the degenerate
argument. **A `bvudiv`-by-defining-relation pass here must ship with a fuzz
generator that deliberately emits a zero divisor, or it is not gated at all.**
**[C]/[I]**

**Also worth knowing: there is no published comparison of division encodings
anywhere in the SAT/SMT literature.** Three major solvers ship three different
dividers (Z3 restoring with restore-multiplexers, Bitwuzla two-stage borrow
chain, Boolector cellular non-restoring) with no cited justification for any of
them. **[P]/[C]** That makes it a cheap and genuinely novel experiment, and a
natural first knob for a configurable encoder.

### 8.4 Multipliers: what the encoding can and cannot buy

- **The negative result is real but is not about encodings.** Beame & Liew
  (JACM 66(3):22, 2019) *refute* the conjecture that multiplier equivalence
  needs exponential resolution: polynomial-size regular resolution proofs exist
  for degree-2 ring identities on array, diagonal and Booth multipliers. **The
  short proofs live in the proof system CDCL uses, and CDCL cannot find them.**
  **[P]** So no encoding closes the gap — the answer is a different method
  (algebraic / Gröbner; Kaufmann, Biere & Kauers, FMCAD 2019, verify 64-bit
  multipliers in seconds where SAT times out).
- **A propagation-complete multiplier is unlikely to exist**: it would factor
  `r = pq` in at most `n` unit-propagation calls (Brain, SMT 2021). **[P]**
- **Encoding choice is worth up to 64× on ring identities and is PAR-2-neutral
  on real benchmarks.** POS 2026: on a stratified sample of 66 `bvmul`-carrying
  SMT-COMP 2024 QF_BV benchmarks, shift-add solved 34/66 at PAR-2 62.5 s and the
  best alternative solved 34/66 at PAR-2 62.6 s. Verbatim: *"On general QF_BV
  benchmarks most multiplications are small (BW ≤ 32) and the bottleneck is
  rarely the multiplier."* **[P]** This is the measured version of the
  "not recommended" bullet in §6, and it also independently corroborates our own
  reverted-Booth finding (§4.3).
- One useful mechanism result: the dominant variable is **carry propagation, not
  tree topology** — holding layout fixed and swapping the accumulator from
  `bvadd` to `bvxor` moved conflicts by 255×, while sequential → parallel-tree
  moved time by <10 %. **[P]** That is consistent with everything in §2.5 and
  §4 and is a good reason to treat the *adder* as the multiplier's real knob.

### 8.5 Technology-mapped CNF: the numbers Rank 7 needed

**[P]** Eén, Mishchenko & Sörensson, *Applying Logic Synthesis for Speeding Up
SAT*, SAT 2007, LNCS 4501:272–286.

- **Clause reduction vs Tseitin**, averaged over 30 problems: SatELite alone
  29 %, DAG-aware rewriting alone 32 %, technology mapping alone 46 %, all three
  62 %.
- **Solve-time speedup**, Cadence BMC (10 problems), total: tech-mapping alone
  5.7×, all three **22.3×** (harmonic 11.5×). IBM BMC: 4.2× for all three.
- **And the counter-example that matters:** on SAT-Race `manol-pipe` the same
  full pipeline is **0.9× total and 0.3× harmonic — a slowdown.** Their
  explanation: equivalence-checking problems are easier when equivalent points
  in the two circuits are preserved, and the transformations remove exactly
  those. **[P]**
- The one adaptation that makes the mapper a *CNF* mapper is the one §7.1
  quotes from the source: define area as the number of clauses the cut
  introduces.

**[I]** This is the strongest available argument for Rank 7 and simultaneously
the strongest argument for Rank 0 being first: a 22× win on one family and a 3×
*loss* on another, from the same pipeline, is exactly the profile that has to be
measured on our corpora rather than assumed.

**They also independently confirm that the encoding choice is not moot**:
structure-based transformation *without* any CNF simplification (6.9×) already
beat SatELite alone (4.2×), and the authors call the two orthogonal. **[P]**

### 8.6 QF_FP: a sharp constraint on a configurable multiplier

§5.3 argued that a configurable BV encoder is automatically a configurable FP
encoder. The literature adds a constraint that changes the interface.

**[P]** Brain, SMT 2021, open questions, verbatim:

> *"As presented we are computing a 2n bit output. For bit-vector multiplication
> we only need the low n bits, for floating-point we need the high n+1 bits."*

**BV and FP want opposite halves of the multiplier's output.** Our
`lower_mul_op` truncates to the low `width` bits
(`crates/axeyum-bv/src/lib.rs:2278-2327`) — correct for `bvmul`, and exactly
wrong for an FP significand multiply, which needs the high bits plus a sticky OR
of everything below. **[C]/[P]** A `MultiplierTopology` whose signature bakes in
"truncate low" cannot serve QF_FP; the output-range must be a parameter. Note
SymFPU records that a truncated-high multiplier would roughly halve `fp.mul`'s
cost and **is not implemented in any solver**. **[P]**

**A second FP datum that should redirect effort.** SymFPU is parametric over a
back-end, and across all three of its symbolic back-ends the *only* circuit
routines ever overridden are **two shift variants** (`orderEncodeBitwise`,
`stickyRightShiftBitwise`) — never the multiplier, never the divider. **[P]**
The revealed preference is that FP needs shift forms that plain
`bvshl`/`bvlshr` cannot express (sticky-fused, order-encode,
normalise-and-report-amount). If a configurable encoder is built with QF_FP in
mind, **the shifter is the first thing to make configurable, not the
multiplier.**

Finally, the reuse is measured in the right direction: Bitwuzla's CAV 2024
bit-blasting abstraction is a pure BV-layer change that knows nothing about FP,
and it improved **six FP logics** (QF_FP +23 solved / −13 % time; QF_BVFPLRA +9
/ −46 %; FP +5 / −16 %) — while costing QF_BV 13 instances. **[P]**

### 8.7 Two literature claims that the code survey contradicts

Recorded because both appear in a peer-reviewed source and are wrong about the
shipping code, and someone will otherwise cite them:

- Brain (SMT 2021) states *"Bitwuzla uses a Wallace tree reduction step."*
  It does not: `mul_helper`
  (`references/bitwuzla/src/lib/bitblast/bitblaster.h:438-477`) is a plain
  shift-add array with a serial half/full-adder chain, two constant-folding
  shortcuts, and a dedicated `bv_mul_square`. **[C]** §2.4 of this document
  reads the same code.
- Brain (SMT 2021) states that circuit-producing solvers use
  *"an encoding, such as Plaisted-Greenbaum."* Boolector, Bitwuzla and cvc5 all
  emit full bi-implications, and EMS07 explicitly declined PG. **[C]/[P]** The
  literature names PG generically where the implementations use Tseitin.

### 8.8 What remains unverified

The paper survey could not obtain: Plaisted & Greenbaum's 1986 original
(paywalled — the polarity characterisation above is taken from the TACAS 2010
and JSAT 2006 secondary sources); the two papers on the DRAT **unit-deletion**
hazard (*Two Flavors of DRAT*, POS@SAT 2018; *Frying the Egg, Roasting the
Chicken*, CPP 2020) — **a real hazard for our DRAT route whose details are not
verified**; Nadel's CAV 2014 automatic rewrite-rule generation; and Bruttomesso's
2008 thesis. No published preprocessing on/off ablation for QF_BV exists at all.
