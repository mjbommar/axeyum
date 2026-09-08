# Bit-blasting and AIG: encoding quality upstream of the SAT solver

Lane: `research-bitblast-aig`. Read-only survey, 2026-09-08.

Every claim is tagged: **[C]** read from source code (cited `file:line`),
**[P]** from a paper, **[I]** inference by the author of this note. No
measurement in this document was produced by running anything — measurements
quoted from our own tree are quoted from the comment or document that already
records them, and are attributed as such.

Sibling lanes own the other files in this directory; this file covers the AIG
and bit-blasting layer only.

---

## 0. The one-paragraph answer

Our pipeline has three layers — term → AIG (`axeyum-bv`), AIG construction
(`axeyum-aig`), AIG → CNF (`axeyum-cnf`). Measured against Bitwuzla, **the CNF
layer is the strongest of the three and is ahead of Bitwuzla's**: we already do
Plaisted–Greenbaum polarity encoding, XOR/ITE/AND-tree gate fusion, and
fanout-guarded gate extraction, where Bitwuzla's `aig_cnf.cpp` does ITE
extraction and plain Tseitin with two `TODO`s for the rest. **The AIG layer is
where the gap is**: we apply local rules at construction time only, and have no
post-construction optimisation of any kind — no rewriting pass, no SAT
sweeping, no cut enumeration. **The circuit layer has specific, countable
inefficiencies** in the shapes we emit for XOR, the unsigned comparator, and the
divider, all of which are self-contained function bodies.

The highest-value-per-effort items are not the famous ones. Restructuring
`Aig::xor` (one function, ~6 lines) makes every half-adder in the system share a
node it currently duplicates. Reformulating `lower_unsigned_less` (one function)
drops its per-bit cost from about seven AND nodes to four, and that saving is
multiplied `width` times inside the divider. Those come before ABC-style
rewriting, which is a large build.

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
  `crates/axeyum-bv/src/lib.rs:2560-2640`. **[C]**
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
  (`references/bitwuzla/src/preprocess/pass/normalize.cpp:64`,
  `score() { return d_bitblaster.num_aig_ands(); }`). **We independently
  converged on it and ours is wired into dispatch.** **[C]**
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

Per bit position: ours ≈ 16 AND nodes per bit-pair over `width+1` bits;
Bitwuzla's ≈ 11 over `width` bits. **[I]** The divider is quadratic, so this is
the largest single-operator gap in the table.

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
STP's own gate count (7 vs 11) bracketing my hand count of our shape (9 —
we are between the two, because our XOR is the cheap 3-gate form but does not
share its conjunction with the carry). Boolector's `half_adder`
(`references/boolector/src/btoraigvec.c:221-234`) and Bitwuzla's
(`references/bitwuzla/src/lib/bitblast/bitblaster.h:501-511`) both do the
sharing too. **Three of three reference solvers share the half-adder
conjunction; we do not.** **[C]/[I]**

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
  circuits. Counting spellings in `crates/axeyum-fp/src/lib.rs` (8257 lines):
  `bv_sub` ×37, `bv_or` ×27, `bv_shl` ×26, `bv_add` ×11, `bv_lshr` ×5,
  `bv_mul` ×2, `bv_udiv`/`bv_urem` ×2 each, plus comparisons. **[C]** So every
  QF_FP query flows through the *same* `lower_terms` circuit library, and the
  adder and shifter are the FP hot path (alignment/normalisation shifts and
  significand subtraction). **A configurable BV encoder is automatically a
  configurable FP encoder** — no separate work, and the adder improvement in
  §2.5(a) lands on QF_FP for free.
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
"Beyond QF_BV" says which other divisions inherit the gain.

*(Ranking finalised after the ABC and Boolector/STP/Z3 surveys; see §3 and §7.)*
