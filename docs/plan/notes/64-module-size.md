# Lane notes: `agent-module-size` — the price of the axiom-free carrier

The shipped front door reconstructs over the **constructed** reals and a
refutation rests on zero carrier axioms. The module it hands back was
**2,623,005 bytes**. This is where that goes and what moved it.

## Measurement, not intuition (2026-08-18, `a6ee37c6a` + this lane)

`cargo run -p axeyum-solver --features full --example front_door_carrier`,
re-measured rather than trusted:

| fixture | over `Real` | over `CReal` |
| --- | --- | --- |
| strict-bound `x<0, 0<=x` | 8,898 B / 15 axiom lines | 2,623,005 B / 3 |
| three-row `x+y<=0, 1<=x, 1<=y` | 40,740 B / 22 | 2,673,154 B / 5 |
| sos-square `x*x<0` | 2,388 B / 10 | 2,551,806 B / 2 |

The brief's figures reproduced exactly.

### The renderer already emits only reachable declarations

`write_lean_module_impl` opens with `reachable_decl_order(&[goal, proof])` — a
constant-closure walk, not an environment dump. Measured: the `CReal` context
holds **445** declarations and the strict-bound module emits **280** top-level
blocks (sos-square 292). So **the selection layer has essentially no
headroom**: 37% of the environment is already discarded, and what remains is
cited. `CReal.add_assoc` is in the module because the Farkas combination
genuinely uses it.

### Where the bytes are

Blocks, strict-bound: `theorem` 213 blocks / 2,510,020 B, `def` 47 / 109,764 B,
`inductive` 14 / 1,603 B, `axiom` 3 / 273 B. By namespace: `Rat` 1,187,380 B,
`CReal` 1,066,827 B, `AxNat` 217,621 B, `Int` 140,590 B. **The final theorem
term is 4,193 bytes** — 0.16% of the module. The mass is the prelude's proof
*bodies*.

By character class: identifiers **69.6%** (291,180 occurrences), parentheses
12.9%, spaces 11.9%, universe annotations 2.1%. `AxNat.succ` alone is 335,450
bytes across 33,545 occurrences.

### The mechanism: a hash-consed DAG printed as a tree

| declaration | kernel DAG | printed tree | blow-up |
| --- | --- | --- | --- |
| `CReal.mul_assoc` | 1,296 | 324,609 | 250x |
| `CReal.left_distrib` | 1,438 | 238,777 | 166x |
| `CReal.add_assoc` | 1,693 | 76,469 | 45x |
| `Rat.add_le_add` | 3,677 | 66,463 | 18x |

Across all 445 declaration values: **1,488,996 printed nodes, 77,224 DAG
nodes**.

`render_lean_module_compact` existed and hoisted repeated subterms already —
and saved **0.6%**. The reason is one line in `compact_share_candidates`:
`num_loose_bvars(expression) == 0`. Only *closed* nodes could be hoisted,
because a top-level `def` has no binder to read a loose variable in, and a
proof body is almost entirely open terms.

### The ceiling for in-file sharing is 7.7x, not 19x

Raw DAG sharing (77,224 nodes) is **not reachable**: two occurrences of one
hash-consed open node under two different binders denote two different terms,
and sharing them is unsound, not merely awkward. The correct ceiling is the
**named DAG** — nodes keyed by (node, the chain of binder occurrences its loose
variables read). Measured: **193,197** keys against 1,488,996 printed nodes,
i.e. **7.7x**. Per declaration: `CReal.mul_assoc` 62.6x, `CReal.add_assoc`
14.0x, `Rat.add_le_add` 4.3x.

## What landed

| fixture | before | after | factor |
| --- | --- | --- | --- |
| strict-bound | 2,623,005 B | **1,303,499 B** | 2.01x |
| three-row | 2,673,154 B | **1,329,314 B** | 2.01x |
| sos-square | 2,551,806 B | **1,441,470 B** | 1.77x |
| strict-bound over `Real` (control) | 8,898 B | 7,358 B | 1.21x |
| three-row over `Real` (control) | 40,740 B | 21,770 B | 1.87x |

Carrier axioms 0/0/0 against the `Real` control's 12/17/8, and the module's
`axiom` lines still equal `Kernel::axiom_footprint` (3/5/2) —
`--require-axiom-free` exits 0.

Scope-aware `let` sharing (`ScopeId`, `ShareKey`, `scoped_share_plan`,
`write_scope_lets` in `lean_pp.rs`), and the front door switched to the compact
writer (`render_ctx_module`, `gate_and_render_lra_module`).

A scope id is a hash chain folded over the binder occurrences enclosing a
position. Two occurrences sharing an id sit under the same binders, so one
`let` may serve both; occurrences under different binders get different ids and
are bound separately. Each `let` is emitted at the top of the innermost body
whose binders the term reads. Closed nodes normalize to `ROOT_SCOPE` and keep
the old cross-scope sharing.

`Pi` and `Let` bodies are deliberately **not** homes: `let` is a term form and
this writer will not put one inside a type arrow, so a key homed there would be
referenced by a name nothing binds.

`compact_share_plan` — the top-level `def` planner — is unchanged and still
refuses open terms; the guard `compact_plan_never_hoists_open_binder_dependent_terms`
still holds.

## What is left, and why it is the bigger number

Byte reduction achieved is far below the 7.7x node-count ceiling, because a
share *reference* is pure overhead: at ~3.7 bytes per printed node, a name has
to be short to pay. Measured in two steps on strict-bound: scope-aware sharing
with the long `axeyum_proof_share_N` spelling gave 1,877,436 B (1.40x), and
shortening the scoped names to `_sN` -- nothing else changed -- gave 1,303,499 B
(2.01x). Naming was worth more than half the total saving. The top-level `def`
names keep the long spelling: there are few of them and they are what a reader
greps for.

**The remaining order of magnitude is a shared prelude, not better sharing.**
Every query module inlines the same constructed development. A Lean `import` of
one emitted-once carrier module would take the per-query module to single-digit
kilobytes — a ~500x change against ~5x for anything the writer can do alone —
and `#print axioms` still traverses imported proofs, so the axiom-free claim is
untouched. It is out of scope here because it changes the emitted-module
contract: `lean_crosscheck`'s 77 families, `lean_module_fixtures`,
`int_inequality_lean_reconstruct` and `regex_emptiness_lean_reconstruct` all
hand a **single file** to `lean`, and the prelude would need compiling to
`.olean` with `LEAN_PATH` set before any query module could be read. That is an
ADR plus a harness change, and it should be taken as its own increment.
