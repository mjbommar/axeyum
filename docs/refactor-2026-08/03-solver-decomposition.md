# 03 — Decomposing `axeyum-solver`

**The finding.** One crate is 51% of the workspace. That is worth fixing, and it
is the *least* urgent item in this folder — because the same measurement that
shows the crate is oversized also shows it is already organised for the split.

Do this **after** [`01`](01-int-real-keystone.md) and
[`02`](02-composition.md), or the split will freeze today's seams into crate
boundaries, and today's seams are exactly what those two items are fixing.

> **Started 2026-08-15.** The `solver-decomp` lane built
> `scripts/analyze_solver_module_graph.py` (`3740597f5`) and landed the first
> slice (`25ab64649`): quantifier certificate **data** now lives apart from its
> checkers, because each type was defined beside its checker and that made
> `Model` — the crate's base value type — depend on the dispatcher, the `QF_BV`
> route, the e-graph and the theory solvers, and back to `Model`.
>
> | | largest dependency cycle |
> |---|---|
> | before | **65 modules, 115,840 lines** — half the crate |
> | after | **24 modules, 58,215 lines** (25.8%) |
>
> Measured by that script and re-measured before landing, not quoted. **No crate
> was extracted**; the 267-entry façade is untouched and ADR-0001's
> "boundary proven by use" bar has not been argued for anything yet. Lane notes:
> [`96-solver-decomp.md`](../plan/archive/96-solver-decomp.md).
>
> Note this contradicts the "least urgent" framing above in one respect: the
> cycle was worth breaking on its own merits, independently of `01` and `02`,
> because a value type depending on the search that produces it is a defect at
> any crate boundary. The ordering advice still holds for **extracting crates**.

## The measurement

```
axeyum-solver        236,275 lines    51% of the workspace
                     164 top-level modules
                     13 of 22 workspace crates as dependencies
                     278 integration test files + 83 in-source test modules
```

Public surface:

```
7    direct `pub` items in lib.rs
267  `pub use` re-exports
```

**That ratio is the good news.** The crate is a *façade over modules*, not a
tangle of cross-referencing types with a wide public API. Moving modules out
means moving files and keeping the façade — consumers need not notice.

Modules group cleanly, by their own naming:

| group | modules | examples |
|---|---:|---|
| quantifiers | **38** | `qinst_egraph.rs` (10,646), `quant_*` |
| arithmetic | 20 | `lra_online.rs`, `dpll_lia.rs`, `nra_real_root.rs`, `int_*` |
| arrays / BV | 18 | `abv.rs` (10,669), `array_axiom.rs`, `bitblast_*` |
| uninterpreted functions | 8 | `ufbv_online.rs`, `euf_*` |
| strings | 7 | `word_*`, `regex_*`, `lex_*` |
| dispatch / API | 5 | `auto.rs` (9,430), `evidence.rs`, `incremental.rs` |
| proof / evidence | 3 | `reconstruct/` |

And a feature flag already draws one boundary:

```toml
full = ["dep:axeyum-cas", "dep:axeyum-egraph", "dep:axeyum-fp",
        "dep:axeyum-lean-kernel", "dep:axeyum-smtlib", "dep:axeyum-strings"]
```

The minimal deployment profile (`qfbv`, the default) already excludes six
crates' worth of capability. The split is partly specified in `Cargo.toml`
already.

## What ADR-0001 requires

The project's crate policy is explicit and this plan does not get to ignore it:

> Crate split is deliberately minimal; add crates only after a boundary is
> proven by use.

Every existing crate was justified that way — `axeyum-smtlib` and
`axeyum-bench` as exercised boundaries, `axeyum-query`/`axeyum-rewrite` by
ADR-0005, the circuit/lowering/CNF trio by ADR-0006.

So decomposition is **not** licensed by size alone. Each proposed crate needs a
boundary *proven by use*, and the honest position is that most are not yet
proven. What follows is therefore a set of candidates ranked by how close each is
to having that proof, not a plan of record.

## Candidates, ranked by strength of the boundary argument

### D1 — `reconstruct/` → its own crate. **Strongest case.**

- It is the trusted-path proof layer and the only part that touches
  `axeyum-lean-kernel`.
- It has an external consumer story: certificates a third-party kernel accepts.
- Its dependency direction is one-way (it consumes solver results; nothing in
  the theories consumes it).
- The boundary is *already exercised*: 19 certificates checked by official Lean
  v4.30.0, and a replay path into Lean's own kernel from an empty environment.
- It has its own distinct scale limit (the reconstruction arena), which argues
  for its own budget and its own gates.

This is the one where "proven by use" is arguably already satisfied.

**Measured 2026-08-16, and the ranking does not survive it.** Every claim above
is true. The one that was never measured is the *width* of the boundary, and
that is what decides whether a crate can be cut. Using
`scripts/analyze_solver_module_graph.py`'s own resolved graph (facade items
included, so `crate::abv::…` call sites count):

| candidate crate | layer lines | depends on | those lines | inbound edges |
| --- | ---: | ---: | ---: | ---: |
| the evidence layer, as the analyzer defines it (7 modules) | 41,405 | **71 modules** | 83,660 | 5 |
| the reconstruct family, dropping `evidence` and `smtlib` | 34,278 | **57 modules** | 71,979 | 10 |
| `reconstruct` alone | 23,497 | **58 modules** | 77,543 | 8 |
| `evidence` alone | 4,272 | **72 modules** | 115,160 | 1 |

There is no cut that yields a small trusted core. However the line is drawn,
the extracted crate would depend on 57–72 modules and 72k–115k lines of what
remains — between 32% and 51% of the crate. That is not a boundary; it is a
layer sitting on top of nearly the whole solver.

The *direction* is exactly as claimed — 5 edges in, and nothing from the theory
core — so the fix is not to invert anything. Nor are the inbound edges the
obstacle: `solver → reconstruct` is two one-line delegating methods on the
façade (`prove_unsat_to_lean`, `prove_unsat_to_lean_module`,
`solver.rs:183-198`), and the other three (`lex_reconstruct`,
`lia_interpolant`, `uflia_interpolant`) are evidence-shaped modules that would
join the new crate. **The obstacle is mass, and mass is measurable.**

The reason is visible in one line of `reconstruct/direct.rs:923`:

```rust
let cert = crate::abv::const_array_default_mismatch_refutation(arena, assertions)
```

Reconstruction reaches into each theory to *pull* its refutation constructor,
so its fan-out grows with every theory. Inverting that — a theory hands back a
certificate value that `reconstruct` consumes, rather than `reconstruct`
naming the theory — collapses the fan-out without moving a file.

So D1's precondition is a number, not a judgement: **the outbound module count
of each module in the layer.** `analyze_solver_module_graph.py` now records it
and `--check` fails when it grows, exactly like the cycle set — a *narrowing*
is reported as progress rather than punished, since a gate that failed on the
work it exists to encourage would be worse than none:

```
reaches out into  array_bv_abs -> 1, evidence -> 67, int_reconstruct -> 9,
                  reconstruct -> 55, smtlib -> 8
```

`reconstruct -> 55` and the table's `reconstruct alone -> 58` are the same
measurement under two layer definitions: the gate excludes edges to the other
six layer modules (they would travel with it into the crate), the table does
not. The gate's number is the one to drive down.

Extraction becomes an ADR-0001 argument worth making when it is small. Today it
would move 23k lines out and leave them depending on 77k.

### D2 — quantifiers → its own crate. **Largest, weakest-tested boundary.**

38 modules and the biggest single file in the workspace after `abv.rs`. Size is
the argument, and size is the weakest argument. Needs a measured statement of
what the quantifier layer requires from the theories and what it exports, before
a boundary is drawn.

### D3 — theory modules → grouped modules, **not crates, yet**.

Arithmetic (20), arrays/BV (18), UF (8) and strings (7) are natural groups, but
they interlock through dispatch and share the term IR. The right first step is
*intra-crate* structure — make each group a directory module with an explicit
internal interface — and let a crate boundary be proposed only once that
interface stops changing.

Note that `axeyum-strings` **already exists** as a separate crate (7,883 lines)
while seven string modules live in the solver. Clarifying that division is worth
more than a new crate.

## The precondition nobody should skip

A crate split moves files. Files that move are files whose gates must actually
see them — and on 2026-08-14 `cargo fmt --all --check` was found blind to **156
modules / 221,445 lines of this exact crate**, including the entire trusted
reconstruction layer, because `mod reconstruct;` sits inside
`macro_rules! full_modules` and rustfmt does not expand macros.

That is fixed ([`04`](04-gates-and-truth.md)), and the fix is a precondition for
this item rather than an aside: **do not refactor a crate whose gates cannot
prove which files they examined.**

## Sequencing

1. `04` first — gates that prove their own scope. **Done.**
2. `01` and `02` — because they change what the seams *are*. `02` W2 is done
   (the two real-algebra engines now share a corpus).
3. **`D3` intra-crate grouping** — cheap, reversible, and it produces the
   evidence that would justify `D2` or a theory crate later.
4. **`D1` (`reconstruct/`) — narrowing, not extracting.** The 2026-08-16
   measurement moved this from first to after `D3`: the boundary is one-way as
   claimed but 58 modules wide, so a crate today buys nothing and pins the
   fan-out in place. The work is inverting the theory→certificate pull and
   watch the number fall; the crate is what that earns.
5. `D2` and theory crates — only with a boundary argument that ADR-0001 would
   accept, and an ADR to match.

The reordering is itself the point of `analyze_solver_module_graph.py`: `D1`
was ranked first on four true qualitative claims, and one number that nobody
had taken moved it two places down.
