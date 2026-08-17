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

**Every count in that table is wrong and "cleanly" is wrong — measured
2026-08-17, under `D3` below.**
The rows sum to 99 of the crate's modules; there are 165. Re-derived from names,
the four theory rows are 34 / 29 / 5 / 6, not 20 / 18 / 8 / 7. More to the point,
grouping by name is not the same as grouping by *edges*, and nobody had measured
the edges.

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

**Measured 2026-08-16.** The division is not messy, and it is not
engine-versus-plumbing either. There are **two independent string routes** plus
a shared evidence layer:

| | lines | what it is |
| --- | ---: | --- |
| `axeyum-strings` (crate) | 7,885 | the unbounded symbolic engine — regex derivatives, arrangements, word-equation inference, lex order, refutation, derivation checking |
| `axeyum-solver::strings` | 1,305 | the **bounded** route: strings as `(len, content)` bit-vectors, no new IR sort, regex by Thompson NFA over bounded positions. The BMC fragment |
| `axeyum-solver::string_theory` | 1,962 | the online CDCL(T) driver, which consumes the crate |
| `word_alethe`, `word_reconstruct`, `lex_reconstruct`, `regex_reconstruct` | 3,629 | evidence and proof emission |

`strings.rs` references `axeyum_strings` **zero** times, and that is correct
rather than duplication: it is a different decision procedure for the same
theory. Every other module here references the crate 2–11 times.

So the boundary is already clean, and D3's string question is not "which side
does this file belong on". It is this:

**Both routes decide `str.in_re`, and nothing compares them.** The composition
is deliberately complementary — `apply_word_route` "adds `sat` only where the
verdict is `unknown`", and `upgrade_bounded_string_unknown` turns `unknown` into
`unsat` via the unbounded abstraction. Each route only ever fills the other's
gaps, so **in the shipped product the two can never be observed disagreeing**.
A wrong verdict from either is invisible to the other by construction. No test
runs both on an instance both can decide; the string differential fuzzes all
compare a single route against Z3.

This is the same shape as the two real-algebra engines in
[`02`](02-composition.md) W2 — two implementations of one question, no shared
corpus — and there the corpus found a panic and a dead branch on its first run.

#### Measured 2026-08-17: three of the four proposed groups are not groups

D3 proposes making each theory group a directory module "with an explicit
internal interface". A group only *has* an internal interface if its members
talk to each other more than they talk outward. That ratio had never been taken.
It has now, and it does not support the proposal.

**Method.** Graph from `scripts/analyze_solver_module_graph.py`'s
`build_graph` — comments, string literals and `#[cfg(test)]` code stripped, and
all 606 item names re-exported by the `lib.rs` façade resolved back to their
defining modules, so `use crate::{Evidence, SolverConfig};` counts as the edges
it really is. The crate is **165 top-level modules, 225,494 code lines, 628
distinct directed module→module edges** (1,153 call sites). Membership is by
module *name*, since that is what the table above claimed groups the crate,
applied in the precedence order strings → quantifiers → arrays/BV → arithmetic →
UF → evidence → dispatch, so a name matching two groups (`uflia_online`,
`qfabv_alethe`, `quant_bv_*` — there are 47 such) lands in the theory group
rather than the evidence or dispatch one. That precedence is the *most
favourable* one for D3: it maximises every theory group. An edge is **internal**
when both endpoints are in the group and **crossing** when exactly one is.

| proposed group | doc claimed | modules | code lines | internal | crossing (out / in) | internal : crossing |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| arithmetic | 20 | **34** | 60,756 | 39 | 158 (99 / 59) | **0.25** |
| arrays / BV | 18 | **29** | 42,188 | 8 | 108 (49 / 59) | **0.07** |
| uninterpreted functions | 8 | **5** | 8,383 | 4 | 40 (12 / 28) | **0.10** |
| strings | 7 | **6** | 5,734 | **0** | 13 (8 / 5) | **0.00** |
| *(quantifiers, `D2`)* | 38 | **41** | 31,541 | 33 | 146 (69 / 77) | *0.23* |

Every one of these is under 1.0: **each proposed group has at least four times
as many edges leaving it as staying inside it.** But a low ratio is expected for
any small subset of a graph, so the number means nothing without a null. Two,
both over the real graph with group sizes fixed, 20,000 trials, seed 20260817:
*uniform* draws an arbitrary set of the same size; *degree-matched* draws from
the same total-degree quintiles, so a group of hub modules is compared against
other hubs rather than against leaves.

| group | observed | uniform null | p | degree-matched null | p | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| arithmetic | 0.247 | 0.118 | 0.002 | 0.177 | 0.045 | **a real cluster** |
| arrays / BV | 0.074 | 0.095 | 0.671 | 0.063 | 0.394 | **indistinguishable from an arbitrary set of 29 modules** |
| UF | 0.100 | 0.008 | 0.002 | 0.014 | 0.002 | **real, and tiny** |
| strings | 0.000 | 0.011 | 1.000 | 0.001 | 1.000 | **less connected than random** |
| *quantifiers* | 0.226 | 0.154 | 0.102 | 0.110 | 0.012 | *real, weakly* |

So, group by group:

- **arithmetic — supported.** The only theory row that is both large and
  cohesive by both nulls. It is also 70% bigger than the doc's 20 and, at
  60,756 lines, more than a quarter of the crate. Even here the interface would
  be wide: 99 outbound crossing edges, 46 of them into dispatch.
- **arrays / BV — not supported, and this is the clearest result.** Eight
  internal edges across 29 modules and 42,188 lines, which two independent nulls
  say is what you get from *any* 29 modules. The nine `array_*` scenario modules
  and `abv` do not form a neighbourhood; they are separately-reached leaves. Its
  crossing edges point at `dispatch` (18 out, 12 in) and at the evidence layer
  (41 **in** — the single largest flow into the group), not at each other. A
  directory here relabels edges; it does not create an interface.
- **UF — real but not worth a directory at this size.** Five modules, and three
  of its four internal edges terminate on `euf_egraph`; that is a star, not a
  module. Widening the name rule until every `uf`-named module joins gives 18
  modules / 25,104 lines at ratio 0.12 — but it does so by swallowing
  `uflia_online`, `uflra_online`, `ufbv_online` and `qfufbv_alethe`, which are
  theory-*combination* routes and belong to two groups by construction. The
  doc's 8 is between these two readings and matches neither.
- **strings — not a group at all. Zero internal edges.** The six modules never
  reference one another: `strings` and `word_alethe` have no outbound edges in
  this crate at all, `lex_reconstruct` / `regex_reconstruct` / `word_reconstruct`
  each have exactly one (→ `reconstruct`), and `string_theory`'s five all leave
  the group. Their cohesion is entirely through the **external**
  `axeyum-strings` crate, which an intra-crate graph does not model — which is
  the 2026-08-16 finding above restated as a number. A `strings/` directory
  would be a directory whose members are mutually unaware.

And the fallback of grouping less finely does not rescue it: merging all four
theory groups into one `theories` module gives **74 modules, 117,061 lines,
74 internal and 273 crossing edges — ratio 0.27**, statistically no better than
arithmetic alone at a third of the size. There is no theory-shaped partition of
this crate that converts crossing edges into internal ones at scale, because the
crossing edges do not run between sibling theories. Of the four groups' 319
crossing edges, 46 are theory-to-theory (23 edges, each counted once as an
outbound and once as an inbound); the other **273 leave the theories
altogether** — 115 to `dispatch`, 87 to the evidence/reconstruction layer, 51 to
modules no name rule assigns, 20 to quantifiers.

**What D3 should therefore do.** Group arithmetic and stop. For arrays/BV, UF
and strings the file move would produce a directory and no interface, and the
"let a crate boundary be proposed once that interface stops changing" clause
would never get an interface to watch. The edges say the actual seam in this
crate is not between theories but between the theories and the two things they
all reach — dispatch and evidence — which is the same obstacle `D1` hit from the
other side (`reconstruct` reaching *down* into 55 modules). Narrowing that one
interface is worth more than four directories.

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
   evidence that would justify `D2` or a theory crate later. **Narrowed
   2026-08-17 by the edge measurement above: group arithmetic (the one group
   with cohesion both nulls accept) and do not move arrays/BV, UF or strings.**
   Three of the four proposed groups have fewer internal edges than an arbitrary
   set of modules the same size — strings has *zero* — so those directories
   would carry no interface for the later crate argument to watch.
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
