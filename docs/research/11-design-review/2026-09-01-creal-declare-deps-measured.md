# `creal.rs`'s dependency graph, measured against the table that claims it

Lane `creal-split`, 2026-09-01. Slice A of the refactor named in
[2026-08-27-architecture-review.md](2026-08-27-architecture-review.md) §1.
Producer: `scripts/creal-declare-deps.py`; artifact:
`artifacts/refactor/creal-declare-deps.json`.

## What was already true, and what was not

The review's §1 proposes "each `declare_*` announces the declarations it
depends on; the builder topologically sorts them". Lane `creal-steps` landed
half of that on 2026-08-27 (`de853af65`): `STEPS` is a table of 211 entries,
each naming its `requires`/`provides` as `fn(CRealPrelude) -> NameId`
accessors, and `validate_step_order` runs as a preflight before any kernel
work.

The half that did **not** land, and is easy to read as landed:

- **The builder does not sort.** `STEPS`'s array order *is* the build order.
  `validate_step_order` only asks whether that hand-written order happens to be
  a valid topological order for the table.
- **Nothing checks the table against the code.** `requires`/`provides` were
  extracted once by a throwaway script that, by the extracting lane's own
  account, was deliberately not committed. Every declaration added since has
  had to maintain them by hand.

So the preflight's strength is bounded by a table nobody re-derives, and a
missing `requires` entry costs nothing while the order is right — then
silently fails to fire the moment it is not.

## Method

`scripts/creal-declare-deps.py` re-derives the graph from `creal.rs` plus the
49 non-test `creal/*.rs` modules: 1,914 functions indexed, and per `STEPS`
entry the transitive call-graph closure's `CRealPrelude` field writes
(`name: p.foo` and the `name,` shorthand inside a `Declaration` literal,
`add_inductive` with its constructors and kernel-generated recursor, the
`NatOps::theorem` sink) and reads (every other `p.foo`).

Five things had to be right before the numbers meant anything, and each was
wrong first — every one produced a clean, plausible, entirely false report:

| defect | what it printed |
| --- | --- |
| `intern_names`/`STEPS` parsed from the string-stripped text | 0 steps, 0 field names, and every finding "clean" |
| `#[cfg(test)] mod creal_tests;` treated as a block | 100+ functions blanked; `CReal.zero` "required by 115 steps, provided by none" |
| bare calls resolved to any same-named function in `creal/` | `declare_transitivity` depends on the RIEMANN SUM (`rsum` is imported from `rat_prelude::group`; `integral.rs` defines its own) |
| closures indexed module-globally | `motive`/`step`/`induct_ty` repeat per `declare_*`; only the last survived, giving 5 spurious `out_of_order` violations |
| `pub rat: RatPrelude` counted as a field | all 211 steps require a whole sub-prelude no step provides |

The script therefore carries its own controls: it aborts if it parses zero
fields, zero names, zero steps, or leaves a field unmapped, and
`--self-check` permutes one step before a step it demonstrably depends on and
**requires the violation scan to fire** — because "0 violations" is also what
a scan examining nothing prints.

    $ python3 scripts/creal-declare-deps.py --report --self-check
    SELF_CHECK|PASS|moved 'declare_carrier' before its provider of `CReal.Regular`|violations=1

## Findings

    CREAL_DECLARE_DEPS|steps=211|fields=606|fns=1914
      linear order is a valid topological order: True
      order violations (measured graph):         0
      steps whose table disagrees with the code: 175
      steps with no dependents (leaves):         47
      modules with >1 dispatch entry:            23
      fields provided by >1 step:                0

**1. The order is sound. The table describing it is not.**

Against the measured graph the hand-written order has **zero** violations, and
every one of the 606 `NameId` fields is provided by exactly one step — no gaps,
no duplicates. That is the same verdict `validate_step_order` gives, now
independently derived.

But the table itself is missing **977 of the 4,831 measured `requires` edges**
(20%), across 175 of the 211 steps. `trig_fn` and `integral` are worst
(`declare_integral_endpoint_close` names 29 fewer dependencies than it has).

**2. Two `provides` entries name declarations their step does not make** —
the first concrete defect, and it disarms the preflight over a 48-step window.

`STEPS[50]` (`mul_self_zero::declare_mul_self_zero`) claims to provide
`p.seq` and `p.shared_index_to_canonical`. `creal/mul_self_zero.rs` declares
neither: it declares exactly `rat_sq_le`, `rat_sq_sandwich`,
`rat_index_ratio_le_one`, `rat_unit_eq_one`, `eq_zero_of_mul_self_zero`.
`CReal.seq` is provided by step 2; `CReal.sharedIndexToCanonical` by step 98
(`integral::declare_shared_index_to_canonical`).

Consequence: `validate_step_order` believes `sharedIndexToCanonical` is
available from step 50 onward. A step placed anywhere in 51..97 that needs it
passes the preflight and then fails in the kernel with the bare `UnknownConst`
the preflight exists to replace. Nothing does today — the eight real consumers
all sit at 99 or later — so this is a silently weakened guard, not a live bug.
It is exactly the shape CLAUDE.md calls worse than no checker.

**3. The god-struct's cost, quantified.** 606 fields (441 at the review;
`creal.rs` is now 17,050 lines against 9,284). 23 of the 33 `creal/` modules
carry more than one `STEPS` entry — `integral` alone has 46, `supremum` 20,
`trig_fn` 14 — so "one dispatch entry per module" is not what the table is,
and a lane adding a declaration to `integral.rs` still edits `creal.rs` twice
(the struct and the table) plus `intern_names`.

**47 steps have no dependents at all.** Nothing later in the build reads any
field they provide. Those are the free candidates for a per-module registry:
moving their fields out of `CRealPrelude` cannot break a consumer, because
they have none.

## What this says about the next slice

The measured graph is complete enough to *sort* by (0 violations, 606/606
fields with exactly one provider), so a topological builder is buildable. Two
cautions for whoever does it:

- **Sort by the measured graph, not by the table.** The table is missing a
  fifth of the edges, so a sort driven by it is under-constrained and free to
  produce an order the code does not support.
- **The 977 missing edges must be repaired first, or the repair must be
  generated.** Maintaining 4,831 edges by hand across 211 entries is the
  same shared-append-point problem `PLAN.md` and the ADR index already solved
  by generation.

Re-run after any merge that touches `creal`:

    python3 scripts/creal-declare-deps.py --self-check --strict

`--strict` exits **2** when the table and the code disagree, so the exit
status depends on the finding. It exits 2 today.

## Addendum: Slice B landed, and what it does and does not fix

`build_creal_prelude_uncached` now computes its order (`plan_step_order`,
Kahn's algorithm with the array index as tie-break) instead of validating a
hand-written one, and the two false `provides` above are deleted.

**No behaviour change today.** The tie-break makes the plan the array order
whenever the array order is valid, which it is — so the kernel sees the
identical sequence of `add_declaration` calls. `kernel_declaration_projection`
is byte-identical across the change: SHA-256
`576296bf531513e04749c77fb2162f374e3006cb837355ee0f06c7721ecd0c87`, 14,673
rows, before and after. `creal` prelude construction (release,
`AXEYUM_PRELUDE_CACHE=0`, three iterations) 20.196 / 20.272 / 20.215 s before
against 20.110 / 20.494 / 20.135 s after.

**The order-inversion demonstration.** With `declare_projections` and
`declare_carrier` swapped in the table — the second requires `CReal`, which
the first provides:

| builder | result |
| --- | --- |
| level 1 (`validate_step_order` preflight) | **exit 101**, `step 1 ('declare_projections') requires CReal, provider Some((2, "declare_carrier"))` — build refused |
| level 2 (`plan_step_order`) | **exit 0**, projection byte-identical to the unpermuted run, same SHA-256 |

Both measured by rebuilding `kernel_declaration_projection` against the
permuted table; the permutation was then reverted.

**What is NOT fixed.** The planner can only use the edges the table names, and
the table names 3,934 of 4,831. A reordering across one of the missing 897 is
outside what the plan constrains. Closing that means generating
`requires`/`provides` rather than maintaining them by hand — the same remedy
`PLAN.md` and the ADR index already needed, for the same reason.

**"Second dispatch entry point" patches: none found.** The review predicted
duplicate declarations added elsewhere to work around order. There are zero:
every one of the 606 fields is declared by exactly one step. The 23 modules
with more than one `STEPS` entry are legitimately multi-step (`integral` has
46), not patched. The failure the review saw left a different trace — the two
false `provides` claims, which is a table that *says* a second provider
exists rather than code that has one.
