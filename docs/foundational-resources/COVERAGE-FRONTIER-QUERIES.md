# Coverage Frontier Queries

This is the planning-oriented companion to the aggregate coverage view in
[CONSUMER-QUERIES.md](CONSUMER-QUERIES.md). Use it when a resource builder wants
to rank fields, fragments, curriculum nodes, or decidability classes by the
current mix of checked evidence, finite replay rows, replay-only refutations,
and Lean/theorem horizons.

The command reads only the public JSON contract:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by field \
  --require-any
```

The output reports concept counts, pack counts, total expected rows, checked
rows, replay-only rows, replay-only `unsat` rows, Lean-horizon rows, checked-row
ratio, suggested action labels, and sample packs. It is a work-selection view,
not a theorem, benchmark, or solver-parity metric.

## Start Here

Rank field pressure:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by field \
  --require-any
```

Rank fragment pressure with machine-readable output:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by fragment \
  --min-replay-unsat 1 \
  --format json \
  --require-any
```

Rank curriculum-node pressure inside a field:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by curriculum-node \
  --field topology \
  --min-horizon 1 \
  --require-any
```

Use the older aggregate command when totals matter more than prioritization:

```sh
python3 scripts/query-foundational-resources.py coverage \
  --by field \
  --require-any
```

## Action Labels

`coverage-frontier` emits small action labels:

- `seed-pack`: atlas concepts exist but no pack is attached to the group.
- `add-checked-evidence`: at least one pack in the group has no checked row.
- `proof-upgrade`: the group has replay-only `unsat` rows that may be worth
  comparing against existing certificate coverage.
- `theorem-horizon`: the group has Lean-horizon rows that must stay out of
  finite evidence and benchmark summaries.
- `maintain`: the group has packs and no current frontier flag from this view.

These labels are hints. Before promoting any replay-only row, read
[Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) and
[Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md). Before treating
any horizon row as future proof work, read
[Theorem Horizon Queries](THEOREM-HORIZON-QUERIES.md).

## Useful Filters

Replay-only refutation pressure:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by field \
  --min-replay-unsat 5 \
  --require-any
```

Lean-horizon pressure:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by field \
  --min-horizon 5 \
  --require-any
```

Low checked-evidence density:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by field \
  --max-checked-ratio 0.35 \
  --require-any
```

Route or topic slices use the same public text and fragment filters as the
aggregate coverage command:

```sh
python3 scripts/query-foundational-resources.py coverage-frontier \
  --by curriculum-node \
  --field real_analysis \
  --fragment QF_LRA \
  --text gradient \
  --require-any
```

## Boundary

The grouped counts intentionally double-count multi-field and multi-fragment
packs, just like `coverage`. A row about finite projected gradient can belong to
real analysis, numerical analysis, linear algebra, and optimization at once.
That is useful for planning pressure and bad for corpus-total claims.

Use this command to choose the next resource increment:

1. Pick a high-pressure group.
2. Drill into it with `packs`, `checks`, `upgrade-frontier`, or
   `horizon-frontier`.
3. Decide whether the next commit should add learner wording, a checked proof
   row, a Lean-horizon note, or a new pack.

Do not use frontier rank to claim theorem coverage, solver superiority,
benchmark quality, or Z3/cvc5/Lean parity.
