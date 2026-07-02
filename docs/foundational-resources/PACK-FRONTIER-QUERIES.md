# Pack Frontier Queries

This is the pack-level drilldown beneath
[Coverage Frontier Queries](COVERAGE-FRONTIER-QUERIES.md). Use it after a field,
fragment, curriculum node, or decidability group shows pressure and the next
question is: "Which concrete pack should a resource builder inspect first?"

The command reads only the public JSON contract:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --field real_analysis \
  --require-any
```

Rows report the pack id, fields, total expected rows, checked rows,
replay-only `unsat` rows, Lean-horizon rows, checked-row ratio, suggested
actions, route-promotion states, finite-shadow state, and pack path. It is a
worklist view, not theorem coverage, benchmark quality, or solver-parity
evidence.

## Start Here

Drill from a high-pressure field into concrete packs:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --field real_analysis \
  --require-any
```

Find theorem-boundary packs that already have checked finite context:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --field topology \
  --action theorem-horizon \
  --shadow-state checked-finite-shadow \
  --require-any
```

Find low checked-evidence density inside a field:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --field measure_theory \
  --max-checked-ratio 0.35 \
  --require-any
```

Machine-readable output is available for downstream tools:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --field real_analysis \
  --action proof-review \
  --format json \
  --require-any
```

## Action Labels

`pack-frontier` emits pack-level action labels:

- `proof-upgrade`: replay-only `unsat` rows exist and the advertised route has
  no or partial checked same-pack contrast.
- `proof-review`: replay-only `unsat` rows exist, but same-pack route contrast
  is already covered; review before adding duplicate checked rows.
- `theorem-horizon`: at least one Lean/theorem-boundary row is attached to the
  pack.
- `low-checked-density`: fewer than 35% of expected rows are checked evidence.
- `maintain`: no current pack-level frontier flag from this view.

These labels are deliberately conservative. `proof-review` often means "read
the nearby checked rows first", not "promote another row". `theorem-horizon`
means the pack must keep finite examples and general theorem claims on separate
consumer paths.

## Useful Filters

Route-focused proof review:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --route Farkas \
  --solver-reuse promoted \
  --require-any
```

Curriculum-node drilldown:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --curriculum-node calculus \
  --min-horizon 1 \
  --require-any
```

Fragment demand with a low-density cap:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --fragment QF_LRA \
  --max-checked-ratio 0.35 \
  --require-any
```

Promotion-state filtering:

```sh
python3 scripts/query-foundational-resources.py pack-frontier \
  --promotion-state covered-by-route-contrast \
  --require-any
```

The current corpus may have no rows for some action or promotion-state filters.
That is a real answer: it means the public JSON does not currently expose that
kind of pack-level pressure.

## Boundary

Use this command after `coverage-frontier` and before opening individual pack
files:

1. Pick a pressured field, fragment, curriculum node, or decidability group.
2. Run `pack-frontier` with the matching filter.
3. Open the returned pack path and decide whether the next commit is a checked
   row, a proof-review note, a Lean-horizon clarification, or no-op maintenance.
4. Use `checks`, `upgrade-frontier`, or `horizon-frontier` for row-level details.

Do not use pack-frontier rank to claim theorem coverage, solver superiority,
benchmark readiness, or Z3/cvc5/Lean parity.
