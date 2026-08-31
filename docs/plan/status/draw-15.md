# Lane: draw-15

<!-- plan-section: lane-status -->

Status: DONE (2026-08-31)

Draw 15 is authored and `GUARD PASSED`. Five draws had declined in a row (10,
12, 13, 14) on one constraint — cycle index 3 is a held-out slot and nothing
late-sorting, topically fresh and reduction-blind could sit in it. ADR-1160
removed it by declaring `DecidablePred` and `Nat.findGreatest`
construction-only, leaving exactly one refusal: R11's disclosure step, which is
authorable rather than measurable. This lane authored it.

**Layout A**, chosen over ADR-1160's layout B on a measurement:

    Batteries.Data.Nat.Bisect                   natural-avg-pair          held-out
    Init.Data.Nat.MinMax                        natural-minmax            development
    Mathlib.Combinatorics.Enumerative.Stirling  natural-stirling-numbers  train
    Mathlib.Data.Nat.Find                       natural-find-greatest     held-out

The hypothesis that made the choice look important — that layout B's
Fib/bitwise vocabulary would eat screening margin from the existing held-out
`natural-bit-decode` — is **wrong**: under both layouts, zero existing held-out
families' topic or vocabulary counts move. What separates them is dispatch
supply over the drawn ten: `natural-stirling-numbers` draws 1 reduction-settled
row and 0 already in the environment, `natural-fib-and-bitwise` draws 4 and 1.

**Both R11 disclosure sweeps were run and read**, against a freshly rebuilt
`shape_search` (env=2629, four declarations more than ADR-1160's 2625). Two
findings no gate reports: `Nat.lnp_bounded_search` is a BOUNDED least-element
search over a decidable predicate with the extremality clause — the structural
dual of `findGreatest_eq_iff` — and `Nat.exists_most_significant_bit` is a
greatest-satisfying-index existence statement. Neither settles a drawn row;
both are transportable skeletons, so the family is less blind than a stem count
suggests, and that is disclosed. `natural-avg-pair`'s review was redone rather
than carried from ADR-1115, because that one predates ADR-1160's finding that
R12 cannot see a quantified defining equation.

Also recorded: `shape_search --concl <Const>` indexes the conclusion HEAD, so
`--concl Nat.countRange` is ABSENT despite 21 matching declarations. Three of
this lane's absence checks proved nothing until re-run with `--const`.

Gates, all green: `gen-autogenesis-nursery-refill.py` (entries 380 → 420),
`--check`, `check-autogenesis-nursery.py`,
`create-autogenesis-nursery-dispatch-baseline.py --check` (tripwire literal
unmoved), `check-holdout-closed-evaluation.py` (`held_out=166 closed_shaped=0
violations=0`), `check-autogenesis-holdout-isolation.py` (`held_out` 146 → 166,
`settled=0`, `references=0`), `check-holdout-adjacency.py` (16 held-out
families, 0 refused, both new ones `reviewed`), `validate-facts.py`,
`check-settled-fact-statements.py` PASS.

## Landed changes

| commit | what |
| --- | --- |
| `99ce806b7` | refresh the kernel environment snapshot 2625 → 2629; the manifest is byte-identical under the refresh |
| `e26076356` | draw 15 — layout A `FAMILY_MODULES`/`FAMILY_ROUTES`, both R11 disclosure reviews, regenerated manifest, 40 fact files |

## Next

`natural-fib-and-bitwise` stays available as a pre-screened index-2 candidate,
and ADR-1160's three remaining index-3 candidates (`Factorization.Root`,
`MaxPowDiv`, `Factorization.LCM`) are pre-screened but each draws boundary
equations its construction would settle, so each needs the reading before use.
