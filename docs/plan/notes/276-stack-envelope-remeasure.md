# Notes: 276-stack-envelope-remeasure

Detail moved out of [`../status/276-stack-envelope-remeasure.md`](../status/276-stack-envelope-remeasure.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `nat`'s own release row is **unchanged** at 65,536 — it still only warns
  "margin < 2x below pin", it did not fail.
- Growth across the three consumers is wildly uneven — 2×, 8×, 32× — which a
  single uniform upstream cause would not produce.
- Each prelude's own recent commit history explains its own rate far better:
  `int_prelude.rs`/`int_prelude/` picked up small, incremental lemmas
  (`Int.gcd_div`, `Int.fib_two_mul`, `Int.emod_natAbs_bound`) — consistent
  with the smallest growth. `creal_point.rs` (the `cpoint` prelude) picked up
  a run of Euclidean geometry identities carried "squared throughout" to
  avoid introducing a square root (Heron's formula, Menelaus, Ceva, the
  Euler line, Cauchy-Schwarz, circumcentre/radical-axis) — large algebraic
  terms, matching the 8×. `complex.rs` picked up the polynomial/factor-theorem
  family (`Complex.polyMul`, `hornerFromTop`/`factorQuotient`, FTA-approx
  groundwork) plus the modulus triangle inequality — the heaviest additions
  of the three, matching the 32×.

Conclusion: attribute prelude-specific growth to that prelude's own recent
commits, not to a shared upstream driver, unless the failing prelude's own
row is otherwise unexplained.

## No divergent term found

All three re-derivations bisected cleanly to a passing power of two (the
`--measure` procedure's own criterion for "this is a resource limit, not a
bug"). Nothing failed to find a passing power of two; nothing here needed
the divergent-term escalation.

## Judgment call on the three sub-2x-margin rows

`nat`, `rat` and `creal` all currently report "margin < 2x below pin" under
`--check` (build at the pin, abort at half the pin). None of the three
FAILED — they are not in scope. I did **not** raise any of them:

- They pass. Raising a pin that isn't failing is optional headroom, not a
  fix, and the task said explicitly to make that call rather than default to
  raising.
- `nat_prelude/` and `creal/` are explicitly other lanes' files this
  session; touching their pins without touching their code would be a
  guess, not a measurement.
- If one goes red later, the procedure is identical:
  `--measure --profile release --prelude <name>`.

## Commits

- `c3a17bf16` — first commit, in-flight measurements (integer + cpoint
  release rows)
- (see `git log` for the final TSV commit with all six updated rows and the
  documentation of what grew — landed same session)

`scripts/check-kernel-stack-envelope.sh --check` (default profile, release)
is green: 6/6 preludes within budget, each with a demonstrated failure at
half its pin.

Debug `--check` for `cpoint` is slow (~60s+ per probe under this
`--check`'s own margin-halving loop) and was not run to full completion
within budget; all three debug rows were independently confirmed via direct
bisection probes matching `--measure`'s output exactly, so this is a
reporting gap, not an unverified number.
