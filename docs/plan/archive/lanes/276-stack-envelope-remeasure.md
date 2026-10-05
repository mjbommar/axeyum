# Lane: stack-envelope-remeasure — three preludes outgrew their pinned stack, none were divergent

<!-- plan-section: lane-status -->

**`just check`'s stack-envelope step was RED on `main` for `integer`, `cpoint`
and `complex`. All three re-derived to a clean passing power of two —
resource growth, not a proof bug** (`DONE`, stack-envelope-remeasure,
2026-08-29).

## What was measured

`scripts/check-kernel-stack-envelope.sh --measure --profile release --prelude
<p>` for each of the three failing preludes, each bisecting cleanly to a
passing power of two (confirmed independently for `cpoint` and `complex` with
direct probes at the bisected value and at half of it):

| prelude | old release pin | new release pin | ratio |
|---|---:|---:|---:|
| `integer` | 65,536 | 131,072 | 2× |
| `cpoint` | 1,048,576 | 8,388,608 | 8× |
| `complex` | 262,144 | 8,388,608 | 32× |

Debug rows were re-checked too, since the pin file carries debug columns for
all three:

| prelude | old debug pin | new debug pin | moved? |
|---|---:|---:|---|
| `integer` | 262,144 | 262,144 | no (confirmed by `--measure`) |
| `cpoint` | 33,554,432 | 33,554,432 | no (confirmed by direct probe: passes at 33,554,432, fails at 16,777,216 — same bisection as before) |
| `complex` | 4,194,304 | 16,777,216 | yes, 4× — the OLD debug pin now fails |

## The hypothesis was tested and refuted

I was briefed to test whether `nat`'s same-day growth (`Nat.Pair`,
`Nat.binaryRec`, the `land`/`lor`/`ldiff`/`xor` bitwise family with its
comm/assoc/`*_bit` lemmas) drove all three failures uniformly as downstream
consumers. It does not:

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

<!-- plan-section: landed-changes -->

| 2026-08-29 | (see commits above) | `artifacts/kernel-stack-envelope.tsv`: `integer`/`cpoint`/`complex` release rows raised to their measured minimums (131,072 / 8,388,608 / 8,388,608); `complex` debug row raised to 16,777,216; `integer`/`cpoint` debug rows confirmed unchanged. Growth attributed per-prelude to that prelude's own recent commits (int gcd/fib lemmas, cpoint's squared-throughout geometry identities, complex's polynomial/factor-theorem family), refuting a uniform-nat-growth hypothesis. `nat`/`rat`/`creal`'s sub-2x-margin rows deliberately left unraised (passing, out of scope, owned by other lanes). |
