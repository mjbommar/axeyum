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

Detail moved to [`../notes/276-stack-envelope-remeasure.md`](../notes/276-stack-envelope-remeasure.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | (see commits above) | `artifacts/kernel-stack-envelope.tsv`: `integer`/`cpoint`/`complex` release rows raised to their measured minimums (131,072 / 8,388,608 / 8,388,608); `complex` debug row raised to 16,777,216; `integer`/`cpoint` debug rows confirmed unchanged. Growth attributed per-prelude to that prelude's own recent commits (int gcd/fib lemmas, cpoint's squared-throughout geometry identities, complex's polynomial/factor-theorem family), refuting a uniform-nat-growth hypothesis. `nat`/`rat`/`creal`'s sub-2x-margin rows deliberately left unraised (passing, out of scope, owned by other lanes). |
