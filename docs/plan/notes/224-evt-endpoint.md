# Notes: 224-evt-endpoint

Detail moved out of [`../status/224-evt-endpoint.md`](../status/224-evt-endpoint.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. Calls `axeyum_cas::extremum::polynomial_extremum(x^3-6x, -3, 2)` — the SAME
   certificate `F:cas-extremum-irrational-argmax` cites
   (`extremum::tests::irrational_argmax`) — and translates `cert.poly`/`a`/`b`
   to `i128` (`poly_ab_to_int`, mirroring `cas_ivt_bridge_tests::sign_bracket_to_int`).
2. Computes `p(-3) = -9`, `p(2) = -4` in plain Rust `i128` (untrusted side;
   if wrong, the kernel-side reduced constant will not match the asserted
   bound and `add_declaration` rejects — not silently), builds the shifted
   coefficient vectors `q`, `r`.
3. Admits `0 < polyEval q 4 (ofInt -1)` and `0 < polyEval r 4 (ofInt -1)`
   through `Kernel::add_declaration`, reusing
   `cas_ivt_bridge_tests::{poly_eval_to_of_int, n_term_polynomial, int_lit,
   of_int, zero_lt_via_nat_le, built, rational_to_int}` VERBATIM (made
   `pub(crate)` for this reuse — a one-line visibility change per helper, no
   logic touched) rather than re-deriving them beside the original.
4. Carries a swapped-statement negative control (the lower leg's TRUE proof
   term re-ascribed against the FALSE statement `q(-1) < 0`, confirmed
   `Err(..)`).

**Mutation-verified by this lane, not taken on the previous lane's pattern
alone.** Changed the lower leg's kernel-side bound from the exact `14` to a
wrong-but-plausible `16` (`Nat.le 1 16` is itself true, just not the
proposition the reduced term inhabits):

```
Err(TypeMismatch { expected: ExprId(1579401), got: ExprId(1579415) })
```

Test FAILED as expected; reverted, it passes again (`cargo test -p
axeyum-lean-kernel --lib --no-run` rebuilt clean, then the test binary run
directly both before and after). `git status --porcelain` confirmed clean of
the mutation afterward (only the intended new/modified files remain staged
for commit).

**Checker discriminates both ways**, run with `/usr/bin/grep` and `[[:space:]]`
avoided entirely (uses `\.\.\.` literal dots, no `\t`):

```
cargo test -p axeyum-lean-kernel --lib \
  rat_prelude::cas_evt_bridge_tests::tests::evt_endpoint_exclusion_kernel_checked \
  -- --exact 2>/dev/null \
  | grep -cE '^test rat_prelude::cas_evt_bridge_tests::tests::evt_endpoint_exclusion_kernel_checked \.\.\. ok$'
```

Passing test -> `1`, exit 0. Mistyped filter (0 tests run) -> `0`, exit 1.
Wrong kernel bound -> the `ok` line disappears -> `0`, exit 1 (verified above
via the mutation).

**Nothing was relabelled and no checker was weakened.** `F:cas-extremum-irrational-argmax`
and `F:cas-ivt-cbrt2-in-1-2` (read-only per this lane's scope) are untouched.
The new fact `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` is a SIBLING,
not an edit — folding this evidence into
`F:cas-extremum-irrational-argmax` would make `classify_cas_certificate_fact`
label the WHOLE certificate (root differentiation, Sturm count included) as
kernel-reconstructed, which `cas_ivt_bridge_tests.rs`'s own module doc warns
against, exactly the reasoning the previous lane already established for the
IVT sibling pair.

**What this fact does NOT claim, stated plainly.** `x = -1` is NOT the true
argmax (`-sqrt(2)` is); the fact only shows `x = -1` beats both endpoints,
which is exactly the "the maximum is interior" content EVT's decidable-fragment
row-3 was missing, and no more. `p'`'s differentiation, `-sqrt(2)` being a
root of `p'`, and the Sturm completeness count all remain `cas-internal`.

**Gates run**: `rustfmt --edition 2024 --check` on the three touched files
(clean after one `rustfmt` pass — no manual formatting was needed beyond
that), `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
warnings` (clean), the target test itself (passing, `--exact`, nonzero count
confirmed), and the sibling `cas_ivt_bridge_tests::` suite re-run to confirm
the visibility changes (private `fn` -> `pub(crate) fn` on six helpers, no
logic changes) did not regress it (`2 passed`). The full workspace
`--workspace --lib` sweep did NOT run this pass (out of scope for a
single-module change and expensive under lane contention); the coordinator
re-verifies before merge per standing practice.
