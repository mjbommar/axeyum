# Lane: import-projrec — structure eta on a stuck recursor major

<!-- plan-section: lane-status -->

**Implemented structure eta reduction of a stuck recursor major premise
([ADR-0466](../../research/09-decisions/adr-0466-structure-eta-reduces-a-stuck-recursor-major.md)),
and stopped before measuring what it buys** (`WIP`, import-projrec, 2026-08-15).
Cut off by the account's monthly spend limit at the words *"now the real-Lean
crosscheck"*; landed by the coordinator in `c1d9c6f3b` after re-running its gates.

**Where it came from.** [`import-wfrec`](91-import-wfrec.md) fixed a ζ-reduction
hole and handed over `Nat.Linear.Poly.denote_reverse` as the next binding root in
both corpora, with the mismatch already probed: `Prod.rec` (6 args) against
`(Nat.brecOn.go.{1} … Nat.mul._f).1` (1 arg), and a named model in Lean's own
`lazy_delta_reduction_step`.

**Gates, re-run on the assembled worktree rather than inherited:**

```
cargo check --workspace --all-features                     exit 0
cargo test -p axeyum-lean-kernel                           276 lib + every suite, 0 failed
  --test structure_eta_recursor_major                      6 passed
  --test real_lean_structure_eta_recursor_crosscheck       1 passed
  --test k_like_reduction                                  7 passed
cargo clippy -p axeyum-solver -p axeyum-lean-kernel
  --all-targets --all-features -- -D warnings              exit 0
```

That `k_like_reduction` line matters. An earlier lane reported it **failing** in
the shared worktree and correctly judged it *not theirs*; what it was seeing was
this lane's edit in an intermediate state. Both readings were right at the time,
which is the ordinary hazard of a shared checkout and the reason the private-index
protocol exists.

**What is NOT claimed.** The **paired corpus A/B was never run**, so the
import-census effect of this rule is **unmeasured** — no CLEAN-rate movement may
be attributed to it. `import-wfrec` retained the 500-stream `Init`+`Std` corpus
with both paired analyses and the pairing script at
`/nas3/data/axeyum/lean-import-scale/initstd-500-streams/` precisely so the next
lane's A/B costs no re-export. Run that before quoting a number.

**Also unresolved:** whether this rule closes `Nat.Linear.Poly.denote_reverse` at
all. Lean's `try_unfold_proj_app` branch — the one whose comment names
well-founded recursion explicitly — still has no counterpart here.
