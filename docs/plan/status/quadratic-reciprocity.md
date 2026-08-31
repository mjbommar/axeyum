# Lane: quadratic-reciprocity

<!-- plan-section: lane-status -->

Status: **the routing question is answered; the law is NOT proved** (2026-08-31)

## What this lane was asked

Size, and if reachable close, the law of quadratic reciprocity for distinct odd
primes `p, q`: `(p|q)·(q|p) = (−1)^((p−1)/2 · (q−1)/2)`. The brief said
explicitly that the honest deliverable might be a precise obstruction rather
than a theorem, and that a lane must establish early whether Eisenstein's
lattice-point count hits the missing-aggregate wall ADR-1135 named for the
determinant's multiplicativity.

## What it found

**Eisenstein routes AROUND that wall.** The rectangle of lattice points never
has to exist as an object: a finite family here is a function plus a bound, and
the partition argument is a double `sumRange` with a `countRange` inside plus a
pointwise trichotomy. The step that decides it is now a kernel theorem.

**The law is not proved, and neither of Eisenstein's two steps is.** The
remaining obstruction is named in ADR-1260 and it is a DIFFERENT kind of gap
from ADR-1135's: **`Int.sumRange` does not exist** (the Int prelude has
`prodRange` and no sum aggregate at all — 291 registered Int names, 20 matching
`prodRange`, 0 matching `sumRange`), and Eisenstein's lemma is a signed-sum
argument. That is a missing construction over an existing carrier, not a missing
carrier, and nothing structural blocks it.
<!-- absent: Int.sumRange -- the obstruction; when it lands this paragraph is stale -->

## Landed changes

| what | where |
| --- | --- |
| `Nat.sumRange_const`, `Nat.countRange_eq_sumRange`, `Nat.sumRange_swap`, `Nat.countRectangle_partition`, `Nat.countRectangle_partition_compl` — five declarations, all admitted on the FIRST kernel attempt, all axiom-free | `crates/axeyum-lean-kernel/src/nat_prelude/lattice_count.rs` (new) |
| name fields, registration, build-order call | `crates/axeyum-lean-kernel/src/nat_prelude.rs` |
| the five names added to the environment-derived coverage list | `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` |
| `compl_sum_eq` exported (`pub(super)`) rather than re-derived — it was built inline for `countRange_compl` and was private | `crates/axeyum-lean-kernel/src/nat_prelude/finite_set.rs` |
| the decision, the obstruction, the mutation table, and what the controls do not catch | `docs/research/09-decisions/adr-1260-eisenstein-routes-around-the-missing-aggregate-wall.md` |
| re-runnable numeric verification: 8 claims, 10 controls, two of them recorded as deliberately SURVIVING | `docs/research/09-decisions/adr-1260-eisenstein-checks.py` |

## Verification run in this lane

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **313 passed, 0 failed**
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **65 passed, 0 failed**
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py` — PASS
- the three prior QR lanes' scripts (ADR-1230, ADR-1235) re-run — PASS

## Not done, deliberately

**No facts were registered for the five new declarations.** A fact's
`formal.statement` must be the machine-rendered type from
`kernel_declaration_projection --release`, never hand-transcribed, and that
release build did not fit in this lane's budget. This is the one piece of
follow-up the work needs.

## What a next lane should take

`Int.sumRange` plus its defining equations, `sumRange_add` and `sumRange_congr`
— roughly a mirror of `nat_prelude/defs.rs`'s construction over `Int.add`. That
unblocks Eisenstein's lemma (step 1), which is the binding constraint. ADR-1260
sizes the other two residues (the row-count-is-a-floor lemma, and the
`p·y ≠ q·x` side condition, which is Euclid's lemma and cheap).
