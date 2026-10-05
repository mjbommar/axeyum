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
from ADR-1135's: **`Int.sumRange` did not exist** when this lane ran (the Int
prelude had `prodRange` and no sum aggregate at all — 291 registered Int names,
20 matching `prodRange`, 0 matching `sumRange`), and Eisenstein's lemma is a
signed-sum argument. That was a missing construction over an existing carrier,
not a missing carrier, and nothing structural blocked it. **It has since landed**
(ADR-1275, `int_prelude/sum.rs`), so this paragraph records the obstruction as it
stood on 2026-08-31 and not as it stands now.
<!-- was-absent: Int.sumRange -- the obstruction; landed in ADR-1275 and the sentence above is now past tense -->

## Landed changes

| what | where |
| --- | --- |
| `Nat.sumRange_const`, `Nat.countRange_eq_sumRange`, `Nat.sumRange_swap`, `Nat.countRectangle_partition`, `Nat.countRectangle_partition_compl` — five declarations, all admitted on the FIRST kernel attempt, all axiom-free | `crates/axeyum-lean-kernel/src/nat_prelude/lattice_count.rs` (new) |
| name fields, registration, build-order call | `crates/axeyum-lean-kernel/src/nat_prelude.rs` |
| the five names added to the environment-derived coverage list | `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` |
| `compl_sum_eq` exported (`pub(super)`) rather than re-derived — it was built inline for `countRange_compl` and was private | `crates/axeyum-lean-kernel/src/nat_prelude/finite_set.rs` |
| the decision, the obstruction, the mutation table, and what the controls do not catch | `docs/research/09-decisions/adr-1260-eisenstein-routes-around-the-missing-aggregate-wall.md` |
| re-runnable numeric verification: 8 claims, 10 controls, two of them recorded as deliberately SURVIVING | `docs/research/09-decisions/adr-1260-eisenstein-checks.py` |
| five ledger facts, statements taken verbatim from `kernel_declaration_projection` | `artifacts/facts/F-nat-{sumrange-const,countrange-eq-sumrange,sumrange-swap,countrectangle-partition,countrectangle-partition-compl}.json` |

## Verification run in this lane

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **313 passed, 0 failed**
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **65 passed, 0 failed**
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py` — PASS
- the three prior QR lanes' scripts (ADR-1230, ADR-1235) re-run — PASS
- `python3 scripts/validate-facts.py` — exit 0
- `python3 scripts/check-settled-fact-statements.py` — PASS, 2258 pinned, drifted 0
- `python3 scripts/check-absence-claims.py` — OK, 44 markers, every claim still holds
- `scripts/check-merge-hygiene.sh` — PASS


## Mutation table

Six mutations of `lattice_count.rs`, each run against the whole `nat_prelude::`
sweep with the file restored afterwards: **five REJECTED, one
ADMITTED-and-SURVIVED**. The survivor is the corollary's two `Nat` binders in
the opposite order — true, admitted, and not the theorem meant, and no numeric
test can catch it because the partition totals `m·n` either way. Full table and
the two self-corrections it forced are in ADR-1260.

## What a next lane should take

`Int.sumRange` plus its defining equations, `sumRange_add` and `sumRange_congr`
— roughly a mirror of `nat_prelude/defs.rs`'s construction over `Int.add`. That
unblocks Eisenstein's lemma (step 1), which is the binding constraint. ADR-1260
sizes the other two residues (the row-count-is-a-floor lemma, and the
`p·y ≠ q·x` side condition, which is Euclid's lemma and cheap).
