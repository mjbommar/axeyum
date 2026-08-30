# Lane: nat-binaryrec — `Nat.Pair`, `Nat.binaryRec`, and the `fastFib` keystone

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-binaryrec, 2026-08-29).** Both pieces of
infrastructure `docs/plan/status/250-nat-fastfib-minfac.md` named as blocking
`Nat.fastFib` are landed and kernel-checked: a **product type** and a
**bit-halving recursion combinator**, plus the recursive equation that makes
the combinator usable in a proof rather than only in a computation.
`Nat.fastFib` itself was **not** built — see "Where I stopped".

The honesty question the brief asked is answered against Mathlib's actual
source, and the answer changes what a future `fastFib` lane should aim at:
**a fuel encoding is a different construction, so `F:ml430-nat-fastfib-eq-cde11774`
stays `open` even after `fastFib` is built.**

New declarations: 4 definitions + 14 theorems + 1 inductive family (3 names).
`nat_prelude::` sweep **133 passed, 0 failed** (was 132). `nat` trusted
surface unchanged at **0**.

## 1. Was a pair type already available? No — and here is how I determined it

`Prod` appears in four files, and **none of them is a prelude declaration**:

| site | what it is |
| --- | --- |
| `inductive/inductive_tests.rs:1399` | a **test fixture** — `prod_two_params_one_ctor` admits `Prod α β` through `add_inductive` and checks its recursor's iota rule. Never built into any prelude. |
| `inductive.rs:23`, `env.rs:122` | module-doc prose naming `Prod` as a shape the inductive layer supports |
| `creal.rs:4042`, `creal/ivt.rs:2324` | doc comments explaining a deliberate choice NOT to introduce one |
| `nat_prelude/diagonal.rs:39`, `int_prelude/bezout_witnesses.rs:55` | doc comments recording the same absence |

Detail moved to [`../notes/255-nat-binaryrec.md`](../notes/255-nat-binaryrec.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-binaryrec | `Nat.Pair` (+`mk`/`rec`/`fst`/`snd`/`fst_mk`/`snd_mk`/`eta`/`ext`) — this prelude's first product type; `Prod` was a test fixture only, confirmed by enumerating every non-test `add_inductive` call site |
| 2026-08-29 | nat-binaryrec | `Nat.binaryRecAux`/`Nat.binaryRec` + 4 refl equations + `binaryRecAux_agree_of_fuel` (double-fuel) + `binaryRec_succ`; new facts `F:nat-binary-rec-fuel-irrelevance`, `F:nat-binary-rec-succ` |
| 2026-08-29 | nat-binaryrec | `Nat.lt_two_mul_of_pos`/`Nat.half_le_of_succ_le_succ` — the halving arithmetic promoted out of four unnamed private copies (`log.rs`, `binary.rs`, `powsq.rs`, `rec_agreement.rs`); the copies are NOT yet deleted |
| 2026-08-29 | nat-binaryrec | `F:ml430-nat-fastfib-eq-cde11774` confirmed staying `open`: Mathlib's `binaryRec` is well-founded recursion with a dependent `Sort u` motive, ours is a non-dependent fuel encoding — a different `def`, so any `fastFib` built here lands as a new local fact. `Nat.fastFib` NOT built. |
