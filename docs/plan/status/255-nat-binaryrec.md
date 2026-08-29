# Lane: nat-binaryrec — `Nat.binaryRec`, a pair type, and `Nat.fastFib`

<!-- plan-section: lane-status -->

**IN PROGRESS (nat-binaryrec, 2026-08-29).** Early skeleton commit, per the
standing rule that a lane's first commit lands within its first ten tool
calls even if incomplete. Findings so far:

- `Prod` in this repository is a **test fixture only** (`inductive/
  inductive_tests.rs::prod_two_params_one_ctor`), not a prelude declaration —
  pending confirmation by reading `kernel.environment()`.
- The established pair device here is a **`Bool`-selected function**, not a
  product: `Nat.xgcdAux … (sel : Bool)` (`int_prelude/bezout_witnesses.rs`),
  `Nat.divModState` (`ops.rs`), and `creal/ivt.rs`'s `Bool -> CReal` bracket
  carrier all use it deliberately.

Remainder of this document is written as the work lands.
