# Notes: int-modeq-kernel

Detail moved out of [`../status/int-modeq-kernel.md`](../status/int-modeq-kernel.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Not attempted**: the remaining six of the eleven declined facts
(`modeq-add-left`, `modeq-add-left-cancel`, `modeq-dvd-iff`, `modeq-neg`,
`modeq-of-dvd`, `modeq-of-mul-left`) are CONGRUENCE lemmas needing an existing
`ModEq` hypothesis, structurally different from the five unconditional
identities closed here, and each would need its own case-split-on-sign
argument built on top of `modeq.rs`'s existing conditional congruence family
— a well-scoped next task, flagged in doc 293, not started.

**Two genuine blockers found and reported, not forced through**:

1. Operation registration (ADR-0602): `scripts/validate-autogenesis-operations.py`'s
   `EXECUTION_DRIVERS` set has no shape for "a hand-authored kernel-lane proof
   with no producer/checker/executor pipeline component" — every existing
   entry is either a fully-automated search proposer or import-mediated.
   Adding a new driver value requires editing `scripts/`, out of this lane's
   scope. `operations.json` left untouched (`operations=27`, unchanged)
   rather than registering a misdescriptive entry against an existing driver.
2. Contract route/recipe mismatch (asked for by the brief, confirmed):
   `producer-contracts/int-modeq-family-v1.json` labels its `route` as
   `kernel-lane`, but every operation ever run against it
   (`authoritative-mathlib-modeq-family-v1`,
   `authoritative-mathlib-nat-modeq-remainder-family-v1`) uses an
   IMPORT-mediated executor (author an s5 Lean adapter, export, feed the
   statement-adapter importer, then run `propose_modeq_family`). This lane's
   five proofs are the first genuinely `kernel-lane` closure in this family
   and happened entirely outside the contract. Contract file not edited
   (another lane may own it); finding reported in doc 293.

Verification: `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 34
passed, 0 failed. `cargo test -p axeyum-lean-kernel --lib` (full crate) — 832
passed, 0 failed (511.79s, ran in background per the foreground-preference
rule, confirmed complete before this report). `validate-facts.py` — 805
facts, 0 errors. `validate-autogenesis-operations.py` — unchanged, 27.
`validate-producer-contract-declines.py` — unchanged, 27.
`check-autogenesis-holdout-isolation.py` — PASS, held_out=37 unchanged.
