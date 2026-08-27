# Lane: int-modeq-kernel — the unconditional `Int.ModEq` family

<!-- plan-section: lane-status -->

**Closed five of doc 292's eleven declined `Int.ModEq` facts** (`DONE`,
int-modeq-kernel, 2026-08-27). Doc 292's batched flywheel turn declined
eleven unconditional `Int.ModEq` identities with `TerminalNotClosed` — the
combinator-over-hypothesis producer has no congruence step for a fact with no
hypothesis to combine. This lane proved a new general kernel theorem,
`Int.modEq_add_mul_left : ∀ n a q, ModEq n (add (mul n q) a) a`, unconditional
in `n` (case-split on `n`'s `Int.rec` shape: `0` trivial via the `emod`
zero-identity; positive via the existing `Int.modEq_iff_dvd` bridge at one
concrete shape; negative reduced to the positive case via the already-proved
`Int.modEq_neg_modulus`/`Int.emod_neg` pair — no new magnitude bound needed
anywhere), plus five direct corollaries: `Int.add_modEq_left`,
`Int.add_modEq_right`, `Int.mod_modEq`, `Int.modulus_modEq_zero`,
`Int.modEq_sub`. All six are `Kernel::add_declaration`-checked `Theorem`s with
empty `axiom_footprint`. Full account:
[`docs/autogenesis/293-int-modeq-unconditional-shift-family.md`](../../autogenesis/293-int-modeq-unconditional-shift-family.md).

Five facts flipped `open` → `proved`
(`F:ml430-int-add-modeq-left-ee732b5b`, `F:ml430-int-add-modeq-right-e58108ee`,
`F:ml430-int-mod-modeq-6bec7847`, `F:ml430-int-modulus-modeq-zero-5b57a898`,
`F:ml430-int-modeq-sub-3148f130`), each with three evidence rows (statement
pin, axiom footprint, concrete corroboration at `n := 0`, `n := 5`, `n := -4`,
mutation-verified in an isolated snapshot). The corresponding five decline
artifacts were AMENDED (not deleted, doc 291's convention) with the later
admission and the actual route.

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending) | `Int.modEq_add_mul_left` + five corollaries (`Int.add_modEq_left`, `Int.add_modEq_right`, `Int.mod_modEq`, `Int.modulus_modEq_zero`, `Int.modEq_sub`) in `crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`, proved unconditionally in the modulus via `case_split` on `Int.rec` shape — no `0 < n` hypothesis anywhere, closing five of doc 292's eleven declined `Int.ModEq` facts. `derived_laws` recounted 126 → 132 (counted, not incremented). New concrete-instantiation test at n := 0/5/-4, mutation-verified. Five facts flipped `open` → `proved`; five decline artifacts amended (not deleted). `cargo test -p axeyum-lean-kernel --lib`: 832 passed, 0 failed. |
