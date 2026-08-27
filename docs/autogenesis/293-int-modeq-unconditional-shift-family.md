# 293 — The unconditional `Int.ModEq` shift family: closing five of doc 292's eleven declines

Date: 2026-08-27
Lane: int-modeq-kernel

## Task

Doc 292's batched flywheel turn dispatched every admissible fact and got 26
declines, 0 proofs. Eleven were `Int.ModEq` facts declining with
`DeclineReason::TerminalNotClosed`: the contract's producer
(`propose_modeq_family`) only closes combinator-over-hypothesis shapes
(refl/symm/trans/comm applied to an already-given equality); every one of
these eleven is an unconditional identity with no hypothesis to run a
combinator over.

This lane's job was to prove as many of the eleven as reachable by one route,
in `crates/axeyum-lean-kernel/src/int_prelude/` directly (bypassing the
producer/import pipeline entirely, per ADR-0601's "three producers, one trust
anchor" — a `kernel-lane` producer is exactly as legitimate as an imported
one, and the trust anchor is `Kernel::add_declaration`, not which crate wrote
the term).

## The diagnosis, verified before building anything

`Int.ModEq n a b := emod a n = emod b n`
(`crates/axeyum-lean-kernel/src/int_prelude/modeq.rs`). Every congruence law
in that file needs `0 < n`, because its only bridge to `Int.dvd`
(`declare_modeq_iff_dvd`) needs `Int.emod_lt_of_pos`, the only proved bound on
`emod`'s magnitude — and that bound only holds for a positive divisor. The
brief's diagnosis was that `Int.emod _ 0` is total (`Int.emod a 0 = a`, from
`crates/axeyum-lean-kernel/src/int_prelude/division.rs`'s own header), so the
unconditional facts should be reachable by a route that never needs the
magnitude bound at `n = 0` or at a negative `n` — confirmed by reading
`division.rs` directly rather than trusting the brief: `Int.emod`'s
`negSucc _, ofNat 0` row collapses via `Nat.mod_zero` to exactly the identity,
and the header states this explicitly as "no case to split."

## The route: one new general lemma, five corollaries

`Int.modEq_add_mul_left : ∀ n a q, ModEq n (add (mul n q) a) a` — adding any
integer multiple of the modulus does not change the residue, for **every**
`n : ℤ`. Proved unconditionally by `case_split` on `n`'s `Int.rec` shape
alone (`a`, `q` stay symbolic throughout — only the modulus's sign matters):

- **`n = ofNat 0`**: `mul zero q = zero` (`Int.mul_comm` + `Int.mul_zero`),
  then `add zero a = a` (`Int.add_comm` + `Int.add_zero`); the goal closes by
  lifting that `Eq` into `emod(_, zero)` directly (the same idiom
  `declare_modeq_refl` already uses — `Int.ModEq` unfolds to exactly that
  `Eq`, no positivity anywhere in this branch).
- **`n = ofNat (succ k)`** (a genuine positive modulus): the EXISTING
  `Int.modEq_iff_dvd` bridge, applied at the one concrete shape where its
  hypothesis is free — `0 < ofNat (succ k)` is `NatOps::zero_lt_succ k`
  applied through the definitional reduction `Int.lt (ofNat 0) (ofNat (succ
  k)) ≡ Nat.lt 0 (succ k)` (the same technique `declare_order_theorems`'s own
  `zero_lt_one` uses, generalized from the literal `1` to a symbolic `succ
  k`). The divisibility witness is `neg q`: `a - (mul n q + a) = neg (mul n
  q) = mul n (neg q)`, via a new private helper `sub_add_self_left` (built
  from the EXISTING `cancel_common_addend`, applied at `(0+a) - (x+a) = 0-x`)
  and `Int.mul_neg`.
- **`n = negSucc k`** (a genuine negative modulus — the leg no other
  congruence law in `modeq.rs` can reach): reduces to the SAME positive-shape
  argument at `m := ofNat (succ k)`, witness `neg q` (i.e. run the positive
  case at `mul m (neg q)`), then cross to modulus `neg m` — which IS
  `negSucc k` up to defeq — via the ALREADY-proved
  `Int.modEq_neg_modulus`, followed by one rewrite turning `mul m (neg q)`
  into `mul (neg m) q` (a new private `local_neg_mul`, `Int.mul_neg` +
  `Int.mul_comm`) so the term matches what the case-split's own goal
  literally names.

No magnitude bound was ever needed for a negative or zero modulus — the
brief's diagnosis was correct, and the negative leg's existing blocker
(`division.rs`'s own header: "no proved analogue for a negative modulus")
never enters this proof at all, because it goes through
`Int.modEq_neg_modulus` instead of a second copy of `modEq_iff_dvd`.

Five direct corollaries, each a specialization plus a rewrite, not new
case-split work:

| theorem | route |
|---|---|
| `Int.add_modEq_left : ∀ n a, ModEq n (add n a) a` | `q := 1`, rewrite `mul n 1 → n` (`Int.mul_one`) |
| `Int.add_modEq_right : ∀ n a, ModEq n (add a n) a` | `add_modEq_left` rewritten via `Int.add_comm` |
| `Int.mod_modEq : ∀ a n, ModEq n (emod a n) a` | `a := emod a n`, `q := ediv a n`, rewritten via `Int.ediv_add_emod`, flipped with `Int.ModEq.symm` |
| `Int.modulus_modEq_zero : ∀ n, ModEq n n zero` | `a := 0`, `q := 1`, rewritten via `Int.mul_one`/`Int.add_zero` |
| `Int.modEq_sub : ∀ a b, ModEq (sub a b) a b` | `n := sub a b`, `a := b`, `q := 1`, rewritten via `Int.mul_one` and the already-proved `cancel_neg_add` (`(a-b)+b = a`) |

All six declarations: `crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`.

## Kernel verification

`cargo test -p axeyum-lean-kernel --lib int_prelude::` — **34 passed, 0
failed** (up from 33; one new test added), including:

- `int_prelude_admits_all_declarations` — the whole prelude, including these
  six, builds via `Kernel::add_declaration` end to end.
- `every_int_declaration_is_checked_and_axiom_free` — environment-derived
  coverage (not a hand list): failed on first run naming exactly the six new
  names, fixed by adding them to `derived_laws`, recounted 126 → 132 by
  **counting** the array (not incrementing — CLAUDE.md's standing rule),
  verified: 132 `p.` entries between the function's opening and closing
  bracket.
- `derived_laws_have_no_axiom_footprint` — `Kernel::axiom_footprint` is `[]`
  for all six.
- `the_modeq_ledger_rows_are_stated_without_a_positivity_hypothesis` —
  extended with the six names' exact `render_lean` output, each asserted to
  contain no `Int.lt Int.zero` premise. Every string was PREDICTED before
  running (from the Rust construction) and matched the kernel's own output
  exactly on first measurement — no guessing against the kernel.
- **New**: `add_modeq_family_computes_at_concrete_values` — applies each of
  the six theorems to literal `Int` numerals at three regimes (`n := 0`,
  `n := 5`, `n := -4`) and confirms via `Kernel::def_eq` that both `emod`
  sides of each `ModEq` reduce to the SAME literal, not merely that both are
  stuck. At `n = 0` specifically, confirms the shared value is genuinely the
  input `a` (or `0`, for `modulus_modEq_zero`) — the case that motivates
  unconditionality at all.

Two mutations, each in an isolated `scripts/lane-snapshot.sh` copy (never the
shared checkout), each killing exactly one test:

- Swapping the argument order inside one pinned rendered-type string: **33
  passed / 1 failed** (only `the_modeq_ledger_rows_are_stated_without_a_positivity_hypothesis`).
- Changing the expected reduced literal in the concrete-values test (`2 →
  3`, where `5*3+2 mod 5` genuinely is `2`): **33 passed / 1 failed** (only
  `add_modeq_family_computes_at_concrete_values`).

`cargo test -p axeyum-lean-kernel --lib` (the full crate, not just
`int_prelude::`) was also run in the background per this task's own
foreground-preference rule for anything bounded; it completed with exit code
0 before this report was written (background task `b40rk6gek`), so the
change is confirmed not to have regressed anything else in the crate.

No `Nat`-namespace name was added (every new declaration is under `Int`), so
the `arith_model`/`characterization` namespace-collision check the brief
flags was not required and was not run.

## Facts closed

Five of the eleven `Int.ModEq` facts doc 292 declined:

- `F:ml430-int-add-modeq-left-ee732b5b` (`Int.add_modEq_left`)
- `F:ml430-int-add-modeq-right-e58108ee` (`Int.add_modEq_right`)
- `F:ml430-int-mod-modeq-6bec7847` (`Int.mod_modEq`)
- `F:ml430-int-modulus-modeq-zero-5b57a898` (`Int.modulus_modEq_zero`)
- `F:ml430-int-modeq-sub-3148f130` (`Int.modEq_sub`)

Each flipped `open` → `proved`, `proof_route: "kernel-lean"`,
`axiom_footprint: []`, three evidence rows each (statement pin, axiom
footprint, concrete corroboration), all `check_status: "checked"` with a
`checker_command` that fails on the finding, not merely on completion.
`python3 scripts/validate-facts.py`: **805 facts checked, 0 errors**.

The remaining six of the eleven (`modeq-add-left`, `modeq-add-left-cancel`,
`modeq-dvd-iff`, `modeq-neg`, `modeq-of-dvd`, `modeq-of-mul-left`) are
CONGRUENCE lemmas — they take an existing `ModEq n a b` hypothesis and
conclude a related `ModEq`, unlike the five closed here, which are
unconditional IDENTITIES with no hypothesis at all. Generalizing those six to
an arbitrary (including negative) modulus is a genuinely different, larger
task: it means re-deriving `modeq.rs`'s whole `add_left`/`add_right`/`mul_*`/
`cancel`/`dvd_iff`/`of_dvd`/`of_mul_left` congruence family unconditionally
(the same case-split-on-sign technique this lane used generalizes to each of
them individually, since `Int.modEq_neg_modulus`/`Int.modEq_of_neg_modulus`
already exist as the negative-to-positive bridge for ANY `ModEq`-shaped
conclusion — but each one needs its own `0`-case argument and its own
positive-case construction, none of which reduces to `modEq_add_mul_left`).
Flagged as a well-scoped next task, not attempted here to keep this lane's
diff reviewable.

## Decline artifacts: amended, not deleted

Per doc 291's convention, the five corresponding decline artifacts under
`artifacts/autogenesis/` were AMENDED with a new top-level `amendment` field
recording the later admission and the actual route — every required field
(`producer.result: "declined"`, `decline_reason`, `decline_message`, etc.)
is untouched, because the decline is still true: `propose_modeq_family`
genuinely cannot close any of these five goals today, for exactly the stated
reason. Verified: `python3 scripts/validate-producer-contract-declines.py`
still reports `PRODUCER_CONTRACT_DECLINES_OK|declines=27` (unchanged count)
after the amendment.

One decline's own prediction was wrong in an interesting way, recorded in its
amendment: `mathlib-int-add-modeq-left-decline-v1.json`'s `next` field named
"a natAbs-based magnitude bound generalizing `Int.emod_lt_of_pos`" as the
missing ingredient. That bound was never built or needed — the actual route
sidesteps it entirely by only ever invoking the EXISTING positive-only bound
at one concrete shape, and handling the negative modulus through a modulus
transformation (`Int.modEq_neg_modulus`) rather than a stronger inequality.
Simpler than predicted.

## Operation registration: attempted, genuinely blocked, not forced

ADR-0602 ("admission precedes registration") calls for a retrospective
operation receipt once a fact is honestly proved. `python3
scripts/validate-autogenesis-operations.py` still reports
`AUTOGENESIS_OPERATIONS_OK|operations=27` (unchanged) because **no entry was
added** — every existing entry's `executor.driver` must be one of a fixed,
hardcoded set in `scripts/validate-autogenesis-operations.py`'s
`EXECUTION_DRIVERS`, checked with `raise RegistryError` for anything else.
Every driver in that set names either a fully-automated search/induction
proposer (`axeyum-lean-kernel/nat-zero-add-induction-v1`, `.../nat-mul-one-episode-apply-v1`)
or an import-mediated multi-target executor
(`axeyum-lean-import/modeq-family-multi-target-v1`,
`.../imported-candidate-family-multi-target-v1`, …). None of them describes
"an agent read a Mathlib statement and hand-wrote a new Rust kernel proof
directly against `Kernel::add_declaration`, with no producer/checker/executor
pipeline component running at all" — which is exactly what happened here, and
exactly what a `kernel-lane` producer contract (ADR-0601) is supposed to
cover.

Registering a genuinely accurate entry would need a new `EXECUTION_DRIVERS`
value such as `axeyum-lean-kernel/hand-authored-shift-family-v1`, added to
`scripts/validate-autogenesis-operations.py` — a file this lane's brief puts
explicitly out of scope (`Do NOT edit ... scripts/`). Rather than force
through an entry using an existing driver that would misdescribe what
happened (claiming an import or a search pipeline produced this proof, when
neither did), or edit a file outside this lane's scope, this lane leaves
`operations.json` untouched and reports the gap: **the operation registry's
schema currently has no shape for a hand-authored kernel-lane proof that
bypasses every existing pipeline**, and closing that gap is a `scripts/`-side
task for whichever lane owns that file. `validate-facts.py` confirms an
operation entry is not required for a fact's `proved` status (805 facts, 0
errors, with these five facts carrying no operation reference) — this is a
provenance-tracking gap, not a soundness one.

## The contract route/recipe mismatch: confirmed, not touched

The task asked whether `int-modeq-family-v1`'s labeled `route: kernel-lane`
disagrees with its actual recipe. Read directly from
`artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json` and the
operations this lane inspected while looking for a template
(`authoritative-mathlib-modeq-family-v1`,
`authoritative-mathlib-nat-modeq-remainder-family-v1`): every operation ever
registered against this contract's shape uses an IMPORT-mediated executor
(`axeyum-lean-import/modeq-family-multi-target-v1` or
`axeyum-lean-import/imported-candidate-family-multi-target-v1`) — author an
s5 Lean adapter, export via `lean4export`, feed
`crates/axeyum-lean-import/examples/statement_adapter_import.rs`, then run
`propose_modeq_family`. **Confirmed mismatch**: the contract's `route` field
says `kernel-lane`, but every executor that has ever run against it is
import-mediated, not a from-scratch kernel construction. This lane's own five
proofs are the FIRST genuinely `kernel-lane` closure in this family, and they
happened entirely OUTSIDE the contract (no adapter authored, no export run,
`propose_modeq_family` never invoked) — which is exactly what exposed the
mismatch, rather than resolving it. Per the brief, the contract file itself
(`artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json`) was NOT
edited; this is a finding for whichever lane owns it.

## Scope discipline

Touched: `crates/axeyum-lean-kernel/src/int_prelude.rs` (six new `NameId`
fields + six dispatch calls — necessary parent-module infrastructure for any
new named declaration, not itself inside `int_prelude/` but unavoidable),
`crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`,
`crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs`, the five
fact JSON files, the five decline JSON files (amendment only), this doc, and
`docs/plan/status/int-modeq-kernel.md`.

Not touched: `crates/axeyum-lean-kernel/src/creal/`, `complex/`,
`crates/axeyum-cas/`, `scripts/`, either producer contract instance,
`python/axeyum/agent/`, `artifacts/autogenesis/operations.json`.

## Verification run

```
cargo test -p axeyum-lean-kernel --lib int_prelude::
  34 passed; 0 failed
python3 scripts/validate-facts.py
  805 facts checked, 0 errors
python3 scripts/validate-autogenesis-operations.py
  AUTOGENESIS_OPERATIONS_OK|operations=27
python3 scripts/validate-producer-contract-declines.py
  PRODUCER_CONTRACT_DECLINES_OK|declines=27
python3 scripts/check-autogenesis-holdout-isolation.py
  AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1100|settled=0|references=0|verdict=PASS
```
