# Lane: producer-widen — widen the conclusion-directed producer to a second family

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, producer-widen, 2026-08-28).** Task: widen
`producers::conclusion_directed_application` (lane 198, which closed ten open
`nat.modeq` facts) to a **second** family of currently-open facts.

**Outcome: no operation registered, so `facts_via_multi_target` is unchanged.**
(`operations=29`, `multi_target_operations=5`, and a read-only recomputation
over `operations.json` x fact status gives `facts_via_multi_target=31`, one
above the 30 the brief quotes; `gen-production-provenance-ledger.py --check`
was already stale on `main` before this lane started and was **not**
regenerated here, since regenerating would commit another lane's pending
delta.)
The lane found — and this is the deliverable — that the binding constraint is
not the producer's grammar and not family shape. It is that **Mathlib's own
proof is axiom-bearing for 61 of the 63 resolvable open propositions**, so no
transport can close them, and every widening must AUTHOR an axiom-free contract
per family. Three measurements, each re-derivable.

**Holdout isolation, before and after, unchanged and PASS:**
`held_out=37|files_scanned=1101|settled=0|references=0`. The two entirely
held-out families (`natural-logarithm` 21 open, `natural-square-root` 16 open —
37 facts, the whole partition) were excluded by **partition per fact**, never by
count, and no held-out target was measured, exported, or named. **No target was
dropped for any other reason**; nothing outside the exclusion was skipped.

## 1. The producer reaches 0 of 35 open palette facts

Every open, non-held-out fact with a proof-free target capsule in
`/nas3/.../reference-packs/open-fixed-palette-v1` (35), through
`examples/conclusion_directed_transport_probe`:

| outcome | count |
| --- | --- |
| accepted | **0** |
| declined at statement import (`dif_pos` 11, `Quot` 9, `Eq.subst` 3, `Nat.mod_lt` 2, `propext` 1) | **26** |
| imported, then `NoConclusionMatch` | **9** |

The 9 were run with **every theorem present in their own capsule** transported
(24 or 47 roots, `transport_declines=0`) — not the
`open-lemma-candidate-ranking-v1` names, 10 of whose 12 entries are
`MissingRoot` in every capsule because the pack exports each target with one
*target-agnostic elementary palette* and nothing family-specific. So those 9
declines are not candidate starvation: all 9 are **induction-shaped**, and no
application of an elementary lemma closes them.

The 26 are unreachable **whatever contract is authored** — the trusted
declaration is reached through the proposition's own definition closure, before
any candidate is considered. `import_statement_ndjson` rejects the entire
stream (`lib.rs:2069`), by design.

## 2. Mathlib's proof is axiom-bearing for 61 of 63

New, gated: `artifacts/autogenesis/open-frontier-axiom-freeness-census-v1.json`,
`#print axioms` over every open non-held-out ledger proposition that names a
Mathlib declaration, in the pinned environment
(`c5ea0035…`, Lean `d024af09…`):

| | |
| --- | --- |
| propositions | 68 |
| resolve in Mathlib v4.30 | 63 |
| **axiom-bearing** | **61** |
| **axiom-free** | **2** — `Nat.self_le_factorial`, `Nat.descFactorial_le` |
| absent at the pinned commit (`Int.fib_*`) | 5 |

This bounds ONE route and must not be over-read: an axiom-bearing Mathlib proof
does **not** mean no axiom-free proof exists — `nat.modeq` was closed
axiom-free against lemmas that all carry `propext`. What it does mean is that
"transport the Mathlib proof" is closed as a route, so the family-at-a-time
authored contract is the unit of work, which is exactly why one family cost
lane 198 a whole lane.

Spot-checks that pin the two families a brief would reach for first:
`Nat.dvd_lcm_left`, `Nat.dvd_lcm_right`, `Nat.dvd_lcm_of_dvd_left`,
`Nat.dvd_of_lcm_left_dvd` are all `[propext, Quot.sound]`, and so is plain
`Nat.dvd_trans` — so the `nat.dvd` lcm-transport family the queue suggests is
**four one-application theorems whose every ingredient is axiom-bearing**, and
any contract for it must first rebuild `Nat.gcd`'s recurrence, which lane 198
already measured as blocked (`Nat.gcd.eq_def` carries `Quot.sound`).

## 3. The Lean toolchain is now provisioned on this host

`scripts/provision-lean-import-toolchain.sh` — idempotent, pinned, `--verify`
does no network. Measured: ~5 minutes cold, all three pieces.

This is the finding a brief should carry forward. `command -v lean` is empty on
a host that has Lean, `docs/contributor-guide/fleet-hosts.md` records Mathlib as
s5-only, and this lane spent a third of its budget establishing that **s4 can in
fact run the whole import route**: `elan` has the pinned 4.30.0 toolchain, the
mathlib4 olean cache is already in `~/.cache/mathlib`, a blobless clone of
mathlib4 at `c5ea0035…` is 92 MB, and `lean4export` at `a3e35a58…` builds in
under a minute. The tree now lives at `/data0/axeyum/lean-import-toolchain`.

## What the next lane should do

1. `scripts/provision-lean-import-toolchain.sh --verify` (seconds, no network).
2. Pick a family from the **9 importable** targets, not from the 26 — the other
   26 cannot be reached however good the contract is.
3. Author the axiom-free contract in `scripts/lean/`, and confirm with
   `#print axioms` **before** exporting: a candidate with a non-empty footprint
   is rejected by `import_candidate_statement_ndjson`, not by the producer.
4. The `natural-factorial` cluster is the best-conditioned start — `Nat.factorial`,
   `Nat.descFactorial` and `Nat.ascFactorial` are all axiom-free *definitions*,
   `Nat.factorial_succ`/`Nat.factorial_pos`/`Nat.mul_le_mul_left`/`Nat.le_trans`
   are all axiom-free, and `Nat.self_le_factorial` has an axiom-free Mathlib
   proof, which is a witness that an axiom-free route exists. Its producer is
   `bounded_induction`, not `conclusion_directed_application`: these goals need
   the induction hypothesis, not a bigger application.

**Not attempted, and not claimed:** no fact status changed, no operation was
registered, and `cargo fmt --all --check` / `clippy` were not run because this
lane added no Rust.

<!-- plan-section: landed-changes -->

| 2026-08-28 | producer-widen | measured: conclusion-directed producer reaches 0 of 35 open non-held-out palette facts — 26 blocked at statement import, 9 induction-shaped |
| 2026-08-28 | producer-widen | new gated census: 61 of 63 open non-held-out propositions have an axiom-BEARING Mathlib proof, so transport cannot close the frontier; 6 guards each mutation-verified to kill exactly one control |
| 2026-08-28 | producer-widen | `scripts/provision-lean-import-toolchain.sh` — s4 CAN run the whole import route; pinned mathlib4 + lean4export provision in ~5 min |
