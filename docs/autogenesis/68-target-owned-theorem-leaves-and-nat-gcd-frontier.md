# Target-owned theorem leaves and the Nat.gcd frontier

## Result

Theorem composition can now treat an explicit, compatible, axiom-free theorem
already owned by the target as a proof-dependency leaf. The source theorem and
its type dependencies remain selected; only the unrelated proof behind that
theorem is cut. Every leaf is checked in both kernels, required reachable and
footprint-empty, bound into a distinct receipt schema, and replayed.

The real Lean 4.30 r082 retry moves the `Nat.dvd_gcd` frontier twice:

| Explicit target leaves | Source closure | `Nat.div_mod_exec` present | First rejection |
|---|---:|---|---|
| `Nat.dvd_mod_iff` | 66 | yes | `Nat.div_mod_exec` |
| `Nat.dvd_mod_iff`, `Nat.mod_lt` | 57 | no | `Nat.gcd_succ` |

Both declines leave the 315-declaration target caller unchanged. The second
<!-- was-absent: Nat.div_mod_exec -->
attempt therefore closes the prior division mismatch: it does not suppress the
error; `Nat.div_mod_exec` is absent from the selected closure, and independent
admission proceeds to a different mathematical boundary.

## Contract and controls

ADR-0531 fixes the V1 policy. `Kernel::root_declaration_closure_with_theorem_leaves`
stops dependency traversal at the value of an explicit checked theorem while
retaining its type graph. `compose_checked_theorem_slice_with_target_leaves`
then applies the ordinary target reuse and admission gates in a private clone.

Controls cover:

- exact proof-only cutting and dependency order;
- empty, duplicate, missing, non-theorem, and unreachable leaves;
- a valid same-name theorem with the wrong type;
- a target theorem whose kernel footprint reaches an assumption;
- receipt leaf mutation and exact replay; and
- unchanged caller state on every decline.

The pre-existing V5 composition receipt serialization remains unchanged. The
earlier constructive specialization still reproduces byte-for-byte with SHA-256
`54d2a0805cf41f3c1e5c9cf9592848e665d6341d5ff5e23bdd14d1889b330575`.

## Why Nat.gcd_succ is a new foundation

The imported r082 slice contains `Nat.gcd` but not `Nat.gcd_succ`. Native
Axeyum proves a same-statement theorem over its own well-founded gcd
implementation, but that proof term is not definitionally equal over Lean's
imported implementation and the target kernel rejects it.

The obvious official support is also unsuitable for the axiom-free route:

| Official Lean 4.30 theorem | Declaration identity | Kernel footprint |
|---|---|---|
| `Nat.gcd_succ` | `5508f854491d6efee655061a69710e2b7250883f6a4d08afa0f1472cee94e217` | `Quot`, `Quot.lift`, `Quot.mk`, `Quot.sound` |
| `_private.Init.Data.Nat.Gcd.0.Nat.gcd.eq_1` | `9673ec16e49e53dffb698e4a2f7a8ff7c2791c5730805485d94d1ddd254f8bee` | `Quot`, `Quot.lift`, `Quot.mk`, `Quot.sound` |

The high-level proof reaches the generated recursion equation, and the equation
itself reaches `Quot.sound` through Lean's well-founded implementation. A fresh
Lean 4.30 control also rejects `rfl`; the successor equation is not merely
hidden definitional reduction.

This is not permission to import the quotient footprint. The next bottom-up
task is an axiom-free target-side gcd computation contract, or a downstream
`Nat.dvd_gcd` proof route that avoids this equation entirely.

## Immutable evidence

The sealed pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/5fb817301-lean430-nat-gcd-target-leaf-frontier-v1/manifest.json`

Its manifest SHA-256 is
`5619dcefce4aea6be55a3f66fa8d81d2a2869a654b5e5d036db3ccb848d21154`.
The directory is mode `0555`; all six files are mode `0444`. It binds:

- the exact target-leaf implementation and source-closure primitive at commit
  `5fb8173012d5248118f9b564c2afb89c9532b9d7`;
- the constructive `Nat.dvd_mod_iff` pack and unchanged r082 stream;
- both target-leaf closure measurements and semantic error digests;
- fresh official exports and independent Axeyum audits of both gcd theorems;
- Lean 4.30, Lean commit, and lean4export commit identities; and
- zero proof search, target-outcome access, ledger writes, or failed-clone
  publication.

## Validation and reproduction

The complete importer all-target suite passes, including the 336-second
official-Lean differential. Kernel export tests, warning-denied all-target
Clippy, the plan checker, ten checker tests, generated-plan checks, ADR-index
checks, and links pass.

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_mod_invariant_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  --probe-dvd-gcd

cargo run -q -p axeyum-lean-import \
  --example lean4export_import -- \
  /path/to/nat-gcd-succ.ndjson Nat.gcd_succ

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

No fact status changes and no ledger credit is due: the downstream
`Nat.dvd_gcd` theorem still declines, now at a narrower and independently
measured foundation.

## Subsequent resolution

The named frontier is closed by the target-specific pointwise fuel proof in
[Axiom-free official `Nat.gcd_succ`](71-axiom-free-official-nat-gcd-succ.md).
That theorem has an empty footprint, and the same three-leaf `Nat.dvd_gcd`
composition now succeeds and replays. This note remains the immutable negative
measurement that selected the repair.
