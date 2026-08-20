# Nat division composition mismatch

## Result

The unchanged Mathlib 4.30.0 r082 `Nat.dvd_gcd` composition control still
declines, but the rejection is now semantic and durable rather than a pair of
process-local expression IDs. The target kernel expects the official
`Nat.div_mod_exec` theorem statement over imported `Nat.mod`. The translated
native proof instead infers the native division step whose next remainder is a
`Bool.rec` rollover expression.

The first bounded mismatch occurs where imported `Nat.add` consumes that
remainder:

| Expected | Inferred |
|---|---|
| `Nat.mod (Nat.succ n) (Nat.succ k)` | `Bool.rec (Nat.succ (Nat.mod n (Nat.succ k))) Nat.zero (Nat.beq (Nat.mod n (Nat.succ k)) k)` |

This is not authority to declare the expressions equivalent. The target
kernel rejected the proof, the private clone was discarded, and the caller
environment identity remained unchanged.

## The actual next dependency

The complete native source closure for `Nat.dvd_gcd` contains 92 declarations.
Exactly two direct consumers in that closure depend on `Nat.div_mod_exec`:

| Consumer | Target status |
|---|---|
| `Nat.mod_lt` | already reusable through target-checked definitional equality |
| `Nat.dvd_mod_iff` | missing and still attempts the incompatible native proof chain |

A target-aware dependency-cut experiment excluded nothing: the full closure
and the proposed cut both contained 92 declarations. It was removed rather
than promoted as a zero-delta API. Reusing `Nat.mod_lt` alone cannot bypass the
independent `Nat.dvd_mod_iff` dependency.

The next repair is therefore narrower than “transport `Nat.div_mod_exec`” and
more honest than weakening definitional equality: construct an axiom-free
target-side `Nat.dvd_mod_iff` proof or bridge over the already imported
official `Nat.mod`, then replay the unchanged `Nat.dvd_gcd` root.

## Official Lean support audit

The reusable `lean4export_import` example now accepts an optional theorem name
and reports its canonical declaration identity, kernel-derived axiom
footprint, and direct theorem dependencies. Fresh Lean 4.30.0 exports were
generated for the two obvious official support theorems:

| Theorem | Declaration identity | Kernel axiom footprint | Decision |
|---|---|---|---|
| `Nat.dvd_mod_iff` | `99bc389ae70b1b688ad37a9728c978c38b72b4ce8e95df7333ab7099edb5e1ee` | `propext` | reference only |
| `Nat.mod_add_div` | `bd40e537243af5794fc9d576e60056ba5a11e35101f7af6c49a416ffae99a4c1` | `propext` | reference only |

Importing either official proof would make this presently axiom-free library
slice assumption-bearing. Both are therefore rejected as durable support.
Their statements and dependency shapes remain useful reference material for
constructing a different proof whose footprint the kernel measures as empty.

The immutable reference audit is:

`/nas3/data/axeyum/autogenesis/reference-audits/a12d44858-lean430-nat-division-support-v1/manifest.json`

Its manifest SHA-256 is
`c462b234b64342bd4a43cf844c6aaaa05c9c13cc3ce3f2cc4a7a049d435f4c7f`.
The directory is mode `0555`; all five files are mode `0444`. The manifest
binds Lean 4.30.0, Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, lean4export commit
`a3e35a584f59b390667db7269cd37fca8575e4bf`, both streams, both audit reports,
and 719 imported declarations admitted across the two independent imports.
It records zero proof-search invocations and zero ledger writes.

## Exact composition evidence

The semantic diagnostic implementation is commit
`f099a4a37d58b0d976d73a564cb13245462c8b11`. The theorem-audit CLI is commit
`a12d44858124d26848f807d985e972637d4bd0d7`. The immutable composition
observation is:

`/nas3/data/axeyum/autogenesis/probes/f099a4a37-nat-div-mod-exec-mismatch-v15/observation.json`

| Artifact | SHA-256 |
|---|---|
| Mathlib r082 stream | `6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd` |
| Composition probe | `3d1eb42b583f60317fd6d9b5cea335c23e91a64d1d51f27aceebeb5f1c2f871a` |
| Composition API | `bfdc63a1ed7e1a9ee9f8d0de933ad654a3e951f5a6ea0e95ddcc4b84f17f2ad6` |
| Observation | `b7e467c0ef0cf6487f2476abfe4718172662c75ab8bd70215d5e59bf6468d025` |
| Rendered rejection string | `78f77e0ef5ee8fd7a6326a2bdee23c8a08efd9c69a9b53c8e01fecea0ffdb3e5` |

Two executions were byte-identical. The observation records 24 kernel
submissions, zero search invocations, zero ledger writes, and no displayed
proof bodies. Existing V5 receipts and their environment transitions are
unchanged; diagnostics do not alter admission authority.

## Validation and reproduction

The focused theorem-composition suite has 14 passing tests. The complete
importer all-target suite passes, including the official-Lean differential
run. Importer Clippy passes with warnings denied, and formatting is clean. The
tracked checker now rejects arena IDs, a changed semantic diagnostic, a changed
92-declaration closure, a changed direct-consumer split, mutable external
evidence, altered theorem identities, or any footprint other than the observed
`propext` result.

```sh
cargo test -p axeyum-lean-import theorem_composition --lib
cargo test -p axeyum-lean-import --all-targets
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings

cargo run -p axeyum-lean-import \
  --example lean4export_import -- \
  /path/to/export.ndjson Nat.dvd_mod_iff

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next bounded increment

1. State `Nat.dvd_mod_iff` against the imported target declarations, especially
   official `Nat.mod` and exact `Nat.dvd`.
2. Prefer a direct constructive proof using the target's already checked
   arithmetic lemmas; treat official proof dependencies as hints, not imports.
3. Submit the candidate to a fresh target kernel and require an empty axiom
   footprint.
4. Confirm the bridge actually removes the `Nat.div_mod_exec` dependency from
   the `Nat.dvd_gcd` composition path.
5. Replay `Nat.dvd_gcd` unchanged and let its next independent rejection choose
   the following bottom-up increment.
