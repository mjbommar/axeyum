# Lean execution filesystem ownership decoupling — 2026-07-24

## Result

Lean's current execution and acceptance seals no longer depend on the
SMT-owned `scripts/smtcomp_repro/resume_fs.py` or its fixture worker. The
filesystem primitives used by Lean are vendored in
`scripts/lean_vendored_resume_fs.py`; Lean's interruption fixture is
`scripts/lean_resume_fs_fixture_worker.py`.

This closes the cross-lane source-identity defect where an ordinary SMT edit
invalidated Lean acceptance even though Lean behavior had not changed. It does
not add a Lean execution outcome, paired cell, complete population, complete
axis, terminal gate, or parity credit.

## Ownership boundary

The current Lean input sets now seal only Lean-owned implementation files:

| input | SHA-256 |
| --- | --- |
| `scripts/lean_vendored_resume_fs.py` | `a60e6d300f193c5f7ee8444573e84a35d145f65a79c444000a0f6e5bf1416a5e` |
| `scripts/lean_resume_fs_fixture_worker.py` | `858fd5fcc45022e5e704f9becda885d190f5384c7f851dd8f23a3409e295f54b` |
| `scripts/lean_execution_store.py` | `acf0fa7f30f8509b298968daa8a505f7cb0010274ce8a42b2fa070411105dc9a` |
| `scripts/lean_execution_acceptance.py` | `70b7f064e4d2a080fc6551b489cbca10081202b978fd8953d0332040037feada` |

`scripts/lean_execution_store.py` imports the vendored primitives directly and
uses ROOT-relative Lean script paths for both the primitive and worker. The
live acceptance and U2 repository-input maps exclude both
`scripts/smtcomp_repro/resume_fs.py` and
`scripts/smtcomp_repro/resume_contract.py`.

The retained TL0.7.4 and TL0.6.3 R3 result authorities still describe the
historical source bytes that actually produced those immutable records. Their
SMT-era input identities are selected only for the two exact historical
implementation revisions. New or synthetic authorities use the current
Lean-owned inputs. This preserves evidence provenance without keeping a live
cross-lane dependency.

## Verification

At integration commit `3c977f21`, the following clean-tree gate passed:

```sh
just parity-docs
```

The decisive independence probe copied the tree to
`/tmp/lean-verify.OSAzIu/source`, changed only
`scripts/smtcomp_repro/resume_fs.py` from SHA-256 `b05c3218...` to
`31a64b89...`, and then passed both:

```sh
python3 scripts/lean_execution_acceptance.py result --check
just parity-docs
```

The mutated run ended with `PARITY_DOCS` reporting `disagree=0` and
`public_inventory_wrong=0`. The Lean terminal report remained deliberately
unchanged at 0/10 complete populations, 0/12 complete axes, zero paired cells,
zero satisfied gates, and `terminal_ready=false`.

Focused regression coverage also passed 92 tests with one expected skip,
including all 16 worktree/tmpfs interruption cells and the retained R3 amended
authority check.

## Resume rule

Future Lean execution-store changes may update the Lean-owned vendored module
and its sealed hash together. Future SMT filesystem changes must not require a
Lean seal update. Re-run the mutated-SMT copy probe whenever the ownership
boundary or repository-input maps change.
