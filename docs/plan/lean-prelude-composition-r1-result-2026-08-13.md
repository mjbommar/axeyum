# Lean prelude composition R1 result

Date: 2026-08-13

Status: **complete locally; publication and hosted CI are recorded separately**

Authority: [Lean kernel requirements](lean-kernel-requirements-2026-08-13.md),
R1; [ADR-0387](../research/09-decisions/adr-0387-fallible-composable-lean-preludes.md).

## Result

R1 / TL3.3 is implemented. Logic, Nat, axiomatized Int, axiomatized Real, and
multiple finite string alphabets now compose in one `Kernel`. Every public
prelude builder returns `Result`, registers an exact declaration snapshot, and
uses a whole-package environment checkpoint. A failed invocation removes its
new declarations and clears environment-sensitive inference caches. A repeat
validates the snapshot and returns the original handles without changing the
environment.

Theory identities are now unambiguous:

- natural-number library declarations remain under `Nat.*`;
- the integer carrier is `Int` and its 33 remaining assumptions are `Int.*`;
- the real carrier is `Real` and its 29 remaining assumptions are `Real.*`;
- a string alphabet of size `n` uses `axeyum.string.n.*`.

The runtime-derived ledger remains 65 assumptions: 34 integer, 30 real, and
one string `append`. Its reviewed semantic classifications were preserved
while every name, rendered canonical type, and SHA-256 identity was regenerated
from the actual kernel environment. The former 28-name Int/Real collision set
is now empty.

## Executable controls

`prelude_composition.rs` builds logic + Nat + Int + Real + string alphabets of
sizes two and three in one kernel. It infers representative `Nat.add`,
`Int.add`, and `Real.add` applications; checks a proof of a conjunction holding
both a Nat equality and an Int equality; repeats every package and checks equal
handles plus unchanged environment length.

The negative control pre-populates `Int.eq_em`, the final integer-package
member, with a wrong but well-formed declaration. Construction reaches that
late collision, returns an error, and leaves the entire pre-call environment
byte-for-byte equal: the conflicting declaration remains, while the attempted
`Int` carrier and every earlier package member are absent.

## Local evidence

The following completed with exit zero and nonzero tests where applicable:

```text
cargo test -p axeyum-lean-kernel
  includes prelude_composition: 2 passed
  includes rado_shell_arithmetic: 9 passed

cargo test -p axeyum-solver --features full
  library: 1121 passed; 0 failed
  all enabled integration tests and doctests passed; documented heavy gates ignored

cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings
cargo clippy -p axeyum-solver --all-targets --features full -- -D warnings

python3 scripts/gen-lean-axiom-ledger.py --check
  total=65; real=30; integer=34; string=1; unclassified=0

python3 -m unittest scripts.tests.test_lean_axiom_ledger
  7 passed

python3 scripts/check-parity-docs.py
just foundational-resources
just plan-authority links
```

The R1.3 source search finds only two bounded integer conversions in
`prelude.rs`; neither consumes a trusted-gate `Result`. No builder converts a
kernel rejection into `expect` or panic.

## Mathematical-research consequence and boundary

The Rado rigidity proof uses natural shell indices and signed defects
simultaneously. R1 removes the infrastructure defect that prevented an honest
direct ℕ+ℤ encoding of that argument. It deliberately does **not** select the
signed-Int encoding over the zero-axiom natural-deficit alternative, discharge
the integer package's 34 assumptions, formalize `thm:rigid`, or upgrade the
paper's current 14-theorem syntax export to an official-Lean check. Those remain
R2/R4/R7 decisions and evidence obligations.
