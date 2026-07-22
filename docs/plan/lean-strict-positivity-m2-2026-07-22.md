# Lean strict positivity: M2 public matrix and generated-grammar result

Status: complete; M3 official/import boundary next

Date: 2026-07-22

Parents:

- [TL2.11 execution plan](lean-strict-positivity-tl2.11-plan-2026-07-22.md);
- [proposed ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md);
- [M1 trusted-preflight result](lean-strict-positivity-m1-2026-07-22.md).

## Result

M2 exercises the M1 checker only through the public
`Kernel::add_inductive` path. The new `strict_positivity` integration binary
contains a readable twelve-row contract matrix and a separate fixed-seed
structural grammar. It does not call private positivity helpers.

The twelve public rows cover:

- no occurrence and canonical direct recursion;
- one- and two-level positive `Pi` codomains;
- canonical recursive-indexed occurrence;
- negative-domain, mixed-polarity, and deep-negative shapes;
- wrong fixed parameter, foreign-head nesting, family occurrence in an index,
  and wrong index arity.

The rows span `Prop` and `Type`, zero/one parameter, zero/one index, first and
later failing fields, and first/later constructors. Every non-admission checks
the exact typed payload and exact ordered environment equality after failure.
Direct recursion still admits; valid positive recursive-indexed and reflexive
forms still stop at their existing feature declines.

## Generated grammar

The deterministic grammar uses seed `4158505354524943`, exhausts its declared
profile/sort/production/depth/field-position corners, and uses the fixed-seed
stream for constructor-order variations. Expectations are assigned from each
production before invoking the kernel. Reducible `let` and positive `Pi`
contexts exercise WHNF traversal; foreign application, negative domains,
wrong parameters/arity, and self-indices exercise the two rejection classes.

Each complete run produces 840 identity-unique public-family cases:

```text
schema=axeyum-lean-strict-positivity-grammar-v1
seed=4158505354524943
cases=840
outcomes=admit:174,recursive-indexed:42,reflexive:144,non-positive:270,invalid:210
profiles=0p0i:240,1p0i:270,1p1i:330
sorts=prop:420,type:420
depths=0:168,1:168,2:168,3:168,4:168
descriptor-fnv1a64=02985687422aa0ff
```

The test runs the complete grammar twice, compares the serialized bytes, and
then compares them with this compiled-in frozen summary. Duplicate identities,
missing outcome/profile/sort/depth classes, population shrinkage below 256, or
descriptor drift fail the test.

One useful product-boundary observation is explicit rather than hidden:
positivity WHNFs a reducible `let` around a canonical family application, but
the later, deliberately narrower recursive-field classifier still returns the
existing reflexive feature decline for that raw field. This is not a positivity
rejection and does not widen admission; TL2.12 owns that later semantics.

## Bounded gates

All Rust commands used two build jobs and the 4 GiB wrapper:

```text
cargo test -p axeyum-lean-kernel --test strict_positivity
  -> 2 passed; 0 failed

cargo test -p axeyum-lean-kernel
  -> 182 unit tests and every integration binary passed
  -> final doctest link hit the known /tmp LLD bus-error boundary

TMPDIR=$PWD/target/tl211-tmp cargo test -p axeyum-lean-kernel --doc
  -> 1 passed; 0 failed

cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings
  -> pass

TMPDIR=$PWD/target/tl211-tmp RUSTDOCFLAGS='-D warnings' \
  cargo doc -p axeyum-lean-kernel --no-deps
  -> pass
```

The isolated doctest rerun changes only temporary linker placement; it uses the
same source, toolchain, package, and memory cap. Focused rustfmt and
`git diff --check` pass.

## Remaining gates

M2 does not accept ADR-0352 or complete TL2.11/T6.0.2. M3 must now:

1. execute every immutable official source twice with pinned Lean 4.30 under
   the registered one-worker/4 GiB policy;
2. add a mandatory official differential that fails closed when Lean is
   required but absent;
3. exercise importer propagation with a clearly synthetic, type-correct wire
   mutation if the format permits it without conflating source and wire credit;
4. rerun the immutable official construct-matrix control and prove no product
   outcome drift.

Only M4 may accept the ADR, close the research question, and mark TL2.11 and
T6.0.2 complete.
