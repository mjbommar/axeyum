# 02 — The components are adjacent, not composed

**The finding.** axeyum's pitch is an SMT solver, a computer-algebra system, a
Lean-compatible kernel and a proved library in one Rust process with no C
dependency. That is accurate as an inventory. It is not yet accurate as an
*architecture*: the pieces sit beside each other and rebuild, duplicate, or
ignore one another at the seams.

If the product is the integration, then the seams **are** the product.

## Three measured instances

### C1 — Two real-algebra engines

```
crates/axeyum-solver/src/nra_real_root.rs   7,684 lines
crates/axeyum-cas/src/sturm.rs                303 lines
```

Sturm sequences, real algebraic numbers and interval arithmetic exist **twice**,
with different caps, no shared tests, and no awareness of each other. The larger
implementation is in the solver and is materially stronger; a bridge that routed
the solver at the CAS version would have been a **downgrade**, which is what the
lane tasked with building that bridge discovered by measuring first.

Related and unfixed: `interval_arith::abs()` can **panic** where every sibling
returns `None`.

The genuine gap turned out to be narrow and elsewhere — `ideal_contains`
returned `Option<bool>`, and *a bare bool is not evidence* under ADR-0386's own
standard. That is the shape to expect: where two implementations exist, the real
defect is usually in neither, but in what neither of them produces.

### C2 — Two colouring encoders, and a gate that does not exist

```
crates/axeyum-search/src/colouring.rs    633 lines
crates/axeyum-cnf/src/colouring.rs     1,354 lines
```

`crates/axeyum-search/src/colouring.rs:10` states:

> `tests/encoding_parity.rs` compares them directly.

`crates/axeyum-search/tests/` contains `offdiag_schur.rs` and `vdw.rs`. **There
is no `encoding_parity.rs`.** Two encoders for the same object, a comment
asserting they are compared, and nothing comparing them — in a crate whose
entire output is claims about which formulas are unsatisfiable.

### C3 — The Lean kernel is rebuilt from scratch on every query

```
build_nat_prelude on a fresh Kernel      ~26 ms
revalidate a cached package, same Kernel   6.6 µs        ≈ 4,000×
```

Six reconstruction routes each call `Kernel::new()` per query —
`reconstruct.rs:375`, `int_reconstruct.rs:168`, `lex_reconstruct.rs:179`,
`regex_reconstruct.rs:231`, `word_reconstruct.rs:273`,
`reconstruct/arithmetic.rs:173`. For queries that themselves take single-digit
milliseconds, **prelude construction dominates the evidence path**.

And the cost is not static. `nat_prelude.rs` grew **3,856 → 9,969 lines in 60
commits in one session**. So:

> **Every theorem the library gains makes every evidence-producing query
> slower**, because the library and the evidence path share a data structure
> they rebuild instead of sharing.

That is a compounding tax on exactly what [`01`](01-int-real-keystone.md) is
trying to grow, and it worsens the moment `Int` is built on proved `Nat`.

## The work

### W1 — Kernel reuse, with the safety mechanism first

Reuse is only sound with two things that a peer session has already built and
tested:

- a monotone `revision: u64` on `Environment`, bumped on **every** mutation
  including the replacement path in `insert_unchecked`. The whnf cache was keyed
  on `env.len()` — a *count*, which cannot see an in-place replacement and
  repeats across a rollback, so a stale entry can be revived by a later
  environment reaching the same size. Unreachable through today's trusted gates;
  the point is that the cache should not depend on that argument holding for
  every future caller of an explicitly untrusted insert.
- **rollback eviction**, so a reused kernel cannot hand back handles into
  rolled-back declarations. Verified by removing the eviction line and watching
  the test fail, then restoring it — a negative control exercised rather than
  asserted.

With those in place, converting the six call sites is mechanical.

### W2 — One real-algebra engine

Decide which implementation is canonical (the measurement says the solver's),
give it one set of caps, and give the two a shared test corpus. Fix the
`interval_arith::abs()` panic on the way — a function that panics where its
siblings decline is a decline route that cannot be used from a `unknown`-first
API.

### W3 — One colouring encoder, and the parity gate the comment promises

Collapse `axeyum-search`'s copy onto `axeyum_cnf::colouring`, or write
`tests/encoding_parity.rs` and make the comment true. **Do not leave a third
state where the comment is deleted and the duplication remains** — that trades a
visible defect for an invisible one.

### W4 — Name the composition boundaries in the dependency contract

[`foundational-dag.md`](../research/08-planning/foundational-dag.md) already
specifies which mathematical contracts must exist before a layer may depend on
another. It does not yet say **which component owns a capability**, which is how
two Sturms and two colouring encoders came to exist without anyone deciding.
Add ownership to the contract: one capability, one owner, and a cross-crate
duplicate is a contract violation rather than an accident someone notices later.

## The test for whether this landed

Not a benchmark. **A change in one component that is felt correctly by another
without anyone wiring it.** The campaign produced exactly one such moment: a
modelling-layer extension for per-colour constraints propagated through the
encoder, the local-search predicate and the independent verifier, and **caught a
wrong `unsat`** that every downstream tool would otherwise have certified —
because the proof would have been a valid proof of the wrong formula.

That is what composition buys, and it is currently an accident rather than a
property.
