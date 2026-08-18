# Lane: agent-kernel-adversary — attacking the kernel with Lean's kernel

<!-- plan-section: lane-status -->

**Eight more kernel-vs-Lean violations found and fixed; the differential's 37%
blind spot is closed (`DONE`, agent-kernel-adversary, 2026-08-18).** Every
axiom-freedom claim in this repository is a claim about what a 5,254-line Rust
kernel accepts, so the only corroboration that is not circular is an independent
implementation refusing what we admit.
`crates/axeyum-lean-import/tests/real_lean_wire_differential.rs` is that attack:
identical `lean4export` bytes to our `import_ndjson` admission gates and to
official Lean 4.30.0's `addDeclCore`, with only "ours accepts + Lean rejects"
fatal. Measured against the pinned toolchain (`leanprover/lean4:v4.30.0`;
4.34.0-rc1 is also installed and was **not** used).

- **Widened from 5 mutation families to 51**, 92 mutants to 134 checked of 3,438
  generated. New: universe-level substitution (`succ`/`param`/`max`/`imax`
  operand, kind and swap), binder order (the only two-record mutation — a
  positional calculus's most exposed axis), binder info and body, `let`
  type/value/body and the type↔value swap, `proj` index/struct/type-name,
  `const` name/universe/universe-arity, de Bruijn shifts both ways, declaration
  `levelParams`, and the whole `inductive` record — family and constructor
  types, `cidx`, `numFields`, `numParams`, `numIndices`, `numNested`, `isRec`,
  recursor arities, the `k` flag and every ι-rule. Selection is stratified by
  family, not a stride, so a narrow family cannot be sampled away; a floor
  (`MIN_FAMILIES`) and an exhaustive family list make a family that stops
  generating fail rather than shrink a count.
- **Two defects, eight violations.** (1) *Universe closure*, 5 violations:
  `Kernel::check_declaration` ran only *relative* checks — the type infers to a
  `Sort`, the value's type is def-eq to it — and both hold with a free `u` on
  both sides, so a declaration's `levelParams` list was decorative. Lean refuses
  this categorically (`invalid reference to undefined universe level
  parameter`). The inductive gate needed the same check separately, because it
  type-checks its group itself and never routes through `check_declaration`;
  that was the one violation the first fix left behind. It sits in
  `add_inductive_group` (the gate), not its caller, so it is inside the trusted
  closure and cannot be reached around. (2) *The recursor `k` flag*, 3
  violations: our importer compared every other recursor field against the one
  this kernel generated and read `k` only to reject it on nested and mutual
  groups. `k` licenses ι-reducing a recursor application whose major premise is
  not a constructor, so it is not descriptive metadata.
- **The 32-mutant coverage gap is closed, not documented around.** The previous
  run printed 32 mutants as "ours declined, Lean accepted"; measured, all 32
  were **Lean accepting bytes it never read** — 225 of 603 expression records
  (37% of the stream) are reachable only from a recursor type or an ι-rule, and
  `addDeclCore` receives neither. `scripts/lean/replay-lean4export.lean` now
  looks every carried family, constructor and recursor up in the environment
  Lean just built and compares it field by field against Lean's own
  regeneration, falling back to `Kernel.isDefEqGuarded` so that our importer's
  `def_eq` criterion and Lean's agree (without that, a defeq-but-not-syntactic
  mutant would be reported as a violation it is not). That verdict is its own
  variant with its own liveness floor, so it can never be mistaken for
  `addDeclCore` speaking. `stricter_than_lean` fell **32 -> 1**, and the one
  survivor is explained rather than counted: `Or.inl` rewritten to `Or.inr`
  inside `Or.rec`'s type, which Lean closes by definitional proof irrelevance
  (its inference is unchecked, so it types the ill-typed side) and our `def_eq`
  declines — incompleteness, in the safe direction.
- **Every guard was killed to prove it guards.** Removing the
  `check_declaration` check kills exactly the two type/value tests; removing the
  `add_inductive_group` check kills exactly the constructor test; removing the
  `k` comparison kills exactly the `k` test. Neither universe guard masks the
  other, and each regression file carries a well-typed control that still passes
  — including "the logic prelude still builds", since a check that is slightly
  too strict would be a worse regression than the one being fixed.
- Trusted core moves **5,148 -> 5,254** function-body lines (246 of 1,018
  functions, ceiling 5,500); `scripts/check-kernel-trusted-core.py` green with 5
  guards, 0 failures.

**Next:** the `Or.rec` residue is the only unexplained-shaped thing left and is
now explained, but it points at a real difference — Lean's kernel infers types
in an unchecked mode inside proof irrelevance and ours does not. Worth deciding
deliberately rather than by omission. Beyond that: the development the mutator
damages is the logic prelude plus five declarations; running the same corpus
over the `nat`/`int` preludes would put `natVal` literals and deeper recursor
families on the wire, and `quot` records are still generated by nothing.

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | Kernel-vs-Lean differential widened to 51 mutation families; recursor/constructor regeneration compared against Lean's own, closing the 37% of the stream `addDeclCore` never reads; two defects fixed — universe closure on `check_declaration` **and** the inductive gate, and the recursor `k` flag validated on import |
