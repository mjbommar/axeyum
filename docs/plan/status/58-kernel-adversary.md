# Lane: agent-kernel-adversary — attacking the kernel with Lean's kernel

<!-- plan-section: lane-status -->

**Round 3: a fourth kernel-vs-Lean defect found and fixed, and the corpus
widened from 51 families to 66 over a development that finally carries the
constructs the kernel works hardest on (`DONE`, agent-kernel-adversary-2,
2026-08-18).** Rounds 1 and 2 damaged a `Prop`-only development, so 51 families
were rewiring the same handful of record shapes. Round 3 put a Type-valued
STRUCTURE (with a theorem provable only by structure eta), a `Nat` LITERAL (with
a theorem provable only by literal/constructor conversion), an INDEXED family, a
PARAMETERIZED recursive family, a MUTUAL group, an `axiom`, an `opaque` and the
`abbrev`/`opaque` reducibility hints on the wire, and added 15 families for
fields nothing had ever damaged: `levelParams` and `all` on families,
constructors and recursors; universe-parameter PERMUTATION at the binding site
and at the `Const` reference; a short universe-argument list; ι-rule right-hand
sides exchanged between rules of one recursor, and the rules permuted.

- **2 violations in 126 mutants across 66 families**, one defect reached two
  ways (`True.rec`, `Acc.rec`): **a recursor's `levelParams` was decorative.**
  `ind.rec-uparams` renames the motive universe parameter at the binding site,
  leaving the type and every ι-rule mentioning the old name, now free. Lean's
  kernel generated `Sort uparam.0` where the stream said `Sort u`; we admitted
  it. Round 2's universe-closure check in `Kernel::check_declaration` could not
  have caught it — a recursor is *generated* here and then compared, never
  admitted from the stream, so the kernel is never handed the exported binding
  list — and the comparison alpha-renames the exported parameters onto the
  generated ones **positionally**, so a parameter the exported list does not
  bind is not in the map, passes through untouched, and `def_eq` (which treats
  an unbound `Param` exactly like a bound one) accepts it. Fixed in
  `validate_generated_recursor` / `validate_rec_rules`; regression
  `crates/axeyum-lean-import/tests/recursor_universe_params_must_be_bound.rs`.
- **The new guard masked an older one, and that was caught by killing it.**
  Running the closure check before `recursor_universe_substitution` made a
  TRUNCATED `levelParams` report "unbound universe parameter" instead of
  "universe-parameter arity differs", silently taking over the case
  `official_nested_inductive_groups::recursor_metadata_mutations_reject_exactly`
  pins. Reordered. Final controls: removing the type check kills exactly one
  test, removing the ι-rule check kills exactly one *different* test, and no
  other test in the crate moves either way.
- **The instrument's reach is the binding constraint, and it is now measured.**
  With the fix reverted, a 66-mutant sweep (one per family) passes clean and a
  126-mutant sweep finds the defect twice — so a clean round is evidence in
  proportion to its budget. Default budget raised 144 -> 396 (134 -> 299 checked,
  290 s); cost is 0.98 s/mutant, all of it the `lean --run` subprocess, so the
  full 4,747-mutant corpus is ~80 minutes (`AXEYUM_WIRE_MUTANTS=99999`).
  `MIN_MUTANTS` (a ratchet on the GENERATOR, independent of budget) raised
  24 -> 3,600, since a floor of 24 against 4,747 would not notice 99% of the
  corpus disappearing.
- **Two axes named as unreachable rather than faked.** A NESTED group cannot be
  compared through this instrument: `addDeclCore` regenerates the group's own
  recursor but not the auxiliary one the frontend publishes (measured — the
  undamaged stream failed on `axeyum_wire_rose.rec_1`), so every field of an
  auxiliary recursor is a byte Lean never reads. Admitting it would have meant a
  false failure or an exemption that restores the 37% blind spot, so the group
  is off the wire and `restore_nested_inductive_group` — the fourth admission
  gate — has **no adversarial coverage**. And `quot` records cannot
  discriminate at all: `addDeclCore` ignores a quotient package's carried types
  and adds its own, so it accepts every damaged quotient record.

<details><summary>Round 2 (agent-kernel-adversary, 2026-08-18)</summary>

**Eight kernel-vs-Lean violations found and fixed; the differential's 37%
blind spot is closed.** Every
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

</details>

**Next (round 4).** Three named places, in order of expected yield. (1) The
`nat`/`int`/`rat`/`string` preludes as the development: round 3 put ONE `Nat`
literal on the wire and the literal arithmetic table (`nat_binop_table`, sixteen
name-and-shape lookups keyed by the environment's own declarations) is still
never exercised adversarially. (2) The `Or.rec` residue — Lean's kernel infers
types in an unchecked mode inside proof irrelevance and ours does not; that is a
real difference and should be decided deliberately rather than by omission.
(3) The nested gate, which needs a *different* instrument than this one: a
kernel-vs-kernel comparison that replays Lean's own frontend expansion, since
`addDeclCore` alone provably cannot see the auxiliary recursor.

<!-- plan-section: landed-changes -->

| 2026-08-18 | (this change) | Round 3: corpus widened 51 -> 66 mutation families over a development that now carries a Type-valued structure, a `Nat` literal, an indexed family, a parameterized family and a mutual group; a fourth defect found and fixed — a **recursor's** `levelParams` was decorative, because a recursor is generated and compared rather than admitted, and the comparison's positional alpha-rename leaves an unbound parameter untouched |
| 2026-08-18 | `2633d7186` | Kernel-vs-Lean differential widened to 51 mutation families; recursor/constructor regeneration compared against Lean's own, closing the 37% of the stream `addDeclCore` never reads; two defects fixed — universe closure on `check_declaration` **and** the inductive gate, and the recursor `k` flag validated on import |
