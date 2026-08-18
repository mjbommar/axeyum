# Lane: agent-module-size — the emitted Lean module's size

<!-- plan-section: lane-status -->

**The shipped constructed-reals module halved, with what it proves unchanged
(`WIP`, agent-module-size, 2026-08-18).** Front door, measured through
`examples/front_door_carrier --require-axiom-free` (exit status depends on the
finding): strict-bound **2,623,005 -> 1,303,499 B**, three-row 2,673,154 ->
1,329,314, sos-square 2,551,806 -> 1,441,470. `Real` control 8,898 -> 7,358 and
40,740 -> 21,770. Carrier axioms still 0/0/0 against 12/17/8, and the module's
`axiom` lines still equal `Kernel::axiom_footprint` (3/5/2).

**The first bullet of the brief was already done and the second is the real
number.** `write_lean_module_impl` already opens with a constant-closure walk:
the `CReal` context holds **445** declarations and the module emits **280**
blocks. So the selection layer has no headroom — what is emitted is cited. The
size is a hash-consed DAG printed as a *tree*: `CReal.mul_assoc` is 1,296
kernel nodes and **324,609** printed ones (250x); across all declaration values,
1,488,996 printed against 77,224 DAG nodes. The final theorem term is 4,193
bytes, 0.16% of the module.

**Why the existing compact writer saved 0.6%.** `compact_share_candidates`
requires `num_loose_bvars == 0`, because a top-level `def` has no binder to read
a loose variable in — and a proof body is almost entirely open terms. Landed:
scope-aware `let` sharing (`ScopeId` = a hash chain over enclosing binder
occurrences; a `let` is emitted at the top of the innermost body whose binders
the term reads), and the front door switched to the compact writer.

**Raw-DAG sharing is unsound, so 19x is not the ceiling — 7.7x is.** One node
under two different binders is two terms. Keyed by (node, binder chain) the
reachable floor is 193,197 keys, i.e. **7.7x** in nodes; 2.01x in bytes, because
a reference is overhead against ~3.7 bytes per printed node (which is why the
scoped names are `_sN`).

**Next: a shared prelude, worth ~500x, not more sharing.** Every module inlines
the same development; a Lean `import` of one emitted-once carrier module makes
the per-query module kilobytes. Out of scope here: it changes the
single-file contract that `lean_crosscheck` (77 families), `lean_module_fixtures`
and two more suites all assume, and needs an `.olean` build plus `LEAN_PATH`.
ADR-sized. Details: `docs/plan/notes/64-module-size.md`.
