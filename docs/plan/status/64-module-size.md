# Lane: agent-module-size — the emitted Lean module's size

<!-- plan-section: lane-status -->

**The shipped constructed-reals module halved, with what it proves unchanged
(`WIP`, agent-module-size, 2026-08-18).** Through
`examples/front_door_carrier --require-axiom-free` (exit status depends on the
finding, and it exits 0): strict-bound **2,623,005 -> 1,304,276 B**, three-row
2,673,154 -> 1,330,091, sos-square 2,551,806 -> 1,442,247. Carrier axioms still
0/0/0 against the `Real` control's 12/17/8, and the module's `axiom` lines still
equal `Kernel::axiom_footprint` (3/5/2). `scripts/check-lean-gate.sh`: **OK, 462
real-Lean checks under the pinned Lean 4.30.0, `lean_crosscheck` 77 of 77.**

**Bullet one of the brief was already done; bullet three is the real answer.**
`write_lean_module_impl` already opens with a constant-closure walk — the
`CReal` context holds **445** declarations and the module emits **280** blocks,
so selection has no headroom. The final theorem term is 4,193 bytes, 0.16% of
the module. The size is a hash-consed DAG printed as a *tree*: `CReal.mul_assoc`
is 1,296 kernel nodes and **324,609** printed ones.

**Why the existing compact writer saved 0.6%.** `compact_share_candidates`
requires `num_loose_bvars == 0` — a top-level `def` has no binder to read a
loose variable in, and a proof body is almost entirely open terms. Landed:
scope-aware `let` sharing (`ScopeId` = a hash chain over enclosing binder
occurrences; each `let` sits at the top of the innermost body whose binders the
term reads), and the front door switched to the compact writer.

**Raw-DAG sharing is unsound, so 19x is not the ceiling — 7.7x is** (193,197
scope-correct keys against 1,488,996 printed nodes). Achieved 2.01x in bytes: a
reference is overhead against ~3.7 bytes per node, which is why scoped names are
`_sN`. Naming alone was worth more than half the saving.

**A `let` chain is nested syntax** — 2,897 bindings in one lemma blew Lean's
default `maxRecDepth` of 512, so the banner now sets 65536 (elaborator counter
only; the kernel still checks every term).

**Next: a shared prelude, worth ~500x, not more sharing.** It changes the
single-file contract four Lean suites assume and needs an `.olean` build plus
`LEAN_PATH`. ADR-sized. Detail: `docs/plan/notes/64-module-size.md`.
