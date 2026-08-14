# agent-h FEEDBACK — roadmap feedback for axeyum itself

Cited by file and line. Every claim below is a measurement made this session;
the raw output is in `logs/`.

---

## F-H1 (P0, tooling) — `cargo fmt` is blind to 221,445 lines of `axeyum-solver`, including the whole trusted reconstruction layer

`crates/axeyum-solver/src/lib.rs:56` opens `macro_rules! full_modules`, and
**156 `mod` declarations live inside its expansion body** — among them
`mod reconstruct;` (`lib.rs:183`), the entire Lean proof-reconstruction tree.
rustfmt does not expand macros, so it never visits those files.

Reproduced, not inferred:

```
$ printf '\nfn __fmt_probe(  ) ->    usize {   let    x=1  ;  x  }\n' \
    >> crates/axeyum-solver/src/reconstruct/resolution.rs
$ cargo fmt -p axeyum-solver -- --check
$ echo $?
0
```

Exit 0, no output, on code no formatter would accept. Counted by walking the
macro body and summing the files it names: **156 modules, 221,445 lines** that
`cargo fmt --all --check` — the documented gate in `CLAUDE.md` and a CI job —
does not read.

This is the same shape as the corpus gate that ran zero tests for 15 days: an
exit status standing in for a measurement. Two consequences worth acting on:

1. The gate should assert the file set it formatted is the file set on disk
   (`cargo fmt -- --check` plus a `find crates -name '*.rs'` reconciliation), so
   a module that leaves the gate's view is a build failure rather than silence.
2. `CLAUDE.md`'s multi-agent rule "format single files with
   `rustfmt --edition 2024 <file>`" is not equivalent to the gate. Run on
   `reconstruct.rs`, it also rewrote **five sibling modules I had not touched**
   (`arithmetic.rs`, `bitblast.rs`, `cnf.rs`, `direct.rs`, `quantifier.rs`) —
   because rustfmt *does* follow `mod` declarations when the file is its own
   root. In a shared checkout that is a clobber waiting to happen. I reverted
   all five and kept only the files I own.

## F-H2 (P1, docs/roadmap) — `DP_POOL_BUDGET` is documented as the reconstruction ceiling and is not on the path

`NEXT-MATH-STACK.md` item 1 names the failure at
`crates/axeyum-solver/src/reconstruct/resolution.rs:1315`
("Davis–Putnam working set exceeded 4096 clauses") as the thing to fix. It
guards `reconstruct_resolution_step_dp` (`resolution.rs:1241` at `f19282dc`,
`:1535` after `1b2b13c70`), which is the **third** fallback in
`reconstruct_resolution_step` (`:428` / `:746`):

1. `reconstruct_ordered_rup_step` (`:467` / `:785`) — replays the LRAT hint
   order. This is what proofs from our own
   `solve_with_drat_proof` -> `elaborate_drat_to_lrat*` -> `lrat_to_alethe`
   pipeline take.
2. `reconstruct_rup_closure_step` (`:1091` / `:1385`).
3. `reconstruct_resolution_step_dp` — DP, the only user of the budget.

Across 22 Rado instances from 85 to 4.57 million LRAT hints — all completed —
**the DP fallback was never entered**. The real bound is the kernel expression arena, measured at
**~90-100 bytes of RSS per interned node**, with the inlined route consuming
**~190-400 nodes per LRAT hint** (rising with clause width). A lane sent at the
DP budget would have spent its session on a guard that does not fire.

Worth fixing in the roadmap text, because the same mis-citation would send the
next lane the same way.

## F-H3 (P1, architecture) — the bit-blast lane's compaction machinery never reached the SAT lane

Everything the clausal front door needed already existed in
`crates/axeyum-solver/src/reconstruct/bitblast.rs`:

- backward slicing from the empty clause (`bitblast.rs:1505-1533`),
- CPS clause encoding and `construct_cps_rup_from_trace`
  (`resolution.rs:800` at `f19282dc`, `:1106` after), which builds a whole RUP
  chain once instead of folding `k` materialised binary resolvents,
- `ctx.closed_aliases.cps_clauses` (`reconstruct.rs:219`, `bitblast.rs:1638`),
  which admits each clause as a closed `Declaration::Theorem`.

`reconstruct_resolution_proof` (`resolution.rs:318` / `:424`) used none of it, and it is
the route the doc comment calls "the clausal-layer foundation shared by all
clausal proofs (`QF_BV`, SAT)". Wiring it up (this session's
`reconstruct_resolution_proof_compact`) bought **5.6x fewer expression nodes and
55x less wall time at n=141**, with the ratios still rising at the top of the
measured range.

The general lesson: `ClosedAliasMode` is set in exactly one file
(`quant_bv_instance_set_lean.rs:3689`) and read in one other. A capability with
one caller is a capability the rest of the system does not know it has. It
should be a documented reconstruction *mode* on `ReconstructCtx`, not a private
bool two routes happen to flip.

## F-H4 (P1, kernel) — the arena has no release path, and that is now the binding constraint

`Kernel` (`crates/axeyum-lean-kernel/src/lib.rs:247`) holds `exprs`,
`expr_meta`, `expr_intern` as monotone `SegmentedVec`s. Nothing is ever freed.
With the compact route, each learned clause becomes a closed
`Declaration::Theorem` whose body is **complete and never referenced structurally
again** — downstream terms hold a single `Const`. That declaration is exactly the
unit that could be serialised and dropped, which is what would make proof size
bounded by disk rather than by RAM.

Measured stakes, on two instances a factor of two apart:
`r4-a3-b1/F_81` cost **11.6 GB** (2.16M hints, 16.2 min) and `r4-a1-b1/F_45`
**24.6 GB** (4.57M hints, 32.4 min) — **linear in hint count to within 6%**, at
~80 B/node and ~72-76 nodes/hint. The 741 cover's average cube is comparable in
size to these, and there are 6,241 of them; they cannot share an arena and cannot
be checkpointed out of one.

I did not make this change: `axeyum-lean-kernel` is off-limits this session (an
unreachable codex CLI session holds uncommitted WIP there). Reporting it as the
next step, with the shape it wants:

- a checkpoint API that serialises admitted `Declaration::Theorem`s to a spool
  and truncates the arena behind them, keeping only the declaration *types*
  in the environment;
- `write_lean_module_compact_with_inductives`
  (`crates/axeyum-lean-kernel/src/lean_pp.rs:273`) already streams the rendered
  module to an `io::Write`, so the *output* side is solved for **memory** — only
  the working arena is not.

**But the render has a throughput wall of its own, and it is the next one.**
Measured on `r4-a3-b1/F_81`: the module streamed out at **160,366 B/s**
(10,457,470 -> 20,079,452 bytes over exactly 60 s, `DIARY.md`). At that rate a
proof the size of `r4-a1-b1/F_45` — 346M arena nodes, ~1.7 GB of rendered Lean —
takes about **three hours to write**, after a 32-minute reconstruction. Two
consequences:

1. Certificate emission needs its own throughput work, not just its own memory
   story. 160 KB/s is slow enough that it dominates the pipeline at r4 scale.
2. It may not be worth doing at that scale at all: Lean needs ~190x a module's
   size in RAM (measured 3.85 GB for 20.7 MB), so a 1.7 GB module implies
   **~320 GB** to check. Above roughly 100k hints the useful artefact is the
   kernel-checked reconstruction, not a Lean module nobody can check. A
   size-aware policy — render below a threshold, report the in-tree kernel
   verdict above it — would be more honest than emitting an uncheckable file.

## F-H5 (P2, evidence) — `False` is not a statement, and nothing was checking what it was proved from

Both reconstruction routes end at a kernel-checked `False`. That gate cannot
distinguish "refuted this CNF" from "refuted something else", because the
hypotheses are opaque `Axiom`s the reconstruction declared itself. A
reconstruction that mis-encoded a clause would produce a perfectly well-typed
`False` from a formula that is not the problem.

`declared_assumption_clauses` (new, `resolution.rs`) decodes each `assume`-role
axiom back out of its `Prop` encoding into `±atom` keys so a caller can require
that every hypothesis is an actual clause of the source CNF. Across 22 completed
instances the answer was **zero alien axioms** (both routes on the 9 where the
inlined route finishes; compact on all 22, up to the 4.57M-hint `r4-a1-b1/F_45`) — the encoding is right — but
that is now a *measured* fact rather than an assumed one, and the check costs
nothing.

Recommendation: make the footprint audit part of every emitted certificate, not
an optional probe. A `#print axioms` list is only meaningful next to a statement
of what those axioms are supposed to be.

**The emitted Lean module has the same gap, and it is worse there.** A third
party reading `artifacts/lean-certs/*.lean` sees `axiom axeyum.reconstruct.prop._3 : Prop`
and `axiom axeyum.reconstruct.hyp._4 : Or prop._3 (Or prop._2 prop._1)`. Nothing
ties `prop._3` to DIMACS variable `v37` or `hyp._4` to line 12 of `F_141.cnf`.
Lean's acceptance is therefore evidence that *some* clause set is unsatisfiable,
not that *this CNF* is. Tamper controls confirm the binding is tight
(weakening, relabelling, or even permuting one hypothesis clause is rejected —
`DIARY.md`), but the mapping itself is missing from the artefact. The fix is a
generated comment block, or better a checked-in sidecar, giving
`prop._N -> v_k` and `hyp._M -> <clause>` so the certificate is self-describing.

## F-H6 (P2, ledger) — the committed Rado certificates carry DRAT but not Lean

`artifacts/claims/rado/*/` ships `F_n.cnf`, `F_n.drat.gz`, `witness.txt`,
`claim.json`. There is no Lean certificate, and as of this session there can be
one for every `r3` instance in the ledger (18 checked, `n` up to 286) and for
`r4` up to at least `n = 56`, at a cost of seconds and a few MB gzipped. The
axiom footprint is *strictly smaller* than the published competitor's
(no `propext`, no `Classical.choice`, no `Quot.sound`, no `em`), which is a
claim worth making in the ledger where a referee will see it.
