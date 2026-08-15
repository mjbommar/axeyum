# Lane: quant-pins — the three quantified-LIA golden pins, and the gate that did not exist

<!-- plan-section: lane-status -->

**Green then broken, and the breaking commit is `0fc7cc357` (`WIP`, quant-pins,
2026-08-15).** Three golden-module suites were red on `main`:
`quant_affine_growth_lean`, `quant_residue_lean`, `quant_eq_partition_lean`.
Each pins `(source.len(), fnv1a)` of a reconstructed Lean module.

**The bisect, by measurement, not attribution.** The failure was first attributed
to `d326c74af`, then observed to fail at `a0cf53d66`, `2c30bd453` and
`82244b43c` too, which raised a reasonable "these pins were never green" — the
file was introduced by `a9b90777c`, whose subject is *"rescue: preserve
uncommitted quantified-reasoning worktree"*. That hypothesis is **refuted**. All
three pins were last set by `b4604bae7`, and on a `git archive`
snapshot of `b4604bae7` all three suites pass (4 / 6 / 3 tests, 0 failed). On a
snapshot of `0fc7cc357` all three fail. In the whole range
`b4604bae7..82244b43c`, **exactly one commit touches any `crates/*/src/` file**
and it is `0fc7cc357`, which touches only `int_prelude`.

| commit | affine growth | residue | eq partition |
|---|---|---|---|
| `b4604bae7` | ok 4/4 | ok 6/6 | ok 3/3 |
| `0fc7cc357` | 79_801 → **174_524** | 33_339 → **83_060** | 51_989 → **112_303** |

**What was actually wrong: nothing in the producer.** `0fc7cc357`
(`integer: axiom=6 → 1`) turned `Int.add_assoc`, `Int.mul_assoc`,
`Int.left_distrib`, `Int.add_le_add` and `Int.add_lt_add_of_le_of_lt` from
asserted axioms into theorems. A reconstructed module emits its *reachable*
declarations, so an axiom that cost one line now costs its whole proof term.
**Fewer axioms, more bytes.** The modules are better than the ones the pins
described.

**Why it shipped.** `0fc7cc357` did re-pin the one golden module it knew about,
`diophantine_lean_reconstruct` — and that is the one that is listed in
`scripts/check-lean-gate.sh`. The three that moved silently are in **no gate**:
not in the Lean gate, and not in the lane's own
`cargo test -p axeyum-lean-kernel`. Only `cargo test --workspace --all-features`
(so `./scripts/check.sh`, `just check`) compiles them at all.

**The prose guard.** Each of the three pins carried a comment reading, in words,
*"Checked, not merely stable — Lean 4.30.0 accepts this module, `#print axioms`
reports only ledger axioms and the query hypotheses, and there is no
`sorryAx`."* Nothing in the tree checked that. It is
[`04-gates-and-truth.md`](../../refactor-2026-08/04-gates-and-truth.md)'s
prose-guard class exactly: a guard that exists in a comment. The byte pin was
the only executable content, and a byte pin says nothing about validity.

**Fix.** Three families registered in `lean_crosscheck.rs`
(`quantified_lia_euclidean_residue`, `quantified_lia_affine_growth`,
`quantified_lia_equality_partition`), which *is* in `check-lean-gate.sh`. Real
Lean 4.30.0 now reads exactly the modules those pins cover — the representative
slice went **70 → 73 families, 73 of 73 checked, 0 failed** — and each `#print
axioms axeyum_refutation` was read, not assumed:

- affine growth → `[Int.euclidean_decomposition, dio.hyp._14, dio.x._0 … x._3]`
- residue (clock-3) → `[Int.euclidean_decomposition, dio.hyp._3, dio.x._0]`
- equality partition → `[dio.hyp._97]` — the query hypothesis alone, no ledger axiom

Only then were the three constants re-pinned, from the value the failing test
printed. That is why this is a re-pin and not a relaxed pin: the module on the
other side of the new constant has been read by an external Lean-grade kernel.

**Unrelated red found while sweeping, not mine.**
`deadline_honored::wide_aufbv_division_honors_config_timeout` fails under load
(it asserts an oversized row is refused *before* lowering and instead gets
`Unknown(Timeout)` from application discovery) — a budget test measuring a
loaded machine, the same reference-frame problem as the frontier ratchet. Worth
a lane; it is not a golden-pin issue.

**Next.** `Int.euclidean_decomposition` is the last integer axiom, and
`int-remainder` names it as its next target. When it is discharged these three
modules move again — but now they will move against a Lean-checked baseline
instead of a comment.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `6389e0194` | Three quantified-LIA golden pins repaired at their real cause (`0fc7cc357`, `integer: axiom=6 → 1`, grew the emitted proof terms), and the acceptance claim their comments made was turned into three real-Lean `lean_crosscheck` families: 70 → 73 modules, 73 of 73 checked by Lean 4.30.0. |
