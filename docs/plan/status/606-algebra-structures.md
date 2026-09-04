# Lane: algebra-structures — polynomial rings, modules and subgroups over the `AlgS` spine (W2-9, W3-2, W1-11)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, algebra-structures, 2026-09-04).** All three of
the algebra shelves ADR-1595 unblocked were built and landed: **58
declarations, every one with an empty `Kernel::axiom_footprint`, at a total
cost of ONE kernel rejection** (a Rust-side `Nat.rec` universe slip, not a
mathematical obstruction). Designs, the setoid cost construction by
construction, and every stopping point are in
[ADR-1609](../../research/09-decisions/adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md).

- **W2-9 — `AlgS.Poly.*`, 15 declarations.** A polynomial is a coefficient
  function `Nat -> R.carrier`; `AlgS.Poly.commGroup` is the full 16-field
  additive `AlgS.CommGroup` of `R[X]` over an abstract `AlgS.CommRing`.
  Convolution is an antidiagonal walk (no `Nat.sub` exists at that build
  position), and `antidiagFrom_congr`/`antidiagFrom_add` discharge `mulCongr`,
  `distribL` and `distribR`. **Not** a `CommRing` instance: `mulOneL`/`mulOneR`,
  `mulComm` and `mulAssoc` each need a reindexing lemma for the walk — the same
  lemmas `rat_prelude/diagonal.rs` is still missing concretely over ℚ, and none
  of which `Quot.sound` would supply.
- **W3-2 — `AlgS.Module.*`, 23 declarations.** `IsModule` as a five-fold `And`
  with five accessors; `smul_zero`, `zero_smul`, `neg_smul`; `AlgS.idem_eq_e`;
  the instances `selfModule` (`R` over itself) and **`polyModule` (`R[X]` over
  `R`)**; and a basis layer (`linComb`, `coeffAgree`, `spans`,
  `linearIndependent`, `isBasis`, `linComb_congr`). **Dimension is blocked on
  `AlgS.Field`, which needs `Apart`** — a separate open question ADR-1595 named,
  unrelated to quotients. A module RECORD is blocked on a different thing again:
  `FieldSpec` fixes one universe per `FieldKind`, so no record can hold another
  record; ADR-1609 sizes that change to `structures.rs`.
- **W1-11 (subobject half) — `AlgS.Subgroup.*`, 20 declarations.** `IsSub`,
  `le`/`inter`/`top`/`bot`, the bounded meet-semilattice laws, closure of
  `IsSub` under all three constructions, and **`ker_isSub`**, which joins this
  half to the `AlgS.Hom.firstIso` half. The JOIN is absent: it needs a word
  closure (a parameterized inductive over `G.carrier`), sized in ADR-1609.

**The finding for ADR-1595, and it runs in the ADR's favour.** ADR-1595 priced
the setoid route at three lines on a theorem the `Eq` route could also have
done. Here the `Eq` route **cannot state the polynomial ring at all**:
`Alg.CommGroup`'s law fields are literal `Eq`, so `comm` for polynomials would
be an equality of two lambdas — `funext`, which the kernel does not have and
`Quot.sound` does not supply. Every construction whose carrier is a function
space is reachable only over the setoid spine. The measured tax elsewhere is
one field per structure (`AlgS.Module.smulCongrP`, `AlgS.Subgroup.IsSub`'s
`respects`), each discharged in one application at every instance, and
`respects` is load-bearing rather than bureaucratic (a kernel-read test refuses
`bot_le` without it).

**Next for whoever picks this up**, in order: (1) move `AlgS.Poly` to a build
position after `Nat` arithmetic and restate the walk as
`sumRange (fun i => g i (n − i)) (succ n)` before attacking `mulAssoc`; (2) the
subgroup join, which is also what makes a NORMAL subgroup statable and
generalizes `AlgS.Hom.quotient` from "quotient by a kernel" to "quotient by a
normal subgroup"; (3) `AlgS.Field` + `Apart` as its own decision, since it
gates dimension. The ℚ linear-algebra bridge is sized in ADR-1609 and its real
cost is `rowEchelon_isEchelon` (ADR-1554 obligation 4), which predates this
lane — do not price it as small.

<!-- plan-section: landed-changes -->

| 2026-09-04 | algebra-structures | `AlgS.Poly.*` (W2-9): the polynomial ring over an abstract `AlgS.CommRing`; 15 declarations, empty footprint; `dc5765ca6` |
| 2026-09-04 | algebra-structures | `AlgS.Module.*` (W3-2): modules over an abstract `AlgS.CommRing`, with `R` and `R[X]` as instances; 23 declarations, empty footprint; `31f06cb80` |
| 2026-09-04 | algebra-structures | `AlgS.Subgroup.*` (W1-11): subgroups as a bounded meet-semilattice, and `ker_isSub`; 20 declarations, empty footprint; `3e8363829` |
| 2026-09-04 | algebra-structures | ADR-1609: the designs, the setoid cost per construction, and every stopping point sized |
| 2026-09-04 | algebra-structures | three fact-ledger entries (`F:algs-poly-distrib-l`, `F:algs-poly-module`, `F:algs-subgroup-ker`), each with a checker whose exit status depends on the suite's exact pass count |
