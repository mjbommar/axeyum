# Lane: frame-carrier

<!-- plan-section: lane-status -->

Status: complete (2026-09-05). Roadmap W2-21 — a topological carrier built as a
frame, with the open-ball frame of ℝ as the first instance. ADR-1643.

## What this lane did

Executed [ADR-1602](../../research/09-decisions/adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)'s
fourth recommendation — *topology proper, when it is needed, is a frame* — in a
new file `crates/axeyum-lean-kernel/src/top_frame.rs`, registered from the crate
root. Nothing under `metric.rs`, `metric_prod.rs`, `creal.rs` or `creal/` was
touched.

`Top.Frame` is a sixteen-field `Sort 2` record built with the `AlgS` spine's own
`declare_record`: `le` (reflexive, transitive), `inf`, `top`, `bot`, a
**countable** join `sup : (Nat → carrier) → carrier`, the four universal
properties, and one direction of the frame distributive law. The ℝ instance is
`Top.ballFrame` over `Top.Opens := Rat → Nat → Prop`.

**53 declarations**, **0 axioms** in any footprint, **11 of 11** tests passing
(`--release --test-threads=4`, 45 s), and **0 kernel refusals** across the whole
development — every proof term was admitted on its first kernel run.

## The four findings

1. **A frame's setoid equality is derived, not a field.** `Metric` carries
   `equiv` plus three laws plus `distCongr` because `CReal.Equiv` is independent
   data (ADR-0512). A frame is a poset, so `Equiv a b := le a b ∧ le b a` is
   forced by antisymmetry and the three laws are theorems. Six fewer obligations
   per instance, at zero cost.
2. **`Nat → Bool` cannot be the carrier.** ADR-1624's decidable-subset
   representation is the natural first guess for "a set of ball indices", and it
   fails on the defining operation: `sup f i = ∃ n, f n i` is not a `Bool`.
   No re-indexing repairs it — the problem is the codomain, not the index.
3. **The pairing round-trip is held out, so the ball index is a pair.** The
   planned `sup` re-indexes through `Nat.pair`/`Nat.unpairLeft`, which needs
   `unpairLeft (pair a b) = a` — the content of the family `natural-avg-pair`
   (`Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing`), registered
   **held-out with ten rows**. Indexing a ball by its centre *and* radius
   (`Rat → Nat → Prop`) removes the need for a pairing, and with it the need for
   a surjective `Rat.enum : Nat → Rat` the brief had sized as its own commit.
   The partition check the lane ran *before writing any term* is what caught it.
4. **`CReal.density` IS the covering property.** `Top.ball_density` is the reals
   prelude's own density lemma applied, and the restatement type-checks by δβ.
   Nothing had to be re-derived, because `Top.MemBall` is written in
   `creal/density.rs`'s two-sided sandwich rather than as `|x − q| < ε`.

## What did not land

Hausdorff separation *from* `CReal.Apart`. `Top.ball_separated` proves the
geometry (strictly separated brackets ⟹ no shared point) in four steps; the
missing half is index selection — eliminate the `Or`, read `CReal.lt`'s rational
gap, apply the Archimedean property, discharge two `Rat` inequalities. Sized at
250–400 lines of term building against lemmas that all exist. ADR-1643 records
the route.

Also not attempted, and stated as a limit rather than an omission:
`Top.ballFrame` is the frame **presented by** the rational-ball basis, not the
lattice of open subsets of ℝ. Getting the latter means quotienting by the
covering relation.

## Two shared files repaired in passing

`examples/shape_search.rs` carried two copies of its coverage sentence and of
its `--include-constructed` usage line — one ending `… and intspace`, one ending
`… and rn` — a "keep both sides" resolution of two lanes appending to the same
line, so the tool documented two different, each-incomplete group lists.
Collapsed, and `top` added as an indexed group so the next lane does not read a
confident ABSENT for `Top.Frame`. `scripts/validate-facts.py`'s
`KERNEL_THEOREM_RE` has the same duplication; there it is harmless (a regex
alternation is a union), so this lane added its own line rather than
restructuring a shared regex mid-flight, and recorded it.

<!-- plan-section: landed-changes -->

| 2026-09-05 | frame-carrier | `7e8fc512e` — `Top.Frame`, a sixteen-field pointfree topological carrier with a countable join, its nine derived generic theorems, the open-ball frame of ℝ (`Top.Opens`, `Top.ballFrame`), and the point lemmas; 53 declarations, all axiom-free, 11 of 11 tests |
| 2026-09-05 | frame-carrier | `c4754b326` — `top_frame_theorem_inventory` (exit status depends on both an absent filter and a nonempty footprint), and `Top.MemBall`/`Top.MemOpen` folded into the three statements that had spelled them out |
| 2026-09-05 | frame-carrier | `2db998539` — ADR-1643, four facts, the `top` group `shape_search` was blind to, and the repair of two duplicated "keep both sides" lines in `shape_search` |
