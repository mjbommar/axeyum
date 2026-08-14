# Did agent-a's per-colour extension carry? — the integration record

The question this lane exists to answer: **is `ColouringFamily`'s per-colour
extension a capability, or a one-target special case?** agent-a built it for
generalized off-diagonal Schur numbers `S(3;s,t,u)`. Van der Waerden's
`w(2;3,t)` is off-diagonal by nature — colour 1 must avoid 3-term arithmetic
progressions, colour 2 must avoid `t`-term ones — in a different area of
mathematics, with a different defining relation and, as it turned out, the
opposite cost profile.

**It carried. Unmodified, and further than agent-a's own driver did.**

## 1. What was reused, exactly

Everything below was consumed **without a single edit**, at commit `c0403d000`
and its ancestors:

| component | file | how it was used |
|---|---|---|
| `constraints_for_colour`, `colour_dependent`, `symmetry_blocks` | `family.rs:56,69,82` | implemented, defaults untouched |
| `ColouringFamily::problem` dispatch | `family.rs:107` | routes diagonal to the uniform encoder and off-diagonal to `per_colour`, with no change |
| `ColouringProblem::per_colour` | `colouring.rs:144` | per-colour scopes and caller-supplied blocks |
| `encode_block_symmetry_breaking` | `colouring.rs:363` | block-restricted ordering |
| `constraint_violated`, `scope`, `first_monochromatic` | `colouring.rs:214,237,443` | the scoped violation predicate |
| `decode_model`, `Witness` | `colouring.rs:409,459` | model to colouring |
| `verify_witness` | `family.rs:126` | untrusted-witness gate |
| `solve_with_drat_proof{,_streaming}`, `TextProofSink`, `parse_drat`, `check_drat_backward` | `axeyum-cnf` | search, proof production, proof checking |
| `harness::run_cover`, `cover::colour_branch_plan`, `CoverOptions`, the ledger | `harness.rs:348`, `cover.rs:638` | cube cover on a third family |
| `search::min_conflicts` | `search.rs` | the SLS lane |
| the claim ledger and its checker's shape | `artifacts/claims/`, `scripts/check-claim-certificates.py` | a new family slotted in beside two others |

**The diff to existing library code is 78 lines, all additive**: two lines in
`lib.rs` (module + re-export) and 76 in `family.rs` (spec parsing plus its
tests). The single *edit* to anything pre-existing was one line of an existing
test — `parse_family("vdw:k=2").is_err()` in
`family_specs_reject_unknown_families_and_keys`, which had been using `vdw` as
its example of an unknown family and could no longer do so.

## 2. What had to be added

| piece | lines |
|---|---:|
| `crates/axeyum-search/src/vdw.rs` (family, progression enumeration, independent verifier, blocks, published-value reference table, 12 unit tests) | 651 |
| `crates/axeyum-search/tests/vdw.rs` (5 integration tests incl. the negative control) | 202 |
| `family.rs` spec parsing + tests | +76 |
| `lib.rs` | +2 |
| `scripts/check-claim-certificates.py`: the family's independent Python semantics | +366 |
| **everything else — encoder, CDCL, DRAT sink, backward checker, cube cover, ledger, local search** | **0** |

That is the same shape as agent-a's accounting, and it should be: the second
family costs the family.

## 3. The strongest evidence, and it is accidental

agent-a's driver is written against the concrete type `OffDiagonalSchur` and
calls `family.minimal_problem(n)`, an inherent method. Mine is written against
**`Box<dyn ColouringFamily>` and `parse_family(spec)`**, so a single binary
drives `W(4,3)`, `W(2,5)`, `w(2;3,20)` and, without recompilation, every Rado
and Schur instance in the crate. Nothing in the trait had to change to make
that work.

I did not plan that as a test; I wrote the driver that way because I had two
spellings (`vdw:c=4,k=3` and `vdw:k1=3,k2=20`) to support. It is the sharper
demonstration precisely because it was not designed to be one: the abstraction
holds at the `dyn` boundary, where a special case would have leaked a concrete
type.

## 4. The soundness precondition, in a second family

The per-colour extension's whole reason for existing is that colour classes may
be ordered by least element only between colours that forbid the same sets.
That precondition is *not* a property of Schur numbers; it is a property of
off-diagonal colouring, and it reappeared here immediately.

Measured, not asserted: `w(2;3,4)` at `n = 17` is satisfiable (`w(2;3,4) = 18`)
and **every** good colouring gives integer 1 the colour that avoids four-term
progressions. Encoded with the whole palette declared interchangeable, the same
instance comes back `unsat` — with a DRAT refutation that our own backward
checker accepts, because the refutation is correct and the formula is not the
problem. That is
`crates/axeyum-search/tests/vdw.rs::whole_palette_symmetry_breaking_produces_a_wrong_unsat`.

The instance is load-bearing in exactly the way agent-a warned. Scanning
`w(2;3,5)` over `n = 1..=21` and `w(2;3,6)` over `n = 1..=31`, the two encodings
**agree everywhere**: 0 flips in 52 instances. A control built on either would
have passed while testing nothing. Only `w(2;3,4)`, and only at `n = 15, 16, 17`
— the top three sizes below the threshold — exposes it.

The reverse case is new here and had to be added deliberately: for the
*diagonal* `W(r,k)` the colours genuinely are interchangeable, so the full
whole-palette break is sound and worth a great deal. `colour_dependent()` is
therefore `!is_diagonal()`, which routes `W(r,k)` back down the stock uniform
encoder — the byte-identical one the Rado certificates were produced with — and
`w(2;3,t)` with `t != 3` to blocks `{1}`, `{2}`, i.e. no colour symmetry at all.
`w(2;3,3)` is `W(2,3)` and the family says so: same label, same encoding, same
number, reached by both spellings.

## 5. Where the cost profile inverted, which is the real portability test

agent-a's headline was a subsumption reduction worth up to **1,402×**, and the
resulting finding that *enumeration, not solving,* was the wall.

**Neither transfers, and both failures are informative.**

The reduction transfers to nothing: every length-`k` progression is a set of
exactly `k` points, so `S ⊆ S'` forces `S = S'`, and a progression is determined
by its set, so there are no duplicates either. The forbidden list is already a
subsumption-minimal antichain. This is measured, not argued —
`VanDerWaerden::subsumed_pair` searches for a containing pair and
`the_antichain_reduction_has_nothing_to_remove` runs it over 15 configurations
including `k = 12` at `n = 135`. Ratio **1.000**.

So the clause count is exactly the progression count, `O(n²/k)`, and every
instance in this lane built in under 10 ms. `w(2;3,20)` at `n = 389` is 42,204
clauses over 778 variables. Where agent-a spent 164 s enumerating to keep 451k
clauses refuted in 0.1 s, this family builds instantly and then **the proof is
the wall**:

| cell | n | clauses | DRAT steps | proof bytes | solve | check |
|---|---:|---:|---:|---:|---:|---:|
| w(2;3,10) | 97 | 2,973 | 164,912 | 10.9 MB | 1.2 s | 1.3 s |
| w(2;3,11) | 114 | 4,014 | 1,017,863 | 83.9 MB | 9.7 s | 12.0 s |
| w(2;3,12) | 135 | 5,521 | 6,347,847 | 623 MB | 82.2 s | 110.3 s |
| w(2;3,13) | 160 | 7,628 | — | **6.0 GB** | ~1,300 s | **OOM** |

The formula grows linearly and the proof grows by a factor of six per step of
`t`. One framework, two families, opposite bottlenecks — which is a better test
of the framework than a second instance of the same shape would have been, and
it is why the cover machinery mattered here (section 7).

## 6. One process, twenty seconds — the comparison worth keeping

`W(2,5) = 178` (2 colours, no monochromatic 5-term progression):

```
n = 177  sat, colouring replayed by first_violation
n = 178  unsat, 8,278 clauses, 2,153,837 DRAT steps, 139 MB,
         solve 20.05 s, check 22.19 s, 43.2 s end to end
```

One process, one solve, our own checker, no external tool of any kind.

The only prior machine-checked certification of this value that a literature
audit found is an unreviewed 2026 repository that reached it with **3,627 cubes
of cube-and-conquer, per-cube LRAT certificates, an LRAT-Catcher composition
pass and a Lean 4 reflection proof** — a pipeline of march_cu, CaDiCaL,
drat-trim, lrat-check, CakeML's `cake_lpr` and Lean. The peer-reviewed
certifications that exist at all (PBLean, arXiv:2602.08692) cover `W(2,3) = 9`
and the upper half of `W(2,4) = 35`, via VeriPB into Lean. Ahmed, Kullmann and
Snevily, who computed the `w(2;3,t)` row, produced no proof object and wrote
that one "would be highly desirable"; Marijn Heule's `vdWaerden` repository
holds 44 certificates and every one is a lower-bound colouring.

The claim is not that our CDCL core is faster than kissat. It is that **the
distance from "a number" to "a checked certificate" is a five-line function
call here and a six-tool pipeline there**, and that the difference shows up at
the exact scale where the six-tool pipeline is a research contribution.

## 7. Where the framework did not help — honest seams

Cited by file and line, in decreasing order of how much they cost me.

1. **`parse_drat` materialises the whole proof, and there is no streaming
   checker.** `check_drat_backward(&formula, &steps)` takes a slice, so the
   proof must be parsed into memory first. At `w(2;3,13)`, `n = 160`, the CDCL
   core streamed a 6.0 GB text DRAT to disk in ~22 minutes and the checker was
   **OOM-killed on a 26 GiB host**. The verdict was real and unusable: an
   unchecked refutation is not a certification. This is the single wall that
   stopped the row. `crates/axeyum-cnf/src/proof_sat.rs:222` streams the proof
   out; nothing streams it back in.
2. **The cover route is the framework's own answer and it also OOMs.**
   `harness::run_cover` at depth 8 with 14 workers refuted **247 of 256 cells**
   of that same `n = 160` instance — every one of the 247 with its per-cell
   proof re-derived by the backward checker, 85,262,947 steps, 1,983 s of
   solving and 3,423 s of checking — and was then killed at 7.4 GB of retained
   cell proofs, with a single cell's proof reaching 282 MB. Nine cells short of
   a certified value. `CoverOptions` has `workers`, `cell_conflicts`,
   `cell_time`, `total_time`, `check_step_cap` and `compose_step_cap`
   (`harness.rs:77-106`) — every budget except the one that killed it, a
   **memory** budget. The nine survivors are the cells where the branch points
   take the long-progression colour, so they are also the ones a depth-aware
   splitter should have split further.
3. **`ColouringFamily::constraints` forces an off-diagonal family to publish a
   relaxation, and for this family the honest relaxation is empty.**
   `family.rs:47` requires the sets forbidden in *every* colour. A length-`k1`
   progression has `k1` points and a length-`k2` one has `k2`, so for `k1 != k2`
   the intersection is **empty** — and a `ColouringProblem` with no constraints
   encodes a formula that is satisfiable for every `n`, which reads exactly like
   a genuine `sat`. `offdiag.rs:569` has the same hazard and documents it; I
   documented it again and put an `assert!(!problem.forbidden().is_empty())` in
   the driver. Two families in, this is a trait shape problem, not a family
   problem: `constraints()` should not be the primary method with
   `constraints_for_colour` as its refinement.
4. **There is still no `decide(family, n) -> Decision` in the crate.** agent-a
   reported this; I hit it identically and my response was to copy
   `offdiag_frontier.rs` and edit it. The decide/bundle/verify loop — solve,
   decode, replay, write, re-check — is now ~700 lines living outside the
   repository in **two** copies that share a lineage and no code. Everything
   valuable in it (a `Verdict` that distinguishes `UnsatChecked` from
   `UnsatUnchecked`; refusing to print an established value from an unchecked
   proof; writing nothing that was not re-checked first) is exactly the policy
   the library should own.
5. **Engine selection is folklore, and the folklore is wrong half the time.**
   See FEEDBACK item 2: agent-a measured CDCL beating `min_conflicts` by three
   orders of magnitude and wrote that down; on `W(4,3)` at `n = 75` the CDCL
   core exhausts its default conflict budget in 44 s while the instance is a
   4-colour satisfiable search problem. Each lane rediscovers this by burning an
   hour.
6. **The claim checker needs a fresh Python implementation per family** — 366
   lines here. That second implementation *is* the third derivation and is
   worth having; it is a cost, not a freebie, and it is the point at which "one
   framework" becomes "one framework plus a reimplementation in another
   language".
7. **The claim gate was red and one error was hiding the rest.** `novelty` was
   written into claims and enforced by `check-claim-certificates.py` but was
   absent from `claim.schema.json` and from `validate-claims.py`'s field list,
   so all 62 claims carrying it failed with `unknown field 'novelty'` — and
   `validate-claims.py` returns after the field check, so that one error masked
   everything behind it. Admitting the field exposed **229** real errors, 228 of
   them pre-existing in `offdiag-schur` claims. Separately,
   `classify_payload` sniffed `colouring-text` from the whole file instead of
   the comment-stripped body, so the provenance header every producer in this
   tree writes made **61 witnesses** fail their own format contract. Both are
   fixed in this lane's commit; the 228 are not mine to fix and are reported.

## 8. Verdict

The extension is a **capability**. A second family, in a different area of
mathematics, with a different defining relation, an inverted cost profile and
its own reason for needing per-colour scopes, consumed it with 78 lines of
additive change to existing library code and zero changes to the encoder, the
solver, the proof sink, the checker, the cover harness or the ledger — and drove
all of it through `dyn ColouringFamily` rather than a concrete type.

What did not carry is as informative: the subsumption reduction (ratio 1.000
here, measured), the "enumeration is the wall" finding (inverted), and the
engine-selection folklore (inverted). Those are family-level facts that the
framework currently has no place to record, and each lane pays for them again.
