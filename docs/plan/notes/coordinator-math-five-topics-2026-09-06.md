# coordinator-math, 2026-09-06 — detail behind the five topics

Companion to
[status/coordinator-math-five-topics-2026-09-06.md](../status/coordinator-math-five-topics-2026-09-06.md).

## Results worth re-reading

**Three prior sizings were overturned by re-measurement, not by argument.**
ADR-1625 priced the metric completion against the wrong term former, and its
"1 of 33 lemmas reusable" rested on an inverted inference: a lemma stated about
`CReal` is *applicable* to a `CReal`-valued distance, not disqualified by it.
33 of 33 instantiate. ADR-1658 oversized a valuation lemma by an order of
magnitude — one `lt_or_ge` and three `dvd_trans`, not a lane. And the product
space's index range already existed as `Rat.sumMaps`, built for Cauchy–Binet:
the recorded absence was correct about names and wrong about structure, which
is the third false absence that week found by searching for the STEP rather
than the name.

**Two mutation findings about tests, not code.** A mutant weakening a metric
isometry to a bound was ADMITTED and passed 11 of 11 tests — including the one
written for exactly that case, because it re-derived the distinction inline
instead of consuming the shipped declaration. Separately, a solver fixture
named `..._wrapper_carries_lean_module` measured the honest route and asserted
only that a module existed, so it would have stayed green if the wrapper broke.
Both are one defect: **a guard must consume the declaration it names and assert
the surface consumers actually read.** A rename does not fix it; asserting the
rendered identifier does, so the name cannot drift from the route a second
time.

**The SoS fallback was worse than reported.** It is a hand-inlined copy of the
honest structural route minus its banner — which is why the two guards written
for exactly this could not fire, since the content classifier keys on a marker
the wrapper never applied. It emitted byte-identical modules for `x*x < 0` and
`(x-y)*(x-y) < 0`, so the artifact could not express which query it refuted.
The fix keys the name on the axiom footprint; the attested name is deliberately
**not** a substring of the honest one, because three consumers ask with a bare
`contains(...)` and a suffix would have satisfied every new assertion while
leaving all three conflating.

## Corrections to claims this session had published

Each was published before it was checked, and each was caught by the peer
coordinator rather than by me.

1. **The axiom-free headline.** "2,584 of 2,687" mixes evidence routes.
   `validate-facts.py` marks the cross-route reading not comparable; the honest
   form is in ADR-1674, and "all `kernel-lean` facts are axiom-free" is false by
   exactly two. Both places that state it now name the command and say the
   denominator moves — it moved by 14 within an hour of being written.
2. **Two committed SHAs** attributed the SoS work to another session's merge.
   Cause: reading `git log -1` after a backgrounded land, by which time a peer
   merge had landed on top. Capture the SHA from the merge command's own output.
3. **The census reason.** "Did not run — two timeouts" was wrong: the wrapper
   returned and the process ran 2.5 hours more, orphaned. The conclusion
   survives; the reason did not. See ADR-1673's correction block.
4. **The 430 uncovered theorems** (2026-09-04 audit) is not reproducible by its
   own method. Retired in all 14 places it was quoted; measured figure 721 of
   3,079 registered theorem names.

## Process notes for the next coordinator

- **Put `check-kernel-suites.sh` FIRST in a pre-push battery.** It is the step
  most likely to fail on a composition, and last place makes that cost the whole
  run. Budget it against the CURRENT load, not an idle-machine intuition: 1800 s
  sufficed at load 2 and not at load 24.
- **The pre-run is not the hook.** A manual list that omits expensive gates is
  useful, but never reason "the pre-run passed, so the push will pass".
  `hooks/pre-push` runs workspace clippy via `check-clippy-complete.sh`; most
  manual lists do not. Read the hook rather than grepping it — its comments
  discuss gates it does not run, so a bare grep misleads in both directions.
- **Refuse a merge commit whose staged set is not the lane's own diff plus the
  generated allowlist.** A merge takes the whole index; one merge this session
  swept 23 files belonging to a peer, and conflict resolution leaves a wide
  window for their files to appear.
- **Set `AXEYUM_AGENT` to a session-distinct value** (`coordinator-math`, not
  `coordinator`): two coordinators used the same string and 11 commits carry
  indistinguishable `Agent:` trailers.
- **Sweep for orphans at the end of any session that reaped a worktree.** Three
  turned up in one evening, from a timeout whose child outlived it, a killed
  shell whose child did not die, and a detached diagnostic kept past its answer.
  See [measurement-hazards](../../contributor-guide/measurement-hazards.md).
- **Composition, not correctness, is what breaks a shared main.** Both push
  failures this session were two branches each green alone: a 32nd prelude
  builder landing after a census was written against 31, caught by that census
  on its first opportunity.
