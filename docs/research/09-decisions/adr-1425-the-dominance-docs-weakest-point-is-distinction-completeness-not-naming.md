# ADR-1425: the dominance document's weakest point is distinction-completeness, not the row-3 naming gap

Date: 2026-09-01
Status: Accepted
Lane: `dominance-doc-reverify`

Index-summary: Re-verifying [09-the-dominance-claim-verified-across-three-domains.md](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md) against a tree one day newer found its own headline §7.4/§8 finding — "number theory's row-3 certificates exist in code and no fact names them" — already fixed by the commit that landed hours before the document was published (ADR-1055, four facts, independently re-confirmed proved here). This ADR records the resulting re-ranking: future work on strengthening the row-3 argument should target ADR-1400's eleven distinction-incomplete certificates (sturm.rs's half-open interval convention and gosper.rs's three indistinguishable acceptance modes first, both because they are silent-failure classes a mutation suite structurally cannot find and because one sits directly under this document's own cited IVT row), not the naming gap, which is now ten modules and shrinking on its own. Also recorded: the CAS-certificate route count is 54, not 19 and not 56 — two facts reported as landed today do not exist in this tree, and should not be cited until independently re-confirmed present.
Index-status: Accepted

## Context

`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
is written and maintained as the single referee-facing artifact for this
repository's central dominance claim. Its own stated method is that every
number is re-measured, not inherited, and that failures belong in the body.
That method implies the document itself needs periodic re-verification, since
a "verified this sitting" artifact is stale from the moment the sitting ends.

This lane (`dominance-doc-reverify`) was dispatched to do exactly that,
against a tree one day newer than the document's 2026-08-31 draft. The full
measurement trail is in the document itself (§1, §7, §8, §9 as amended by
commit `479b1cf1a`); this ADR records only the decision that should bind
future prioritization.

## What was found

1. **The document's own headline finding (§7.4, echoed as the primary
   weakness in §8) was already fixed by the time it was published.** Commit
   `79238b1ca` (`feat(facts): four cas-internal row-3 facts for
   number-theory certificates`, ADR-1055, lane `row3-citability`) landed
   hours before the dominance document did. Four facts —
   `F:cas-ntheory-pratt-primality-mersenne89`,
   `F:cas-ntheory-factorization-certificate`,
   `F:cas-ntheory-crt-certificate`, `F:cas-ntheory-compositeness-certificate`
   — all `epistemic_status: proved`, each with the discriminating
   `grep -cE '^test … ok$'` checker shape this repository's own gates
   require. One re-run directly in this worktree from a fresh build
   confirms `ok` against the tested count.

2. **A same-day, wider CAS audit (ADR-1400) is a stronger and more durable
   finding than the one it supersedes.** It measured **eleven certificates
   that cannot express a distinction their own producer makes** — the same
   shape that let a forged refutation pass in `nra_monomial_bound_cert`
   (this repository's canonical soundness lesson), now found to recur
   structurally across the CAS crate rather than being a one-off. Two are
   consequential enough to prioritize:
   - `sturm.rs`'s `(lower, upper]` half-open convention lives only in
     prose; `real_algebraic::verify_ivt_certificate` — the bridge the
     dominance document's own §2.2 cites for the IVT row — consumes it on
     trust.
   - `gosper.rs`'s three acceptance modes (full certification, and a weaker
     mode C that fires *because* full certification failed) return an
     indistinguishable value, so a caller cannot tell "certified" from
     "downgraded."

   Unlike a naming gap, which is fixed by writing one fact, a
   distinction-incomplete certificate is fixed only by changing the
   certificate's type — and mutation testing cannot find the gap, because
   the guard that would catch it was never written. This is why it outranks
   the (now much smaller) naming gap as the thing worth spending effort on.

3. **The naming gap is real but smaller than reported, and shrinking on its
   own.** The audit's own two upstream numbers were both wrong in opposite
   directions (unmasked doc-comment prose inflated the certificate-surface
   numerator; a filename convention undercounted the fact-route
   denominator). Corrected: 27 of 55 modules carry a genuine certificate
   surface (not 40 of 53); `cas-certificate` is the `proof_route` of 54
   facts (not 19). Ten certificate-carrying modules still have no naming
   fact (`boolean_circuit`, `geometry_json`, `gf2_artifact`, `gf2_search`,
   `gf2_shard`, `gf2_tensor`, `gosper`, `groebner_cert`, `lib`,
   `telescoping_json`) — the audit's own prose claims "seven," which
   contradicts its own enumerated list of ten; this ADR does not adjudicate
   which is right and defers to whichever lane next touches that audit.

4. **Two facts reported to this lane as landed today do not exist in this
   tree.** `F:cas-boolean-circuit-nand-only-full-adder` and
   `F:cas-gf2-tensor-karatsuba-degree-2-rank-three`, said to take
   `cas-certificate` from 54 to 56, are absent — `ls artifacts/facts/` and
   `validate-facts.py`'s own `proof_route` census both confirm 54, with a
   positive control of 25 `^F-cas-` filenames still present. Do not cite 56
   until these are independently confirmed present on `main`.

## Decision

**Future work strengthening the row-3 / decidable-fragment half of the
dominance argument should target ADR-1400's distinction-completeness gap
first, in the order that audit ranks it, not the row-3 naming gap** — the
naming gap this document originally flagged as its weakest point is closed
for number theory and materially smaller everywhere else, while the
distinction-completeness gap is a soundness-adjacent defect class (the same
shape CLAUDE.md already treats as the canonical lesson from
`nra_monomial_bound_cert`) that a naming fix cannot repair and that no
existing gate in this repository can detect.

Concretely, the two modules named in finding 2 above are the recommended
next targets when this argument is next strengthened: `sturm.rs` because it
sits under a row this document already scores (IVT), and `gosper.rs` because
its three-mode ambiguity is the sharpest instance the audit found.

The dominance document itself
(`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`)
now carries this re-ranking in its own §8 and a re-verification date in its
header; this ADR exists so the decision is discoverable independent of that
document's next revision.

## Consequences

- A lane picking up row-3 work for number theory should not re-litigate the
  naming gap this ADR closes; it should read ADR-1400's per-module table
  and pick from the `COULD RECONSTRUCT` or distinction-incompleteness lists.
- Any citation of "cas-certificate = 56" or of the two facts named in
  finding 4 should be treated as unverified until re-confirmed against a
  live tree.
- The dominance document's §5.1 deeper gate census (`semantic_falsification`,
  `mutation_control`, `circularity`, `independent_replay`) was **not**
  re-verified by this lane and remains a day stale; a future re-verification
  pass should re-run it rather than assume it is still current.
