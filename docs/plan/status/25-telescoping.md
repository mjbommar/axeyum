# Lane: creative telescoping (definite hypergeometric summation)

<!-- plan-section: lane-status -->

**New lane — certified definite hypergeometric summation (2026-08-14).**
Opened the domain the CAS stack was one step away from: `gosper.rs` decided
*indefinite* summation, and the definite half — Zeilberger's algorithm / creative
telescoping — did not exist as a checkable object. Landed
`crates/axeyum-cas/src/telescoping.rs` (an untrusted linear-algebra search over a
degree-bounded ansatz, minimal recurrence order first, nullspace in
`BigRational`) and `crates/axeyum-cas/src/telescoping_check.rs` (an independent
checker sharing no code with it). Five classical identities proved end to end and
filed as facts:

| identity | order | recurrence | certificate `R` |
|---|---|---|---|
| `∑_k C(n,k) = 2ⁿ` | 1 | `2S(n) − S(n+1) = 0` | `k/(n−k+1)` |
| `∑_k (−1)^k C(n,k) = 0` | **0** | `n·S(n) = 0` | `−k` |
| `∑_k C(n,k)² = C(2n,n)` | 1 | `(4n+2)S(n) − (n+1)S(n+1) = 0` | `k²(3n+3−2k)/(n−k+1)²` |
| `∑_k k·C(n,k) = n·2^{n−1}` | 1 | `(2n+2)S(n) − nS(n+1) = 0` | `(k−1)(n+1)/(n−k+1)` |
| Chu–Vandermonde (recurrence only) | 1 | `(m+n−p)S(p) − (p+1)S(p+1) = 0` | `k(k+n−p)/(p−k+1)` |

The independence is carried by concrete evidence, not by two people writing the
same algebra twice: the checker cross-checks every symbolic shift ratio against
`F` computed from **actual factorials in exact bignum rationals**, then confirms
the pointwise telescoping identity and the summed recurrence the same way. Ten
tamper controls — `P+1`, `2P`, `Q+k`, a wrong recurrence constant, a degree bump
in `a_j`, a zeroed recurrence, a certificate re-pointed at a *different summand*,
a summation window narrower than the support, and two wrong closed forms — are
all rejected.

Schema: added `proof_route: cas-certificate` and `formal.language: cas-term`
(`artifacts/ontology/fact.schema.json`, `scripts/validate-facts.py`). A
telescoping certificate is **not** a `search-certificate`: a replayed witness
settles one finite instance, while an identity in `ℚ(vars)` settles every
instance at once, and their footprints differ in kind. `axiom_footprint` names
the real assumptions, including the one this lane does **not** discharge —
`cas.telescoped-term-natural-boundary`, that `R·F` keeps `F`'s support and
acquires no pole inside it.

Ordered follow-on work:

1. **Degree bounds instead of a degree sweep** (Abramov universal denominator +
   Gosper–Petkovšek normal form). The single biggest win: the search cost is
   dominated by the ladder, not by the linear algebra — Chu–Vandermonde took
   ~250 s on default limits and seconds on tight ones. This also replaces the
   heuristic `Q` ladder, which is where completeness is currently lost.
2. **Symbolic base cases.** Without them every multi-parameter identity stops at
   its recurrence, as Chu–Vandermonde did; with them the whole
   Vandermonde/Gauss/Saalschütz family follows.
3. **A `CasExpr` → `HyperTerm` front door and a committed identity corpus**, so a
   hundred identities are one regression sweep and the existing `prove_wz_sum`
   callers can migrate onto the checkable route.
4. **Serialise `TelescopingCertificate` to `artifacts/`** so an evidence row
   points at the certificate itself rather than at a test that rebuilds it.

Full write-up, including what the fragment does *not* cover:
[`docs/mathematics-2026-08/diary-telescoping.md`](../../mathematics-2026-08/diary-telescoping.md).

<!-- plan-section: landed-changes -->

| 2026-08-14 | `telescoping` | Creative telescoping (Zeilberger) with an independent certificate checker; 5 classical binomial identities landed as `cas-certificate` facts; 10 tamper controls reject perturbed certificates | `crates/axeyum-cas/src/telescoping.rs`, `crates/axeyum-cas/src/telescoping_check.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `artifacts/facts/F-*binomial*.json`, `artifacts/facts/F-chu-vandermonde-convolution-recurrence.json` |
