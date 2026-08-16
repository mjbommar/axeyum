# Lane: telescoping-scale (Gosper–Petkovšek bounds, symbolic base cases, certificate artifacts)

<!-- plan-section: lane-status -->

**Continuation lane — took the four ranked follow-ons from lane `telescoping`
(2026-08-14).** All four landed; the first two landed properly, and the honest
limit moved from "the search is a degree sweep" to a much more specific place.

**(1) The degree sweep and the `Q` ladder are gone.** The search now derives what
it used to guess. For each order, `ρ(k) = r(k)·D(k)/D(k+1)` is put into
**Gosper–Petkovšek normal form** `(a/b)·(s(k+1)/s(k))`, which makes Gosper's
criterion the single polynomial equation `a(k)x(k+1) − b(k−1)x(k) = s(k)N(k)` and
hands back the certificate outright as `R = b(k−1)x(k)/(s(k)D(k))`. So the
certificate **denominator is derived** (`s·D`, no ladder), the certificate
**degree in `k` is derived** (Gosper's classical bound), and the recurrence
coefficients are solved for over the **field `ℚ(parameters)`** with no degree
ansatz at all — `Limits::max_recurrence_degree` is deleted, not defaulted. What
was up to 72 linear systems per order is one.

Measured, release build, `examples/telescoping_search_cost.rs` (committed, so the
claim is reproducible):

| identity | before | after |
|---|---|---|
| `∑_k C(n,k)` | 55.7 ms | 1.3 ms |
| `∑_k C(n,k)²` | 137.5 ms | 3.8 ms |
| `∑_k k·C(n,k)` | 40.2 ms | 1.3 ms |
| `∑_k C(m,k)C(n,p−k)`, default limits | **18.5 s** | **46.7 ms** (396×) |
| `∑_k C(n,k)³` (Franel) | **declined after 9.8 s** | **found, order 2, 109 ms** |

The bounds **do** subsume the heuristic: every identity the old engine found, the
new one finds with the same classical recurrence, and the tests assert those
coefficients exactly. `J ≥ 2` came free as predicted.

**(2) Symbolic base cases.** `check_closed_form_symbolic` settles a base case
with the parameters left symbolic: substitute only the shift variable, read the
**forced support** off the `Γ` factors whose argument became parameter-free
(Chu–Vandermonde at `p = 0`: `Γ(k+1)⁻¹` forces `k ≥ 0`, `Γ(−k+1)⁻¹` forces
`k ≤ 0`, support `{0}`), *check* — not assume — that every window point outside
it vanishes, and cancel the symbolic `Γ` powers pairwise. Both sides must reduce
to a rational; a leftover `Γ` is refused as not comparable, never compared by
coefficient. This is what the previous lane called its sharpest gap.

**(4) Certificates are artifacts.** `artifacts/cas-certificates/*.json`, seven of
them, written by a checker-gated emitter and re-checked **from the file** by a
sweep that never calls the search. Fact evidence rows now point at the
certificate instead of at a test that rebuilds it. Hand-rolled deterministic
codec; the crate still depends on nothing but `axeyum-ir` and `num-*`.

**(3) not taken.** The `CasExpr` → `HyperTerm` front door and a surface-syntax
corpus. Depth over breadth; the serialised format covers part of the same need
(a corpus is a directory and one command sweeps it) and gives a parser an obvious
target.

Three new facts (the `cas-certificate` route is now 8; `validate-facts.py` 0 errors):
`F:chu-vandermonde-convolution` (the closed form, symbolic base case),
`F:cross-binomial-row-sum` (`∑_k C(m,k)C(n,k) = C(m+n,n)`),
`F:franel-numbers-recurrence` (the first order-2 certificate on this route). New
axiom named where it is used: `cas.symbolic-gamma-arguments-avoid-poles`.

15 tamper/limit controls now, all rejecting: the previous lane's ten, plus a
symbolic closed form with the wrong base, one with the wrong ratio but the right
base *value*, one leaving an uncancelled `Γ`, a window that does not **strictly**
contain the forced support, and an unbounded support that declines instead of
truncating. The artifact sweep adds its own: an edited numerator, an edited
recurrence coefficient, a certificate re-pointed at a neighbouring file's
summand, and truncated / foreign-format / decimal-bearing files.

**The next honest limit is `MvPoly`'s `i128` coefficients, specifically inside
`MvPoly::gcd`.** Apéry's `∑_k C(n,k)²C(n+k,k)²` declines, and the cause is
measured rather than assumed: the derived degree bound is 2, which is exactly the
degree at which the certificate exists (verified out of tree), so the search
design is not what fails — the primitive-PRS pseudo-remainder overflows `i128` on
the degree-8 shift quotient, already at order 0. The fix is a subresultant PRS or
bignum coefficients in `MvPoly`, both changes to a module the whole crate depends
on. Two smaller limits: `leading_integer_zeros` still declines when the leading
recurrence coefficient mentions more than the shift variable (a Saalschütz-type
identity will hit it), and a symbolic base case needs the support pinned by
parameter-free `Γ` factors.

Full write-up:
[`docs/mathematics-2026-08/diary-telescoping-scale.md`](../../mathematics-2026-08/diary-telescoping-scale.md).

<!-- plan-section: landed-changes -->

| 2026-08-14 | `telescoping-scale` | Gosper–Petkovšek derived denominator and degree bound replace the `Q` ladder and the degree sweep (Chu–Vandermonde 18.5 s -> 46.7 ms); order-2 recurrences reachable (Franel); symbolic base cases close Chu–Vandermonde's closed form; certificates serialised to `artifacts/cas-certificates/` and re-checked from file; 3 new facts | `crates/axeyum-cas/src/telescoping.rs`, `crates/axeyum-cas/src/telescoping_check.rs`, `crates/axeyum-cas/src/telescoping_json.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `crates/axeyum-cas/tests/telescoping_certificate_artifacts.rs`, `artifacts/cas-certificates/*.json`, `artifacts/facts/F-chu-vandermonde-convolution.json`, `artifacts/facts/F-cross-binomial-row-sum.json`, `artifacts/facts/F-franel-numbers-recurrence.json` |
