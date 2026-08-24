# `axeyum-cas` public API inventory for a PyO3 binding (`axeyum._native` / `axeyum.cas`)

Read-only survey, 2026-08-24. Paths are relative to `crates/axeyum-cas/`.
Crate: 65,143 lines across 45 `src/*.rs` files; `src/lib.rs` is 29,329 lines of
which lines 1–18,808 are API and 18,809–29,329 are `#[cfg(test)] mod tests`.

Tiers used below: **R** = required for a first binding, **P** = phase two,
**C** = certificate tier (must be split into producer vs. checker objects).

---

## 0. Findings that shape the whole binding

1. **There is NO text parser for `CasExpr`.** `grep -rn 'pub fn parse'` over the
   crate returns nothing; there is no `impl FromStr` anywhere. The only two
   `parse_*` functions (`lib.rs:2011 parse_rational_render`, `lib.rs:10937
   parse_log_polynomial_term`) are private helpers. `impl std::fmt::Display for
   CasExpr` exists (`lib.rs:858`) so expressions render, but the render is
   **not round-trippable**. The binding must build expressions by constructors
   (`CasExpr::var/int/rat/pow/…` plus the `Add/Sub/Mul/Neg/Div` operator impls at
   `lib.rs:823-857`). A Python-side parser (or `sympy`-to-constructor bridge) is
   out-of-crate work.
2. **No serde on any certificate type.** `serde::{Serialize, Deserialize}` is
   derived only in `gf2_shard.rs` and `gf2_artifact.rs` (on private `Raw*` wire
   structs, `gf2_artifact.rs:97/112/119`). Everything else — `GeometryCertificate`,
   `TelescopingCertificate`, `SosArtifact`, `CofactorOutcome`, `MvPoly`,
   `CasExpr`, `MultiPoly` — derives only `Debug, Clone, PartialEq, Eq`. JSON
   exists **only** through three hand-rolled deterministic writers/readers:
   `geometry_json`, `telescoping_json`, `sos/json`. Anything else is
   `Debug`-only and needs a hand-written `__repr__`/`to_dict`.
3. **No `Send`/`Sync` or lifetime hazards.** `grep` for `Rc<`, `RefCell`, `Cell<`,
   `*const`, `*mut`, `unsafe` across `src/` returns zero real hits; `unsafe_code`
   is denied workspace-wide. Every public type is owned plain data (`String`,
   `Vec`, `BTreeMap`, `Rational` (Copy i128 pair), `MvPoly`), so all are `Send +
   Sync + 'static` and safe to put behind `#[pyclass]`. The only borrow-shaped
   returns are `SosArtifact::kind() -> &'static str` (fine), and two borrowing
   iterators — `MvPoly::terms() -> impl Iterator<Item = (&Monomial, &Rational)>`
   and `Monomial::powers() -> impl Iterator<Item = (&str, u32)>` — which must be
   **collected into owned Vecs** at the boundary.
4. **`Rational` is not re-exported.** `lib.rs:51` does `use axeyum_ir::{Rational,
   poly};` but there is no `pub use axeyum_ir::Rational`. The binding crate must
   depend on `axeyum-ir` directly and wrap `Rational` itself (`axeyum-ir/src/
   rational.rs`: `new(i128,i128)` **panics on den==0**, `checked_new` returns
   `Option`, plus `integer/zero/numerator/denominator/is_integer/is_zero/recip/
   checked_{neg,add,sub,mul,div,cmp}`). All CAS coefficient arithmetic is
   **checked `i128`**: overflow surfaces as `None`, never a wrong answer.
5. **`Option::None` almost always means "honest unknown / overflow", not error.**
   This is a hard rule of the project. The binding must NOT map `None` to a
   Python exception uniformly — `None` from `normalize`, `factor`, `integrate`,
   `limit`, `MvPoly::add` etc. means *declined or i128 overflow*. Map to Python
   `None` and let a `Declined` sentinel carry reasons where the Rust type
   provides one (`DeclineReason`, `GeometryDecline`, `AnsatzDecline`).
6. **Panic surface is small but real.** 58 `panic!`/`unwrap`/`expect` sites in
   the 18.8k API region of `lib.rs`; the documented one a caller can trigger is
   `CasExpr::rat(num, 0)` (`lib.rs:436`, "# Panics ... if `den` is zero"). Wrap
   `rat` in `Rational::checked_new` and raise `ValueError` instead.

---

## 1. Core expression types (tier R)

| module | path:line | signature (exact) | type | hazards | Python name | tier | notes |
|---|---|---|---|---|---|---|---|
| lib | `src/lib.rs:129` | `pub enum CasExpr { Const(Rational), Var(String), Add(Vec<CasExpr>), Mul(Vec<CasExpr>), Neg(Box<CasExpr>), Div(Box<CasExpr>,Box<CasExpr>), Pow(Box<CasExpr>,u32), Unary(UnaryFunc,Box<CasExpr>) }` | type | none | `cas.Expr` | R | Not in normal form; `normalize` supplies the canonical form. |
| lib | `src/lib.rs:156` | `pub enum UnaryFunc` (36 variants; 4 carry a `u32`: `BesselJ/BesselI/NthRoot/PolyGamma`) | type | none | `cas.UnaryFunc` | R | `UnaryFunc::name(self) -> String` at `:242`. |
| lib | `:426` | `pub fn int(n: i128) -> Self` | ctor | none | `Expr.int` | R | |
| lib | `:436` | `pub fn rat(num: i128, den: i128) -> Self` | ctor | **panics on den==0** | `Expr.rat` | R | Guard with `Rational::checked_new`. |
| lib | `:442/:448/:454` | `pub fn var(name:&str)/zero()/one() -> Self` | ctor | none | `Expr.var/zero/one` | R | |
| lib | `:460` | `pub fn pow(self, exp: u32) -> Self` | ctor | none | `Expr.pow` / `__pow__` | R | Consumes `self`; exponent is `u32` only — no negative/symbolic powers. |
| lib | `:466-:659` | `ln, exp, sin, cos, tan, atan, sqrt, nth_root(q:u32), cbrt, airy_ai, airy_bi, lambert_w, erf, gamma, digamma, polygamma(n:u32), factorial, bessel_j(n:u32), bessel_i(n:u32), si, ci, ei, li, abs, sign, floor, ceiling` (all `pub fn f(self) -> Self`), plus `pub fn imaginary_unit() -> Self` | ctor | consume `self` | same names | R | 27 unary builders; PyO3 wrappers must `clone()`. |
| lib | `:670` | `pub fn differentiate(&self, var:&str) -> CasExpr` | pure fn | none | `Expr.differentiate` | R | Total — always succeeds. |
| lib | `:728` | `pub fn differentiate_n(&self, var:&str, n:usize) -> CasExpr` | pure fn | none | `Expr.differentiate_n` | R | |
| lib | `:748` | `pub fn substitute(&self, var:&str, replacement:&CasExpr) -> CasExpr` | pure fn | none | `Expr.substitute` | R | |
| lib | `:791` | `pub fn eval(&self, env:&BTreeMap<String,Rational>) -> Option<Rational>` | pure fn | none | `Expr.eval` | R | `None` = unbound var or i128 overflow. |
| lib | `:823-857` | `impl Add/Sub/Mul/Neg/Div for CasExpr` | ctor | consume | `__add__` etc. | R | Only route to build compound exprs without variants. |
| lib | `:858` | `impl std::fmt::Display for CasExpr` | pure fn | none | `__str__` | R | **Not** parseable back. |
| lib | `:984` | `pub struct MultiPoly` (fields private) | type | none | `cas.MultiPoly` | R | Public methods only: `zero()` `:991`, `is_zero()` `:1017`, `to_univariate(&self,var)->Option<Vec<Rational>>` `:1421`, `to_expr()->CasExpr` `:1445`, `eval(&self,env)->Option<Rational>` `:1536`. **No public constructor from terms** — reachable only via `normalize`. |
| lib | `:1555` | `pub fn normalize(expr:&CasExpr) -> Option<MultiPoly>` | pure fn | none | `cas.normalize` | R | The canonicalizer; `None` = outside the polynomial fragment or overflow. |
| lib | `:1580` | `pub struct RatFunc { num: MultiPoly, den: MultiPoly }` | type | none | **do not bind** | — | Public struct with **zero public methods and zero public fields** (`:1587-2024` are all private `fn`). Unusable from outside the crate as it stands. |
| lib | `:2025` | `pub enum Certainty { Certified, DecidableUncertified, Heuristic }` | type | none | `cas.Certainty` | R | Trust tag. |
| lib | `:2036` | `pub enum ZeroTest { Certified { equal: bool, witness: MultiPoly }, Unknown }` | type | none | `cas.ZeroTest` | **C** | The witness IS the certificate: re-`normalize` the difference to re-check. `Unknown` = i128 overflow, never a wrong answer. `certainty()` at `:2054`. |
| lib | `:2169` | `pub fn equal(a:&CasExpr, b:&CasExpr) -> ZeroTest` | producer+checker | none | `cas.equal` | **C** | Decidable zero-test; produces a re-checkable witness in one call. |
| mvpoly | `src/mvpoly.rs:192` | `pub struct MvPoly` | type | none | `cas.MvPoly` | R | The polynomial type **every certificate route speaks**. Bind before anything in §2. |
| mvpoly | `:201/:209/:215/:222` | `zero()`, `constant(Rational)`, `var(&str)`, `from_terms<I: IntoIterator<Item=(Monomial,Rational)>>(I) -> Option<MvPoly>` | ctor | none | `MvPoly.*` | R | `from_terms` returns `Option` (overflow). |
| mvpoly | `:247-:313` | `is_zero`, `term_count`, `terms() -> impl Iterator<Item=(&Monomial,&Rational)>`, `variables()->BTreeSet<String>`, `degree_in(&str)->u32`, `total_degree()->u64`, `leading_coeff(&str)->MvPoly` | pure fn | `terms()` borrows | `MvPoly.*` | R | Collect `terms()` to `Vec<(Monomial, Rational)>` for Python. |
| mvpoly | `:352-:404` | `add/neg/sub/mul(&self,&MvPoly)->Option<MvPoly>`, `pow(&self,u32)->Option<MvPoly>` | pure fn | none | `__add__` etc. | R | `None` = **i128 coefficient overflow**, not an error. |
| mvpoly | `:414-:497` | `derivative_in`, `evaluate(&BTreeMap<String,Rational>)->Option<Rational>`, `divide->Option<(MvPoly,MvPoly)>`, `divides->Option<bool>`, `exact_div->Option<MvPoly>` | pure fn | none | same | R | |
| mvpoly | `:544/:565/:669` | `gcd(&MvPoly)->Option<MvPoly>`, `gcd_cost(&MvPoly)->GcdCost`, `squarefree(&str)->Option<Vec<(MvPoly,u32)>>` | pure fn | none | same | P | |
| mvpoly | `:597/:636` | `to_cas_expr(&self)->CasExpr`, `from_cas_expr(&CasExpr)->Option<MvPoly>` | pure fn | none | `MvPoly.to_expr/from_expr` | R | The bridge between the two polynomial worlds. |
| mvpoly | `:61` | `pub struct Monomial` — `one()`, `from_powers(&[(&str,u32)])`, `total_degree()->u64`, `exponent_of(&str)->u32`, `powers()->impl Iterator<Item=(&str,u32)>` | type/ctor | `powers()` borrows | `cas.Monomial` | R | |

---

## 2. Certificate routes — producer / certificate / independent checker (tier C)

These are the crate's identity: **untrusted producer, trusted small checker.** The
binding must expose them as two objects, never one `prove()` that returns a bool.

### 2.1 Gröbner cofactors (`groebner_cert.rs`) — the substrate of the geometry route

| item | path:line | signature | role |
|---|---|---|---|
| producer | `groebner_cert.rs:298` | `pub fn reduce_with_cofactors(generators: &[MvPoly], target: &MvPoly, limits: Limits) -> CofactorOutcome` | P |
| producer | `:321` | `pub fn unit_ideal_cofactors(generators: &[MvPoly], limits: Limits) -> CofactorOutcome` | P (weak Nullstellensatz) |
| producer | `:339` | `pub fn reduce_many_with_cofactors(generators: &[MvPoly], targets: &[MvPoly], limits: Limits) -> Vec<CofactorOutcome>` | P |
| producer | `:354` | `pub fn reduce_many_with_cofactors_traced(...) -> (Vec<CofactorOutcome>, ReductionStats)` | P + telemetry |
| certificate | `:142` | `pub enum CofactorOutcome { Reduced { cofactors: Vec<MvPoly>, remainder: MvPoly }, Declined(DeclineReason) }` | C |
| budgets | `:65` | `pub struct Limits { reduction_steps: u64, pair_iterations: u64, basis_size: usize, poly_terms: usize, order: MonomialOrder }`; `Limits::fast()` `:91` = `(20_000, 4_000, 64, 512, Lex)`; `Default = fast()` | — |
| decline | `:114` | `pub enum DeclineReason` with `is_ceiling(self) -> bool` `:135` — distinguishes a **tripped budget** from an **i128 overflow**. Expose both; a frontier theorem that "declines" is uninterpretable otherwise. | — |
| telemetry | `:171` | `pub struct ReductionStats { pairs_processed, pairs_queued, basis_extensions, pairs_coprime_lead: u64, max_basis_len, max_poly_terms: usize, reduction_steps_spent: u64 }` — advisory only, recorded on success too | — |

**No independent checker fn here.** The check is arithmetic the caller performs:
`Σ cofactors[i]·generators[i] + remainder == target`, via `MvPoly::mul/add`. The
binding should ship that as `CofactorOutcome.check(generators, target) -> bool`
implemented in Rust from `MvPoly` primitives, and the exit status must depend on
the comparison. Nothing about ideal membership may be claimed on `Declined`.

### 2.2 Geometry (`geometry_certify.rs` / `geometry_check.rs` / `geometry_json.rs`)

The most complete producer/checker/serialize triple in the crate.

| item | path:line | signature | notes |
|---|---|---|---|
| producer | `geometry_certify.rs:777` | `pub fn certify(problem: &GeometryProblem, limits: Limits) -> ProofOutcome` | Gröbner-saturation route; searches the smallest condition subset. |
| producer | `:941` | `pub fn certify_by_linear_elimination(problem: &GeometryProblem, handover: Option<Limits>) -> ProofOutcome` | linear-block route, optional Gröbner handover. |
| producer | `:1065` | `pub fn certify_any_route(problem: &GeometryProblem, limits: Limits) -> ProofOutcome` | **the front door** — bind this. |
| budgets | `:664` | `pub fn geometry_limits() -> Limits` | calibrated to the corpus; order defaults to `DegRevLex`. |
| certificate | `:529` | `pub struct GeometryCertificate { id, title, statement: String, coordinate_gloss: Vec<(String,String)>, coordinates: Vec<String>, hypotheses: Vec<Constraint>, saturations: Vec<Saturation>, generators: Vec<MvPoly>, conclusions: Vec<CertifiedConclusion>, degenerate_witnesses: Vec<DegenerateWitness>, generic_witnesses: Vec<GenericWitness> }` | all fields `pub`; `Debug` only. |
| outcome | `:558` | `pub enum ProofOutcome { Certified(Box<GeometryCertificate>), NotInSaturatedIdeal { conclusion_id: String, remainder: MvPoly }, Declined(GeometryDecline) }` | three-way, not bool. |
| decline | `:582` | `pub enum GeometryDecline { Reduction(DeclineReason), TooManyConditions, UnverifiedWitness, UndividableMultiplier, RefutedByOwnWitness }` | `RefutedByOwnWitness` = **the theorem as stated is false**; must surface distinctly in Python. |
| **checker** | `geometry_check.rs:103` | `pub fn check_certificate(certificate: &GeometryCertificate, options: &CheckOptions) -> GeometryVerdict` | independent re-derivation. |
| verdict | `geometry_check.rs:62` | `pub enum GeometryVerdict { Verified(GeometryReport), Rejected(String) }`, `is_verified()` `:72` | |
| report | `geometry_check.rs:43` | `pub struct GeometryReport { conclusions_checked, degenerate_witnesses_checked, generic_witnesses_checked, numeric_points_checked: usize, conditions_used: Vec<String> }` | counts, not adjectives — expose all five, they are what makes the checker falsifiable. |
| check opts | `geometry_check.rs:79` | `pub struct CheckOptions { numeric_points: usize, half_range: i128 }`, `Default = { 24, 6 }` | |
| JSON | `geometry_json.rs:41 / :282` | `pub fn to_json(&GeometryCertificate) -> String` / `pub fn from_json(&str) -> Result<GeometryCertificate, String>` | deterministic, hand-rolled; `FORMAT = "axeyum-geometry-certificate"` `:30`, `VERSION: i128 = 1` `:33`. Also `condition_of(&Saturation) -> Condition` `:399`. |
| problems | `geometry_certify.rs:478` | `pub struct GeometryProblem { id, title, statement, coordinate_gloss, hypotheses: Vec<Constraint>, nondegeneracy: Vec<Condition>, conclusions, degenerate_witnesses, generic_witnesses }` | |
| builders | `geometry_certify.rs:73-231` | `Pt::free/fixed/sub/add/scale`; free fns `det, dot, dist_sq, collinear, parallel, perpendicular, equidistant, concyclic, midpoint, centroid, same_point` → `Option<MvPoly>` | the DSL for stating a theorem; bind all of them. `Constraint::new(id,desc,poly)` `:250`, `Condition::new` `:278`. |
| witnesses | `:398/:469` | `DegenerateWitness::rational(...)`, `is_gaussian()`, `point() -> Option<BTreeMap<String,Gaussian>>`; `GenericWitness { description, assignment }` | `Gaussian` at `:312` with `checked_add/checked_mul`. |
| corpus | `geometry_corpus.rs:75 / :190` | `pub fn corpus() -> Vec<GeometryProblem>` / `pub fn frontier() -> Vec<GeometryProblem>` | the committed test population — ideal Python fixture source. |
| helper | `:700 / :723` | `searchable_subsets(&GeometryProblem) -> Vec<Vec<usize>>`, `subset_is_refuted(&GeometryProblem,&[usize]) -> bool` | |
| const | `:624` | `pub const INVERSE_PREFIX: &str = "Zinv"` | saturation variable prefix; determinism-relevant. |

### 2.3 Creative telescoping / Zeilberger (`telescoping*.rs`)

| item | path:line | signature | notes |
|---|---|---|---|
| producer | `telescoping.rs:547` | `pub fn zeilberger(term: &HyperTerm, shift_var: &str, sum_var: &str, limits: &Limits) -> TelescopingOutcome` | doc says explicitly: result is **not** verified. |
| outcome | `:533` | `pub enum TelescopingOutcome { Found(Box<TelescopingCertificate>), Declined }` | |
| certificate | `:456` | `pub struct TelescopingCertificate { term: HyperTerm, shift_var: String, sum_var: String, recurrence: Vec<MvPoly>, certificate_numerator: MvPoly, certificate_denominator: MvPoly }`, `order() -> usize` `:474` | |
| budgets | `:487` | `pub struct Limits { max_order, max_unknowns, max_poly_terms: usize, max_certificate_degree, max_parameter_degree: u32, max_dispersion: i64 }`; `Limits::classical()` `:513` = `(2, 8, 400, 4_000, 32, 6)`; `Default = classical()` | none of these is a degree *ansatz*: starving one makes the search decline, never mislead. |
| term DSL | `:122/:220/:252/:1361/:1375` | `LinearForm::new(&[(&str,i64)], i64)`, `Factor`, `HyperTerm::new(Vec<Factor>)`, `factorial_factor(LinearForm, i32) -> Factor`, `binomial_factors(&LinearForm,&LinearForm,i32) -> Vec<Factor>` | bind all; this is how a summand is stated. `shift_variable(&MvPoly,&str,i64)->Option<MvPoly>` `:428`. |
| **checker** | `telescoping_check.rs:141` | `pub fn check_certificate(certificate: &TelescopingCertificate, options: &CheckOptions) -> Verdict` | re-derives shift ratios with its own implementation; shares no code with the producer. |
| verdict | `:123` | `pub enum Verdict { Verified(CheckReport), Rejected(Vec<String>) }`, `is_verified()` `:134` | |
| report | `:107` | `pub struct CheckReport { ratio_samples, pointwise_samples, certificate_poles_in_window, recurrence_samples: usize }` | four counts; a zero count is the fail-signal. |
| check opts | `:69/:86/:98` | `pub struct CheckOptions { samples: BTreeMap<String,Vec<i64>>, window: (i64,i64), min_ratio_samples: usize }`; `CheckOptions::over(shift_var,&[i64],(i64,i64))`, `.with(var,&[i64])` | builder chain; expose both. |
| closed form | `:1202 / :1316` | `check_closed_form(cert, closed_form: &HyperTerm, base: i64, opts) -> Result<ClosedFormReport, Vec<String>>` and `check_closed_form_symbolic(...) -> Result<SymbolicClosedFormReport, Vec<String>>` | `ClosedFormReport` `:1175`, `SymbolicClosedFormReport` `:1277`. |
| eval | `:728/:800/:947/:1117` | `evaluate_term(&HyperTerm,&BTreeMap<String,i64>)->Option<BigRational>`, `evaluate_poly`, `evaluate_term_symbolic->Option<SymbolicValue>`, `symbolic_window_sum(...)->Result<(SymbolicValue,usize),String>` | `SymbolicValue` `:862` with `zero/is_zero/coefficient/is_rational/gamma_count/checked_add`. Internal caps: `MAX_CONCRETE_POWER = 4_096`, `MAX_SYMBOLIC_DISPLACEMENT = 32` (private consts). |
| JSON | `telescoping_json.rs:84 / :302` | `to_json(&CertificateDocument) -> String` / `from_json(&str) -> Result<CertificateDocument,String>` | `FORMAT` `:41`, `VERSION: i128 = 1` `:44`; `CertificateDocument { id, title, certificate, options, closed_form: Option<ClosedFormClaim> }` `:49`; `ClosedFormClaim { term, base: i64, symbolic: bool }` `:65`. |
| alias | `:1547` | `pub type Form = LinearForm;` | |

### 2.4 Sum-of-squares / Positivstellensatz (`sos.rs`, `sos/`)

There is **no search producer here** — the artifacts are authored by hand or by an
external SDP and re-derived by the checker. The Python tier is therefore
checker-first.

| item | path:line | signature | notes |
|---|---|---|---|
| certificate atom | `sos.rs:86` | `pub struct SosSum`; `new(Vec<(Rational,MvPoly)>) -> Result<Self,String>` `:98`, `squares()->&[(Rational,MvPoly)]`, `len`, `is_empty`, `expand()->Result<MvPoly,String>` `:136` | `new` validates coefficients; `Result<_,String>` → raise `ValueError`. |
| dynamics | `:155` | `pub struct VectorField`; `lie_derivative(&self,&MvPoly)->Result<MvPoly,String>` `:172`, `is_closed()->bool` `:197` | |
| problems | `:213/:253/:300` | `LyapunovProblem { id, description, system, v, lower, upper, decay, naive_failure }`, `BarrierProblem { id, description, system, initial, unsafe_region, barrier, initial_witness, unsafe_witness }`, `PsdNotSosProblem { id, description, variables, form, multiplier, half_degree }` | every field `pub`. |
| certificates | `:238/:276/:318` | `LyapunovCertificate { lower_gap, upper_gap, decrease }`, `BarrierCertificate { initial_multipliers, initial_margin, initial_gap, unsafe_multipliers, unsafe_margin, unsafe_gap, decrease }`, `PsdNotSosCertificate { multiplied: SosSum, dual: BTreeMap<Monomial,Rational> }` | |
| artifact | `:329` | `pub enum SosArtifact { Lyapunov(LyapunovProblem,LyapunovCertificate), Barrier(..), PsdNotSos(..) }`; `id()->&str` `:341`, `kind()->&'static str` `:352` | |
| **checker** | `sos.rs:414` → `sos/check.rs:46` | `pub fn check(artifact: &SosArtifact) -> Result<CheckReport,String>` / `pub fn check_artifact(...)` | front door. |
| checkers | `sos/check.rs:64/:282/:447` | `check_lyapunov(&LyapunovProblem,&LyapunovCertificate)`, `check_barrier(...)`, `check_psd_not_sos(...)` — each `-> Result<CheckReport,String>` | per-kind. |
| report | `sos.rs:373/:364` | `pub struct CheckReport { obligations: Vec<Obligation>, rate: Option<Rational> }`, `len()`, `is_empty()`; `Obligation { name, detail: String }` | `is_empty()` exists precisely because "a checker that discharges no obligation and exits zero is indistinguishable from one that passed" — **the Python wrapper must assert non-empty**. `rate` = certified exponential decay rate for Lyapunov. |
| helper | `sos.rs:427` | `pub fn sum_of_variable_squares(&[String]) -> Result<MvPoly,String>` | the checker builds the norm itself; expose so callers can reproduce. |
| psd | `sos/psd.rs:24/:52` | `pub enum Psd`, `pub fn is_psd(matrix: &[Vec<Rational>]) -> Psd` | exact rational PSD test. |
| corpus | `sos/corpus.rs:28/:38/:61/:141/:233` | `all() -> Vec<SosArtifact>`, `by_id(&str) -> Option<SosArtifact>`, `damped_rotation_lyapunov()`, `energy_barrier_reachability()`, `motzkin_psd_not_sos()` | |
| JSON | `sos/json.rs:37/:346` | `to_json(&SosArtifact)->String`, `from_json(&str)->Result<SosArtifact,String>` | |
| const | `sos/check.rs:39` | `pub const REPLAY_POINTS: usize = 16` | |

### 2.5 GF(2) irreducibility artifacts (`gf2.rs`, `gf2_artifact.rs`, `gf2_independent.rs`, `gf2_shard.rs`)

The one route with **two independent checkers** and a real on-disk artifact format.

| item | path:line | signature | notes |
|---|---|---|---|
| producer | `gf2.rs:1710` | `pub fn certify_irreducible(polynomial: &Gf2Poly, limits: Gf2Limits) -> Result<Option<IrreducibilityCertificate>, Gf2Error>` | `Ok(None)` = reducible (decided); `Err` = budget/shape. |
| certificate | `gf2.rs:1692` | `pub struct IrreducibilityCertificate` (+ `FrobeniusReduction` `:1672`, `RabinBezout` `:1681`) | portable Rabin certificate. |
| **checker 1** | `gf2.rs:1785` | `pub fn check_irreducible_certificate(&IrreducibilityCertificate, Gf2Limits) -> Result<(),Gf2Error>` | packed-word checker. |
| **checker 2** | `gf2_independent.rs:131` | `pub fn check_irreducible_certificate_independent(&IrreducibilityCertificate, IndependentCheckLimits) -> Result<(),Gf2Error>` | dense re-implementation; expose **both** and require both to pass. |
| artifact | `gf2_artifact.rs:49` | `pub struct HalfDegreeArtifact { id: String, producer: String, certificate: IrreducibilityCertificate }` | `producer` records the untrusted producer's identity — the tier boundary, made data. |
| serialize | `:134/:160` | `to_canonical_json(&HalfDegreeArtifact, ArtifactLimits) -> Result<String,ArtifactError>` / `from_canonical_json(&str, ArtifactLimits) -> Result<HalfDegreeArtifact,ArtifactError>` | the only **serde**-backed route in the crate. |
| validate | `:185` | `pub fn validate(&HalfDegreeArtifact, ArtifactLimits) -> Result<(),ArtifactError>` | fail-closed. |
| budgets | `:22` | `ArtifactLimits { max_bytes: 32 MiB, max_id_bytes: 256, max_producer_bytes: 256, primary: Gf2Limits, independent: IndependentCheckLimits }` | |
| consts | `:14/:16/:18` | `FORMAT = "axeyum-gf2-half-degree-irreducible"`, `VERSION: u32 = 1`, `STATEMENT = "monic irreducible f over GF(2), deg(f)=n, deg(f-x^n)<=floor(n/2)"` | |
| search | `gf2_search.rs:95` | `search_sparse_half_degree(degree: usize, SparseSearchLimits) -> Result<SparseSearchOutcome, SparseSearchError>` | untrusted producer. |
| shards | `gf2_shard.rs:150/:163/:178/:256` | `to_canonical_manifest_json`, `from_canonical_manifest_json`, `check_shard_directory(&Path, ArtifactLimits) -> Result<ShardCheckSummary,ShardError>`, `sha256_hex(&[u8]) -> String` | filesystem-touching; gate behind an explicit Python opt-in. |
| poly | `gf2.rs:16-130` | `Gf2Poly::{from_words, from_exponents(&[usize],Gf2Limits)->Result, zero, one, x, words, degree->Option<usize>, is_zero, coefficient, exponents, is_half_degree_shaped}` | `Gf2Context` `:1461` carries the work counter (`add/multiply/square/div_rem/gcd`). |

### 2.6 Sturm / interval arithmetic (checker-shaped pure fns, no certificate object)

| item | path:line | signature | notes |
|---|---|---|---|
| sturm | `sturm.rs:92` | `pub fn count_real_roots_in(p: &[Rational], lower: Rational, upper: Rational) -> Option<usize>` | exact Sturm count; `None` = overflow. |
| sturm | `:135` | `pub fn isolate_real_roots(p: &[Rational]) -> Option<Vec<(Rational,Rational)>>` | |
| sturm | `:220` | `pub fn approximate_real_roots(p: &[Rational], width: Rational) -> Option<Vec<Rational>>` | `width` is the caller's explicit resource limit. |
| interval | `interval_arith.rs:25` | `pub struct Interval` (Copy); `new(a,b)->Option<Interval>` (`None` when `a>b`), `degenerate(a)`, `lower/upper/width/midpoint`, `contains/contains_interval`, `add/sub/mul/neg/div/pow/intersection/hull/abs` all `-> Option<Interval>` | `div` returns `None` when the divisor straddles 0 — that is the soundness guard, not an error. |
| interval | `:245` | `pub fn evaluate_polynomial(coeffs: &[Rational], x: &Interval) -> Option<Interval>` | the enclosure primitive. |

### 2.7 Ancillary certificate-adjacent routes

| item | path:line | signature | notes |
|---|---|---|---|
| ansatz | `cofactor_ansatz.rs:156` | `pub fn cofactors_by_ansatz(generators:&[MvPoly], target:&MvPoly, limits: AnsatzLimits) -> AnsatzOutcome` | producer that **self-verifies**: re-expands before returning. `AnsatzOutcome { Solved{cofactors,degree}, NotInDegree(u32), Declined(AnsatzDecline) }` `:100`. `NotInDegree` is a *decision* about the degree slice, never about the ideal — must not render as "unknown". `AnsatzLimits::geometry()` `:78`. |
| linear elim | `linear_elim.rs:575/:585/:449/:190` | `eliminate(&[MvPoly],&MvPoly)->Option<LinearElimination>`, `eliminate_blocks(..., Vec<LinearBlock>)`, `detect_linear_blocks(...)->Vec<LinearBlock>`, `combination(&[MvPoly],&[MvPoly])->Option<MvPoly>` | `combination` is the re-expansion checker for any cofactor list. |
| integral | `lib.rs:13431/:13468/:13444` | `pub struct CertifiedIntegral { antiderivative: CasExpr, certificate: ZeroTest }`; `pub fn integrate(&CasExpr,&str)->Option<CertifiedIntegral>`; `is_certified(&self)->bool` | producer + certificate in one value: the certificate is `equal(d/dx antiderivative, integrand)`. Bind `certificate` as a first-class `ZeroTest`, not a bool. |
| integral | `lib.rs:13671/:14510/:13686` | `pub struct DefiniteIntegral { value, antiderivative: CasExpr, certificate: ZeroTest }`; `definite_integrate(...)`; `is_certified()` | `DefiniteIntegral` derives only `Debug, Clone` (no `PartialEq`). |
| derivative | `lib.rs:13368` | `pub fn prove_derivative(expr:&CasExpr, var:&str, claimed:&CasExpr) -> ZeroTest` | direct checker. |
| moments | `lib.rs:5755/:5827/:5844/:6175/:6225` | `CertifiedSquaredBinomialFallingMoment` + `prove_squared_binomial_falling_moment(u32)`, `CertifiedSquaredBinomialMoment` + `prove_squared_binomial_moment(u32)`, `prove_wz_sum(...)`; both have `is_certified()` (`:5768`, `:5859`) | caps: `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT = 255` `:5750`, `MAX_PROVED_SQUARED_BINOMIAL_MOMENT = 35` `:5838`. |
| groebner | `groebner.rs:394/:448/:496/:106` | `reduce(&MvPoly,&[MvPoly])->Option<MvPoly>`, `groebner_basis(&[MvPoly])->Option<Vec<MvPoly>>`, `ideal_contains(&[MvPoly],&MvPoly)->Option<bool>`, `pub enum MonomialOrder` | **unbudgeted** (`Option` on overflow only) — prefer `groebner_cert` for anything user-facing. |

---

## 3. Remaining public surface (terse; tier P unless noted)

`lib.rs` exposes ~135 further top-level `pub fn`s, essentially all
`fn(&CasExpr, …) -> Option<CasExpr>` pure functions. Grouped:

- **Simplification (tier R):** `simplify` `:6714`, `trigsimp` `:6774`,
  `simplify_under_assumptions(&CasExpr,&Assumptions)` `:8367`, `simplify_radicals`
  `:8445`, `evaluate_trig` `:8683`, `expand` `:13279` (`Option`), `collect` `:13307`,
  `cancel` `:13353`, `apart` `:6516`, `rewrite_exp` `:9333`, `expand_log` `:9386`,
  `expand_trig` `:9409`, `logcombine` `:9638`.
- **Numerics (tier R):** `evalf(&CasExpr, &[(&str,f64)]) -> Option<f64>` `:9840`,
  `rationalize(f64, max_denominator: i128) -> Option<Rational>` `:9691`,
  `nsimplify(f64, i128) -> Option<CasExpr>` `:9733`. `evalf`'s `bindings` slice of
  `(&str, f64)` needs an owned-dict conversion at the boundary.
- **Polynomials:** `degree, coeff, leading_coeff, poly_gcd, poly_lcm, content,
  primitive_part, is_irreducible, poly_div, factor` (`:2354`–`:2704`),
  `factor_expr`/`factor_univariate_over_q` (`factor_int.rs`), `resultant` `:7914`,
  `discriminant` `:7956`, `cyclotomic_polynomial` `:8252`.
- **Solving:** `solve` `:3544`, `solve_linear_system` `:2781`,
  `solve_polynomial_system` `:3210`, `solve_polynomial_inequality` `:3675`
  (+`InequalityOp` `:3630`, `RealInterval` `:3644`), `real_root_intervals` `:3863`,
  `count_real_roots` `:3872`, `approximate_real_roots` `:3887`, `real_roots ->
  Option<Vec<AlgebraicReal>>` `:3898`.
- **ODE/recurrence:** `dsolve_euler_cauchy, dsolve_homogeneous,
  dsolve_inhomogeneous, dsolve_first_order_linear, dsolve_separable, dsolve_exact,
  dsolve_bernoulli, apply_initial_conditions, solve_recurrence` (`:3982`–`:4848`).
- **Sums/products:** `definite_sum, infinite_sum, finite_product, sum_polynomial`
  (`:5130`–`:6459`), `gosper_sum`/`geometric_power` (`gosper.rs:105/:132`),
  `residue` `:6615`.
- **Linear algebra:** `Matrix` (`matrix.rs`), `matrix_rank, trace,
  characteristic_polynomial, companion_matrix, eigenvalues, eigenvectors,
  null_space, diagonalize, matrix_exp, linear_ode_system, jordan_form,
  minimal_polynomial, qr_decomposition, cholesky_decomposition, gram_schmidt,
  hermite_normal_form, smith_normal_form` (`:6822`–`:8206`, `normalforms.rs`).
- **Vector calculus:** `gradient, jacobian, divergence, curl, hessian, laplacian,
  wronskian, dot, cross, norm` (`:7610`–`:8206`).
- **Transforms/series:** `series`/`series_at` (`series.rs:194/:331`),
  `laplace_transform, inverse_laplace, z_transform, inverse_z_transform,
  laurent_series, series_reversion` (`:12044`–`:13207`), `limit` `:10333` +
  `LimitPoint` `:10318`.
- **Integration:** `iterated_integral, numeric_integrate, improper_integrate,
  fourier_series, average_value, root_mean_square` (`:14650`–`:15712`).
- **Complex:** `conjugate, real_part, imaginary_part, modulus, argument,
  roots_of_unity` (`:10214`–`:10300`).
- **Modules:** `assumptions` (`Assumptions::new/positive/negative/nonnegative/
  nonzero/sign_of/is_*`, `Sign`), `algebraic` (`AlgebraicReal` +
  `real_roots(&[Rational])`), `sets` (`Interval` — **name-collides with
  `interval_arith::Interval`, disambiguate in Python**, `RealSet`, `finite_set`),
  `permutation` (`Permutation`), `orthopoly` (8 families), `hyperbolic` (9 fns),
  `special` (`gamma, beta, zeta, polygamma_at_one, dirichlet_eta,
  dirichlet_lambda`), `stats` (`mean, median, mode, variance, covariance,
  sample_variance`) + `standard_deviation/sample_standard_deviation/correlation`
  in `lib.rs`, `ntheory`/`ntheory_advanced`/`ntheory_more`, `combinatorics`,
  `approx` (`lagrange_interpolation, newton_divided_differences, pade,
  pade_fraction`), `boolean` (`BoolExpr`), `gfp` (`add/sub/mul/scale/neg/div_rem/
  gcd/pow_mod/is_irreducible/factor_berlekamp/roots` over `&[i128]` mod p),
  `gf2_extension` (14 trace/closed-form producers, `Result`-returning, all
  budget-carrying — tier P at best; large report structs, `Debug` only).

---

## 4. `examples/` — the proven entry points

13 examples; these are the call sequences known to compile and run, and are the
best template for the Python API shape. Prebuilt binaries live under
`target/release/examples/`.

| example | library functions it calls |
|---|---|
| `cas_tour.rs` | `CasExpr::{var,int,pow,exp,sin}`, `expand`, `differentiate`, `integrate` + `CertifiedIntegral::is_certified`, `limit`/`LimitPoint::Finite`, `series`, `series_at`, `factor`, `factor_expr`, `apart`, `cancel`, `equal`/`ZeroTest`, `solve`, `solve_polynomial_inequality`/`InequalityOp`, `real_root_intervals`, `resultant`, `discriminant`, `gosper_sum`, `sum_polynomial`, `gradient`, `eigenvectors`, `minimal_polynomial`, `Matrix`, `dsolve_homogeneous`, `dsolve_inhomogeneous`, `definite_integrate`, `evaluate_trig`, `simplify_radicals`, `standard_deviation`, `ntheory`, `ntheory_advanced`, `stats`, `axeyum_ir::Rational` |
| `certified_calculus.rs` | `CasExpr::{var,int,pow}`, `expand`, `differentiate`, `equal` + `ZeroTest::Certified{equal,witness}`, `integrate`/`is_certified`, `cancel` |
| `emit_geometry_certificates.rs` | `geometry_corpus::corpus`, `geometry_certify::certify_any_route`, `geometry_check::check_certificate`, `geometry_json::to_json` |
| `emit_sos_certificates.rs` | `sos::corpus`, `sos::check`, `sos::json` |
| `emit_telescoping_certificates.rs` | `telescoping::{HyperTerm,LinearForm,zeilberger,Limits}`, `telescoping_check::{CheckOptions,check_certificate}`, `telescoping_json::to_json`, `mvpoly::MvPoly` |
| `sos_certify.rs` | `sos::*`, `sos::check` |
| `geometry_linear_route.rs` | `geometry_certify`, `geometry_check`, `geometry_corpus`, `groebner_cert`, `linear_elim::eliminate`, `MvPoly` |
| `geometry_cofactor_routes.rs` | `cofactor_ansatz`, `geometry_certify`, `geometry_corpus`, `groebner_cert`, `linear_elim`, `MvPoly` |
| `geometry_obstruction.rs` | `geometry_certify`, `geometry_corpus`, `groebner_cert::ReductionStats`, `groebner::MonomialOrder`, `MvPoly` |
| `geometry_order_audit.rs` | `geometry_certify::certify`, `geometry_corpus::corpus`, `geometry_json::to_json`, `groebner::MonomialOrder` |
| `geometry_probe.rs` | `geometry_certify::certify`, `geometry_corpus`, `groebner_cert`, `ideal_contains`, `MonomialOrder` |
| `pappus_condition_subsets.rs` | `geometry_certify::GeometryProblem`, `geometry_corpus::corpus`, `MvPoly` |
| `telescoping_search_cost.rs` | `telescoping`, `telescoping_check`, `MvPoly` |

Integration tests that pin the artifact formats (also good binding fixtures):
`tests/geometry_certificate_artifacts.rs`, `tests/sos_certificate_artifacts.rs`,
`tests/telescoping_certificate_artifacts.rs`, `tests/telescoping_identities.rs`,
`tests/geometry_encoding_agreement.rs`, `tests/gf2_artifact_cli.rs`.
Seven `src/bin/axeyum-gf2-*.rs` CLIs show the GF(2) artifact/shard flows.

---

## 5. Recommended `axeyum.cas` shape

- `axeyum.cas` (tier R): `Expr`, `UnaryFunc`, `MvPoly`, `Monomial`, `MultiPoly`,
  `Rational`, `normalize`, `equal`, `simplify`, `simplify_under_assumptions`,
  `simplify_radicals`, `evaluate_trig`, `evalf`, `expand`, `factor`, `integrate`,
  `differentiate`, `Assumptions`, `ZeroTest`, `Certainty`.
- `axeyum.cas.certify` (tier C): one submodule per route, each exporting
  `produce(...) -> Outcome` and `Certificate.check(options) -> Verdict`, with the
  `Verified(report)` counts reachable from Python. Do not collapse a verdict to
  `bool`: `is_verified()` plus the report counts are what make the checker
  falsifiable, and every route's `Declined`/`Rejected` variant carries a reason
  the binding must not discard.
- Skip `RatFunc` (no public surface) and `groebner::{reduce, groebner_basis,
  ideal_contains}` (unbudgeted) for a first cut.
