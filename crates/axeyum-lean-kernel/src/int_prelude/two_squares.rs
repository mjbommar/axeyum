//! **Sums of two squares over ℤ** — the Brahmagupta–Fibonacci identity, the
//! predicate it makes multiplicative, and the mod-4 boundary refutation
//! (W3-10, ADR-1633).
//!
//! ## What this file is for
//!
//! Fermat's two-square theorem ("an odd prime `p ≡ 1 (mod 4)` is a sum of two
//! squares") is a *descent*: from one representation `m·p = a² + b²` with
//! `0 < m < p` you manufacture a strictly smaller `m'`. Two of that descent's
//! three ingredients are cheap and reusable on their own, and they are what
//! this module lands:
//!
//! - the **composition law** — `(a²+b²)(c²+d²)` is again a sum of two squares,
//!   in two conjugate forms. The descent uses the second form
//!   ([`declare_brahmagupta_fibonacci_swap`]) because that is the one whose
//!   two summands are each divisible by `m` when `c ≡ a` and `d ≡ b (mod m)`;
//!   the first form is the one every textbook states.
//! - the **congruence core** — `m ∣ ac+bd` and `m ∣ ad−bc` under exactly those
//!   hypotheses (`declare_modeq_descent_cross_terms`), which is the step that
//!   makes the descent's division by `m` legal.
//!
//! The third ingredient — choosing `c`, `d` in `(−m/2, m/2]` and bounding
//! `m' = (c²+d²)/m < m` — is **not** here; see the "What is not here" section
//! and `docs/plan/status/two-squares-2026-09-05.md` for the measured size.
//!
//! ## Why the identity goes through the ring producer
//!
//! `(a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²` is a pure commutative-ring identity
//! over ℤ in four variables, so it is exactly `ring::int`'s fragment
//! (ADR-1582): `neg`/`sub` are ring operations there, not declined atoms. The
//! proof term is **searched for and emitted, never written by hand** — which
//! is the point of ADR-0601's producer discipline, and is why this file
//! contains no `mul_comm`/`left_distrib` chain at all. Measured: both forms
//! are admitted by `ring::int::declare` at arity 4 on the first attempt.
//!
//! ## Why `IsSumOfTwoSquares` is a `Definition` and not an inlined `∃∃`
//!
//! The composition law, the refutation and (eventually) the descent all
//! quantify over the same double existential. Inlining it would make each
//! statement a different-looking term and defeat `shape_search --const`, which
//! is the retrieval route this repository actually uses
//! (`docs/contributor-guide/finding-existing-lemmas.md`). A `Definition` also
//! gives the fact ledger one name to cite.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong**, so
//! `two_squares_tests` settles what
//! `IsSumOfTwoSquares` MEANS by reduction at concrete small arguments: `5`,
//! `13` and `17` are witnessed, and `3`, `7` and `11` are refuted through the
//! mod-4 theorem. The witnesses are the smallest available (`1²+2²`, `2²+3²`,
//! `1²+4²`) because `Nat` numerals here are unary and cost is superlinear in
//! the largest magnitude formed — no test in this file forms a square above
//! `17`.
//!
//! ## The mod-4 refutation
//!
//! `n ≡ 3 (mod 4)` ⟹ `n` is not a sum of two squares. Every square is `0` or
//! `1` mod `4` (`declare_sq_modeq_four_zero_or_one`), so a sum of two is
//! `0`, `1` or `2` — never `3`. The parity split is
//! `Nat.even_or_odd_exists` read at `natAbs n` (`Int.Even n` is *defined* as
//! `Nat.Even (natAbs n)`, `parity.rs`), and each branch is closed by
//! `Int.ediv_two_mul_two_of_even` / `Int.ediv_two_mul_two_add_one_of_odd`
//! turning `n` into `2k` / `2k+1` with `k := n / 2` — an explicit definable
//! witness, so no existential is opened. The `4 ∣ …` step is
//! `Int.modEq_add_mul_left`, which is unconditional in the modulus and
//! therefore needs no `0 < 4` side condition.
//!
//! The three impossible residues are refuted by **reduction**: `ModEq 4 r 3`
//! unfolds to `Eq Int (emod r 4) (emod 3 4)`, both sides closed numerals, and
//! `Int.emod` is a structural `Int.rec`/`Nat.rec` definition (`division.rs`),
//! so the kernel computes them. `0 ≠ 3`, `1 ≠ 3`, `2 ≠ 3` then come from
//! `Int.natAbs` injectivity plus `Nat.ne_of_beq_eq_false` — the same route
//! `mult_order_tests.rs` uses, lifted here into the prelude because the
//! theorem needs it, not only a test.
//!
//! ## What is NOT here, and why
//!
//! `Int.fermatTwoSquares` (`p` prime, `p ≡ 1 (mod 4)` ⟹ `IsSumOfTwoSquares
//! (ofNat p)`) does **not** land. The entry into the descent does
//! (`declare_exists_mul_isSumOfTwoSquares_of_residue`: from
//! `Int.firstSupplementaryLawResidue`'s witness `x` with `x² ≡ −1 (mod p)`,
//! `p ∣ x²+1`, so some multiple of `p` IS a sum of two squares). What is
//! missing is the *bounded* choice of representatives and the strict decrease
//! of the measure — an ordering argument over `Int` (`|c| ≤ m/2 ⟹ c² ≤ m²/4`,
//! then `c²+d² ≤ m²/2 < m²`) for which this prelude has no `Int` absolute-value
//! order lemmas at all: `natAbs` exists and `Int.le`/`Int.lt` exist, but
//! `natAbs_le_iff`, `mul_le_mul` over ℤ and `sq_le_sq` do not. That is the
//! sized obstruction, not the descent's algebra.

use super::euler::{int_exists_elim, int_exists_intro};
use super::ops::IntDev;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.IsSumOfTwoSquares`: strictly above every height this
/// prelude uses elsewhere (`bezout_witnesses::INT_GCD_AB_HEIGHT`, 32, is the
/// previous high point), following the same "one monotone sequence over the
/// whole prelude" convention `ring.rs`'s `RING_HEIGHT` documents.
const SUM_OF_TWO_SQUARES_HEIGHT: u16 = 33;

// ============================================================================
// local plumbing
// ============================================================================

/// `Exists.{1} Int predicate`. A nine-line local mirror of `euler.rs`'s own
/// private `int_exists`; copied rather than re-exported so this module adds
/// no edit to a file other lanes are also touching.
pub(super) fn int_exists(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let exists = d.kernel().const_(name, vec![one]);
    d.apply(exists, &[int_ty, predicate])
}

/// `fun (b : Int) => Eq Int n (add (mul a a) (mul b b))` — the inner body of
/// `IsSumOfTwoSquares n` with the first square already fixed at `a`.
pub(super) fn inner_predicate(d: &mut IntDev<'_>, n: ExprId, a: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let aa = d.imul(a, a);
    let bb = d.imul(b, b);
    let sum = d.iadd(aa, bb);
    let body = d.ieq(n, sum);
    d.lam_fv(b_fv, int_ty, body)
}

/// `fun (a : Int) => Exists.{1} Int (fun b => Eq Int n (a*a + b*b))`.
pub(super) fn outer_predicate(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = inner_predicate(d, n, a);
    let body = int_exists(d, inner);
    d.lam_fv(a_fv, int_ty, body)
}

/// `Int.IsSumOfTwoSquares n`.
pub(super) fn is_sum_of_two_squares(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let f = d.int().is_sum_of_two_squares;
    d.const_app(f, &[n])
}

/// The two-step introduction: from `proof : Eq Int n (a*a + b*b)` build
/// `IsSumOfTwoSquares n` (as the unfolded double existential — definitionally
/// the declared constant).
fn intro_sum_of_two_squares(
    d: &mut IntDev<'_>,
    n: ExprId,
    a: ExprId,
    b: ExprId,
    proof: ExprId,
) -> ExprId {
    let inner = inner_predicate(d, n, a);
    let step = int_exists_intro(d, inner, b, proof);
    let outer = outer_predicate(d, n);
    int_exists_intro(d, outer, a, step)
}

/// `Int.ofNat k` for a small `u32` numeral.
pub(super) fn int_num(d: &mut IntDev<'_>, k: u32) -> ExprId {
    let n = d.num(k);
    d.of_nat(n)
}

/// `Int.ModEq n a b`.
pub(super) fn imodeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().mod_eq;
    d.const_app(f, &[n, a, b])
}

/// `Not (Eq Int (ofNat x) (ofNat y))` for distinct small numerals, by pushing
/// the equation through `Int.natAbs` onto `Nat` and refuting it with
/// `Nat.ne_of_beq_eq_false`.
///
/// The construction `mult_order_tests.rs` carries as a test helper, lifted
/// into the prelude because
/// [`declare_not_is_sum_of_two_squares_of_modeq_four_three`] needs it inside a
/// theorem and not only inside a test.
pub(super) fn ofnat_ne(d: &mut IntDev<'_>, x: u32, y: u32) -> ExprId {
    assert!(x != y, "ofnat_ne is only for distinct numerals");
    let p = d.int();
    let xv = d.num(x);
    let yv = d.num(y);
    let xi = d.of_nat(xv);
    let yi = d.of_nat(yv);

    let h_ty = d.ieq(xi, yi);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let start = d.refl(xv);
    let moved = d.int_eq_rewrite(xi, yi, h, start, &|d, z| {
        let na = d.const_app(p.nat_abs, &[z]);
        d.eq(xv, na)
    });
    let false_b = d.bool_false();
    let hbeq = d.bool_refl(false_b);
    let body = {
        let f = p.nat.ne_of_beq_eq_false;
        d.const_app(f, &[xv, yv, hbeq, moved])
    };
    d.lam_fv(h_fv, h_ty, body)
}

/// `Or (Int.Even a) (Int.Odd a)`, as `Nat.even_or_odd_exists (natAbs a)`.
///
/// No new proof: `Int.Even n` is **defined** as `Nat.Even (natAbs n)`
/// (`parity.rs`), so the `Nat`-level dichotomy at the magnitude already IS the
/// `Int`-level one, up to one delta unfold the kernel does for free.
fn even_or_odd_int(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let p = d.int();
    let mag = d.const_app(p.nat_abs, &[a]);
    d.const_app(p.nat.even_or_odd_exists, &[mag])
}

/// `ModEq n (mul n q) 0` — a multiple of the modulus is congruent to zero.
///
/// `Int.modEq_add_mul_left` at `a := 0` gives `ModEq n (n*q + 0) 0`, and
/// `Int.add_zero` moves it onto `n*q`. Unconditional in `n`, because
/// `modEq_add_mul_left` is.
fn modeq_mul_zero(d: &mut IntDev<'_>, n: ExprId, q: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let base = d.const_app(p.mod_eq_add_mul_left, &[n, zero, q]);
    let nq = d.imul(n, q);
    let with_zero = d.iadd(nq, zero);
    let drop_zero = d.const_app(p.add_zero, &[nq]);
    d.int_eq_rewrite(with_zero, nq, drop_zero, base, &|d, x| {
        imodeq(d, n, x, zero)
    })
}

// ============================================================================
// `Int.IsSumOfTwoSquares`
// ============================================================================

/// `Int.IsSumOfTwoSquares : Int → Prop :=`
/// `  fun n => ∃ a, ∃ b, Eq Int n (add (mul a a) (mul b b))`.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
fn declare_is_sum_of_two_squares(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let prop = d.kernel().sort_zero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let outer = outer_predicate(d, n);
    let body = int_exists(d, outer);
    let value = d.lam_fv(n_fv, int_ty, body);
    let ty = d.arrow(int_ty, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_sum_of_two_squares,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_OF_TWO_SQUARES_HEIGHT),
    })
}

/// `Int.isSumOfTwoSquares_intro : ∀ n a b, Eq Int n (add (mul a a) (mul b b))
/// → IsSumOfTwoSquares n` — the named introduction rule, so a caller never has
/// to build the double `Exists.intro` by hand.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_is_sum_of_two_squares_intro(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.is_sum_of_two_squares_intro, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let sum = d.iadd(aa, bb);
        let hyp = d.ieq(n, sum);
        let concl = is_sum_of_two_squares(d, n);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let built = intro_sum_of_two_squares(d, n, a, b, h);
        let proof = d.lam_fv(h_fv, hyp, built);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// the Brahmagupta–Fibonacci identity
// ============================================================================

/// `Int.brahmaguptaFibonacci : ∀ a b c d,`
/// `  Eq Int (mul (add (mul a a) (mul b b)) (add (mul c c) (mul d d)))`
/// `        (add (mul (sub (mul a c) (mul b d)) (sub (mul a c) (mul b d)))`
/// `             (mul (add (mul a d) (mul b c)) (add (mul a d) (mul b c))))`
/// — `(a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²`.
///
/// The proof term is **searched for and emitted** by `ring::int` (ADR-1582),
/// never written here.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the emitted term does not check, or
/// `UnknownConst` if the ring producer declined.
fn declare_brahmagupta_fibonacci(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.brahmagupta_fibonacci, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let left = d.iadd(aa, bb);
        let cc = d.imul(c, c);
        let ee = d.imul(e, e);
        let right = d.iadd(cc, ee);
        let lhs = d.imul(left, right);

        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        let u = d.isub(ac, bd);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.iadd(ad, bc);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        let rhs = d.iadd(uu, ww);
        d.ieq(lhs, rhs)
    })
}

/// `Int.brahmaguptaFibonacci' : ∀ a b c d,`
/// `  (a²+b²)(c²+d²) = (ac+bd)² + (ad−bc)²` — the conjugate form.
///
/// This, not [`declare_brahmagupta_fibonacci`], is the form the descent
/// consumes: when `c ≡ a` and `d ≡ b (mod m)` it is `ac+bd ≡ a²+b² ≡ 0` and
/// `ad−bc ≡ ab−ba = 0`, so **both** summands are divisible by `m` and the
/// factor `m²` cancels. In the first form the cross terms are `ac−bd ≡ a²−b²`,
/// which is not divisible by `m` in general.
///
/// # Errors
///
/// As [`declare_brahmagupta_fibonacci`].
fn declare_brahmagupta_fibonacci_swap(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.brahmagupta_fibonacci_swap, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let left = d.iadd(aa, bb);
        let cc = d.imul(c, c);
        let ee = d.imul(e, e);
        let right = d.iadd(cc, ee);
        let lhs = d.imul(left, right);

        let ac = d.imul(a, c);
        let bd = d.imul(b, e);
        let u = d.iadd(ac, bd);
        let ad = d.imul(a, e);
        let bc = d.imul(b, c);
        let w = d.isub(ad, bc);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        let rhs = d.iadd(uu, ww);
        d.ieq(lhs, rhs)
    })
}

/// `Int.isSumOfTwoSquares_mul : ∀ m n, IsSumOfTwoSquares m →
/// IsSumOfTwoSquares n → IsSumOfTwoSquares (mul m n)` — the composition law,
/// i.e. the Brahmagupta–Fibonacci identity read as a closure property.
///
/// Four nested `Exists` eliminations (one per witness) and then a two-step
/// `itrans`: `m*n = (a²+b²)*n = (a²+b²)*(c²+e²)` by congruence in each factor,
/// then [`declare_brahmagupta_fibonacci`] at `(a,b,c,e)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_is_sum_of_two_squares_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.is_sum_of_two_squares_mul, 2, &|d, v| {
        let int_ty = d.int_ty();
        let (m, n) = (v[0], v[1]);
        let mn = d.imul(m, n);
        let hm_ty = is_sum_of_two_squares(d, m);
        let hn_ty = is_sum_of_two_squares(d, n);
        let target = is_sum_of_two_squares(d, mn);
        let inner_arrow = d.arrow(hn_ty, target);
        let stmt = d.arrow(hm_ty, inner_arrow);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);

        let outer_m = outer_predicate(d, m);
        let minor_a = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let inner_m = inner_predicate(d, m, a);
            let ha_ty = int_exists(d, inner_m);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);

            let minor_b = {
                let b_fv = d.fresh_fvar();
                let b = d.kernel().fvar(b_fv);
                let aa = d.imul(a, a);
                let bb = d.imul(b, b);
                let sab = d.iadd(aa, bb);
                let hab_ty = d.ieq(m, sab);
                let hab_fv = d.fresh_fvar();
                let hab = d.kernel().fvar(hab_fv);

                let outer_n = outer_predicate(d, n);
                let minor_c = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let inner_n = inner_predicate(d, n, c);
                    let hc_ty = int_exists(d, inner_n);
                    let hc_fv = d.fresh_fvar();
                    let hc = d.kernel().fvar(hc_fv);

                    let minor_e = {
                        let e_fv = d.fresh_fvar();
                        let e = d.kernel().fvar(e_fv);
                        let cc = d.imul(c, c);
                        let ee = d.imul(e, e);
                        let sce = d.iadd(cc, ee);
                        let hce_ty = d.ieq(n, sce);
                        let hce_fv = d.fresh_fvar();
                        let hce = d.kernel().fvar(hce_fv);

                        // `m*n = (a²+b²)*n = (a²+b²)*(c²+e²)`.
                        let step1 = d.icongr(m, sab, hab, &|d, x| d.imul(x, n));
                        let sab_n = d.imul(sab, n);
                        let sab_sce = d.imul(sab, sce);
                        let step2 = d.icongr(n, sce, hce, &|d, x| d.imul(sab, x));
                        let to_product = d.itrans(mn, sab_n, sab_sce, step1, step2);

                        // `(a²+b²)*(c²+e²) = (ac−be)² + (ae+bc)²`.
                        let identity = d.const_app(p.brahmagupta_fibonacci, &[a, b, c, e]);
                        let ac = d.imul(a, c);
                        let be = d.imul(b, e);
                        let u = d.isub(ac, be);
                        let ae = d.imul(a, e);
                        let bc = d.imul(b, c);
                        let w = d.iadd(ae, bc);
                        let uu = d.imul(u, u);
                        let ww = d.imul(w, w);
                        let squares = d.iadd(uu, ww);
                        let full = d.itrans(mn, sab_sce, squares, to_product, identity);

                        let built = intro_sum_of_two_squares(d, mn, u, w, full);
                        let with_hce = d.lam_fv(hce_fv, hce_ty, built);
                        d.lam_fv(e_fv, int_ty, with_hce)
                    };
                    let body_e = int_exists_elim(d, inner_n, target, hc, minor_e);
                    let with_hc = d.lam_fv(hc_fv, hc_ty, body_e);
                    d.lam_fv(c_fv, int_ty, with_hc)
                };
                let body_n = int_exists_elim(d, outer_n, target, hn, minor_c);
                let with_hab = d.lam_fv(hab_fv, hab_ty, body_n);
                d.lam_fv(b_fv, int_ty, with_hab)
            };
            let body_b = int_exists_elim(d, inner_m, target, ha, minor_b);
            let with_ha = d.lam_fv(ha_fv, ha_ty, body_b);
            d.lam_fv(a_fv, int_ty, with_ha)
        };
        let body = int_exists_elim(d, outer_m, target, hm, minor_a);

        let with_hn = d.lam_fv(hn_fv, hn_ty, body);
        let proof = d.lam_fv(hm_fv, hm_ty, with_hn);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// squares modulo 4, and the boundary refutation
// ============================================================================

/// `Int.sq_of_two_mul : ∀ k, Eq Int (mul (mul k 2) (mul k 2))
/// (mul 4 (mul k k))` — `(2k)² = 4k²`. Emitted by `ring::int`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the emitted term does not check, or
/// `UnknownConst` if the ring producer declined.
fn declare_sq_of_two_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.sq_of_two_mul, 1, &|d, v| {
        let k = v[0];
        let two = int_num(d, 2);
        let t = d.imul(k, two);
        let lhs = d.imul(t, t);
        let four = int_num(d, 4);
        let kk = d.imul(k, k);
        let rhs = d.imul(four, kk);
        d.ieq(lhs, rhs)
    })
}

/// `Int.sq_of_two_mul_add_one : ∀ k, Eq Int (mul (add (mul k 2) 1)
/// (add (mul k 2) 1)) (add (mul 4 (add (mul k k) k)) 1)` —
/// `(2k+1)² = 4(k²+k) + 1`. Emitted by `ring::int`.
///
/// # Errors
///
/// As [`declare_sq_of_two_mul`].
fn declare_sq_of_two_mul_add_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.sq_of_two_mul_add_one, 1, &|d, v| {
        let k = v[0];
        let two = int_num(d, 2);
        let one = d.ione();
        let t = {
            let dbl = d.imul(k, two);
            d.iadd(dbl, one)
        };
        let lhs = d.imul(t, t);
        let four = int_num(d, 4);
        let kk = d.imul(k, k);
        let inner = d.iadd(kk, k);
        let quad = d.imul(four, inner);
        let rhs = d.iadd(quad, one);
        d.ieq(lhs, rhs)
    })
}

/// `Int.sq_modEq_four_zero_or_one : ∀ a, Or (ModEq 4 (mul a a) 0)
/// (ModEq 4 (mul a a) 1)` — **every square is `0` or `1` modulo `4`**.
///
/// The split is [`even_or_odd_int`], and each branch writes `a` as `2k` or
/// `2k+1` with the *definable* witness `k := a / 2` (`Int.ediv_two_mul_two_of_even`
/// / `Int.ediv_two_mul_two_add_one_of_odd`), so no existential is opened and
/// the whole proof stays first-order. The square is then rewritten by
/// [`declare_sq_of_two_mul`] / [`declare_sq_of_two_mul_add_one`] and the
/// residue read off with [`modeq_mul_zero`] / `Int.modEq_add_mul_left`, both
/// unconditional in the modulus.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sq_modeq_four_zero_or_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sq_mod_eq_four_zero_or_one, 1, &|d, v| {
        let a = v[0];
        let four = int_num(d, 4);
        let two = int_num(d, 2);
        let zero = d.izero();
        let one = d.ione();
        let aa = d.imul(a, a);
        let left = imodeq(d, four, aa, zero);
        let right = imodeq(d, four, aa, one);
        let stmt = d.or(left, right);

        let even_ty = d.const_app(p.even, &[a]);
        let odd_ty = d.const_app(p.odd, &[a]);
        let dichotomy = even_or_odd_int(d, a);
        let k = d.iediv(a, two);

        let proof = d.or_elim(
            even_ty,
            odd_ty,
            stmt,
            dichotomy,
            &|d, he| {
                // `a` is even: `a = 2k`, so `a² = 4k² ≡ 0 (mod 4)`.
                let hta = d.const_app(p.ediv_two_mul_two_of_even, &[a, he]);
                let t = d.imul(k, two);
                let tt = d.imul(t, t);
                let at = d.imul(a, t);
                let c1 = d.icongr(t, a, hta, &|d, x| d.imul(x, t));
                let c2 = d.icongr(t, a, hta, &|d, x| d.imul(a, x));
                let tt_aa = d.itrans(tt, at, aa, c1, c2);
                let ring_eq = d.const_app(p.sq_of_two_mul, &[k]);
                let kk = d.imul(k, k);
                let quad = d.imul(four, kk);
                let aa_tt = d.isymm(tt, aa, tt_aa);
                let aa_quad = d.itrans(aa, tt, quad, aa_tt, ring_eq);
                let base = modeq_mul_zero(d, four, kk);
                let quad_aa = d.isymm(aa, quad, aa_quad);
                let moved =
                    d.int_eq_rewrite(quad, aa, quad_aa, base, &|d, x| imodeq(d, four, x, zero));
                d.or_inl(left, right, moved)
            },
            &|d, ho| {
                // `a` is odd: `a = 2k+1`, so `a² = 4(k²+k) + 1 ≡ 1 (mod 4)`.
                let hta = d.const_app(p.ediv_two_mul_two_add_one_of_odd, &[a, ho]);
                let t = {
                    let dbl = d.imul(k, two);
                    d.iadd(dbl, one)
                };
                let tt = d.imul(t, t);
                let at = d.imul(a, t);
                let c1 = d.icongr(t, a, hta, &|d, x| d.imul(x, t));
                let c2 = d.icongr(t, a, hta, &|d, x| d.imul(a, x));
                let tt_aa = d.itrans(tt, at, aa, c1, c2);
                let ring_eq = d.const_app(p.sq_of_two_mul_add_one, &[k]);
                let kk = d.imul(k, k);
                let inner = d.iadd(kk, k);
                let quad = d.imul(four, inner);
                let shape = d.iadd(quad, one);
                let aa_tt = d.isymm(tt, aa, tt_aa);
                let aa_shape = d.itrans(aa, tt, shape, aa_tt, ring_eq);
                let base = d.const_app(p.mod_eq_add_mul_left, &[four, one, inner]);
                let shape_aa = d.isymm(aa, shape, aa_shape);
                let moved =
                    d.int_eq_rewrite(shape, aa, shape_aa, base, &|d, x| imodeq(d, four, x, one));
                d.or_inr(left, right, moved)
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.not_isSumOfTwoSquares_of_modEq_four_three : ∀ n, ModEq 4 n 3 →
/// Not (IsSumOfTwoSquares n)` — **the boundary refutation** (ADR-0603's second
/// grade): an integer congruent to `3` modulo `4` is not a sum of two squares.
///
/// Four leaves under a doubled [`declare_sq_modeq_four_zero_or_one`]. In each
/// leaf `n ≡ r (mod 4)` for `r ∈ {0, 1, 2}` and also `n ≡ 3`, so
/// `ModEq 4 3 r` — which unfolds to `Eq Int (emod 3 4) (emod r 4)`, both sides
/// **closed numerals**, so the kernel computes them and [`ofnat_ne`] closes the
/// leaf. Nothing here is an inequality argument; the whole refutation is
/// reduction plus `Int.natAbs` injectivity.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_not_is_sum_of_two_squares_of_modeq_four_three(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(
        p.not_is_sum_of_two_squares_of_mod_eq_four_three,
        1,
        &|d, v| {
            let int_ty = d.int_ty();
            let n = v[0];
            let four = int_num(d, 4);
            let three = int_num(d, 3);
            let zero = d.izero();
            let one = d.ione();
            let h3_ty = imodeq(d, four, n, three);
            let sum_ty = is_sum_of_two_squares(d, n);
            let concl = d.not(sum_ty);
            let stmt = d.arrow(h3_ty, concl);

            let h3_fv = d.fresh_fvar();
            let h3 = d.kernel().fvar(h3_fv);
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);
            let target = d.false_ty();

            // `ModEq 4 3 n`, shared by every leaf.
            let h3_flipped = d.const_app(p.mod_eq_symm, &[four, n, three, h3]);

            let outer = outer_predicate(d, n);
            let minor_a = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let inner = inner_predicate(d, n, a);
                let ha_ty = int_exists(d, inner);
                let ha_fv = d.fresh_fvar();
                let ha = d.kernel().fvar(ha_fv);

                let minor_b = {
                    let b_fv = d.fresh_fvar();
                    let b = d.kernel().fvar(b_fv);
                    let aa = d.imul(a, a);
                    let bb = d.imul(b, b);
                    let sum = d.iadd(aa, bb);
                    let hab_ty = d.ieq(n, sum);
                    let hab_fv = d.fresh_fvar();
                    let hab = d.kernel().fvar(hab_fv);
                    let sum_n = d.isymm(n, sum, hab);

                    // One leaf: `a² ≡ ra`, `b² ≡ rb`, and `3 ≡ ra + rb (mod 4)`
                    // with `ra + rb` a closed numeral that is not `3`.
                    let leaf = |d: &mut IntDev<'_>,
                                ra: ExprId,
                                rb: ExprId,
                                ha_sq: ExprId,
                                hb_sq: ExprId,
                                residue: u32| {
                        let residues = d.iadd(ra, rb);
                        let hsum = d.const_app(p.mod_eq_add, &[four, aa, ra, bb, rb, ha_sq, hb_sq]);
                        let hn = d.int_eq_rewrite(sum, n, sum_n, hsum, &|d, x| {
                            imodeq(d, four, x, residues)
                        });
                        let hfin = d
                            .const_app(p.mod_eq_trans, &[four, three, n, residues, h3_flipped, hn]);
                        let refute = ofnat_ne(d, 3, residue);
                        d.apply(refute, &[hfin])
                    };

                    let a_split = d.const_app(p.sq_mod_eq_four_zero_or_one, &[a]);
                    let b_split = d.const_app(p.sq_mod_eq_four_zero_or_one, &[b]);
                    let a_zero = imodeq(d, four, aa, zero);
                    let a_one = imodeq(d, four, aa, one);
                    let b_zero = imodeq(d, four, bb, zero);
                    let b_one = imodeq(d, four, bb, one);

                    let body = d.or_elim(
                        a_zero,
                        a_one,
                        target,
                        a_split,
                        &|d, ha_sq| {
                            d.or_elim(
                                b_zero,
                                b_one,
                                target,
                                b_split,
                                &|d, hb_sq| leaf(d, zero, zero, ha_sq, hb_sq, 0),
                                &|d, hb_sq| leaf(d, zero, one, ha_sq, hb_sq, 1),
                            )
                        },
                        &|d, ha_sq| {
                            d.or_elim(
                                b_zero,
                                b_one,
                                target,
                                b_split,
                                &|d, hb_sq| leaf(d, one, zero, ha_sq, hb_sq, 1),
                                &|d, hb_sq| leaf(d, one, one, ha_sq, hb_sq, 2),
                            )
                        },
                    );
                    let with_hab = d.lam_fv(hab_fv, hab_ty, body);
                    d.lam_fv(b_fv, int_ty, with_hab)
                };
                let body_b = int_exists_elim(d, inner, target, ha, minor_b);
                let with_ha = d.lam_fv(ha_fv, ha_ty, body_b);
                d.lam_fv(a_fv, int_ty, with_ha)
            };
            let body = int_exists_elim(d, outer, target, hs, minor_a);
            let with_hs = d.lam_fv(hs_fv, sum_ty, body);
            let proof = d.lam_fv(h3_fv, h3_ty, with_hs);
            (stmt, proof)
        },
    )?;
    Ok(())
}

// ============================================================================
// ℤ is an integral domain: cancellation
// ============================================================================

/// `Int.zero_add : ∀ a, Eq Int (add 0 a) a`. `Int.add_zero` was already here;
/// its mirror was not.
///
/// **Not by `ring::int`.** The producer DECLINED this goal, measured
/// 2026-09-05: its normal form for `add 0 a` is the item list
/// `[Mono[a], Num(0)]` and for `a` it is `[Mono[a]]`, and a trailing zero
/// numeral is not dropped, so the two lists compare unequal and the search
/// reports `NotAnIdentity`. Every zero-collapsing goal in this module hits the
/// same wall, so all four are hand-proved from `add_comm`/`add_zero`/`add_neg`
/// instead — cheaper than teaching the producer to normalize a zero item, and
/// the finding is recorded here rather than re-derived by the next lane.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_zero_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.zero_add, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let lhs = d.iadd(zero, a);
        let stmt = d.ieq(lhs, a);
        let commuted = d.const_app(p.add_comm, &[zero, a]);
        let a_zero = d.iadd(a, zero);
        let drop = d.const_app(p.add_zero, &[a]);
        let proof = d.itrans(lhs, a_zero, a, commuted, drop);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.sub_self : ∀ a, Eq Int (sub a a) 0`.
///
/// `Int.sub` is a plain `Definition` (`sub a b := add a (neg b)`), so this is
/// `Int.add_neg` verbatim up to one delta step — the proof is the constant.
/// See [`declare_zero_add`] for why the ring producer is not used here.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sub_self(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.sub_self, 1, &|d, v| {
        let a = v[0];
        let zero = d.izero();
        let lhs = d.isub(a, a);
        let stmt = d.ieq(lhs, zero);
        let proof = d.const_app(p.add_neg, &[a]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.add_sub_cancel_right : ∀ a b, Eq Int (add (sub a b) b) a`.
///
/// `(a + −b) + b = a + (−b + b) = a + (b + −b) = a + 0 = a`, by
/// `add_assoc`, `add_comm`, `add_neg` and `add_zero`. See
/// [`declare_zero_add`] for why not the ring producer.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_add_sub_cancel_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_sub_cancel_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let neg_b = d.ineg(b);
        let diff = d.isub(a, b);
        let lhs = d.iadd(diff, b);
        let stmt = d.ieq(lhs, a);

        let assoc = d.const_app(p.add_assoc, &[a, neg_b, b]);
        let tail = d.iadd(neg_b, b);
        let regrouped = d.iadd(a, tail);
        let flip = d.const_app(p.add_comm, &[neg_b, b]);
        let flipped_tail = d.iadd(b, neg_b);
        let zero = d.izero();
        let vanish = d.const_app(p.add_neg, &[b]);
        let tail_zero = d.itrans(tail, flipped_tail, zero, flip, vanish);
        let inner = d.icongr(tail, zero, tail_zero, &|d, x| d.iadd(a, x));
        let a_zero = d.iadd(a, zero);
        let drop = d.const_app(p.add_zero, &[a]);
        let (_end, proof) = d.ichain(lhs, &[(regrouped, assoc), (a_zero, inner), (a, drop)]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_sub_mul_comm : ∀ a b, Eq Int (sub (mul a b) (mul b a)) 0` — the
/// commutator of a product, which is what makes the descent's SECOND cross
/// term `ae − bc` vanish modulo `m`.
///
/// `mul_comm` turns the subtrahend into the minuend, then
/// [`declare_sub_self`]. See [`declare_zero_add`] for why not the ring
/// producer.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_mul_sub_mul_comm(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_sub_mul_comm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.imul(a, b);
        let ba = d.imul(b, a);
        let lhs = d.isub(ab, ba);
        let zero = d.izero();
        let stmt = d.ieq(lhs, zero);

        let flip = d.const_app(p.mul_comm, &[b, a]);
        let aligned = d.icongr(ba, ab, flip, &|d, x| d.isub(ab, x));
        let same = d.isub(ab, ab);
        let vanish = d.const_app(p.sub_self, &[ab]);
        let proof = d.itrans(lhs, same, zero, aligned, vanish);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.eq_of_sub_eq_zero : ∀ a b, Eq Int (sub a b) 0 → Eq Int a b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_eq_of_sub_eq_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.eq_of_sub_eq_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let diff = d.isub(a, b);
        let hyp = d.ieq(diff, zero);
        let concl = d.ieq(a, b);
        let stmt = d.arrow(hyp, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `a = (a − b) + b = 0 + b = b`.
        let cancel = d.const_app(p.add_sub_cancel_right, &[a, b]);
        let restored = d.iadd(diff, b);
        let a_restored = d.isymm(restored, a, cancel);
        let shifted = d.icongr(diff, zero, h, &|d, x| d.iadd(x, b));
        let zero_b = d.iadd(zero, b);
        let a_zero_b = d.itrans(a, restored, zero_b, a_restored, shifted);
        let zero_add = d.const_app(p.zero_add, &[b]);
        let proof_body = d.itrans(a, zero_b, b, a_zero_b, zero_add);
        let proof = d.lam_fv(h_fv, hyp, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_ne_zero : ∀ a b, Not (Eq Int a 0) → Not (Eq Int b 0) →
/// Not (Eq Int (mul a b) 0)` — `Int.mul_eq_zero` contrapositive, i.e. ℤ has no
/// zero divisors, stated in the direction a cancellation proof consumes.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_mul_ne_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_ne_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let a_zero = d.ieq(a, zero);
        let b_zero = d.ieq(b, zero);
        let ha_ty = d.not(a_zero);
        let hb_ty = d.not(b_zero);
        let ab = d.imul(a, b);
        let ab_zero = d.ieq(ab, zero);
        let concl = d.not(ab_zero);
        let inner = d.arrow(hb_ty, concl);
        let stmt = d.arrow(ha_ty, inner);

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let target = d.false_ty();
        let split = d.const_app(p.mul_eq_zero, &[a, b, hab]);
        let body = d.or_elim(
            a_zero,
            b_zero,
            target,
            split,
            &|d, h| d.apply(ha, &[h]),
            &|d, h| d.apply(hb, &[h]),
        );
        let with_hab = d.lam_fv(hab_fv, ab_zero, body);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_hab);
        let proof = d.lam_fv(ha_fv, ha_ty, with_hb);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_left_cancel_of_ne_zero : ∀ m a b, Not (Eq Int m 0) →
/// Eq Int (mul m a) (mul m b) → Eq Int a b`.
///
/// `m·a = m·b` gives `m·(a−b) = m·a − m·b = 0` (`Int.mul_sub`, then
/// [`declare_sub_self`]), so `Int.mul_eq_zero` splits, the `m = 0` branch is
/// absurd, and [`declare_eq_of_sub_eq_zero`] closes the other. This is what
/// [`declare_descent_step`] needs to divide out the `m²`, and it is the lemma
/// `shape_search --ns Int --name-contains cancel` reported ABSENT before this
/// module.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_mul_left_cancel_of_ne_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_left_cancel_of_ne_zero, 3, &|d, v| {
        let (m, a, b) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let m_zero = d.ieq(m, zero);
        let hm_ty = d.not(m_zero);
        let ma = d.imul(m, a);
        let mb = d.imul(m, b);
        let heq_ty = d.ieq(ma, mb);
        let concl = d.ieq(a, b);
        let inner = d.arrow(heq_ty, concl);
        let stmt = d.arrow(hm_ty, inner);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // `m*a − m*b = m*b − m*b = 0`.
        let diff_products = d.isub(ma, mb);
        let shifted = d.icongr(ma, mb, heq, &|d, x| d.isub(x, mb));
        let mb_mb = d.isub(mb, mb);
        let self_zero = d.const_app(p.sub_self, &[mb]);
        let products_zero = d.itrans(diff_products, mb_mb, zero, shifted, self_zero);

        // `m*(a−b) = m*a − m*b`, so `m*(a−b) = 0`.
        let diff = d.isub(a, b);
        let distrib = d.const_app(p.mul_sub, &[m, a, b]);
        let m_diff = d.imul(m, diff);
        let m_diff_zero = d.itrans(m_diff, diff_products, zero, distrib, products_zero);

        let split = d.const_app(p.mul_eq_zero, &[m, diff, m_diff_zero]);
        let diff_zero = d.ieq(diff, zero);
        let body = d.or_elim(
            m_zero,
            diff_zero,
            concl,
            split,
            &|d, h| {
                let contradiction = d.apply(hm, &[h]);
                d.absurd(concl, contradiction)
            },
            &|d, h| d.const_app(p.eq_of_sub_eq_zero, &[a, b, h]),
        );
        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let proof = d.lam_fv(hm_fv, hm_ty, with_heq);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// the descent step
// ============================================================================

/// `Int.modEq_descent_cross_terms : ∀ m a b c e, 0 < m → ModEq m c a →
/// ModEq m e b → ModEq m (add (mul a a) (mul b b)) 0 →
/// And (ModEq m (add (mul a c) (mul b e)) 0)
///     (ModEq m (sub (mul a e) (mul b c)) 0)`
/// — **the congruence half of Fermat's descent**, and the reason the descent
/// uses [`declare_brahmagupta_fibonacci_swap`]'s grouping rather than the
/// textbook one.
///
/// With `c ≡ a` and `e ≡ b` modulo `m`, the two cross terms of that grouping
/// are `ac + be ≡ a² + b² ≡ 0` and `ae − bc ≡ ab − ba = 0`. Both are therefore
/// divisible by `m`, which is exactly the licence the descent needs to divide
/// the product `m²·(m'p)` through by `m²`
/// ([`declare_descent_step`]).
///
/// `0 < m` is inherited from `Int.modEq_mul_left`, the only multiplicative
/// congruence in this prelude that is not unconditional in the modulus.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_modeq_descent_cross_terms(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_descent_cross_terms, 5, &|d, v| {
        let (m, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, m);
        let hc_ty = imodeq(d, m, c, a);
        let he_ty = imodeq(d, m, e, b);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let norm = d.iadd(aa, bb);
        let h0_ty = imodeq(d, m, norm, zero);

        let ac = d.imul(a, c);
        let be = d.imul(b, e);
        let first = d.iadd(ac, be);
        let ae = d.imul(a, e);
        let bc = d.imul(b, c);
        let second = d.isub(ae, bc);
        let left = imodeq(d, m, first, zero);
        let right = imodeq(d, m, second, zero);
        let concl = d.and(left, right);

        let stmt = {
            let s3 = d.arrow(h0_ty, concl);
            let s2 = d.arrow(he_ty, s3);
            let s1 = d.arrow(hc_ty, s2);
            d.arrow(pos_ty, s1)
        };

        let pos_fv = d.fresh_fvar();
        let hpos = d.kernel().fvar(pos_fv);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);

        // `ac + be ≡ a² + b² ≡ 0`.
        let t1 = d.const_app(p.mod_eq_mul_left, &[m, c, a, a, hpos, hc]);
        let t2 = d.const_app(p.mod_eq_mul_left, &[m, e, b, b, hpos, he]);
        let t3 = d.const_app(p.mod_eq_add, &[m, ac, aa, be, bb, t1, t2]);
        let part_one = d.const_app(p.mod_eq_trans, &[m, first, norm, zero, t3, h0]);

        // `ae − bc ≡ ab − ba = 0`.
        let ab = d.imul(a, b);
        let ba = d.imul(b, a);
        let s1 = d.const_app(p.mod_eq_mul_left, &[m, e, b, a, hpos, he]);
        let s2 = d.const_app(p.mod_eq_mul_left, &[m, c, a, b, hpos, hc]);
        let s3 = d.const_app(p.mod_eq_neg, &[m, bc, ba, s2]);
        let neg_bc = d.ineg(bc);
        let neg_ba = d.ineg(ba);
        let s4 = d.const_app(p.mod_eq_add, &[m, ae, ab, neg_bc, neg_ba, s1, s3]);
        let commutator = d.isub(ab, ba);
        let vanishes = d.const_app(p.mul_sub_mul_comm, &[a, b]);
        let part_two = d.int_eq_rewrite(commutator, zero, vanishes, s4, &|d, x| {
            imodeq(d, m, second, x)
        });

        let and_intro = d.int().logic.and_intro;
        let paired = d.const_app(and_intro, &[left, right, part_one, part_two]);

        let with_h0 = d.lam_fv(h0_fv, h0_ty, paired);
        let with_he = d.lam_fv(he_fv, he_ty, with_h0);
        let with_hc = d.lam_fv(hc_fv, hc_ty, with_he);
        let proof = d.lam_fv(pos_fv, pos_ty, with_hc);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_mul_of_mul_mul : ∀ m p q,
/// Eq Int (mul (mul m p) (mul m q)) (mul (mul m m) (mul q p))`. Emitted by
/// `ring::int`.
///
/// # Errors
///
/// As [`declare_sq_of_two_mul`].
fn declare_mul_mul_of_mul_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.mul_mul_of_mul_mul, 3, &|d, v| {
        let (m, x, y) = (v[0], v[1], v[2]);
        let mx = d.imul(m, x);
        let my = d.imul(m, y);
        let lhs = d.imul(mx, my);
        let mm = d.imul(m, m);
        let yx = d.imul(y, x);
        let rhs = d.imul(mm, yx);
        d.ieq(lhs, rhs)
    })
}

/// `Int.sq_add_sq_of_mul_left : ∀ m u w,
/// Eq Int (add (mul (mul m u) (mul m u)) (mul (mul m w) (mul m w)))
///        (mul (mul m m) (add (mul u u) (mul w w)))`. Emitted by `ring::int`.
///
/// # Errors
///
/// As [`declare_sq_of_two_mul`].
fn declare_sq_add_sq_of_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.sq_add_sq_of_mul_left, 3, &|d, v| {
        let (m, u, w) = (v[0], v[1], v[2]);
        let mu = d.imul(m, u);
        let mw = d.imul(m, w);
        let mu2 = d.imul(mu, mu);
        let mw2 = d.imul(mw, mw);
        let lhs = d.iadd(mu2, mw2);
        let mm = d.imul(m, m);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        let sum = d.iadd(uu, ww);
        let rhs = d.imul(mm, sum);
        d.ieq(lhs, rhs)
    })
}

/// `Int.descentStep : ∀ m p q a b c e u w, Not (Eq Int m 0) →`
/// `  Eq Int (mul m p) (add (mul a a) (mul b b)) →`
/// `  Eq Int (mul m q) (add (mul c c) (mul e e)) →`
/// `  Eq Int (mul m u) (add (mul a c) (mul b e)) →`
/// `  Eq Int (mul m w) (sub (mul a e) (mul b c)) →`
/// `  Eq Int (mul q p) (add (mul u u) (mul w w))`
/// — **the algebraic half of Fermat's descent**, stated so that
/// `Nat.strongInduction` on the `natAbs` of the multiplier applies directly:
/// the conclusion is again "a multiple of `p` is a sum of two squares", with
/// `q` in `m`'s place.
///
/// The route is one line of mathematics and three of bookkeeping:
/// `(mp)(mq) = (a²+b²)(c²+e²) = (ac+be)² + (ae−bc)² = (mu)² + (mw)²`, the ends
/// are `m²·(qp)` and `m²·(u²+w²)`, and
/// [`declare_mul_left_cancel_of_ne_zero`] divides the `m²` out.
///
/// **The quotients `u` and `w` are hypotheses, not constructed here.** That is
/// deliberate: producing them is exactly what
/// [`declare_modeq_descent_cross_terms`] licenses (both cross terms are
/// divisible by `m`), and keeping them universally quantified means this lemma
/// is reusable by any descent that can exhibit them, not only by the
/// balanced-representative one.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_descent_step(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.descent_step, 9, &|d, v| {
        let (m, pp, q) = (v[0], v[1], v[2]);
        let (a, b, c, e) = (v[3], v[4], v[5], v[6]);
        let (u, w) = (v[7], v[8]);
        let zero = d.izero();
        let m_zero = d.ieq(m, zero);
        let hm_ty = d.not(m_zero);

        let mp = d.imul(m, pp);
        let mq = d.imul(m, q);
        let mu = d.imul(m, u);
        let mw = d.imul(m, w);
        let aa = d.imul(a, a);
        let bb = d.imul(b, b);
        let sab = d.iadd(aa, bb);
        let cc = d.imul(c, c);
        let ee = d.imul(e, e);
        let sce = d.iadd(cc, ee);
        let ac = d.imul(a, c);
        let be = d.imul(b, e);
        let cross_one = d.iadd(ac, be);
        let ae = d.imul(a, e);
        let bc = d.imul(b, c);
        let cross_two = d.isub(ae, bc);

        let h1_ty = d.ieq(mp, sab);
        let h2_ty = d.ieq(mq, sce);
        let h3_ty = d.ieq(mu, cross_one);
        let h4_ty = d.ieq(mw, cross_two);
        let qp = d.imul(q, pp);
        let uu = d.imul(u, u);
        let ww = d.imul(w, w);
        let suw = d.iadd(uu, ww);
        let concl = d.ieq(qp, suw);

        let stmt = {
            let s4 = d.arrow(h4_ty, concl);
            let s3 = d.arrow(h3_ty, s4);
            let s2 = d.arrow(h2_ty, s3);
            let s1 = d.arrow(h1_ty, s2);
            d.arrow(hm_ty, s1)
        };

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_fv = d.fresh_fvar();
        let h3 = d.kernel().fvar(h3_fv);
        let h4_fv = d.fresh_fvar();
        let h4 = d.kernel().fvar(h4_fv);

        // `(m·p)(m·q) = (a²+b²)(c²+e²)`.
        let product = d.imul(mp, mq);
        let step_a1 = d.icongr(mp, sab, h1, &|d, x| d.imul(x, mq));
        let sab_mq = d.imul(sab, mq);
        let step_a2 = d.icongr(mq, sce, h2, &|d, x| d.imul(sab, x));
        let sab_sce = d.imul(sab, sce);
        let to_norms = d.itrans(product, sab_mq, sab_sce, step_a1, step_a2);

        // `= (ac+be)² + (ae−bc)²`.
        let identity = d.const_app(p.brahmagupta_fibonacci_swap, &[a, b, c, e]);
        let c1_sq = d.imul(cross_one, cross_one);
        let c2_sq = d.imul(cross_two, cross_two);
        let crosses = d.iadd(c1_sq, c2_sq);
        let to_crosses = d.itrans(product, sab_sce, crosses, to_norms, identity);

        // `= (m·u)² + (m·w)²`.
        let h3s = d.isymm(mu, cross_one, h3);
        let h4s = d.isymm(mw, cross_two, h4);
        let step_c1 = d.icongr(cross_one, mu, h3s, &|d, x| {
            let sq = d.imul(x, x);
            d.iadd(sq, c2_sq)
        });
        let mu_sq = d.imul(mu, mu);
        let mixed = d.iadd(mu_sq, c2_sq);
        let step_c2 = d.icongr(cross_two, mw, h4s, &|d, x| {
            let sq = d.imul(x, x);
            d.iadd(mu_sq, sq)
        });
        let mw_sq = d.imul(mw, mw);
        let scaled = d.iadd(mu_sq, mw_sq);
        let crosses_scaled = d.itrans(crosses, mixed, scaled, step_c1, step_c2);
        let product_scaled = d.itrans(product, crosses, scaled, to_crosses, crosses_scaled);

        // Both ends carry the factor `m²`.
        let mm = d.imul(m, m);
        let left_shape = d.const_app(p.mul_mul_of_mul_mul, &[m, pp, q]);
        let mm_qp = d.imul(mm, qp);
        let right_shape = d.const_app(p.sq_add_sq_of_mul_left, &[m, u, w]);
        let mm_suw = d.imul(mm, suw);
        let from_mm = d.isymm(product, mm_qp, left_shape);
        let mm_to_scaled = d.itrans(mm_qp, product, scaled, from_mm, product_scaled);
        let cancellable = d.itrans(mm_qp, scaled, mm_suw, mm_to_scaled, right_shape);

        let mm_ne = d.const_app(p.mul_ne_zero, &[m, m, hm, hm]);
        let body = d.const_app(
            p.mul_left_cancel_of_ne_zero,
            &[mm, qp, suw, mm_ne, cancellable],
        );

        let with_h4 = d.lam_fv(h4_fv, h4_ty, body);
        let with_h3 = d.lam_fv(h3_fv, h3_ty, with_h4);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, with_h3);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let proof = d.lam_fv(hm_fv, hm_ty, with_h1);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
///
/// # Errors
///
/// Returns the trusted gate's rejection, or `UnknownConst` if a ring-producer
/// search declined.
pub(super) fn declare_two_squares_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_is_sum_of_two_squares(d)?;
    declare_is_sum_of_two_squares_intro(d)?;
    declare_brahmagupta_fibonacci(d)?;
    declare_brahmagupta_fibonacci_swap(d)?;
    declare_is_sum_of_two_squares_mul(d)?;
    declare_sq_of_two_mul(d)?;
    declare_sq_of_two_mul_add_one(d)?;
    declare_sq_modeq_four_zero_or_one(d)?;
    declare_not_is_sum_of_two_squares_of_modeq_four_three(d)?;
    declare_zero_add(d)?;
    declare_sub_self(d)?;
    declare_add_sub_cancel_right(d)?;
    declare_mul_sub_mul_comm(d)?;
    declare_eq_of_sub_eq_zero(d)?;
    declare_mul_ne_zero(d)?;
    declare_mul_left_cancel_of_ne_zero(d)?;
    declare_modeq_descent_cross_terms(d)?;
    declare_mul_mul_of_mul_mul(d)?;
    declare_sq_add_sq_of_mul_left(d)?;
    declare_descent_step(d)?;
    Ok(())
}
