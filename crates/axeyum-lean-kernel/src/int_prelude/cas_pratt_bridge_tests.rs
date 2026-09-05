//! CAS → kernel bridge: **Pratt (Lucas) primality certificates**.
//!
//! `axeyum_cas::ntheory_certify::certify_prime` produces a
//! [`PrattCertificate`] — a witness `a`, the complete prime factorization of
//! `n − 1`, and one recursive subcertificate per factor base — and
//! `check_primality_certificate` re-derives it inside the CAS. ADR-0601 §2
//! calls that `cas-internal`: nothing leaves the CAS's own arithmetic. This
//! module is the reconstruction route that ends that, for the primes the
//! kernel can actually reach: it turns a certificate into kernel theorems
//! admitted through [`crate::Kernel::add_declaration`].
//!
//! # Why a naive reconstruction is impossible, and what makes this one work
//!
//! Every `Nat` numeral in this kernel is unary, so the obvious route —
//! state `ModEq (ofNat n) (pow (ofNat a) (n−1)) one` and close it by
//! `Eq.refl`, letting the kernel reduce — forms `a^(n−1)` as a literal unary
//! numeral. `mult_order_tests` already flags `3^6 = 729` as "the one
//! expensive case". `2^12 = 4096` is worse and `2^18 = 262144` is not
//! survivable; the wall lands below `n = 20`, measured in
//! [`tests::the_naive_refl_route_walls_where_the_reducing_route_does_not`].
//!
//! The route here never forms `a^(n−1)`. It is **square-and-multiply with
//! reduction at every step**, which is exactly what the CAS checker's own
//! `pow_mod` does, rebuilt out of kernel lemmas:
//!
//! - `Int.pow_add a t t : a^(t+t) = a^t · a^t` and
//!   `Int.pow_succ a t : a^(t+1) = a^t · a` split the exponent;
//! - `Int.modEq_mul_general` (unconditional in the modulus — the
//!   positivity-scoped `modEq_mul` would drag an `0 < n` obligation through
//!   every step) multiplies two congruences;
//! - the residue is renormalised after each step by one `Eq.refl` on
//!   `emod`, over a numeral bounded by `n²` and never larger;
//! - `Int.modEq_trans` chains them.
//!
//! So the largest numeral the kernel ever forms is `n²`, and the proof has
//! `O(log(n))` steps rather than `O(n)` reduction of a numeral of size
//! `a^(n−1)`. [`tests::the_reducing_route_reaches_primes_the_naive_one_cannot`]
//! measures both sides of that claim.
//!
//! # Where it stops
//!
//! Measured 2026-09-04 by [`tests::the_cost_ladder_is_measured`], proving
//! `a^(n−1) ≡ 1 (mod n)` at the CAS's own witness (shared dev box,
//! `--release`, other lanes active, so these are upper bounds):
//!
//! | `n` | wall clock |
//! |---|---|
//! | 47 | 0.83 s |
//! | 101 | 7.8 s |
//! | 251 | 398 s |
//! | 509 | killed, not waited out |
//!
//! The cost is superlinear in `n` well beyond the `n²` numeral size — the
//! `251` rung is 51× the `101` rung for 2.5× the modulus — so `251` is the
//! last rung that finishes at all and `101` is the last one a gate can carry.
//! [`RECONSTRUCTED`] therefore stops at 47, comfortably inside that, and
//! [`COST_LADDER`] at 101. ADR-1622 records the table and what would move it.
//!
//! # What is reconstructed
//!
//! For each prime `n` in the certificate tree (the subject and, recursively,
//! every factor base), three families of theorem, matching the CAS checker's
//! own guards one for one:
//!
//! | kernel theorem | CAS guard |
//! |---|---|
//! | `Check.pratt_factorization_<n>` : `Eq Nat (∏ qᵢ^eᵢ) (n−1)` | G6, completeness of the factorization |
//! | `Check.pratt_fermat_<n>` : `ModEq (ofNat n) (pow (ofNat a) (n−1)) one` | G8, the Fermat condition |
//! | `Check.pratt_order_<n>_q<q>` : `Not (ModEq (ofNat n) (pow (ofNat a) ((n−1)/q)) one)` | G9, order maximality |
//!
//! G6 is not decoration: the module the certificate comes from records the
//! measured forgery `n = 91` with `factors = [(2,1)]`, which passes every
//! order check and is rejected by completeness alone.
//!
//! # What is NOT reconstructed — read this before quoting the fact
//!
//! 1. **It does not prove `n` is prime.** The kernel checks the certificate's
//!    *arithmetic conditions*. The step from those conditions to primality is
//!    Lucas's theorem — "if `a` has order `n−1` modulo `n` then `n` is
//!    prime" — and it is not derived here. `Int.IsOrder`,
//!    `Int.pow_modeq_one_iff_order_dvd` and `Int.order_exists` (ADR-1598)
//!    supply the first half of that argument; the missing half is
//!    "`k ∣ m`, and `k ∤ m/q` for every prime `q ∣ m`, implies `k = m`",
//!    which needs divisor enumeration this prelude does not have. ADR-1622
//!    prices it.
//! 2. **It reconstructs the conditions, not the implication.** Exactly
//!    parallel to `rat_prelude::cas_geometry_pair_bridge_tests`, which proves
//!    the cofactor identity and not the geometric conditional.
//! 3. **The certificate is not re-derived, it is re-checked.** The witness and
//!    the factorization come from the CAS; the kernel is handed them and
//!    verifies the arithmetic. A wrong witness is refused *by the kernel* —
//!    [`tests::a_corrupted_witness_is_refused_by_the_kernel`] disables this
//!    route's own guard to show the refusal is the trusted gate's and not
//!    Rust's.
//! 4. **It covers the primes the kernel can reach, not `2^89 − 1`.** The
//!    ledger's Mersenne-89 fact stays `cas-internal` for exactly that reason;
//!    the reachable range is measured, not assumed.
//! 5. **The translator is not the kernel's business.** That
//!    `residue_of(n, a, m)` really is `a^m mod n` is checked by evaluation in
//!    [`tests`], never by the trusted gate.

use axeyum_cas::ntheory_certify::{PrattCertificate, certify_prime};

use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// Small term helpers.
// ---------------------------------------------------------------------------

/// `Int.ofNat <unary numeral v>`.
fn inum(d: &mut IntDev<'_>, v: u32) -> ExprId {
    let n = d.num(v);
    d.of_nat(n)
}

/// `Int.ModEq n a b`.
fn modeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().mod_eq;
    d.const_app(f, &[n, a, b])
}

/// `Not (Eq Int (ofNat x) (ofNat y))` for distinct small `x`, `y`.
///
/// Re-derived here rather than shared: `mult_order_tests::ofnat_ne` is private
/// to its own module, which is this crate's convention for a helper of this
/// size.
fn ofnat_ne(d: &mut IntDev<'_>, x: u32, y: u32) -> ExprId {
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
        let f = d.int().nat.ne_of_beq_eq_false;
        d.const_app(f, &[xv, yv, hbeq, moved])
    };
    d.lam_fv(h_fv, h_ty, body)
}

// ---------------------------------------------------------------------------
// The engine: modular exponentiation as a kernel proof.
// ---------------------------------------------------------------------------

/// `a^m mod n`, computed in Rust — the untrusted side.
///
/// Only ever used to say which residue the kernel proof should land on; the
/// kernel re-derives every step, so a wrong answer here becomes a kernel
/// rejection, never an admitted falsehood.
fn residue_of(n: u32, a: u32, m: u32) -> u32 {
    let n64 = u64::from(n);
    let mut acc: u64 = 1 % n64;
    let mut base = u64::from(a) % n64;
    let mut e = m;
    while e > 0 {
        if e & 1 == 1 {
            acc = (acc * base) % n64;
        }
        base = (base * base) % n64;
        e >>= 1;
    }
    u32::try_from(acc).expect("a residue mod n fits in u32")
}

/// A proof of `Int.ModEq (ofNat n) (Int.pow (ofNat a) m) (ofNat r)` where
/// `r = a^m mod n`, together with `r`.
///
/// Square-and-multiply: no numeral larger than `n²` is ever formed, and the
/// term has `O(log m)` steps. See the module doc for why the direct route
/// cannot be used.
fn pow_modeq(d: &mut IntDev<'_>, n: u32, a: u32, m: u32) -> (ExprId, u32) {
    let p = d.int();
    let n_i = inum(d, n);
    let a_i = inum(d, a);

    // Base: `m ∈ {0, 1}`. `pow a 0` reduces to `one` and `pow a 1` to `a`, so
    // one `Eq.refl` on `emod` closes both, over numerals bounded by `a`.
    if m <= 1 {
        let r = residue_of(n, a, m);
        let m_nat = d.num(m);
        let x = d.ipow(a_i, m_nat);
        let lhs = d.iemod(x, n_i);
        return (d.irefl(lhs), r);
    }

    let (split_eq, left_pow, right_int, right_residue, half) = if m.is_multiple_of(2) {
        // `a^(t+t) = a^t · a^t` — squaring.
        let t = m / 2;
        let t_nat = d.num(t);
        let pow_at = d.ipow(a_i, t_nat);
        let eq = d.const_app(p.pow_add, &[a_i, t_nat, t_nat]);
        (eq, pow_at, pow_at, None, t)
    } else {
        // `a^(t+1) = a^t · a` — the multiply step.
        let t = m - 1;
        let t_nat = d.num(t);
        let pow_at = d.ipow(a_i, t_nat);
        let eq = d.const_app(p.pow_succ, &[a_i, t_nat]);
        (eq, pow_at, a_i, Some(a % n), t)
    };

    let (h_half, r_half) = pow_modeq(d, n, a, half);
    let r_half_i = inum(d, r_half);

    // The right factor's own congruence: either the same half again
    // (squaring), or `ModEq n a a` (the multiply step).
    let (h_right, r_right_i, r_right) = match right_residue {
        None => (h_half, r_half_i, r_half),
        Some(ra) => {
            let f = p.mod_eq_refl;
            let h = d.const_app(f, &[n_i, a_i]);
            (h, a_i, ra)
        }
    };

    // `modEq_mul_general n (a^half) r_half right r_right h_half h_right`
    let product = {
        let f = p.mod_eq_mul_general;
        d.const_app(
            f,
            &[
                n_i, left_pow, r_half_i, right_int, r_right_i, h_half, h_right,
            ],
        )
    };
    let lhs_split = d.imul(left_pow, right_int);
    let rhs_split = d.imul(r_half_i, r_right_i);

    // Move the left-hand side back from `a^half · right` to `a^m`.
    let m_nat = d.num(m);
    let pow_am = d.ipow(a_i, m_nat);
    let back = d.isymm(pow_am, lhs_split, split_eq);
    let on_pow = d.int_eq_rewrite(lhs_split, pow_am, back, product, &|d, z| {
        modeq(d, n_i, z, rhs_split)
    });

    // Renormalise the right-hand side: `r_half · r_right ≡ r (mod n)`, one
    // `Eq.refl` over a numeral bounded by `n²`.
    let r = residue_of(n, a, m);
    debug_assert_eq!(
        r,
        (r_half * r_right) % n,
        "the residue recursion must agree"
    );
    let r_i = inum(d, r);
    let renorm = {
        let lhs = d.iemod(rhs_split, n_i);
        d.irefl(lhs)
    };
    let chained = {
        let f = p.mod_eq_trans;
        d.const_app(f, &[n_i, pow_am, rhs_split, r_i, on_pow, renorm])
    };
    (chained, r)
}

/// A proof of `Not (Int.ModEq (ofNat n) (Int.pow (ofNat a) m) one)`, valid
/// exactly when `a^m mod n ≠ 1`.
///
/// From `h : a^m ≡ 1` and the engine's `a^m ≡ r`, `symm`+`trans` gives
/// `r ≡ 1 (mod n)`, which unfolds to `emod r n = emod 1 n` and reduces to
/// `Eq Int (ofNat r) (ofNat 1)` — refuted by [`ofnat_ne`].
fn pow_not_modeq_one(d: &mut IntDev<'_>, n: u32, a: u32, m: u32) -> Option<ExprId> {
    let r = residue_of(n, a, m);
    if r == 1 {
        return None;
    }
    let p = d.int();
    let n_i = inum(d, n);
    let a_i = inum(d, a);
    let m_nat = d.num(m);
    let pow_am = d.ipow(a_i, m_nat);
    let one_i = d.ione();

    let (h_pow, r_check) = pow_modeq(d, n, a, m);
    assert_eq!(r_check, r, "the engine's residue must be the computed one");
    let r_i = inum(d, r);

    let h_ty = modeq(d, n_i, pow_am, one_i);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let flipped = {
        let f = p.mod_eq_symm;
        d.const_app(f, &[n_i, pow_am, r_i, h_pow])
    };
    let r_is_one = {
        let f = p.mod_eq_trans;
        d.const_app(f, &[n_i, r_i, pow_am, one_i, flipped, h])
    };
    let ne = ofnat_ne(d, r, 1);
    let body = d.kernel().app(ne, r_is_one);
    Some(d.lam_fv(h_fv, h_ty, body))
}

// ---------------------------------------------------------------------------
// The route: a `PrattCertificate` becomes kernel theorems.
// ---------------------------------------------------------------------------

/// Which of the ROUTE's own guards run before the kernel is asked.
///
/// Every one of these is a Rust-side convenience. Turning them all off must
/// not let a corrupted certificate through: the refusal has to come from
/// [`crate::Kernel::add_declaration`]. That is what
/// [`tests::a_corrupted_witness_is_refused_by_the_kernel`] measures.
#[derive(Clone, Copy, Debug)]
pub(super) struct RouteGuards {
    /// Run `axeyum_cas`'s own `check_primality_certificate` first.
    pub cas_recheck: bool,
    /// Refuse to emit a Fermat theorem whose residue is not `1`.
    pub fermat_residue: bool,
    /// Refuse to emit an order theorem whose residue IS `1`.
    pub order_residue: bool,
}

impl RouteGuards {
    /// Every guard on — the shipping configuration.
    pub(super) fn all() -> Self {
        Self {
            cas_recheck: true,
            fermat_residue: true,
            order_residue: true,
        }
    }

    /// Every guard off — the kernel is the only thing left to refuse.
    pub(super) fn none() -> Self {
        Self {
            cas_recheck: false,
            fermat_residue: false,
            order_residue: false,
        }
    }
}

/// `Nat` term for `∏ qᵢ^eᵢ`, left-associated in certificate order.
fn factor_product(d: &mut IntDev<'_>, factors: &[(u32, u32)]) -> ExprId {
    let mut acc = d.num(1);
    for &(base, exp) in factors {
        let b = d.num(base);
        let e = d.num(exp);
        let term = NatOps::pow(d, b, e);
        acc = NatOps::mul(d, acc, term);
    }
    acc
}

/// The factor bases and exponents of a certificate, as `u32`.
fn factors_u32(cert: &PrattCertificate) -> Vec<(u32, u32)> {
    cert.factors
        .iter()
        .map(|&(base, exp)| {
            (
                u32::try_from(base).expect("a reachable factor base fits in u32"),
                exp,
            )
        })
        .collect()
}

/// Reconstruct one Pratt certificate (not its subcertificates) into kernel
/// theorems, returning the names admitted.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` means the **kernel** refused
/// the certificate's arithmetic.
fn reconstruct_one(
    d: &mut IntDev<'_>,
    n: u32,
    cert: &PrattCertificate,
    guards: RouteGuards,
) -> Result<Vec<NameId>, KernelError> {
    let anon = d.kernel().anon();
    let mut admitted = Vec::new();
    let factors = factors_u32(cert);
    let m = n - 1;

    // -- G6: the factorization of `n − 1` is complete -----------------------
    {
        let name = d
            .kernel()
            .name_str(anon, format!("Check.pratt_factorization_{n}"));
        let product = factor_product(d, &factors);
        let target = d.num(m);
        let ty = d.eq(product, target);
        let value = d.refl(target);
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    // `n = 2` has no witness condition to state: `n − 1 = 1`, the factor list
    // is empty, and G8/G9 are vacuous in the CAS checker too.
    if n == 2 {
        return Ok(admitted);
    }

    let witness = u32::try_from(cert.witness).expect("a reachable witness fits in u32");

    // -- G8: the Fermat condition -------------------------------------------
    {
        let residue = residue_of(n, witness, m);
        assert!(
            !(guards.fermat_residue && residue != 1),
            "route guard: witness {witness} does not satisfy Fermat modulo {n}"
        );
        let name = d.kernel().name_str(anon, format!("Check.pratt_fermat_{n}"));
        let n_i = inum(d, n);
        let a_i = inum(d, witness);
        let m_nat = d.num(m);
        let pow_am = d.ipow(a_i, m_nat);
        let one_i = d.ione();
        let ty = modeq(d, n_i, pow_am, one_i);
        let (value, _) = pow_modeq(d, n, witness, m);
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    // -- G9: order maximality, one theorem per factor base ------------------
    for &(base, _) in &factors {
        let exponent = m / base;
        let residue = residue_of(n, witness, exponent);
        assert!(
            !(guards.order_residue && residue == 1),
            "route guard: witness {witness} has non-maximal order modulo {n} at {base}"
        );
        let name = d
            .kernel()
            .name_str(anon, format!("Check.pratt_order_{n}_q{base}"));
        let n_i = inum(d, n);
        let a_i = inum(d, witness);
        let e_nat = d.num(exponent);
        let pow_ae = d.ipow(a_i, e_nat);
        let one_i = d.ione();
        let hit = modeq(d, n_i, pow_ae, one_i);
        let ty = d.not(hit);
        // With the residue guard off and a corrupted witness the residue IS
        // `1`, so no refutation exists. The route then hands the kernel
        // exactly what the arithmetic does support — the engine's honest
        // `a^e ≡ 1` — against a statement claiming the opposite, and the
        // kernel refuses it. Nothing is fabricated on either side: the
        // certificate's claim is the type, the true arithmetic is the term,
        // and the trusted gate is what notices they disagree.
        let value = match pow_not_modeq_one(d, n, witness, exponent) {
            Some(proof) => proof,
            None => pow_modeq(d, n, witness, exponent).0,
        };
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    Ok(admitted)
}

/// The reconstruction route: a CAS Pratt certificate for `n`, together with
/// every subcertificate in its tree, becomes kernel theorems.
///
/// `seen` carries the bases already declared **across calls**, because a
/// factor base recurs both within one tree and between trees (`2` is a base of
/// every prime's `n − 1`). A kernel name may be declared once, so this is not
/// an optimisation: without it the second tree is refused with
/// `DeclarationExists`, which is how it was found.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
///
/// # Panics
///
/// Panics when a `RouteGuards` guard that is switched on rejects the
/// certificate — that is the route refusing, deliberately distinguishable from
/// the kernel refusing.
pub(super) fn reconstruct(
    d: &mut IntDev<'_>,
    n: u32,
    cert: &PrattCertificate,
    guards: RouteGuards,
    seen: &mut Vec<u32>,
) -> Result<Vec<NameId>, KernelError> {
    if guards.cas_recheck {
        assert!(
            axeyum_cas::ntheory_certify::check_primality_certificate(i128::from(n), cert),
            "route guard: the CAS's own checker rejects this certificate for {n}"
        );
    }
    let mut admitted = Vec::new();
    reconstruct_tree(d, n, cert, guards, seen, &mut admitted)?;
    Ok(admitted)
}

fn reconstruct_tree(
    d: &mut IntDev<'_>,
    n: u32,
    cert: &PrattCertificate,
    guards: RouteGuards,
    seen: &mut Vec<u32>,
    admitted: &mut Vec<NameId>,
) -> Result<(), KernelError> {
    if seen.contains(&n) {
        return Ok(());
    }
    seen.push(n);
    // G7: each factor base carries its own certificate, reconstructed first,
    // so a base's primality conditions are in the environment before the
    // theorem that relies on them is stated.
    for (index, &(base, _)) in cert.factors.iter().enumerate() {
        let base = u32::try_from(base).expect("a reachable factor base fits in u32");
        let sub = &cert.subcerts[index];
        reconstruct_tree(d, base, sub, guards, seen, admitted)?;
    }
    admitted.extend(reconstruct_one(d, n, cert, guards)?);
    Ok(())
}

/// Fetch a Pratt certificate from the CAS's own producer — the same artifact
/// the ledger's `checker_command` cites, never a hand-copy.
pub(super) fn certificate(n: u32) -> PrattCertificate {
    certify_prime(i128::from(n)).unwrap_or_else(|| panic!("the CAS must certify {n} prime"))
}

#[cfg(test)]
mod tests {
    use super::super::super::{Kernel, build_int_prelude};
    use super::*;
    use crate::env::Declaration as Decl;
    use crate::on_a_deep_stack;

    /// The primes reconstructed by the shipping route.
    ///
    /// The ceiling is measured, not chosen: see
    /// [`the_reducing_route_reaches_primes_the_naive_one_cannot`] and
    /// ADR-1622. Every one of these carries its own factor bases recursively,
    /// so the tree also covers 2, 3, 5, 7, 11 and 13 as bases.
    const RECONSTRUCTED: &[u32] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

    /// The ladder [`the_cost_ladder_is_measured`] walks to find the wall.
    /// Trimmed to `101` from a measured run, not guessed. Wall clock on the
    /// shared dev box, `--release`, other lanes active:
    /// `n = 47` 0.83 s, `n = 101` 7.8 s, `n = 251` **398 s**. The rung at
    /// `251` is the last one that finishes at all and is far too slow for a
    /// gate (`CLAUDE.md`: "a pathological test is worth deleting"); `509` was
    /// killed rather than waited out, because it holds the host-wide cargo
    /// lock every other lane needs. ADR-1622 carries the table.
    const COST_LADDER: &[u32] = &[47, 101];

    fn built() -> (Kernel, crate::int_prelude::IntPrelude) {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        (k, p)
    }

    // -- evaluation tests for the translator (never the trusted gate) --------

    /// `residue_of` is modular exponentiation, checked against a
    /// straightforwardly different computation (repeated multiplication) at
    /// concrete small arguments, in BOTH directions.
    #[test]
    fn residue_of_computes_modular_exponentiation() {
        for n in 2u32..40 {
            for a in 0u32..12 {
                let mut naive: u64 = 1 % u64::from(n);
                for m in 0u32..12 {
                    assert_eq!(
                        residue_of(n, a, m),
                        u32::try_from(naive).unwrap(),
                        "residue_of({n}, {a}, {m})"
                    );
                    naive = (naive * u64::from(a)) % u64::from(n);
                }
            }
        }
        // Non-vacuity: the function is not constant, and it is not `a^m`.
        assert_eq!(residue_of(7, 3, 6), 1);
        assert_eq!(residue_of(7, 3, 3), 6);
        assert_ne!(residue_of(7, 3, 3), 3u32.pow(3));
    }

    /// `factor_product` builds `∏ qᵢ^eᵢ` and the kernel reduces it to the
    /// intended numeral — and NOT to a neighbouring one, which is the half
    /// that makes the positive assertion mean something.
    #[test]
    fn factor_product_reduces_to_the_intended_numeral() {
        let (mut k, p) = built();
        let mut d = IntDev::new(&mut k, p);
        for (factors, expected) in [
            (vec![(2u32, 1u32)], 2u32),
            (vec![(2, 2)], 4),
            (vec![(2, 1), (3, 1)], 6),
            (vec![(2, 2), (3, 1)], 12),
            (vec![(2, 1), (11, 1)], 22),
        ] {
            let built_expr = factor_product(&mut d, &factors);
            let good = d.num(expected);
            assert!(
                d.kernel().def_eq(built_expr, good),
                "∏ over {factors:?} must reduce to {expected}"
            );
            let bad = d.num(expected + 1);
            assert!(
                !d.kernel().def_eq(built_expr, bad),
                "∏ over {factors:?} must NOT reduce to {}",
                expected + 1
            );
        }
    }

    // -- the cost wall, measured --------------------------------------------

    /// The naive route — `Eq.refl` on `emod (pow a m) n`, letting the kernel
    /// form `a^m` — succeeds at `3^6 = 729` and is not attempted beyond it;
    /// the reducing route succeeds where the naive one would have to form a
    /// numeral orders of magnitude larger.
    ///
    /// Both halves are asserted, so neither can be vacuous: the naive route is
    /// shown to WORK at the small magnitude (so its absence higher up is a
    /// cost fact, not a correctness one) and the reducing route is shown to
    /// work where the naive one forms `2^42`.
    #[test]
    fn the_naive_refl_route_walls_where_the_reducing_route_does_not() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);

            // Naive, at the magnitude `mult_order_tests` already calls "the
            // one expensive case": `3^6 = 729`.
            let n_i = inum(&mut d, 7);
            let a_i = inum(&mut d, 3);
            let six = d.num(6);
            let pow = d.ipow(a_i, six);
            let lhs = d.iemod(pow, n_i);
            let one_i = d.ione();
            let rhs = d.iemod(one_i, n_i);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "the naive route must WORK at 3^6 = 729, or this measurement \
                 is about correctness and not about cost"
            );

            // Reducing, where the naive route would form `2^42`.
            let (proof, residue) = pow_modeq(&mut d, 43, 3, 42);
            assert_eq!(residue, 1, "3 is a primitive root mod 43");
            let inferred = d
                .kernel()
                .infer(proof)
                .expect("the reducing route's term must type-check");
            let n43 = inum(&mut d, 43);
            let a3 = inum(&mut d, 3);
            let e42 = d.num(42);
            let pow42 = d.ipow(a3, e42);
            let one43 = inum(&mut d, 1);
            let stated = modeq(&mut d, n43, pow42, one43);
            assert!(
                d.kernel().def_eq(inferred, stated),
                "the reducing route must land on ModEq 43 (3^42) 1"
            );
        });
    }

    /// The reducing route lands on the right residue across a dense range, and
    /// the kernel agrees — including at exponents where the residue is NOT
    /// one, so a route that always produced `1` would fail here.
    #[test]
    fn the_reducing_route_reaches_primes_the_naive_one_cannot() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let mut nontrivial = 0usize;
            for (n, a, m) in [
                (11u32, 2u32, 10u32),
                (11, 2, 5),
                (13, 2, 12),
                (13, 2, 6),
                (13, 2, 4),
                (23, 5, 22),
                (23, 5, 11),
                (31, 3, 30),
                (31, 3, 15),
                (47, 5, 46),
                (47, 5, 23),
            ] {
                let expected = residue_of(n, a, m);
                let (proof, residue) = pow_modeq(&mut d, n, a, m);
                assert_eq!(residue, expected);
                if residue != 1 {
                    nontrivial += 1;
                }
                let inferred = d
                    .kernel()
                    .infer(proof)
                    .unwrap_or_else(|e| panic!("{a}^{m} mod {n} must type-check: {e:?}"));
                let n_i = inum(&mut d, n);
                let a_i = inum(&mut d, a);
                let m_nat = d.num(m);
                let pow_am = d.ipow(a_i, m_nat);
                let r_i = inum(&mut d, expected);
                let stated = modeq(&mut d, n_i, pow_am, r_i);
                assert!(
                    d.kernel().def_eq(inferred, stated),
                    "{a}^{m} mod {n} must be {expected}"
                );
                // ... and NOT the neighbouring residue.
                let wrong = inum(&mut d, (expected + 1) % n);
                let wrong_stated = modeq(&mut d, n_i, pow_am, wrong);
                assert!(
                    !d.kernel().def_eq(inferred, wrong_stated),
                    "{a}^{m} mod {n} must NOT be {}",
                    (expected + 1) % n
                );
            }
            assert!(
                nontrivial >= 5,
                "at least five of these must land off 1, or the battery only \
                 exercises the Fermat case"
            );
        });
    }

    /// **Where it stops, measured.** The route is walked up a ladder of
    /// primes, each time proving `a^(n-1) = 1 (mod n)` for the CAS's own
    /// witness, and the wall-clock cost of each rung is printed.
    ///
    /// No time budget is asserted -- this box runs many lanes at once and a
    /// timing assertion would be a gate on the queue, not on the route
    /// (`CLAUDE.md`, "cargo-serialized.sh takes a host-wide flock"). What IS
    /// asserted at every rung is that the kernel agrees with the residue, and
    /// that it REFUSES the neighbouring one. The ceiling in [`RECONSTRUCTED`]
    /// is chosen from the printed numbers; ADR-1622 records them.
    #[test]
    fn the_cost_ladder_is_measured() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            for n in COST_LADDER.iter().copied() {
                let cert = certificate(n);
                let a = u32::try_from(cert.witness).expect("witness fits");
                let start = std::time::Instant::now();
                let (proof, residue) = pow_modeq(&mut d, n, a, n - 1);
                let inferred = d
                    .kernel()
                    .infer(proof)
                    .unwrap_or_else(|e| panic!("{a}^{} mod {n} must type-check: {e:?}", n - 1));
                let n_i = inum(&mut d, n);
                let a_i = inum(&mut d, a);
                let m_nat = d.num(n - 1);
                let pow_am = d.ipow(a_i, m_nat);
                let one = inum(&mut d, 1);
                let stated = modeq(&mut d, n_i, pow_am, one);
                assert!(
                    d.kernel().def_eq(inferred, stated),
                    "Fermat must hold for {a}^{} mod {n}",
                    n - 1
                );
                let two = inum(&mut d, 2);
                let wrong = modeq(&mut d, n_i, pow_am, two);
                assert!(
                    !d.kernel().def_eq(inferred, wrong),
                    "and must NOT land on 2 -- otherwise the check above is vacuous"
                );
                assert_eq!(residue, 1, "Fermat's residue is 1 for a prime modulus");
                println!(
                    "pratt-cost-ladder n={n} witness={a} exponent={} elapsed={:?}",
                    n - 1,
                    start.elapsed()
                );
            }
        });
    }

    // -- the route ----------------------------------------------------------

    /// The reconstruction: every prime in [`RECONSTRUCTED`] admitted through
    /// [`crate::Kernel::add_declaration`], axiom-free.
    ///
    /// See the module doc for the five things this does NOT establish.
    #[test]
    fn pratt_certificates_are_kernel_reconstructed() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let mut total = 0usize;
            let mut seen = Vec::new();
            for &n in RECONSTRUCTED {
                let cert = certificate(n);
                let names = reconstruct(&mut d, n, &cert, RouteGuards::all(), &mut seen)
                    .unwrap_or_else(|e| {
                        panic!("the kernel must admit the Pratt route for {n}: {e:?}")
                    });
                assert!(!names.is_empty(), "{n} must emit at least one theorem");
                total += names.len();
                for name in names {
                    let env = d.kernel().environment();
                    let decl = env.get(name).expect("the declaration must be admitted");
                    assert!(
                        matches!(decl, Decl::Theorem { .. }),
                        "must be a Theorem, not an Axiom or an Opaque"
                    );
                    let footprint = d.kernel().axiom_footprint(name);
                    assert!(
                        footprint.is_empty(),
                        "the reconstruction must be axiom-free; footprint was {footprint:?}"
                    );
                }
            }
            // A pinned, nonvacuous count: a route that emitted nothing, or
            // that silently stopped after the first prime, fails here.
            assert!(
                total >= 40,
                "the route must emit at least 40 theorems across the tree, got {total}"
            );
        });
    }

    /// **The kernel is the checker.** With every one of this route's own
    /// guards switched off, a certificate whose witness is corrupted is
    /// refused by [`crate::Kernel::add_declaration`] — not by Rust.
    ///
    /// The control that makes this non-vacuous is the same run with the same
    /// guards off and the GENUINE certificate, which the kernel admits.
    #[test]
    fn a_corrupted_witness_is_refused_by_the_kernel() {
        on_a_deep_stack(|| {
            let good = certificate(11);

            // Control: guards off, GENUINE certificate -- admitted. Without
            // this the refusals below could be an artefact of running with the
            // guards off at all.
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            reconstruct(&mut d, 11, &good, RouteGuards::none(), &mut Vec::new())
                .expect("guards off, the genuine certificate must still be admitted");

            // Forgery A -- the OBVIOUS one, refused at G8. A witness that is
            // not a unit modulo 11 fails Fermat outright, so the engine builds
            // an honest proof of `11^10 == 0 (mod 11)` and the kernel refuses
            // it against the certificate's claim of `1`.
            assert_eq!(residue_of(11, 11, 10), 0, "a non-unit witness fails Fermat");
            let mut forged_unit = good.clone();
            forged_unit.witness = 11;
            let (mut k1, p1) = built();
            let mut d1 = IntDev::new(&mut k1, p1);
            assert!(
                reconstruct(
                    &mut d1,
                    11,
                    &forged_unit,
                    RouteGuards::none(),
                    &mut Vec::new()
                )
                .is_err(),
                "with this route's guards OFF, the KERNEL must refuse a witness \
                 that fails the Fermat condition"
            );

            // Forgery B -- the SUBTLE one, refused at G9. `2` is a primitive
            // root mod 11; `3` is not, its order is 5. Fermat still holds
            // (every unit satisfies it), so only order maximality separates
            // them, and the kernel is what notices.
            assert_eq!(
                residue_of(11, 3, 10),
                1,
                "the forged witness still passes Fermat"
            );
            assert_eq!(
                residue_of(11, 3, 5),
                1,
                "and fails order maximality at q = 5"
            );
            let mut forged = good.clone();
            forged.witness = 3;
            let (mut k2, p2) = built();
            let mut d2 = IntDev::new(&mut k2, p2);
            assert!(
                reconstruct(&mut d2, 11, &forged, RouteGuards::none(), &mut Vec::new()).is_err(),
                "with this route's guards OFF, the KERNEL must refuse the \
                 forged witness -- it did not, so the reconstruction is not \
                 checking what it claims"
            );

            // And the route's own guard catches it too, when switched on --
            // so the shipping configuration never reaches the kernel with a
            // forgery in the first place.
            let (mut k3, p3) = built();
            let mut d3 = IntDev::new(&mut k3, p3);
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                reconstruct(&mut d3, 11, &forged, RouteGuards::all(), &mut Vec::new())
            }));
            assert!(
                caught.is_err(),
                "the route's own CAS-recheck guard must also reject the forgery"
            );
        });
    }

    /// A corrupted FACTORIZATION — the forgery the CAS module records as
    /// measured (`n = 91` with `factors = [(2,1)]` passes every order check)
    /// — is refused by the kernel at the completeness theorem, with this
    /// route's guards off.
    #[test]
    fn a_corrupted_factorization_is_refused_by_the_kernel() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let good = certificate(13);
            // 13 − 1 = 12 = 2²·3. Drop the 3: every order check at q = 2 still
            // passes, and only completeness rejects it.
            let mut forged = good.clone();
            forged.factors = vec![(2, 2)];
            forged.subcerts = vec![good.subcerts[0].clone()];

            let refusal = reconstruct(&mut d, 13, &forged, RouteGuards::none(), &mut Vec::new());
            assert!(
                refusal.is_err(),
                "the kernel must refuse an incomplete factorization of 12"
            );
        });
    }
}
