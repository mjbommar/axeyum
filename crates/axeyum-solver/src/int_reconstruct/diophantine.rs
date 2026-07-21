//! Diophantine integer-infeasibility reconstruction over the shared integer
//! kernel context.

use std::collections::BTreeMap;

use axeyum_ir::{SymbolId, TermArena, TermId};
use axeyum_lean_kernel::{BinderInfo, ExprId};

use crate::lia_gcd::{DiophantineCertificate, Equality, prove_lia_unsat_by_diophantine_certified};
use crate::reconstruct::ReconstructError;

use super::{
    DIO_UNIT_MAX, IGen, IntReconstructCtx, ZExpr, intlit_zexpr, lin_to_canon_gens, lin_to_zexpr,
};

/// Reconstruct an integer Diophantine refutation to a kernel-checked Lean
/// `False` proof term.
///
/// Handles both the non-divisible-gcd contradiction and the degenerate
/// all-variables-cancelled `0 = constant` row.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] when no supported refutation
/// exists or a bound/normalization check declines, and
/// [`ReconstructError::KernelRejected`] if the assembled proof does not check.
pub fn reconstruct_diophantine_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let (_, proof) = build_and_gate_diophantine(arena, assertions)?;
    Ok(proof)
}

/// The theorem name used for the exported Diophantine refutation Lean module.
const DIO_LEAN_THEOREM: &str = "axeyum_refutation";

/// **Like [`reconstruct_diophantine_proof`], but also renders a self-contained Lean
/// module** (`render_lean_module`) re-proving the refutation. A successful return
/// means the proof was emitted, kernel-checked to `False`, and rendered to
/// externally-checkable Lean source.
///
/// # Errors
///
/// Same as [`reconstruct_diophantine_proof`].
pub fn reconstruct_diophantine_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let (mut ctx, proof) = build_and_gate_diophantine(arena, assertions)?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    Ok(ctx
        .kernel()
        .render_lean_module(DIO_LEAN_THEOREM, false_, proof))
}

/// Shared core: run the Diophantine decision, build the `False` proof over a fresh
/// [`IntReconstructCtx`], and gate it through the kernel (`infer` + `def_eq False`).
/// Returns the context (carrying the full environment) and the gated proof term.
fn build_and_gate_diophantine(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<(IntReconstructCtx, ExprId), ReconstructError> {
    let Some((equalities, cert)) = prove_lia_unsat_by_diophantine_certified(arena, assertions)
    else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no Diophantine (integer-infeasibility) refutation for these assertions"
                .to_owned(),
        });
    };
    let mut ctx = IntReconstructCtx::new();
    let proof = ctx.build_diophantine_false(&equalities, &cert)?;
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "diophantine".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok((ctx, proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "diophantine".to_owned(),
            detail: "Diophantine refutation did not infer to False".to_owned(),
        })
    }
}

/// Map the certificate's [`SymbolId`] keys to dense `0..n` variable indices in a
/// deterministic (sorted) order, so the kernel encoding is stable.
fn dense_index_map(
    equalities: &[Equality],
    cert: &DiophantineCertificate,
) -> BTreeMap<SymbolId, usize> {
    let mut syms: std::collections::BTreeSet<SymbolId> = std::collections::BTreeSet::new();
    for eq in equalities {
        for &s in eq.coeffs.keys() {
            syms.insert(s);
        }
    }
    for &(s, _) in &cert.combined {
        syms.insert(s);
    }
    syms.into_iter().enumerate().map(|(i, s)| (s, i)).collect()
}

impl IntReconstructCtx {
    /// Sum the scaled hypotheses into `h_comb : Eq Z combined_expr (intlit constant)`.
    ///
    /// `combined_expr = Σ_j combined_j x_j` (canonical gens of `combined_dense`). The
    /// proof scales each `h_i : Eq Z L_i (intlit b_i)` by `λ_i` (signed repetition,
    /// via `congr_add` over copies and `congr_neg`), sums them (`congr_add`), and
    /// normalizes both sides; the normalizer's canonical forms must match
    /// `combined_dense` (LHS) and `intlit constant` (RHS), else we decline.
    #[allow(clippy::type_complexity, clippy::too_many_lines)]
    fn combine_equalities(
        &mut self,
        hyps: &[(ExprId, Vec<IGen>, ExprId, i128, ExprId)],
        multipliers: &[i128],
        combined_dense: &[(usize, i128)],
        constant: i128,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine combine declined: {d}"),
        };
        if hyps.len() != multipliers.len() {
            return Err(decline("multiplier/hyp count mismatch"));
        }
        // Build the scaled LHS / RHS ZExprs and a single Eq proof for the whole sum.
        // We accumulate `acc : Eq Z lhs_acc rhs_acc` where lhs_acc/rhs_acc are
        // right-built sums of the scaled terms.
        let mut acc: Option<(ExprId, ExprId, ExprId)> = None; // (lhs, rhs, proof)
        for (eq_idx, (l_expr, _l_gens, r_expr, _b_i, h)) in hyps.iter().enumerate() {
            let (l_expr, r_expr, h) = (*l_expr, *r_expr, *h);
            let lambda = multipliers[eq_idx];
            if lambda == 0 {
                continue;
            }
            // Scaled equality: Eq Z (λ·L_i)(λ·R_i). Build by repeating `h` |λ| times
            // under add, then negating if λ < 0.
            let (mut s_lhs, mut s_rhs, mut s_proof) = (l_expr, r_expr, h);
            let count = lambda.unsigned_abs();
            for _ in 1..count {
                // acc' = add acc base : Eq Z (add s_lhs L_i)(add s_rhs R_i).
                let new_lhs = self.mk_add(s_lhs, l_expr);
                let new_rhs = self.mk_add(s_rhs, r_expr);
                // congr: add s_lhs L_i = add s_rhs L_i (congr_add_left s_proof) then
                //        add s_rhs L_i = add s_rhs R_i (congr_add_right h).
                let mid = self.mk_add(s_rhs, l_expr);
                let cong_l = self.congr_add_left(s_lhs, s_rhs, l_expr, s_proof);
                let cong_r = self.congr_add_right(s_rhs, l_expr, r_expr, h);
                let p = self.eq_trans(new_lhs, mid, new_rhs, cong_l, cong_r);
                s_lhs = new_lhs;
                s_rhs = new_rhs;
                s_proof = p;
            }
            if lambda < 0 {
                let neg_lhs = self.mk_neg(s_lhs);
                let neg_rhs = self.mk_neg(s_rhs);
                let p = self.congr_neg(s_lhs, s_rhs, s_proof);
                s_lhs = neg_lhs;
                s_rhs = neg_rhs;
                s_proof = p;
            }
            acc = Some(match acc {
                None => (s_lhs, s_rhs, s_proof),
                Some((a_lhs, a_rhs, a_proof)) => {
                    let new_lhs = self.mk_add(a_lhs, s_lhs);
                    let new_rhs = self.mk_add(a_rhs, s_rhs);
                    let mid = self.mk_add(a_rhs, s_lhs);
                    let cong_l = self.congr_add_left(a_lhs, a_rhs, s_lhs, a_proof);
                    let cong_r = self.congr_add_right(a_rhs, s_lhs, s_rhs, s_proof);
                    let p = self.eq_trans(new_lhs, mid, new_rhs, cong_l, cong_r);
                    (new_lhs, new_rhs, p)
                }
            });
        }
        let Some((lhs_acc, rhs_acc, proof_acc)) = acc else {
            return Err(decline("all multipliers zero"));
        };
        // Normalize lhs_acc and rhs_acc; check they canonicalize to combined / constant.
        let (lhs_gens, _lhs_k, lhs_norm) = self
            .normalize_kernel(lhs_acc)
            .ok_or_else(|| decline("lhs normalizer declined"))?;
        let (rhs_gens, _rhs_k, rhs_norm) = self
            .normalize_kernel(rhs_acc)
            .ok_or_else(|| decline("rhs normalizer declined"))?;
        let expected_lhs = lin_to_canon_gens(combined_dense, 0);
        let expected_rhs = lin_to_canon_gens(&[], constant);
        if lhs_gens != expected_lhs {
            return Err(decline(
                "combined LHS did not canonicalize to Σ combined_j x_j",
            ));
        }
        if rhs_gens != expected_rhs {
            return Err(decline("combined RHS did not canonicalize to the constant"));
        }
        // We want `h_comb : Eq Z combined_faithful (intlit constant)`, where
        // `combined_faithful` is the FAITHFUL `lin_to_zexpr(combined_dense, 0)` form
        // (the same operand the step-3 reduction uses), NOT the right-nested canonical
        // form. We have:
        //   proof_acc           : Eq Z lhs_acc rhs_acc
        //   lhs_norm            : Eq Z lhs_acc lhs_canon
        //   rhs_norm            : Eq Z rhs_acc rhs_canon
        // and both lhs_acc and combined_faithful canonicalize to the SAME `lhs_gens`.
        let lhs_canon = self.gens_to_expr(&lhs_gens);
        let rhs_canon = self.gens_to_expr(&rhs_gens);
        // Faithful combined form and its own normalization to `lhs_canon`. When the
        // combined row is empty (the degenerate `g = 0` case: all variables cancel),
        // the faithful form is `zero`, which `normalize_kernel` reads as `ZExpr::Zero`
        // and canonicalizes to the empty gen list (= `expected_lhs`). This yields
        // `h_comb : Eq Z zero (intlit constant)` for the `0 = constant` contradiction.
        let combined_faithful = match lin_to_zexpr(combined_dense, 0) {
            Some(z) => self.emit_zexpr(&z),
            None => self.mk_zero(),
        };
        let (cf_gens, cf_kexpr, cf_norm) = self
            .normalize_kernel(combined_faithful)
            .ok_or_else(|| decline("combined faithful normalizer declined"))?;
        if cf_gens != expected_lhs {
            return Err(decline(
                "combined faithful did not canonicalize as expected",
            ));
        }
        debug_assert_eq!(cf_kexpr, combined_faithful);
        // cf_norm : Eq Z combined_faithful lhs_canon.
        // chain: combined_faithful = lhs_canon = lhs_acc = rhs_acc = rhs_canon = const.
        let lhs_canon_to_acc = self.eq_symm(lhs_acc, lhs_canon, lhs_norm); // lhs_canon = lhs_acc
        let cf_to_acc = self.eq_trans(
            combined_faithful,
            lhs_canon,
            lhs_acc,
            cf_norm,
            lhs_canon_to_acc,
        );
        let cf_to_rhs = self.eq_trans(combined_faithful, lhs_acc, rhs_acc, cf_to_acc, proof_acc);
        let cf_to_rcanon =
            self.eq_trans(combined_faithful, rhs_acc, rhs_canon, cf_to_rhs, rhs_norm);
        let const_lit = self.mk_intlit(constant);
        let const_bridge = self.intlit_eq_canon(constant); // Eq Z const_lit rhs_canon
        let rcanon_to_lit = self.eq_symm(const_lit, rhs_canon, const_bridge); // rhs_canon = const_lit
        Ok(self.eq_trans(
            combined_faithful,
            rhs_canon,
            const_lit,
            cf_to_rcanon,
            rcanon_to_lit,
        ))
    }
    /// Prove `m' < 1` from `gm : Eq Z (mul g_lit m') r_lit`, `h_g_pos : lt zero
    /// g_lit`, `h_r_lt_g : lt r_lit g_lit`.
    ///
    /// `le_total m' 1 → Or (le m' 1)(le 1 m')`; the `le 1 m'` branch contradicts
    /// (`g = g·1 ≤ g·m' = r < g`). After `Or.rec` we have `le m' 1`, strengthened to
    /// `lt m' 1` by `lt_of_le_of_ne` with `m' ≠ 1` (else `g·m' = g·1 = g ≠ r`).
    fn prove_m_prime_lt_one(
        &mut self,
        g_lit: ExprId,
        m_prime: ExprId,
        r_lit: ExprId,
        gm: ExprId,
        h_g_pos: ExprId,
        h_r_lt_g: ExprId,
    ) -> ExprId {
        let one = self.mk_one();
        let zero = self.mk_zero();
        // le_total m' one : Or (le m' one)(le one m').
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, m_prime);
            self.kernel.app(e, one)
        };
        let a_prop = self.mk_le(m_prime, one); // le m' one
        let b_prop = self.mk_le(one, m_prime); // le one m'
        // h_g_nonneg : le zero g_lit  (le_of_lt h_g_pos).
        let h_g_nonneg = self.le_of_lt_app(zero, g_lit, h_g_pos);
        // minor_inl : (le m' one) → le m' one  (identity lambda).
        let target = self.mk_le(m_prime, one);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        // minor_inr : (le one m') → le m' one  (derive le m' one from a contradiction).
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_one_mp = self.kernel.fvar(fid); // le one m'
            // mul_le_mul_of_nonneg_left g one m' h_g_nonneg h_le_one_mp : le (mul g one)(mul g m').
            let le_gone_gmp =
                self.mul_le_mul_left_app(g_lit, one, m_prime, h_g_nonneg, h_le_one_mp);
            // cast (mul g one) → g via mul_one.
            let g_one = self.mk_mul(g_lit, one);
            let mul_one = self.mul_one_eq(g_lit); // mul g one = g
            let gmp = self.mk_mul(g_lit, m_prime);
            let le_g_gmp = self.le_cast_left(g_one, g_lit, gmp, le_gone_gmp, mul_one); // le g (g·m')
            // cast (mul g m') → r via gm : Eq Z (mul g m') r.
            let le_g_r = self.le_cast_right(g_lit, gmp, r_lit, le_g_gmp, gm); // le g r
            // lt_of_le_of_lt g r g  (le g r, lt r g) : lt g g.
            let lt_g_g = self.lt_of_le_of_lt_app(g_lit, r_lit, g_lit, le_g_r, h_r_lt_g);
            // lt_irrefl g lt_g_g : False.
            let irr = self.lt_irrefl_app(g_lit);
            let false_proof = self.kernel.app(irr, lt_g_g);
            // ex falso into `le m' one`.
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        // Or.rec A B (fun _ => target) minor_inl minor_inr or_proof : le m' one.
        let le_mp_one = {
            let anon = self.kernel.anon();
            let or_ab = {
                let or_c = self.kernel.const_(self.int.logic.or, vec![]);
                let e = self.kernel.app(or_c, a_prop);
                self.kernel.app(e, b_prop)
            };
            let motive = self.kernel.lam(anon, or_ab, target, BinderInfo::Default);
            let rec = self.kernel.const_(self.int.logic.or_rec, vec![]);
            let e = self.kernel.app(rec, a_prop);
            let e = self.kernel.app(e, b_prop);
            let e = self.kernel.app(e, motive);
            let e = self.kernel.app(e, minor_inl);
            let e = self.kernel.app(e, minor_inr);
            self.kernel.app(e, or_proof)
        };
        // m' ≠ one : Not (Eq Z m' one) = fun (h : Eq Z m' one) => False.
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z m' one
            // congr: Eq Z (mul g m')(mul g one).
            let gmp = self.mk_mul(g_lit, m_prime);
            let g_one = self.mk_mul(g_lit, one);
            let cong = self.congr_mul_right(g_lit, m_prime, one, h_eq); // mul g m' = mul g one
            let mul_one = self.mul_one_eq(g_lit); // mul g one = g
            // mul g m' = g : trans cong mul_one.
            let gmp_eq_g = self.eq_trans(gmp, g_one, g_lit, cong, mul_one); // mul g m' = g
            // r = g : trans (symm gm) (mul g m' = g).
            let r_eq_gmp = self.eq_symm(gmp, r_lit, gm); // gm: Eq (mul g m') r ⇒ Eq r (mul g m')
            let r_eq_g = self.eq_trans(r_lit, gmp, g_lit, r_eq_gmp, gmp_eq_g); // Eq Z r g
            // cast lt r g (h_r_lt_g) along r = g on the LEFT ⇒ lt g g.
            let lt_g_g = self.lt_cast_left(r_lit, g_lit, g_lit, h_r_lt_g, r_eq_g);
            let irr = self.lt_irrefl_app(g_lit);
            let false_proof = self.kernel.app(irr, lt_g_g);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_m_one = self.mk_eq(m_prime, one);
            self.kernel.lam(anon, eq_m_one, body, BinderInfo::Default)
        };
        // lt_of_le_of_ne m' one (le m' one) (m' ≠ one) : lt m' one.
        self.lt_of_le_of_ne_app(m_prime, one, le_mp_one, not_eq)
    }

    /// Prove `0 < m'` from `gm : Eq Z (mul g_lit m') r_lit`, `h_g_pos : lt zero
    /// g_lit`, `h_r_pos : lt zero r_lit`.
    ///
    /// Symmetric to [`Self::prove_m_prime_lt_one`] with `0`: `le_total m' 0`; the
    /// `le m' 0` branch gives `g·m' ≤ g·0 = 0`, i.e. `r ≤ 0`, contradicting `0 < r`.
    /// After `Or.rec` we have `le 0 m'`; `m' ≠ 0` (else `g·m' = 0 ≠ r`) strengthens
    /// to `0 < m'`.
    fn prove_zero_lt_m_prime(
        &mut self,
        g_lit: ExprId,
        m_prime: ExprId,
        r_lit: ExprId,
        gm: ExprId,
        h_g_pos: ExprId,
        h_r_pos: ExprId,
    ) -> ExprId {
        let zero = self.mk_zero();
        // le_total zero m' : Or (le zero m')(le m' zero).
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, zero);
            self.kernel.app(e, m_prime)
        };
        let a_prop = self.mk_le(zero, m_prime); // le zero m'
        let b_prop = self.mk_le(m_prime, zero); // le m' zero
        let h_g_nonneg = self.le_of_lt_app(zero, g_lit, h_g_pos);
        let target = self.mk_le(zero, m_prime);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_mp_zero = self.kernel.fvar(fid); // le m' zero
            // mul_le_mul_of_nonneg_left g m' zero h_g_nonneg h_le_mp_zero : le (mul g m')(mul g zero).
            let le_gmp_gzero =
                self.mul_le_mul_left_app(g_lit, m_prime, zero, h_g_nonneg, h_le_mp_zero);
            // cast (mul g zero) → zero via mul_zero.
            let g_zero = self.mk_mul(g_lit, zero);
            let mul_zero = self.mul_zero_eq(g_lit); // mul g zero = zero
            let gmp = self.mk_mul(g_lit, m_prime);
            let le_gmp_zero = self.le_cast_right(gmp, g_zero, zero, le_gmp_gzero, mul_zero); // le (g·m') zero
            // cast (mul g m') → r via gm on the LEFT.
            let le_r_zero = self.le_cast_left(gmp, r_lit, zero, le_gmp_zero, gm); // le r zero
            // lt_of_lt_of_le zero r zero (lt zero r)(le r zero) : lt zero zero.
            let lt_zero_zero = self.lt_of_lt_of_le_app(zero, r_lit, zero, h_r_pos, le_r_zero);
            let irr = self.lt_irrefl_app(zero);
            let false_proof = self.kernel.app(irr, lt_zero_zero);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_zero_mp = {
            let anon = self.kernel.anon();
            let or_ab = {
                let or_c = self.kernel.const_(self.int.logic.or, vec![]);
                let e = self.kernel.app(or_c, a_prop);
                self.kernel.app(e, b_prop)
            };
            let motive = self.kernel.lam(anon, or_ab, target, BinderInfo::Default);
            let rec = self.kernel.const_(self.int.logic.or_rec, vec![]);
            let e = self.kernel.app(rec, a_prop);
            let e = self.kernel.app(e, b_prop);
            let e = self.kernel.app(e, motive);
            let e = self.kernel.app(e, minor_inl);
            let e = self.kernel.app(e, minor_inr);
            self.kernel.app(e, or_proof)
        };
        // zero ≠ m' : Not (Eq Z zero m') = fun (h : Eq Z zero m') => False.
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z zero m'
            // h_eq_sym : Eq Z m' zero.
            let gmp = self.mk_mul(g_lit, m_prime);
            let g_zero = self.mk_mul(g_lit, zero);
            let h_eq_sym = self.eq_symm(zero, m_prime, h_eq); // m' = zero
            // congr: mul g m' = mul g zero.
            let cong = self.congr_mul_right(g_lit, m_prime, zero, h_eq_sym);
            let mul_zero = self.mul_zero_eq(g_lit); // mul g zero = zero
            let gmp_eq_zero = self.eq_trans(gmp, g_zero, zero, cong, mul_zero); // mul g m' = zero
            // r = mul g m' = zero ⇒ Eq Z r zero.
            let r_eq_gmp = self.eq_symm(gmp, r_lit, gm); // r = mul g m'
            let r_eq_zero = self.eq_trans(r_lit, gmp, zero, r_eq_gmp, gmp_eq_zero); // r = zero
            // cast lt zero r (h_r_pos) along r = zero on the RIGHT ⇒ lt zero zero.
            let lt_zero_zero = self.lt_cast_right(zero, r_lit, zero, h_r_pos, r_eq_zero);
            let irr = self.lt_irrefl_app(zero);
            let false_proof = self.kernel.app(irr, lt_zero_zero);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_zero_m = self.mk_eq(zero, m_prime);
            self.kernel.lam(anon, eq_zero_m, body, BinderInfo::Default)
        };
        // lt_of_le_of_ne zero m' (le zero m')(zero ≠ m') : lt zero m'.
        self.lt_of_le_of_ne_app(zero, m_prime, le_zero_mp, not_eq)
    }
    /// `lt (intlit c) zero` for `c < 0`. Derived from `lt zero (intlit |c|)` by
    /// adding `intlit c` to both sides (`add_lt_add_of_le_of_lt` with `le_refl`),
    /// then renormalizing `intlit c + 0 → intlit c` and `intlit c + intlit |c| → 0`.
    fn lt_neg_intlit_zero(&mut self, c: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(c < 0);
        let abs = c.unsigned_abs();
        let abs_i = i128::try_from(abs).map_err(|_| ReconstructError::UnsupportedTerm {
            term: "|constant| overflow".to_owned(),
        })?;
        // h0 : lt zero (intlit |c|).
        let h0 = self.lt_zero_intlit(abs_i)?;
        let zero = self.mk_zero();
        let c_lit = self.mk_intlit(c);
        let abs_lit = self.mk_intlit(abs_i);
        // h_le : le (intlit c)(intlit c)  (le_refl).
        let h_le = self.le_refl_app(c_lit);
        // add_lt_add_of_le_of_lt c c zero |c| h_le h0 : lt (add c zero)(add c |c|).
        let combined = self.add_lt_add_of_le_of_lt_app(c_lit, c_lit, zero, abs_lit, h_le, h0);
        // cast lhs (add c zero) → c via add_zero.
        let c_zero = self.mk_add(c_lit, zero);
        let c_abs = self.mk_add(c_lit, abs_lit);
        let addz = self.add_zero_eq(c_lit); // add c zero = c
        let lt_c_cabs = self.lt_cast_left(c_zero, c_lit, c_abs, combined, addz);
        // cast rhs (add c |c|) → zero : Eq Z (add (intlit c)(intlit |c|)) (intlit 0).
        let sum_eq_zero = self.intlit_add_eq(c, abs_i, 0)?; // Eq Z (add c |c|) (intlit 0) = zero
        Ok(self.lt_cast_right(c_lit, c_abs, zero, lt_c_cabs, sum_eq_zero))
    }

    /// Build `ne_c : Not (Eq Z zero (intlit constant))` for `constant ≠ 0`. The
    /// returned term is the lambda `fun (h : Eq Z zero c) => …` whose body transports
    /// the sign fact (`lt zero c` for `c > 0`, or `lt c zero` for `c < 0`) along `h`
    /// to `lt zero zero` and closes with `lt_irrefl zero`. `Not (Eq Z zero c)`
    /// def-unfolds to `Eq Z zero c → False`, so the lambda's type is the `Not`.
    fn ne_zero_intlit(&mut self, constant: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(constant != 0);
        let zero = self.mk_zero();
        let c_lit = self.mk_intlit(constant);
        // The sign fact, oriented so a cast along `h : Eq Z zero c` lands on `lt zero zero`.
        // c > 0: lt zero c ; cast RIGHT (c → zero) along (symm h).
        // c < 0: lt c zero ; cast LEFT  (c → zero) along (symm h).
        let fid = self.fresh_fvar();
        let h = self.kernel.fvar(fid); // Eq Z zero c
        let h_sym = self.eq_symm(zero, c_lit, h); // Eq Z c zero
        let lt_zero_zero = if constant > 0 {
            let lt_zero_c = self.lt_zero_intlit(constant)?; // lt zero c
            self.lt_cast_right(zero, c_lit, zero, lt_zero_c, h_sym)
        } else {
            let lt_c_zero = self.lt_neg_intlit_zero(constant)?; // lt c zero
            self.lt_cast_left(c_lit, zero, zero, lt_c_zero, h_sym)
        };
        let irr = self.lt_irrefl_app(zero); // Not (lt zero zero)
        let false_proof = self.kernel.app(irr, lt_zero_zero); // False
        let body = self.kernel.abstract_fvars(false_proof, &[fid]);
        let anon = self.kernel.anon();
        let eq_zero_c = self.mk_eq(zero, c_lit);
        Ok(self.kernel.lam(anon, eq_zero_c, body, BinderInfo::Default))
    }

    /// Declare each input equality `E_i` as a hypothesis axiom `h_i : Eq Z L_i
    /// (intlit b_i)`, returning the `(l_expr, l_gens, r_expr, b_i, h_i)` tuples the
    /// combiner consumes. Declines on any coefficient/rhs magnitude over the bound.
    #[allow(clippy::type_complexity)]
    fn build_hyps(
        &mut self,
        equalities: &[Equality],
        index_of: &BTreeMap<SymbolId, usize>,
    ) -> Result<Vec<(ExprId, Vec<IGen>, ExprId, i128, ExprId)>, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };
        let mut hyps: Vec<(ExprId, Vec<IGen>, ExprId, i128, ExprId)> =
            Vec::with_capacity(equalities.len());
        for eq in equalities {
            let dense: Vec<(usize, i128)> =
                eq.coeffs.iter().map(|(&s, &c)| (index_of[&s], c)).collect();
            for &(_, c) in &dense {
                if c.unsigned_abs() > DIO_UNIT_MAX as u128 {
                    return Err(decline("equality coefficient exceeds the bound"));
                }
            }
            if eq.rhs.unsigned_abs() > DIO_UNIT_MAX as u128 {
                return Err(decline("equality rhs exceeds the bound"));
            }
            let l_gens = lin_to_canon_gens(&dense, 0);
            // Encode L_i as the faithful ZExpr (so it hash-conses with later uses).
            let l_expr = match lin_to_zexpr(&dense, 0) {
                Some(z) => self.emit_zexpr(&z),
                None => self.mk_zero(), // L_i ≡ 0 (no variables) — a 0 = b_i row
            };
            let r_expr = self.mk_intlit(eq.rhs);
            let prop = self.mk_eq(l_expr, r_expr);
            let h = self.hyp_axiom(prop)?;
            hyps.push((l_expr, l_gens, r_expr, eq.rhs, h));
        }
        Ok(hyps)
    }

    /// Close the degenerate `g = 0` row: the combined row is `Eq Z zero (intlit
    /// constant)` with `constant ≠ 0`, a contradiction in any ordered ring (no
    /// discreteness needed). `False := ne_c h_comb`, where `ne_c : Not (Eq Z zero
    /// (intlit constant))` is built from the SIGN of `constant`. Declines if
    /// `|constant|` exceeds the unit-expansion bound (keeps the repeated-`one` build
    /// small).
    fn build_diophantine_false_g0(
        &mut self,
        equalities: &[Equality],
        cert: &DiophantineCertificate,
        index_of: &BTreeMap<SymbolId, usize>,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };
        debug_assert!(cert.combined.is_empty());
        if cert.constant == 0 {
            // gcd(∅) = 0 ∤ d requires d ≠ 0; a `0 = 0` row is not a refutation.
            return Err(decline("g = 0 with constant = 0 (no contradiction)"));
        }
        if cert.constant.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("|constant| exceeds the unit-expansion bound"));
        }
        let combined_dense: Vec<(usize, i128)> = Vec::new();
        let hyps = self.build_hyps(equalities, index_of)?;
        // h_comb : Eq Z zero (intlit constant)  (combined LHS normalizes to `zero`).
        let h_comb =
            self.combine_equalities(&hyps, &cert.multipliers, &combined_dense, cert.constant)?;
        // ne_c : Not (Eq Z zero (intlit constant)) ; False := ne_c h_comb.
        let ne_c = self.ne_zero_intlit(cert.constant)?;
        Ok(self.kernel.app(ne_c, h_comb))
    }

    /// Assemble the `False` proof term for the Diophantine certificate. Handles both
    /// the main `g > 0` discreteness path and the degenerate `g = 0` row
    /// (`0 = constant ≠ 0`, all variables cancelled): the latter is a contradiction
    /// in any ordered ring (no discreteness needed), closed by `ne_c h_comb` where
    /// `ne_c : Not (Eq Z zero (intlit constant))`. Returns a [`ReconstructError`]
    /// (decline) on a bound overflow or a normalizer/identity mismatch; the caller
    /// gates the result through `infer`/`def_eq False`.
    #[allow(clippy::too_many_lines)]
    fn build_diophantine_false(
        &mut self,
        equalities: &[Equality],
        cert: &DiophantineCertificate,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };

        // --- dense variable indices (stable, shared by both paths) -------------
        let index_of = dense_index_map(equalities, cert);

        // --- gcd g and Euclidean (q, r): constant = g·q + r, 0 < r < g ---------
        let mut g: i128 = 0;
        for &(_, c) in &cert.combined {
            g = gcd_i128(g, c);
        }
        if g == 0 {
            // Degenerate `0 = constant ≠ 0` row (all variables cancelled). No
            // discreteness is needed — `0 = c` with `c ≠ 0` is false in any ordered
            // ring; route to the dedicated sign-based close.
            return self.build_diophantine_false_g0(equalities, cert, &index_of);
        }
        let mut r = cert.constant % g;
        let mut q = cert.constant / g;
        if r < 0 {
            r += g;
            q -= 1;
        }
        if !(r > 0 && r < g) {
            return Err(decline("certificate not gcd-infeasible (0 < r < g failed)"));
        }
        if g > DIO_UNIT_MAX || r > DIO_UNIT_MAX || q.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("g / r / q exceed the unit-expansion bound"));
        }
        let gq = g.checked_mul(q).ok_or_else(|| decline("g·q overflow"))?;
        if gq.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("g·q exceeds the unit-expansion bound"));
        }

        let mut combined_dense: Vec<(usize, i128)> = cert
            .combined
            .iter()
            .map(|&(s, c)| (index_of[&s], c))
            .collect();
        combined_dense.sort_by_key(|&(i, _)| i);
        // m = combined / g.
        let mut m_coeffs: Vec<(usize, i128)> = Vec::with_capacity(combined_dense.len());
        for &(i, c) in &combined_dense {
            if c % g != 0 {
                return Err(decline("combined coefficient not divisible by gcd"));
            }
            let cq = c / g;
            if cq.unsigned_abs() > DIO_UNIT_MAX as u128 {
                return Err(decline("m coefficient exceeds the unit-expansion bound"));
            }
            m_coeffs.push((i, cq));
        }
        if m_coeffs.is_empty() {
            return Err(decline("m is empty (no variables); not handled"));
        }

        // === 1. Hypotheses h_i : Eq Z L_i (intlit b_i). =======================
        let hyps = self.build_hyps(equalities, &index_of)?;

        // === 2. Combined: h_comb : Eq Z combined_expr (intlit constant). ======
        let h_comb =
            self.combine_equalities(&hyps, &cert.multipliers, &combined_dense, cert.constant)?;
        let combined_kexpr = match lin_to_zexpr(&combined_dense, 0) {
            Some(z) => self.emit_zexpr(&z),
            None => return Err(decline("combined row empty")),
        };
        let const_expr = self.mk_intlit(cert.constant);

        // === 3. gm : Eq Z (mul g_lit m') (intlit r). ==========================
        // 3a. ring_id1 : Eq Z (mul g_lit m') (add combined_expr (neg (intlit gq))).
        let g_zexpr = lin_to_zexpr(&[], g).ok_or_else(|| decline("g zero (unreachable)"))?;
        let m_prime_zexpr =
            lin_to_zexpr(&m_coeffs, -q).ok_or_else(|| decline("m' has no atoms"))?;
        let prod_zexpr = ZExpr::Mul(Box::new(g_zexpr), Box::new(m_prime_zexpr.clone()));
        let (prod_gens, prod_kexpr, prod_norm) = self
            .normalize(&prod_zexpr)
            .ok_or_else(|| decline("mul(g,m') normalizer declined"))?;
        let expected_prod_gens = lin_to_canon_gens(&combined_dense, -gq);
        if prod_gens != expected_prod_gens {
            return Err(decline("g·m' did not canonicalize to combined − g·q"));
        }
        // rhs1 = add combined (neg (intlit gq)) as a ZExpr, normalized.
        let rhs1_zexpr = ZExpr::Add(
            Box::new(lin_to_zexpr(&combined_dense, 0).ok_or_else(|| decline("combined empty"))?),
            Box::new(ZExpr::Neg(Box::new(intlit_zexpr(gq)))),
        );
        let (rhs1_gens, rhs1_kexpr, rhs1_norm) = self
            .normalize(&rhs1_zexpr)
            .ok_or_else(|| decline("combined − g·q normalizer declined"))?;
        if rhs1_gens != expected_prod_gens {
            return Err(decline("combined − g·q did not canonicalize as expected"));
        }
        let canon_prod = self.gens_to_expr(&prod_gens);
        let rhs1_norm_sym = self.eq_symm(rhs1_kexpr, canon_prod, rhs1_norm); // rhs1_kexpr ← canon? no
        // rhs1_norm : Eq Z rhs1_kexpr canon  ⇒ symm : Eq Z canon rhs1_kexpr.
        let ring_id1 = self.eq_trans(prod_kexpr, canon_prod, rhs1_kexpr, prod_norm, rhs1_norm_sym);

        // 3b. rewrite combined → const inside rhs1, then normalize (const − gq) → r.
        // rhs1_kexpr = add combined_kexpr (neg (intlit gq)).
        let neg_gq_kexpr = {
            let gq_k = self.emit_zexpr(&intlit_zexpr(gq));
            self.mk_neg(gq_k)
        };
        let rhs_after = self.mk_add(const_expr, neg_gq_kexpr);
        let cong = self.congr_add_left(combined_kexpr, const_expr, neg_gq_kexpr, h_comb);
        // const − gq normalizer.
        let after_zexpr = ZExpr::Add(
            Box::new(intlit_zexpr(cert.constant)),
            Box::new(ZExpr::Neg(Box::new(intlit_zexpr(gq)))),
        );
        let (after_gens, after_kexpr, after_norm) = self
            .normalize(&after_zexpr)
            .ok_or_else(|| decline("constant − g·q normalizer declined"))?;
        let expected_r_gens = lin_to_canon_gens(&[], r);
        if after_gens != expected_r_gens {
            return Err(decline("constant − g·q did not canonicalize to r"));
        }
        // after_kexpr is `add (intlit const)(neg (intlit gq))` = rhs_after (hash-cons).
        let r_lit = self.mk_intlit(r);
        let canon_r = self.gens_to_expr(&after_gens);
        let r_bridge = self.intlit_eq_canon(r); // Eq Z r_lit canon_r
        let r_bridge_sym = self.eq_symm(r_lit, canon_r, r_bridge); // canon_r = r_lit
        let after_to_r = self.eq_trans(after_kexpr, canon_r, r_lit, after_norm, r_bridge_sym);
        // rhs1_kexpr =[cong] rhs_after(=after_kexpr) =[after_to_r] r_lit.
        let rhs1_to_r = self.eq_trans(rhs1_kexpr, rhs_after, r_lit, cong, after_to_r);

        // 3c. gm : Eq Z (mul g_lit m') r_lit.
        let gm = self.eq_trans(prod_kexpr, rhs1_kexpr, r_lit, ring_id1, rhs1_to_r);

        // === 4. Discreteness close. ===========================================
        let g_lit = self.mk_intlit(g);
        let m_prime_expr = self.emit_zexpr(&m_prime_zexpr);
        debug_assert_eq!(prod_kexpr, self.mk_mul(g_lit, m_prime_expr));
        let zero = self.mk_zero();
        let one = self.mk_one();

        let h_g_pos = self.lt_zero_intlit(g)?; // lt zero g
        let h_r_pos = self.lt_zero_intlit(r)?; // lt zero r
        let h_r_lt_g = self.lt_intlit_intlit(r, g)?; // lt r g

        let lt_mp_one =
            self.prove_m_prime_lt_one(g_lit, m_prime_expr, r_lit, gm, h_g_pos, h_r_lt_g);
        let lt_zero_mp =
            self.prove_zero_lt_m_prime(g_lit, m_prime_expr, r_lit, gm, h_g_pos, h_r_pos);

        let p_prop = self.mk_lt(zero, m_prime_expr);
        let q_prop = self.mk_lt(m_prime_expr, one);
        let and_proof = self.and_intro(p_prop, q_prop, lt_zero_mp, lt_mp_one);
        Ok(self.no_int_between_app(m_prime_expr, and_proof))
    }
}

/// `gcd(a, b)` as a nonnegative `i128`.
fn gcd_i128(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    i128::try_from(a).unwrap_or(i128::MAX)
}
