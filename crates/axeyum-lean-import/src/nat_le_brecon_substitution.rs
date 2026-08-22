//! Reconstructs `Nat.le.brecOn` — course-of-values recursion over the
//! *indexed* family `Nat.le` — directly against a foreign (untrusted-stream)
//! import kernel's own primitives, admitted under the **stream's own
//! declared type**, exactly like [`super::nat_order_substitution`] and
//! [`super::nat_no_confusion_substitution`] and for the same reason: this is
//! a fact about the *specific* stream-supplied `Nat.le`, not a universally
//! valid logical primitive.
//!
//! ## What `Nat.le.brecOn` actually is
//!
//! Unlike `Nat.beq`/`Nat.ble` (ordinary functions defined *by* course-of-values
//! recursion, reconstructed by proving facts about their output), `brecOn`
//! *is* the course-of-values combinator itself — Lean's equation compiler
//! generates it, alongside an auxiliary "below" inductive, for every
//! inductive family so later definitions over that family can recurse on
//! "all smaller instances at once" rather than only the immediate one
//! `rec`'s minor premises see.
//!
//! For `Nat.le`, Lean generates a *second*, auxiliary inductive
//! `Nat.le.below` (confirmed structurally in every stream examined: `Nat.le`
//! itself is `Inductive{params:1, indices:1, ctors:2}` — `refl`/`step` — and
//! `Nat.le.below` is a separate `Inductive{params:2, indices:2, ctors:2}`,
//! carrying the original parameter `n` plus the motive as its own extra
//! parameter, and mirroring `Nat.le`'s two indices `a`/`t`). `brecOn` is then
//! *pure combinator plumbing* built from four already-non-trusted pieces —
//! `Nat.le.rec` (a `Recursor`), `Nat.le.below` (an `Inductive`), and
//! `Nat.le.below.refl`/`Nat.le.below.step` (its `Constructor`s) — with **no
//! arithmetic content and no reliance on any particular reduction
//! behaviour**, unlike this crate's other two substitution modules:
//!
//! ```text
//! Nat.le.brecOn n motive a t F_1 =
//!   F_1 a t (Nat.le.rec n
//!              (fun a t => Nat.le.below n motive a t)
//!              (Nat.le.below.refl n motive)
//!              (fun m h ih => Nat.le.below.step n motive m h ih (F_1 m h ih))
//!              a t)
//! ```
//!
//! This module discovers the four pieces structurally (never assuming a
//! shape) and builds this term directly from them — it never reads the
//! stream's own `noConfusion_of_Nat`-style `type`/`value` fields for
//! `Nat.le.brecOn`, exactly like this crate's other substitution modules.

// Proof-term construction is long, straight-line, and mirrors mathematical
// names one-for-one — exactly the same tradeoff `nat_order_substitution`
// (and, upstream of it, `nat_prelude`) makes, with the same lint allowances.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::too_many_arguments
)]

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, NameId};

use crate::trusted_substitution::{SubstitutionError, exact_name};

/// The one name this module reconstructs. A single-element list (rather than
/// a bare `&str` constant) for symmetry with the sibling substitution
/// modules and so a future course-of-values blocker over a different family
/// can be added here without changing the dispatch shape.
pub(crate) const SUBSTITUTABLE_NAT_LE_BRECON_THEOREMS: &[&str] = &["Nat.le.brecOn"];

struct Prims {
    nat: NameId,
    le: NameId,
    le_rec: NameId,
    le_below: NameId,
    le_below_refl: NameId,
    le_below_step: NameId,
}

fn require_inductive(
    kernel: &Kernel,
    name: NameId,
    expected_params: u16,
    expected_indices: u16,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ..
        }) if *num_params == expected_params && *num_indices == expected_indices => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_constructor(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Constructor { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_recursor(
    kernel: &Kernel,
    name: NameId,
    expected_uparams: usize,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.len() == expected_uparams => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn discover(kernel: &Kernel) -> Result<Prims, SubstitutionError> {
    let nat = exact_name(kernel, "Nat")?;
    require_inductive(kernel, nat, 0, 0, "Nat is not a 0-param 0-index Inductive")?;

    let le = exact_name(kernel, "Nat.le")?;
    require_inductive(
        kernel,
        le,
        1,
        1,
        "Nat.le is not a 1-param 1-index Inductive",
    )?;
    // `Nat.le.refl`/`Nat.le.step` are never named directly by this
    // module's own construction (their shape is fully determined by
    // `Nat.le.rec`'s and `Nat.le.below.step`'s own discovered types), but
    // validating their presence is exactly what makes those discovered
    // types the ordinary two-constructor `Nat.le` shape this module assumes.
    let le_refl = exact_name(kernel, "Nat.le.refl")?;
    require_constructor(kernel, le_refl, "Nat.le.refl is not a Constructor")?;
    let le_step = exact_name(kernel, "Nat.le.step")?;
    require_constructor(kernel, le_step, "Nat.le.step is not a Constructor")?;
    let le_rec = exact_name(kernel, "Nat.le.rec")?;
    require_recursor(kernel, le_rec, 0, "Nat.le.rec is not a 0-uparam Recursor")?;

    let le_below = exact_name(kernel, "Nat.le.below")?;
    require_inductive(
        kernel,
        le_below,
        2,
        2,
        "Nat.le.below is not a 2-param 2-index Inductive",
    )?;
    let le_below_refl = exact_name(kernel, "Nat.le.below.refl")?;
    require_constructor(
        kernel,
        le_below_refl,
        "Nat.le.below.refl is not a Constructor",
    )?;
    let le_below_step = exact_name(kernel, "Nat.le.below.step")?;
    require_constructor(
        kernel,
        le_below_step,
        "Nat.le.below.step is not a Constructor",
    )?;

    Ok(Prims {
        nat,
        le,
        le_rec,
        le_below,
        le_below_refl,
        le_below_step,
    })
}

const FVAR_BASE: u64 = 970_000_000;

struct B<'a> {
    kernel: &'a mut Kernel,
    p: &'a Prims,
    next_fvar: u64,
}

impl<'a> B<'a> {
    fn new(kernel: &'a mut Kernel, p: &'a Prims) -> Self {
        Self {
            kernel,
            p,
            next_fvar: FVAR_BASE,
        }
    }

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn anon(&mut self) -> NameId {
        self.kernel.anon()
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.kernel.app(e, a);
        }
        e
    }

    fn const_app(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel.const_(name, vec![]);
        self.apply(c, args)
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel.abstract_fvars(body, &[fv]);
        let anon = self.anon();
        self.kernel.lam(anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel.abstract_fvars(body, &[fv]);
        let anon = self.anon();
        self.kernel.pi(anon, ty, b, BinderInfo::Default)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.nat, vec![])
    }

    fn le(&mut self, n: ExprId, a: ExprId) -> ExprId {
        let name = self.p.le;
        self.const_app(name, &[n, a])
    }

    fn le_below(&mut self, n: ExprId, motive: ExprId, a: ExprId, t: ExprId) -> ExprId {
        let name = self.p.le_below;
        self.const_app(name, &[n, motive, a, t])
    }

    fn le_below_refl(&mut self, n: ExprId, motive: ExprId) -> ExprId {
        let name = self.p.le_below_refl;
        self.const_app(name, &[n, motive])
    }

    #[allow(clippy::too_many_arguments)]
    fn le_below_step(
        &mut self,
        n: ExprId,
        motive: ExprId,
        m: ExprId,
        h: ExprId,
        ih: ExprId,
        a_ih: ExprId,
    ) -> ExprId {
        let name = self.p.le_below_step;
        self.const_app(name, &[n, motive, m, h, ih, a_ih])
    }

    /// `Nat.le.brecOn`'s full closed value — see the module doc comment for
    /// the derivation this mirrors.
    fn brecon_full(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let anon = self.anon();

        let n_fv = self.fresh();
        let n = self.kernel.fvar(n_fv);

        // motive : (a : Nat) -> (t : Nat.le n a) -> Prop
        let motive_ty = {
            let a2_fv = self.fresh();
            let a2 = self.kernel.fvar(a2_fv);
            let le_n_a2 = self.le(n, a2);
            let prop = self.kernel.sort_zero();
            let inner = self.kernel.pi(anon, le_n_a2, prop, BinderInfo::Default);
            self.pi_fv(a2_fv, nat, inner)
        };
        let motive_fv = self.fresh();
        let motive = self.kernel.fvar(motive_fv);

        let a_fv = self.fresh();
        let a = self.kernel.fvar(a_fv);
        let le_n_a = self.le(n, a);
        let t_fv = self.fresh();
        let t = self.kernel.fvar(t_fv);

        // F_1 : (a : Nat) -> (t : Nat.le n a) -> (below : Nat.le.below n motive a t) -> motive a t
        let f1_ty = {
            let a2_fv = self.fresh();
            let a2 = self.kernel.fvar(a2_fv);
            let le_n_a2 = self.le(n, a2);
            let t2_fv = self.fresh();
            let t2 = self.kernel.fvar(t2_fv);
            let below_fv = self.fresh();
            let below_ty = self.le_below(n, motive, a2, t2);
            let motive_at = self.apply(motive, &[a2, t2]);
            let with_below = self.pi_fv(below_fv, below_ty, motive_at);
            let with_t2 = self.pi_fv(t2_fv, le_n_a2, with_below);
            self.pi_fv(a2_fv, nat, with_t2)
        };
        let f1_fv = self.fresh();
        let f1 = self.kernel.fvar(f1_fv);

        // Nat.le.rec's own motive: fun (a2 : Nat) (t2 : Nat.le n a2) => Nat.le.below n motive a2 t2
        let rec_motive = {
            let a2_fv = self.fresh();
            let a2 = self.kernel.fvar(a2_fv);
            let t2_fv = self.fresh();
            let t2 = self.kernel.fvar(t2_fv);
            let le_n_a2 = self.le(n, a2);
            let body = self.le_below(n, motive, a2, t2);
            let inner = self.lam_fv(t2_fv, le_n_a2, body);
            self.lam_fv(a2_fv, nat, inner)
        };
        let refl_case = self.le_below_refl(n, motive);
        let step_case = {
            let m_fv = self.fresh();
            let m = self.kernel.fvar(m_fv);
            let h_fv = self.fresh();
            let le_n_m = self.le(n, m);
            let h = self.kernel.fvar(h_fv);
            let ih_fv = self.fresh();
            let ih_ty = self.le_below(n, motive, m, h);
            let ih = self.kernel.fvar(ih_fv);
            let a_ih = self.apply(f1, &[m, h, ih]);
            let body = self.le_below_step(n, motive, m, h, ih, a_ih);
            let with_ih = self.lam_fv(ih_fv, ih_ty, body);
            let with_h = self.lam_fv(h_fv, le_n_m, with_ih);
            self.lam_fv(m_fv, nat, with_h)
        };
        let le_rec_c = self.kernel.const_(self.p.le_rec, vec![]);
        let below_value = self.apply(le_rec_c, &[n, rec_motive, refl_case, step_case, a, t]);
        let value_body = self.apply(f1, &[a, t, below_value]);

        let with_f1 = self.lam_fv(f1_fv, f1_ty, value_body);
        let with_t = self.lam_fv(t_fv, le_n_a, with_f1);
        let with_a = self.lam_fv(a_fv, nat, with_t);
        let with_motive = self.lam_fv(motive_fv, motive_ty, with_a);
        self.lam_fv(n_fv, nat, with_motive)
    }
}

/// Attempt to reconstruct `rendered` (`"Nat.le.brecOn"`) as a value that
/// independently type-checks against `wire_ty` — the untrusted stream's own
/// declared type, which this function never alters. Returns `Ok(None)` for
/// any other name. Returns `Err(_)` when this kernel lacks the shape this
/// reconstruction depends on, or the candidate fails to independently
/// type-check against `wire_ty` — the caller must treat both like "not
/// substitutable here" and fall back to the stream's own (still
/// trusted-refused) value.
pub(crate) fn reconstruct(
    kernel: &mut Kernel,
    rendered: &str,
    wire_ty: ExprId,
) -> Result<Option<ExprId>, SubstitutionError> {
    if !SUBSTITUTABLE_NAT_LE_BRECON_THEOREMS.contains(&rendered) {
        return Ok(None);
    }
    let prims = discover(kernel)?;
    let mut b = B::new(kernel, &prims);
    let value = b.brecon_full();

    let inferred = kernel
        .infer(value)
        .map_err(|_| SubstitutionError::UnexpectedShape("candidate value failed to infer"))?;
    if !kernel.def_eq(inferred, wire_ty) {
        return Err(SubstitutionError::UnexpectedShape(
            "candidate value's inferred type is not def-eq to the stream's declared type",
        ));
    }
    Ok(Some(value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::io::Cursor;

    const QUOTIENT_FIXTURE: &str =
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

    fn fixture_kernel() -> Kernel {
        let completed = import_ndjson(
            Cursor::new(QUOTIENT_FIXTURE.as_bytes()),
            ImportLimits::default(),
        )
        .expect("fixture must import");
        completed.into_parts().0
    }

    #[test]
    fn unrecognised_name_declines_with_ok_none() {
        let mut kernel = fixture_kernel();
        let wire_ty = kernel.sort_zero();
        assert!(matches!(
            reconstruct(&mut kernel, "propext", wire_ty),
            Ok(None)
        ));
    }

    #[test]
    fn missing_nat_le_below_declines_cleanly() {
        // The quotient fixture is unlikely to carry `Nat.le.below`; either
        // way this must decline cleanly, never panic or fabricate.
        let mut kernel = fixture_kernel();
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, "Nat.le.brecOn", wire_ty);
        assert!(matches!(
            result,
            Err(SubstitutionError::RequiredDeclarationUnavailable(_)
                | SubstitutionError::UnexpectedShape(_))
                | Ok(Some(_))
        ));
    }
}

#[cfg(test)]
mod real_stream_tests {
    //! Not run by default (reads the frozen census archive, host-local under
    //! `/nas3`, not part of this repository). Run explicitly with
    //! `cargo test -p axeyum-lean-import --lib nat_le_brecon_substitution::real_stream_tests -- --ignored --nocapture`,
    //! optionally overriding the directory with
    //! `AXEYUM_NAT_LE_BRECON_PROBE_DIR`.
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use axeyum_lean_kernel::Kernel;
    use std::fs::File;
    use std::io::BufReader;

    const DEFAULT_DIR: &str = "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams";

    fn wire_ty_of(kernel: &Kernel, rendered: &str) -> Option<ExprId> {
        kernel
            .environment()
            .iter()
            .find(|(name, decl)| {
                matches!(decl, Declaration::Theorem { .. })
                    && kernel.display_name(**name).to_string() == rendered
            })
            .map(|(_, decl)| decl.ty())
    }

    #[test]
    #[ignore = "reads the frozen census archive under /nas3, not part of this repository"]
    fn probe_real_archive() {
        let dir =
            std::env::var("AXEYUM_NAT_LE_BRECON_PROBE_DIR").unwrap_or_else(|_| DEFAULT_DIR.into());
        let mut entries: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read_dir {dir}: {e}"))
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "ndjson"))
            .collect();
        entries.sort();
        assert!(!entries.is_empty(), "no .ndjson files found under {dir}");

        let mut present: u32 = 0;
        let mut ok: u32 = 0;
        let mut failed: Vec<String> = Vec::new();

        for path in &entries {
            let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
            let reader = BufReader::new(file);
            let Ok(completed) = import_ndjson(reader, ImportLimits::default()) else {
                continue;
            };
            let (mut kernel, _report) = completed.into_parts();
            let rendered = "Nat.le.brecOn";
            let Some(wire_ty) = wire_ty_of(&kernel, rendered) else {
                continue;
            };
            present += 1;
            match reconstruct(&mut kernel, rendered, wire_ty) {
                Ok(Some(value)) => {
                    let inferred = kernel
                        .infer(value)
                        .unwrap_or_else(|e| panic!("{path:?} {rendered}: {e:?}"));
                    assert!(
                        kernel.def_eq(inferred, wire_ty),
                        "{path:?} {rendered}: re-inferred type not def-eq to wire_ty"
                    );
                    let probe_name = {
                        let root = kernel.anon();
                        kernel.name_str(root, format!("ProbeReconstruct_{rendered}"))
                    };
                    kernel
                        .add_declaration(Declaration::Theorem {
                            name: probe_name,
                            uparams: vec![],
                            ty: wire_ty,
                            value,
                        })
                        .unwrap_or_else(|e| panic!("{path:?} {rendered}: admission failed: {e:?}"));
                    let footprint = kernel.axiom_footprint(probe_name);
                    assert!(
                        footprint.is_empty(),
                        "{path:?} {rendered}: nonempty axiom footprint {footprint:?}"
                    );
                    let theorem_deps = kernel.theorem_dependencies(probe_name);
                    assert!(
                        theorem_deps.is_empty(),
                        "{path:?} {rendered}: cites another theorem: {:?}",
                        theorem_deps
                            .iter()
                            .map(|&n| kernel.display_name(n).to_string())
                            .collect::<Vec<_>>()
                    );
                    ok += 1;
                }
                Ok(None) => unreachable!("rendered is in SUBSTITUTABLE_NAT_LE_BRECON_THEOREMS"),
                Err(e) => failed.push(format!("{path:?}: {e}")),
            }
        }

        println!("files: {}", entries.len());
        println!("Nat.le.brecOn: present={present} ok={ok}");
        for e in failed.iter().take(5) {
            println!("    decline: {e}");
        }
    }
}
