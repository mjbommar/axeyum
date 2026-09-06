//! Tests for `complex/components.rs`.
//!
//! Each is an ASCRIPTION test: the declared theorem is instantiated and the
//! result ascribed to a claimed type, and the kernel's verdict is the
//! assertion. Every positive is paired with a negative control differing in
//! one subterm, because the three statements here are exactly the shape where
//! a wrong one still type-checks — `le (abs (re z)) (abs z)` and
//! `le (abs (im z)) (abs z)` have identical shapes, and
//! `Equiv (Complex.abs (ofReal t)) t` differs from the true statement by one
//! `CReal.abs`.

use super::{ComplexPrelude, build_complex_prelude};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, Kernel, on_a_deep_stack};

/// A built `Complex` kernel, as a clone of one template.
fn built() -> (Kernel, ComplexPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, ComplexPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// Instantiate `Complex.abs_ofReal` at a bound `t` and ascribe it to
/// `Equiv (Complex.abs (ofReal t)) X`, where `X` is `CReal.abs t` when
/// `with_abs` and the bare `t` otherwise. Returns the kernel's verdict.
fn abs_of_real_ascription_admitted(kernel: &mut Kernel, p: ComplexPrelude, with_abs: bool) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let creal = p.creal;
    let real = d.kernel().const_(creal.creal, vec![]);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let body = d.lemma(p.components.abs_of_real, &[t]);
    let of_real_t = d.const_app(p.of_real, &[t]);
    let lhs = d.const_app(p.abs, &[of_real_t]);
    let rhs = if with_abs {
        d.const_app(creal.abs, &[t])
    } else {
        t
    };
    let claim = d.const_app(creal.equiv, &[lhs, rhs]);

    let value = d.lam_fv(t_fv, real, body);
    let ty = d.pi_fv(t_fv, real, claim);
    let label = if with_abs {
        "Check.abs_ofReal_is_abs"
    } else {
        "Check.abs_ofReal_is_bare"
    };
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// `Complex.abs_ofReal` really says `|ofReal t| ~ |t|`.
#[test]
fn abs_of_real_is_the_real_modulus() {
    let (mut kernel, p) = built();
    assert!(
        abs_of_real_ascription_admitted(&mut kernel, p, true),
        "abs_ofReal must equate the complex modulus with CReal.abs"
    );
}

/// The negative control: `|ofReal t| ~ t` must be REFUSED.
///
/// The `CReal.abs` on the right is not decoration. `CReal.sqrt` is
/// nonnegative unconditionally (`CReal.sqrt_nonneg`), so the bare-`t` form is
/// false for every negative `t` — and it is exactly the form someone writes
/// who reads `sqrt (t·t)` as `t`. That misreading is also why the proof cannot
/// use `CReal.sqrt_sq` at `t`: its hypothesis is `0 ≤ t`.
#[test]
fn abs_of_real_without_the_real_modulus_is_refused() {
    let (mut kernel, p) = built();
    assert!(
        !abs_of_real_ascription_admitted(&mut kernel, p, false),
        "`Equiv (Complex.abs (ofReal t)) t` must be REFUSED -- it is false for \
         negative t"
    );
}

/// Instantiate `Complex.abs_re_le` (`use_re`) or `Complex.abs_im_le` and
/// ascribe it to a bound on the `re` component (`claim_re`) or the `im` one.
/// Returns the kernel's verdict.
fn component_bound_ascription_admitted(
    kernel: &mut Kernel,
    p: ComplexPrelude,
    use_re: bool,
    claim_re: bool,
) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let creal = p.creal;
    let carrier = d.kernel().const_(p.complex, vec![]);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let theorem = if use_re {
        p.components.abs_re_le
    } else {
        p.components.abs_im_le
    };
    let body = d.lemma(theorem, &[z]);

    let projection = if claim_re { p.re } else { p.im };
    let component = d.const_app(projection, &[z]);
    let abs_component = d.const_app(creal.abs, &[component]);
    let abs_z = d.const_app(p.abs, &[z]);
    let claim = d.const_app(creal.le, &[abs_component, abs_z]);

    let value = d.lam_fv(z_fv, carrier, body);
    let ty = d.pi_fv(z_fv, carrier, claim);
    let label = match (use_re, claim_re) {
        (true, true) => "Check.abs_re_le_bounds_re",
        (true, false) => "Check.abs_re_le_bounds_im",
        (false, true) => "Check.abs_im_le_bounds_re",
        (false, false) => "Check.abs_im_le_bounds_im",
    };
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// `Complex.abs_re_le` bounds the REAL part and `Complex.abs_im_le` the
/// IMAGINARY one.
#[test]
fn each_component_bound_names_its_own_projection() {
    let (mut kernel, p) = built();
    assert!(
        component_bound_ascription_admitted(&mut kernel, p, true, true),
        "abs_re_le must bound |re z|"
    );
    assert!(
        component_bound_ascription_admitted(&mut kernel, p, false, false),
        "abs_im_le must bound |im z|"
    );
}

/// The negative control, and the reason `declare_abs_component_le` is ONE
/// function taking a flag rather than two copies: the two statements have the
/// same shape, so a copy that bounds the wrong projection type-checks against
/// nothing. Each theorem must be REFUSED against the other's claim.
#[test]
fn the_component_bounds_are_not_interchangeable() {
    let (mut kernel, p) = built();
    assert!(
        !component_bound_ascription_admitted(&mut kernel, p, true, false),
        "abs_re_le must NOT prove a bound on |im z|"
    );
    assert!(
        !component_bound_ascription_admitted(&mut kernel, p, false, true),
        "abs_im_le must NOT prove a bound on |re z|"
    );
}
