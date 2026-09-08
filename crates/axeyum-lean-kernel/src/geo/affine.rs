//! `Geo.Affine` — **Playfair's parallel axiom over [`Geo.Incidence`](super)**,
//! with parallelism stated POSITIVELY.
//!
//! Roadmap W3-8, third slice; ADR-1659. ADR-1652 § 5 sized this and found the
//! obstruction was not a missing principle but the SHAPE of the parallel
//! predicate, and this file is that finding acted on.
//!
//! # Why a second record rather than seven more fields on the first
//!
//! [`Geo.Incidence`](super) is Hilbert's incidence group and nothing else: its
//! two models, [`qplane`](super::qplane) and [`rplane`](super::rplane), are
//! models of *that*, and an affine plane is a strictly stronger structure. So
//! `Geo.Affine` **carries a `Geo.Incidence` as its zeroth field** rather than
//! restating twenty-one of them, which also means every theorem already proved
//! over an arbitrary `I : Geo.Incidence` instantiates at `Geo.Affine.inc A`
//! for free — `parallel_trans` below concludes in `Geo.Incidence.Parallel` and
//! `parallelPos_irrefl` consumes `Geo.Incidence.parallel_irrefl`, neither
//! restating anything.
//!
//! Field 0 has type `Geo.Incidence : Sort 2`, which is the same universe
//! situation a carrier field is in (`Sort 1 : Sort 2`), so it is declared with
//! that `FieldKind` and the record lands at `Sort 2` through the same
//! `declare_record` spine — including the ADR-1578 universe control that
//! requires the SAME field list to be REFUSED at `Sort 1`.
//!
//! # The one design decision: `parPos`, not `Geo.Incidence.Parallel`
//!
//! `Geo.Incidence.Parallel l m := ∀ P, on P l → on P m → False` is the
//! classical definition and it is the WRONG primitive for Playfair, for the
//! reason ADR-1652 § 5 measured: it is negative, so Playfair's uniqueness half
//! has to be proved by contradiction, and over `CReal` that route ends at
//! `Not (Apart (a*B − b*A) 0)`, which is tightness — a principle `creal.rs`
//! documents as neither proved nor assumed. This is the same trap `apart`
//! already avoids for points, one dimension up.
//!
//! So `Geo.Affine` carries **`parPos`** as a field of its own, with the models
//! supplying the positive content:
//!
//! | model | `parPos l m` |
//! | --- | --- |
//! | `Geo.qaffine` (ℚ²) | `a l * b m = b l * a m`, and the other two proportionalities NOT both holding |
//! | `Geo.raffine` (ℝ²) | `Equiv (a*B − b*A) 0`, and `∃ k, PosBound ((a*C − c*A)² + (b*C − c*B)²) k` |
//!
//! Read either row as *same direction, and distinct* — and note the ℝ row's
//! second conjunct is a WITNESS, exactly as `apart` and `Nondeg` are.
//! `parPosDisjoint` is what ties the positive notion back to the classical
//! one, and `parallelPos_parallel` is that field's derived form.
//!
//! `off` is the second witnessed primitive, and it is needed for the same
//! reason: Playfair's EXISTENCE half is "through a point **not on** `l`", and
//! over ℝ the negation `on P l → False` constructs no modulus, so the
//! existence proof could not show its parallel is distinct from `l`. The ℝ
//! model reads `off P l` as `∃ k, PosBound (e_P * e_P) k` with `e_P` the
//! incidence expression; the ℚ model reads it as the plain negation, which
//! over ℚ *is* usable because `Rat.mul_eq_zero` decides it.
//!
//! # Field layout
//!
//! | # | field | type |
//! |---|---|---|
//! | 0 | `inc` | `Geo.Incidence` |
//! | 1 | `parPos` | `line inc → line inc → Prop` |
//! | 2 | `off` | `point inc → line inc → Prop` |
//! | 3 | `offNotOn` | `∀ P l, off P l → on inc P l → False` |
//! | 4 | `parPosDisjoint` | `∀ l m P, parPos l m → on inc P l → on inc P m → False` |
//! | 5 | `playfairExists` | `∀ P l, off P l → ∃ m, on inc P m ∧ parPos l m` |
//! | 6 | `playfairUnique` | `∀ P l m n, parPos l m → parPos l n → on inc P m → on inc P n → lEq inc m n` |
//!
//! Fields 5 and 6 are Playfair's axiom split into its existence and uniqueness
//! halves, exactly as `joinExists`/`joinUnique` split Hilbert I.1 — this kernel
//! has no `ExistsUnique`.
//!
//! # Derived theorems
//!
//! ```text
//! Geo.Affine.parallelPos_parallel : ∀ A l m,
//!     Geo.Affine.parPos A l m → Geo.Incidence.Parallel (Geo.Affine.inc A) l m
//! Geo.Affine.parallelPos_irrefl : ∀ A l, Geo.Affine.parPos A l l → False
//! Geo.Affine.parallel_trans : ∀ A l m n,
//!     Geo.Affine.parPos A m l → Geo.Affine.parPos A m n →
//!     (Geo.Incidence.lEq (Geo.Affine.inc A) l n → False) →
//!     Geo.Incidence.Parallel (Geo.Affine.inc A) l n
//! ```
//!
//! `parallel_trans` **is** Playfair's classical corollary "parallelism is
//! transitive", in the only form this kernel can state it: two lines that are
//! each positively parallel to a common line and are DISTINCT share no point.
//! The distinctness hypothesis is not a weakness of the proof, it is the
//! theorem — `l` and `n` may perfectly well be the same line, and deciding
//! which needs `lEq` to be decidable, which it is not over ℝ. Proof: a shared
//! point would put `l` and `n` both through it, both parallel to `m`, so
//! `playfairUnique` makes them `lEq`.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::structures::{
    FieldKind, FieldSpec, MAX_FIELDS, RecordNames, arrow, declare_record, pi_over,
};
use crate::prelude::LogicPrelude;

use super::{
    GeoPrelude, L_EQ, LINE, POINT, and_of, app_all, capp, exists_over, false_of, field, lam_over,
    on_of, rel_ty,
};

// ---------------------------------------------------------------------------
// Field indices. Index a field through these, never with a bare integer.
// ---------------------------------------------------------------------------

/// `Geo.Affine.inc`.
pub const INC: usize = 0;
/// `Geo.Affine.parPos`.
pub const PAR_POS: usize = 1;
/// `Geo.Affine.off`.
pub const OFF: usize = 2;
/// `Geo.Affine.offNotOn`.
pub const OFF_NOT_ON: usize = 3;
/// `Geo.Affine.parPosDisjoint`.
pub const PAR_POS_DISJOINT: usize = 4;
/// `Geo.Affine.playfairExists`.
pub const PLAYFAIR_EXISTS: usize = 5;
/// `Geo.Affine.playfairUnique`.
pub const PLAYFAIR_UNIQUE: usize = 6;

/// The number of fields `Geo.Affine` carries.
pub const AFFINE_FIELD_COUNT: usize = 7;

/// The selector suffixes, in field order. Paired against `declare_record`'s
/// own output in [`declare_affine_record`] so this file's two descriptions of
/// one record cannot drift apart.
pub(crate) const AFFINE_FIELD_SUFFIXES: [&str; AFFINE_FIELD_COUNT] = [
    "inc",
    "parPos",
    "off",
    "offNotOn",
    "parPosDisjoint",
    "playfairExists",
    "playfairUnique",
];

// Free-variable ids. Disjoint from `structures::CTOR_FVAR_BASE` (10_000),
// `SELECTOR_S_FV` (10_900) and `geo.rs`'s own 82_000 band.
const A_P: u64 = 83_000;
const A_L: u64 = 83_001;
const A_M: u64 = 83_002;
const A_N: u64 = 83_003;
/// The bound `A : Geo.Affine` of every derived declaration.
const A_S: u64 = 83_100;
const A_H1: u64 = 83_110;
const A_H2: u64 = 83_111;
const A_H3: u64 = 83_112;
const A_H4: u64 = 83_113;
const A_H5: u64 = 83_114;

// ---------------------------------------------------------------------------
// Field shapes.
// ---------------------------------------------------------------------------

/// `Geo.Incidence` itself — a `Sort 2` inhabitant, so the same `FieldKind`
/// a carrier gets, which is what puts the selector's motive at `Sort 2`.
fn inc_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "inc",
        kind: FieldKind::CarrierSort,
        build: Box::new(move |k, _lg, _l1, _vals| k.const_(p.record.ind, vec![])),
    }
}

/// `line inc → line inc → Prop`.
fn par_pos_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "parPos",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let i = vals[INC];
            let ln = field(k, p, LINE, i);
            rel_ty(k, ln, ln)
        }),
    }
}

/// `point inc → line inc → Prop`.
fn off_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "off",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let i = vals[INC];
            let pt = field(k, p, POINT, i);
            let ln = field(k, p, LINE, i);
            rel_ty(k, pt, ln)
        }),
    }
}

/// `∀ P l, off P l → on P l → False`.
fn off_not_on_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "offNotOn",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, _l1, vals| {
            let i = vals[INC];
            let off = vals[OFF];
            let pt = field(k, p, POINT, i);
            let ln = field(k, p, LINE, i);
            let pp = k.fvar(A_P);
            let l = k.fvar(A_L);
            let hoff = app_all(k, off, &[pp, l]);
            let hon = on_of(k, p, i, pp, l);
            let f = false_of(k, lg);
            let t = arrow(k, hon, f);
            let t = arrow(k, hoff, t);
            let t = pi_over(k, A_L, ln, t);
            pi_over(k, A_P, pt, t)
        }),
    }
}

/// `∀ l m P, parPos l m → on P l → on P m → False`.
fn par_pos_disjoint_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "parPosDisjoint",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, _l1, vals| {
            let i = vals[INC];
            let par = vals[PAR_POS];
            let pt = field(k, p, POINT, i);
            let ln = field(k, p, LINE, i);
            let l = k.fvar(A_L);
            let m = k.fvar(A_M);
            let pp = k.fvar(A_P);
            let hpar = app_all(k, par, &[l, m]);
            let opl = on_of(k, p, i, pp, l);
            let opm = on_of(k, p, i, pp, m);
            let f = false_of(k, lg);
            let t = arrow(k, opm, f);
            let t = arrow(k, opl, t);
            let t = arrow(k, hpar, t);
            let t = pi_over(k, A_P, pt, t);
            let t = pi_over(k, A_M, ln, t);
            pi_over(k, A_L, ln, t)
        }),
    }
}

/// `∀ P l, off P l → ∃ m, on P m ∧ parPos l m`.
fn playfair_exists_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "playfairExists",
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let i = vals[INC];
            let par = vals[PAR_POS];
            let off = vals[OFF];
            let pt = field(k, p, POINT, i);
            let ln = field(k, p, LINE, i);
            let pp = k.fvar(A_P);
            let l = k.fvar(A_L);
            let m = k.fvar(A_M);
            let opm = on_of(k, p, i, pp, m);
            let hpar = app_all(k, par, &[l, m]);
            let body = and_of(k, lg, opm, hpar);
            let ex = exists_over(k, lg, l1, A_M, ln, body);
            let hoff = app_all(k, off, &[pp, l]);
            let t = arrow(k, hoff, ex);
            let t = pi_over(k, A_L, ln, t);
            pi_over(k, A_P, pt, t)
        }),
    }
}

/// `∀ P l m n, parPos l m → parPos l n → on P m → on P n → lEq m n`.
fn playfair_unique_field(p: GeoPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "playfairUnique",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let i = vals[INC];
            let par = vals[PAR_POS];
            let pt = field(k, p, POINT, i);
            let ln = field(k, p, LINE, i);
            let leq = field(k, p, L_EQ, i);
            let pp = k.fvar(A_P);
            let l = k.fvar(A_L);
            let m = k.fvar(A_M);
            let n = k.fvar(A_N);
            let h1 = app_all(k, par, &[l, m]);
            let h2 = app_all(k, par, &[l, n]);
            let opm = on_of(k, p, i, pp, m);
            let opn = on_of(k, p, i, pp, n);
            let concl = app_all(k, leq, &[m, n]);
            let t = arrow(k, opn, concl);
            let t = arrow(k, opm, t);
            let t = arrow(k, h2, t);
            let t = arrow(k, h1, t);
            let t = pi_over(k, A_N, ln, t);
            let t = pi_over(k, A_M, ln, t);
            let t = pi_over(k, A_L, ln, t);
            pi_over(k, A_P, pt, t)
        }),
    }
}

/// The seven field shapes, in declaration order.
pub(crate) fn affine_fields(p: GeoPrelude) -> Vec<FieldSpec> {
    vec![
        inc_field(p),
        par_pos_field(p),
        off_field(p),
        off_not_on_field(p),
        par_pos_disjoint_field(p),
        playfair_exists_field(p),
        playfair_unique_field(p),
    ]
}

// ---------------------------------------------------------------------------
// The handle.
// ---------------------------------------------------------------------------

/// The interned names this module declares.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AffineNames {
    /// The `Geo.Affine` record: its inductive, `mk`, `rec` and 7 selectors.
    pub record: RecordNames,
    /// `Geo.Affine.parallelPos_parallel : ∀ A l m, parPos A l m →
    /// Geo.Incidence.Parallel (inc A) l m` — **the positive notion implies the
    /// classical one**, which is what makes `parPos` a parallelism rather than
    /// an arbitrary relation.
    pub parallel_pos_parallel: NameId,
    /// `Geo.Affine.parallelPos_irrefl : ∀ A l, parPos A l l → False` — a line
    /// is never positively parallel to itself. Derived from
    /// [`Self::parallel_pos_parallel`] and `Geo.Incidence.parallel_irrefl`,
    /// which is where Hilbert I.2 (every line carries a point) enters.
    pub parallel_pos_irrefl: NameId,
    /// `Geo.Affine.parallel_trans : ∀ A l m n, parPos A m l → parPos A m n →
    /// (lEq (inc A) l n → False) → Geo.Incidence.Parallel (inc A) l n` —
    /// **Playfair's classical corollary**; see the module docs for why the
    /// distinctness hypothesis is the theorem rather than a weakness.
    pub parallel_trans: NameId,
}

/// Pre-compute every name this module declares. `geo` is the `Geo` namespace
/// root interned by [`super::intern`].
pub(crate) fn intern(kernel: &mut Kernel, geo: NameId) -> AffineNames {
    let aff = kernel.name_str(geo, "Affine");
    let mk = kernel.name_str(aff, "mk");
    let rec = kernel.name_str(aff, "rec");
    let mut selectors = [mk; MAX_FIELDS];
    for (i, suffix) in AFFINE_FIELD_SUFFIXES.iter().enumerate() {
        selectors[i] = kernel.name_str(aff, *suffix);
    }
    AffineNames {
        record: RecordNames {
            ind: aff,
            mk,
            rec,
            selectors,
            len: AFFINE_FIELD_COUNT,
        },
        parallel_pos_parallel: kernel.name_str(aff, "parallelPos_parallel"),
        parallel_pos_irrefl: kernel.name_str(aff, "parallelPos_irrefl"),
        parallel_trans: kernel.name_str(aff, "parallel_trans"),
    }
}

/// Declare the `Geo.Affine` record and its three derived theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics if the field list has drifted from [`AFFINE_FIELD_COUNT`] or if
/// `declare_record` returns selectors under names other than the ones
/// [`intern`] pre-computed.
pub(crate) fn declare_affine_record(
    kernel: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let a = p.affine;
    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);
    let specs = affine_fields(p);
    assert_eq!(
        specs.len(),
        AFFINE_FIELD_COUNT,
        "field list out of step with AFFINE_FIELD_COUNT"
    );
    let record = declare_record(kernel, lg, l0, l1, l2, a.record.ind, &specs)?;
    assert_eq!(
        record.field_count(),
        AFFINE_FIELD_COUNT,
        "declare_record produced the wrong field count"
    );
    for (i, suffix) in AFFINE_FIELD_SUFFIXES.iter().enumerate() {
        assert_eq!(
            record.sel(i),
            a.record.sel(i),
            "selector {i} ({suffix}) was interned under a different name"
        );
    }

    declare_parallel_pos_parallel(kernel, p)?;
    declare_parallel_pos_irrefl(kernel, p)?;
    declare_parallel_trans(kernel, lg, p)
}

// ---------------------------------------------------------------------------
// Shorthands over a bound `A : Geo.Affine`.
// ---------------------------------------------------------------------------

/// `Geo.Affine` (the record's own type).
fn aff_ty(k: &mut Kernel, p: GeoPrelude) -> ExprId {
    k.const_(p.affine.record.ind, vec![])
}

/// Selector `i` of `Geo.Affine`, applied to `s`.
fn afield(k: &mut Kernel, p: GeoPrelude, i: usize, s: ExprId) -> ExprId {
    capp(k, p.affine.record.sel(i), &[s])
}

// ---------------------------------------------------------------------------
// The derived declarations.
// ---------------------------------------------------------------------------

/// `Geo.Affine.parallelPos_parallel : ∀ A l m, parPos A l m →
/// Geo.Incidence.Parallel (inc A) l m`.
///
/// The conclusion is a `Definition` that unfolds to
/// `∀ P, on P l → on P m → False`, so the whole proof is the `parPosDisjoint`
/// field with its arguments reordered.
fn declare_parallel_pos_parallel(k: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let aff = aff_ty(k, p);
    let s = k.fvar(A_S);
    let i = afield(k, p, INC, s);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);

    let l = k.fvar(A_L);
    let m = k.fvar(A_M);
    let par = afield(k, p, PAR_POS, s);
    let source = app_all(k, par, &[l, m]);
    let target = capp(k, p.parallel, &[i, l, m]);

    let body = {
        let pp = k.fvar(A_P);
        let opl = on_of(k, p, i, pp, l);
        let opm = on_of(k, p, i, pp, m);
        let h = k.fvar(A_H1);
        let h1 = k.fvar(A_H2);
        let h2 = k.fvar(A_H3);
        let disjoint = afield(k, p, PAR_POS_DISJOINT, s);
        let applied = app_all(k, disjoint, &[l, m, pp, h, h1, h2]);
        let t = lam_over(k, A_H3, opm, applied);
        let t = lam_over(k, A_H2, opl, t);
        lam_over(k, A_P, pt, t)
    };

    let ty = {
        let t = arrow(k, source, target);
        let t = pi_over(k, A_M, ln, t);
        let t = pi_over(k, A_L, ln, t);
        pi_over(k, A_S, aff, t)
    };
    let value = {
        let t = lam_over(k, A_H1, source, body);
        let t = lam_over(k, A_M, ln, t);
        let t = lam_over(k, A_L, ln, t);
        lam_over(k, A_S, aff, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.affine.parallel_pos_parallel,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.Affine.parallelPos_irrefl : ∀ A l, parPos A l l → False`.
fn declare_parallel_pos_irrefl(k: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let aff = aff_ty(k, p);
    let s = k.fvar(A_S);
    let i = afield(k, p, INC, s);
    let ln = field(k, p, LINE, i);

    let l = k.fvar(A_L);
    let par = afield(k, p, PAR_POS, s);
    let source = app_all(k, par, &[l, l]);
    let h = k.fvar(A_H1);
    let lifted = capp(k, p.affine.parallel_pos_parallel, &[s, l, l, h]);
    let proof = capp(k, p.parallel_irrefl, &[i, l, lifted]);

    let logic_false = p.cpoint.creal.rat.int.logic.false_;
    let f = k.const_(logic_false, vec![]);
    let ty = {
        let t = arrow(k, source, f);
        let t = pi_over(k, A_L, ln, t);
        pi_over(k, A_S, aff, t)
    };
    let value = {
        let t = lam_over(k, A_H1, source, proof);
        let t = lam_over(k, A_L, ln, t);
        lam_over(k, A_S, aff, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.affine.parallel_pos_irrefl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.Affine.parallel_trans : ∀ A l m n, parPos A m l → parPos A m n →
/// (lEq (inc A) l n → False) → Geo.Incidence.Parallel (inc A) l n`.
fn declare_parallel_trans(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: GeoPrelude,
) -> Result<(), KernelError> {
    let aff = aff_ty(k, p);
    let s = k.fvar(A_S);
    let i = afield(k, p, INC, s);
    let pt = field(k, p, POINT, i);
    let ln = field(k, p, LINE, i);

    let l = k.fvar(A_L);
    let m = k.fvar(A_M);
    let n = k.fvar(A_N);
    let par = afield(k, p, PAR_POS, s);
    let h1_ty = app_all(k, par, &[m, l]);
    let h2_ty = app_all(k, par, &[m, n]);
    let leq = field(k, p, L_EQ, i);
    let same = app_all(k, leq, &[l, n]);
    let f = false_of(k, lg);
    let hne_ty = arrow(k, same, f);
    let target = capp(k, p.parallel, &[i, l, n]);

    let h1 = k.fvar(A_H1);
    let h2 = k.fvar(A_H2);
    let hne = k.fvar(A_H3);

    let body = {
        let pp = k.fvar(A_P);
        let opl = on_of(k, p, i, pp, l);
        let opn = on_of(k, p, i, pp, n);
        let hl = k.fvar(A_H4);
        let hn = k.fvar(A_H5);
        let unique = afield(k, p, PLAYFAIR_UNIQUE, s);
        let derived = app_all(k, unique, &[pp, m, l, n, h1, h2, hl, hn]);
        let clash = k.app(hne, derived);
        let t = lam_over(k, A_H5, opn, clash);
        let t = lam_over(k, A_H4, opl, t);
        lam_over(k, A_P, pt, t)
    };

    let ty = {
        let t = arrow(k, hne_ty, target);
        let t = arrow(k, h2_ty, t);
        let t = arrow(k, h1_ty, t);
        let t = pi_over(k, A_N, ln, t);
        let t = pi_over(k, A_M, ln, t);
        let t = pi_over(k, A_L, ln, t);
        pi_over(k, A_S, aff, t)
    };
    let value = {
        let t = lam_over(k, A_H3, hne_ty, body);
        let t = lam_over(k, A_H2, h2_ty, t);
        let t = lam_over(k, A_H1, h1_ty, t);
        let t = lam_over(k, A_N, ln, t);
        let t = lam_over(k, A_M, ln, t);
        let t = lam_over(k, A_L, ln, t);
        lam_over(k, A_S, aff, t)
    };
    k.add_declaration(Declaration::Theorem {
        name: p.affine.parallel_trans,
        uparams: vec![],
        ty,
        value,
    })
}
