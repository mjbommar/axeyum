//! **Slice 6 of the first-order model theory group** (`fo_*.rs`, ADR-1640):
//! the **arithmetization** of the syntax `fo_syntax.rs` builds — a Gödel
//! numbering `FO.Term.code : Term -> Nat` and `FO.Formula.code : Formula ->
//! Nat`, and the injectivity of both.
//!
//! ```text
//! FO.Code.tri     : Nat -> Nat                     -- 0, 1, 3, 6, 10, ...
//! FO.Code.pair    : Nat -> Nat -> Nat  := fun a b => tri (a + b) + a
//! FO.Code.step    : Nat.Pair -> Nat.Pair           -- one step of the diagonal walk
//! FO.Code.unpair  : Nat -> Nat.Pair    := Nat.rec (mk 0 0) (fun _ ih => step ih)
//! FO.Code.fst     : Nat -> Nat         := fun n => Nat.Pair.fst (unpair n)
//! FO.Code.snd     : Nat -> Nat         := fun n => Nat.Pair.snd (unpair n)
//!
//! FO.Code.unpair_pair    : Π a b, Eq Nat.Pair (unpair (pair a b)) (Nat.Pair.mk a b)
//! FO.Code.fst_pair       : Π a b, Eq Nat (fst (pair a b)) a
//! FO.Code.snd_pair       : Π a b, Eq Nat (snd (pair a b)) b
//! FO.Code.pair_inj_left  : Π a b c d, Eq Nat (pair a b) (pair c d) -> Eq Nat a c
//! FO.Code.pair_inj_right : Π a b c d, Eq Nat (pair a b) (pair c d) -> Eq Nat b d
//! ```
//!
//! ## Why a *new* pairing rather than `Nat.pair`
//!
//! `nat_prelude/avg_pair.rs` already declares `Nat.pair` (Mathlib's/Lean
//! core's `if a < b then b*b + a else a*a + a + b`) and
//! `nat_prelude/unpair.rs` its two `sqrt`-based projections. Neither has a
//! round-trip theorem, and this slice must not supply one: `Nat.pair`,
//! `Nat.avg`, `Nat.unpaired` and `Nat.Primrec` are the constants of the
//! **held-out** families `natural-avg-pair` (10 rows) and
//! `natural-primitive-recursion` in
//! `artifacts/autogenesis/nursery-v2-extension.json`, and a blind evaluation
//! population is a shared resource with no owner — proving
//! `unpairLeft (Nat.pair a b) = a` here would spend a family this lane was
//! not given.
//!
//! So `FO.Code.pair` is a *separate* construction in its own namespace, and
//! it is deliberately the pairing whose inverse is **structurally recursive
//! on the code itself**:
//!
//! - `Nat.pair`'s inverse needs `Nat.sqrt`, whose own recursion is a fuel
//!   loop; inverting it means a theorem about `sqrt (b*b + a)`, i.e. real
//!   arithmetic on top of a fuel-recursive definition.
//! - `FO.Code.pair a b := tri (a + b) + a` enumerates ℕ×ℕ along the
//!   anti-diagonals, and the enumeration's **successor step is a function of
//!   the previous pair alone**: `(a, 0) ↦ (0, a+1)` and `(a, b+1) ↦ (a+1, b)`.
//!   `FO.Code.unpair` is therefore a plain `Nat.rec` iterating that step —
//!   no fuel, no division, no `sqrt`, and every reduction below is
//!   definitional.
//!
//! The whole round trip then costs **one** structural induction (on the code
//! `n`), with case splits on the two components, and the only imported Nat
//! facts are `Nat.zero_add`, `Nat.succ_add`, `Nat.succ_injective` and
//! `Nat.succ_ne_zero`.
//!
//! ## The two enumeration equations
//!
//! ```text
//! FO.Code.pair_zero_succ : Π k,   Eq Nat (pair 0 (succ k)) (succ (pair k 0))
//! FO.Code.pair_succ      : Π a b, Eq Nat (pair (succ a) b) (succ (pair a (succ b)))
//! ```
//!
//! Between them they say that `pair` inverts `step`: they are the two cases
//! the induction below splits on, and `Nat.zero_add` / `Nat.succ_add` are
//! exactly what each needs (`Nat.add` recurses on its RIGHT argument here, so
//! `x + 0 = x` and `x + succ y = succ (x + y)` are `refl` and the other two
//! orientations are theorems).
//!
//! ## These are `Definition`s, so admission proves nothing
//!
//! `FO.Code.pair` with the `tri` dropped, or `step` with its two branches
//! swapped, type-checks exactly as readily. `fo_code/tests.rs` pins every
//! definition by `def_eq` at concrete small arguments — including the whole
//! enumeration `pair a b` for `a + b <= 3`, which a swapped `step` or a
//! transposed `pair` gets wrong at the first off-diagonal entry.

// The mathematical variables in this group are the ones the literature uses --
// `t` for a term, `p`/`q` for formulas, `a`/`b`/`k`/`m`/`n` for naturals.
// Renaming them to satisfy `many_single_char_names` / `similar_names` would
// make every proof term harder to check against the arithmetic it encodes.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_syntax::{apply_all, arrow, gcongr, geq, gsymm, gtrans, lam_fv, lams, pi_fv, pis};
use crate::{
    BinderInfo, Declaration, ExprId, FoSyntaxPrelude, KernelError, LogicPrelude, NameId,
    NatPrelude, ReducibilityHint, build_fo_syntax_prelude,
};

/// Names produced by [`build_fo_code_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoCodePrelude {
    /// The first-order syntax this numbering is of.
    pub syntax: FoSyntaxPrelude,

    // --- the pairing ---------------------------------------------------------
    /// `FO.Code.tri : Nat -> Nat` — the triangular numbers.
    pub tri: NameId,
    /// `FO.Code.pair : Nat -> Nat -> Nat := fun a b => tri (a + b) + a`.
    pub pair: NameId,
    /// `FO.Code.step : Nat.Pair -> Nat.Pair` — one anti-diagonal step.
    pub step: NameId,
    /// `FO.Code.unpair : Nat -> Nat.Pair` — `step` iterated `n` times.
    pub unpair: NameId,
    /// `FO.Code.fst : Nat -> Nat`.
    pub fst: NameId,
    /// `FO.Code.snd : Nat -> Nat`.
    pub snd: NameId,
    /// `FO.Code.pair_zero_succ : Π k, Eq Nat (pair 0 (succ k)) (succ (pair k 0))`.
    pub pair_zero_succ: NameId,
    /// `FO.Code.pair_succ : Π a b, Eq Nat (pair (succ a) b) (succ (pair a (succ b)))`.
    pub pair_succ: NameId,
    /// `FO.Code.unpair_pair : Π a b, Eq Nat.Pair (unpair (pair a b)) (Nat.Pair.mk a b)`.
    pub unpair_pair: NameId,
    /// `FO.Code.fst_pair : Π a b, Eq Nat (fst (pair a b)) a`.
    pub fst_pair: NameId,
    /// `FO.Code.snd_pair : Π a b, Eq Nat (snd (pair a b)) b`.
    pub snd_pair: NameId,
    /// `FO.Code.pair_inj_left : Π a b c d, Eq Nat (pair a b) (pair c d) -> Eq Nat a c`.
    pub pair_inj_left: NameId,
    /// `FO.Code.pair_inj_right : Π a b c d, Eq Nat (pair a b) (pair c d) -> Eq Nat b d`.
    pub pair_inj_right: NameId,
}

/// The handful of names every builder below shares.
pub(crate) struct CodeNames {
    pub(crate) nat: NatPrelude,
    pub(crate) logic: LogicPrelude,
    pub(crate) code_ns: NameId,
    pub(crate) nat_ty: ExprId,
    pub(crate) pair_ty: ExprId,
    pub(crate) tri: NameId,
    pub(crate) pair: NameId,
    pub(crate) pair_inj_left: NameId,
    pub(crate) pair_inj_right: NameId,
}

impl CodeNames {
    /// Re-intern the names this slice's builders share. Interning a name does
    /// not declare it, so this is also what the builders below call BEFORE the
    /// declarations exist.
    pub(crate) fn rebuild(kernel: &mut crate::Kernel, nat: NatPrelude) -> Self {
        let anon = kernel.anon();
        let fo = kernel.name_str(anon, "FO");
        let code_ns = kernel.name_str(fo, "Code");
        let nat_ty = kernel.const_(nat.nat, vec![]);
        let pair_ty = kernel.const_(nat.pair, vec![]);
        let tri = kernel.name_str(code_ns, "tri");
        let pair = kernel.name_str(code_ns, "pair");
        let pair_inj_left = kernel.name_str(code_ns, "pair_inj_left");
        let pair_inj_right = kernel.name_str(code_ns, "pair_inj_right");
        Self {
            nat,
            logic: nat.logic,
            code_ns,
            nat_ty,
            pair_ty,
            tri,
            pair,
            pair_inj_left,
            pair_inj_right,
        }
    }
}

// ============================================================================
// Small Nat/Nat.Pair combinators.
// ============================================================================

/// `Nat.zero`.
pub(crate) fn nzero(kernel: &mut crate::Kernel, c: &CodeNames) -> ExprId {
    kernel.const_(c.nat.zero, vec![])
}

/// `Nat.succ n`.
pub(crate) fn nsucc(kernel: &mut crate::Kernel, c: &CodeNames, n: ExprId) -> ExprId {
    let s = kernel.const_(c.nat.succ, vec![]);
    kernel.app(s, n)
}

/// The unary numeral `Nat.succ^n Nat.zero`. Only ever called at single digits
/// (the largest constructor tag in this group is `8`).
pub(crate) fn numeral(kernel: &mut crate::Kernel, c: &CodeNames, n: u32) -> ExprId {
    let mut e = nzero(kernel, c);
    for _ in 0..n {
        e = nsucc(kernel, c, e);
    }
    e
}

/// `Nat.add a b`.
pub(crate) fn nadd(kernel: &mut crate::Kernel, c: &CodeNames, a: ExprId, b: ExprId) -> ExprId {
    let f = kernel.const_(c.nat.add, vec![]);
    apply_all(kernel, f, &[a, b])
}

/// `Nat.Pair.mk a b`.
pub(crate) fn pmk(kernel: &mut crate::Kernel, c: &CodeNames, a: ExprId, b: ExprId) -> ExprId {
    let f = kernel.const_(c.nat.pair_mk, vec![]);
    apply_all(kernel, f, &[a, b])
}

/// `Nat.Pair.fst p`.
pub(crate) fn pfst(kernel: &mut crate::Kernel, c: &CodeNames, p: ExprId) -> ExprId {
    let f = kernel.const_(c.nat.pair_fst, vec![]);
    kernel.app(f, p)
}

/// `Nat.Pair.snd p`.
pub(crate) fn psnd(kernel: &mut crate::Kernel, c: &CodeNames, p: ExprId) -> ExprId {
    let f = kernel.const_(c.nat.pair_snd, vec![]);
    kernel.app(f, p)
}

/// `Eq Nat a b`.
pub(crate) fn neq(kernel: &mut crate::Kernel, c: &CodeNames, a: ExprId, b: ExprId) -> ExprId {
    let logic = c.logic;
    let ty = c.nat_ty;
    geq(kernel, logic, ty, a, b)
}

/// `Eq Nat.Pair a b`.
pub(crate) fn peq(kernel: &mut crate::Kernel, c: &CodeNames, a: ExprId, b: ExprId) -> ExprId {
    let logic = c.logic;
    let ty = c.pair_ty;
    geq(kernel, logic, ty, a, b)
}

/// `FO.Code.tri n`.
pub(crate) fn tri_app(kernel: &mut crate::Kernel, c: &CodeNames, n: ExprId) -> ExprId {
    let f = kernel.const_(c.tri, vec![]);
    kernel.app(f, n)
}

/// `FO.Code.pair a b`.
pub(crate) fn pair_app(kernel: &mut crate::Kernel, c: &CodeNames, a: ExprId, b: ExprId) -> ExprId {
    let f = kernel.const_(c.pair, vec![]);
    apply_all(kernel, f, &[a, b])
}

/// `False.rec.{0} (fun _ => goal) h` — ex falso at a `Prop` goal.
pub(crate) fn false_elim(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    goal: ExprId,
    h: ExprId,
) -> ExprId {
    let false_const = kernel.const_(c.logic.false_, vec![]);
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, false_const, goal, BinderInfo::Default)
    };
    let zero = kernel.level_zero();
    let rec = kernel.const_(c.logic.false_rec, vec![zero]);
    apply_all(kernel, rec, &[motive, h])
}

/// `Nat.succ_ne_zero n h : False`, for `h : Eq Nat (succ n) Nat.zero`.
pub(crate) fn succ_ne_zero_elim(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    n: ExprId,
    h: ExprId,
) -> ExprId {
    let f = kernel.const_(c.nat.succ_ne_zero, vec![]);
    apply_all(kernel, f, &[n, h])
}

/// `Nat.succ_injective n m h : Eq Nat n m`, for `h : Eq Nat (succ n) (succ m)`.
pub(crate) fn succ_inj(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    n: ExprId,
    m: ExprId,
    h: ExprId,
) -> ExprId {
    let f = kernel.const_(c.nat.succ_injective, vec![]);
    apply_all(kernel, f, &[n, m, h])
}

// ============================================================================
// The build entry point.
// ============================================================================

/// Build the Gödel-numbering package: the diagonal pairing, its structural
/// inverse, and the round-trip / injectivity theorems.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_code_prelude(kernel: &mut crate::Kernel) -> Result<FoCodePrelude, KernelError> {
    let syntax = build_fo_syntax_prelude(kernel)?;
    let c = CodeNames::rebuild(kernel, syntax.nat);

    let tri = declare_tri(kernel, &c)?;
    let pair = declare_pair(kernel, &c)?;
    let step = declare_step(kernel, &c)?;
    let unpair = declare_unpair(kernel, &c, step)?;
    let fst = declare_projection(kernel, &c, unpair, "fst", true)?;
    let snd = declare_projection(kernel, &c, unpair, "snd", false)?;

    let pair_zero_succ = declare_pair_zero_succ(kernel, &c)?;
    let pair_succ = declare_pair_succ(kernel, &c)?;
    let unpair_pair = declare_unpair_pair(kernel, &c, unpair, step, pair_zero_succ, pair_succ)?;
    let fst_pair = declare_projection_pair(kernel, &c, unpair, unpair_pair, fst, true)?;
    let snd_pair = declare_projection_pair(kernel, &c, unpair, unpair_pair, snd, false)?;
    let pair_inj_left = declare_pair_inj(kernel, &c, fst, fst_pair, true)?;
    let pair_inj_right = declare_pair_inj(kernel, &c, snd, snd_pair, false)?;

    Ok(FoCodePrelude {
        syntax,
        tri,
        pair,
        step,
        unpair,
        fst,
        snd,
        pair_zero_succ,
        pair_succ,
        unpair_pair,
        fst_pair,
        snd_pair,
        pair_inj_left,
        pair_inj_right,
    })
}

// ============================================================================
// The definitions.
// ============================================================================

/// `FO.Code.tri : Nat -> Nat := fun n => Nat.rec 0 (fun k ih => ih + succ k) n`
/// — `tri n = 0 + 1 + ... + n`. `tri (succ k)` ι-reduces to `succ (tri k + k)`,
/// which is the only reduction the round trip below needs from it.
fn declare_tri(kernel: &mut crate::Kernel, c: &CodeNames) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, c.nat_ty, BinderInfo::Default)
    };
    let base = nzero(kernel, c);
    let step = {
        let k_id = 1_640_011_u64;
        let ih_id = 1_640_012_u64;
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let sk = nsucc(kernel, c, k);
        let body = nadd(kernel, c, ih, sk);
        lams(kernel, &[(k_id, c.nat_ty), (ih_id, c.nat_ty)], body)
    };
    let n_id = 1_640_013_u64;
    let n = kernel.fvar(n_id);
    let rec = kernel.const_(c.nat.rec, vec![one]);
    let applied = apply_all(kernel, rec, &[motive, base, step, n]);
    let value = lam_fv(kernel, n_id, c.nat_ty, applied);
    let ty = arrow(kernel, c.nat_ty, c.nat_ty);
    kernel.add_declaration(Declaration::Definition {
        name: c.tri,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(c.tri)
}

/// `FO.Code.pair : Nat -> Nat -> Nat := fun a b => Nat.add (tri (Nat.add a b)) a`
/// — the index of `(a, b)` in the anti-diagonal enumeration
/// `(0,0), (0,1), (1,0), (0,2), (1,1), (2,0), (0,3), ...`.
fn declare_pair(kernel: &mut crate::Kernel, c: &CodeNames) -> Result<NameId, KernelError> {
    let a_id = 1_640_021_u64;
    let b_id = 1_640_022_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let sum = nadd(kernel, c, a, b);
    let tri_sum = tri_app(kernel, c, sum);
    let body = nadd(kernel, c, tri_sum, a);
    let value = lams(kernel, &[(a_id, c.nat_ty), (b_id, c.nat_ty)], body);
    let inner = arrow(kernel, c.nat_ty, c.nat_ty);
    let ty = arrow(kernel, c.nat_ty, inner);
    kernel.add_declaration(Declaration::Definition {
        name: c.pair,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(c.pair)
}

/// `FO.Code.step : Nat.Pair -> Nat.Pair` — the successor of a pair in the
/// enumeration:
///
/// ```text
/// step (mk a Nat.zero)     = mk Nat.zero (succ a)      -- start the next diagonal
/// step (mk a (succ b))     = mk (succ a) b             -- walk down this one
/// ```
///
/// Written as a `Nat.rec` on the SECOND component so that both equations hold
/// by ι-reduction, which is what makes every case of `unpair_pair` below close
/// without a rewrite.
fn declare_step(kernel: &mut crate::Kernel, c: &CodeNames) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let p_id = 1_640_031_u64;
    let p = kernel.fvar(p_id);
    let fst_p = pfst(kernel, c, p);
    let succ_fst = nsucc(kernel, c, fst_p);
    let zero = nzero(kernel, c);

    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, c.pair_ty, BinderInfo::Default)
    };
    let base = pmk(kernel, c, zero, succ_fst);
    let step_minor = {
        let b_id = 1_640_032_u64;
        let ih_id = 1_640_033_u64;
        let b = kernel.fvar(b_id);
        let body = pmk(kernel, c, succ_fst, b);
        lams(kernel, &[(b_id, c.nat_ty), (ih_id, c.pair_ty)], body)
    };
    let snd_p = psnd(kernel, c, p);
    let rec = kernel.const_(c.nat.rec, vec![one]);
    let applied = apply_all(kernel, rec, &[motive, base, step_minor, snd_p]);
    let value = lam_fv(kernel, p_id, c.pair_ty, applied);
    let ty = arrow(kernel, c.pair_ty, c.pair_ty);
    let name = kernel.name_str(c.code_ns, "step");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Code.unpair : Nat -> Nat.Pair := fun n => Nat.rec (mk 0 0) (fun _ ih =>
/// step ih) n` — `step` iterated `n` times from `(0, 0)`. Structural on `n`:
/// no fuel, no `Nat.div`, no `Nat.sqrt`.
fn declare_unpair(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    step: NameId,
) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, c.pair_ty, BinderInfo::Default)
    };
    let base = {
        let z = nzero(kernel, c);
        pmk(kernel, c, z, z)
    };
    let step_minor = {
        let k_id = 1_640_041_u64;
        let ih_id = 1_640_042_u64;
        let ih = kernel.fvar(ih_id);
        let step_const = kernel.const_(step, vec![]);
        let body = kernel.app(step_const, ih);
        lams(kernel, &[(k_id, c.nat_ty), (ih_id, c.pair_ty)], body)
    };
    let n_id = 1_640_043_u64;
    let n = kernel.fvar(n_id);
    let rec = kernel.const_(c.nat.rec, vec![one]);
    let applied = apply_all(kernel, rec, &[motive, base, step_minor, n]);
    let value = lam_fv(kernel, n_id, c.nat_ty, applied);
    let ty = arrow(kernel, c.nat_ty, c.pair_ty);
    let name = kernel.name_str(c.code_ns, "unpair");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Code.fst`/`FO.Code.snd : Nat -> Nat`, the two components of `unpair`.
fn declare_projection(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    unpair: NameId,
    label: &str,
    left: bool,
) -> Result<NameId, KernelError> {
    let n_id = 1_640_051_u64;
    let n = kernel.fvar(n_id);
    let unpair_const = kernel.const_(unpair, vec![]);
    let up = kernel.app(unpair_const, n);
    let body = if left {
        pfst(kernel, c, up)
    } else {
        psnd(kernel, c, up)
    };
    let value = lam_fv(kernel, n_id, c.nat_ty, body);
    let ty = arrow(kernel, c.nat_ty, c.nat_ty);
    let name = kernel.name_str(c.code_ns, label);
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

// ============================================================================
// The two enumeration equations.
// ============================================================================

/// `FO.Code.pair_zero_succ : Π k, Eq Nat (pair 0 (succ k)) (succ (pair k 0))`.
///
/// `pair 0 (succ k)` δι-reduces to `tri (succ (0 + k))` and `succ (pair k 0)`
/// to `succ (tri k + k)`, which is `tri (succ k)` reduced. So the whole
/// content is `Nat.zero_add k`, transported under `fun x => pair 0 (succ x)`.
fn declare_pair_zero_succ(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
) -> Result<NameId, KernelError> {
    let k_id = 1_640_061_u64;
    let k = kernel.fvar(k_id);
    let zero = nzero(kernel, c);
    let zero_add = kernel.const_(c.nat.zero_add, vec![]);
    let h = kernel.app(zero_add, k);
    let lhs_arg = nadd(kernel, c, zero, k);

    // congr along `fun x => tri (succ x)`: at `0 + k` that term is `pair 0
    // (succ k)` by δι alone, at `k` it is `succ (pair k 0)`.
    let logic = c.logic;
    let nat_ty = c.nat_ty;
    let proof = gcongr(
        kernel,
        logic,
        nat_ty,
        nat_ty,
        lhs_arg,
        k,
        h,
        &|kern, x| {
            let sx = nsucc(kern, c, x);
            tri_app(kern, c, sx)
        },
        1_640_062_u64,
    );

    let sk = nsucc(kernel, c, k);
    let lhs = pair_app(kernel, c, zero, sk);
    let pk0 = pair_app(kernel, c, k, zero);
    let rhs = nsucc(kernel, c, pk0);
    let concl = neq(kernel, c, lhs, rhs);
    let ty = pi_fv(kernel, k_id, c.nat_ty, concl);
    let value = lam_fv(kernel, k_id, c.nat_ty, proof);
    let name = kernel.name_str(c.code_ns, "pair_zero_succ");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.Code.pair_succ : Π a b, Eq Nat (pair (succ a) b) (succ (pair a (succ b)))`.
///
/// Both sides δι-reduce to `succ (tri _ + a)`; the two `tri` arguments are
/// `succ a + b` and `succ (a + b)`, so the content is `Nat.succ_add a b`.
fn declare_pair_succ(kernel: &mut crate::Kernel, c: &CodeNames) -> Result<NameId, KernelError> {
    let a_id = 1_640_071_u64;
    let b_id = 1_640_072_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);

    let succ_add = kernel.const_(c.nat.succ_add, vec![]);
    let h = apply_all(kernel, succ_add, &[a, b]);
    let sa = nsucc(kernel, c, a);
    let lhs_arg = nadd(kernel, c, sa, b);
    let ab = nadd(kernel, c, a, b);
    let rhs_arg = nsucc(kernel, c, ab);

    // congr along `fun x => succ (tri x + a)`: at `succ a + b` that is the
    // left-hand side, at `succ (a + b)` the right-hand side, both by δι alone.
    let logic = c.logic;
    let nat_ty = c.nat_ty;
    let shape = |kern: &mut crate::Kernel, x: ExprId| -> ExprId {
        let t = tri_app(kern, c, x);
        let sum = nadd(kern, c, t, a);
        nsucc(kern, c, sum)
    };
    let proof = gcongr(
        kernel,
        logic,
        nat_ty,
        nat_ty,
        lhs_arg,
        rhs_arg,
        h,
        &shape,
        1_640_073_u64,
    );

    let lhs = pair_app(kernel, c, sa, b);
    let sb = nsucc(kernel, c, b);
    let inner = pair_app(kernel, c, a, sb);
    let rhs = nsucc(kernel, c, inner);
    let concl = neq(kernel, c, lhs, rhs);
    let binders = [(a_id, c.nat_ty), (b_id, c.nat_ty)];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, proof);
    let name = kernel.name_str(c.code_ns, "pair_succ");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ============================================================================
// The round trip.
// ============================================================================

/// `FO.Code.unpair_pair : Π a b, Eq Nat.Pair (unpair (pair a b)) (Nat.Pair.mk a b)`.
///
/// One structural induction, on the CODE rather than on either component:
///
/// ```text
/// P n := Π a b, Eq Nat (pair a b) n -> Eq Nat.Pair (unpair n) (Nat.Pair.mk a b)
/// ```
///
/// and the theorem is `P (pair a b)` applied to `Eq.refl`. The two cases:
///
/// - `P 0`: every `pair a b` with `(a, b) != (0, 0)` is a `succ` (by
///   `pair_succ` when `a = succ a'`, by `pair_zero_succ` when `a = 0` and
///   `b = succ k`), so `Nat.succ_ne_zero` refutes the hypothesis; the
///   remaining corner is `Eq.refl` because `unpair 0` ι-reduces to `mk 0 0`.
/// - `P (succ m)`: `unpair (succ m)` ι-reduces to `step (unpair m)`. Peel one
///   `succ` off the hypothesis with the matching enumeration equation and
///   `Nat.succ_injective`, feed the result to the induction hypothesis, and
///   `congrArg step` finishes — because `step (mk k 0)` and
///   `step (mk a' (succ b))` ι-reduce to exactly the two goals.
fn declare_unpair_pair(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    unpair: NameId,
    step: NameId,
    pair_zero_succ: NameId,
    pair_succ: NameId,
) -> Result<NameId, KernelError> {
    let zero_lvl = kernel.level_zero();
    let nat_ty = c.nat_ty;
    let pair_ty = c.pair_ty;
    let logic = c.logic;
    let zero = nzero(kernel, c);

    let unpair_of = |kern: &mut crate::Kernel, n: ExprId| -> ExprId {
        let f = kern.const_(unpair, vec![]);
        kern.app(f, n)
    };
    let step_of = |kern: &mut crate::Kernel, p: ExprId| -> ExprId {
        let f = kern.const_(step, vec![]);
        kern.app(f, p)
    };

    // motive := fun n => Π a b, Eq Nat (pair a b) n -> Eq Pair (unpair n) (mk a b)
    let claim_at = |kern: &mut crate::Kernel, n: ExprId| -> ExprId {
        let a_id = 1_640_101_u64;
        let b_id = 1_640_102_u64;
        let a = kern.fvar(a_id);
        let b = kern.fvar(b_id);
        let hyp = {
            let pab = pair_app(kern, c, a, b);
            neq(kern, c, pab, n)
        };
        let concl = {
            let up = unpair_of(kern, n);
            let mk = pmk(kern, c, a, b);
            peq(kern, c, up, mk)
        };
        let with_h = arrow(kern, hyp, concl);
        pis(kern, &[(a_id, nat_ty), (b_id, nat_ty)], with_h)
    };
    let motive = {
        let n_id = 1_640_103_u64;
        let n = kernel.fvar(n_id);
        let body = claim_at(kernel, n);
        lam_fv(kernel, n_id, nat_ty, body)
    };

    // --- base : P 0 ----------------------------------------------------------
    let base = {
        let a_id = 1_640_111_u64;
        let b_id = 1_640_112_u64;
        let h_id = 1_640_113_u64;
        let a = kernel.fvar(a_id);

        // inner motive on `a`
        let inner_claim = |kern: &mut crate::Kernel, av: ExprId| -> ExprId {
            let b = kern.fvar(b_id);
            let hyp = {
                let pab = pair_app(kern, c, av, b);
                neq(kern, c, pab, zero)
            };
            let concl = {
                let up = unpair_of(kern, zero);
                let mk = pmk(kern, c, av, b);
                peq(kern, c, up, mk)
            };
            let with_h = arrow(kern, hyp, concl);
            pi_fv(kern, b_id, nat_ty, with_h)
        };
        let inner_motive = {
            let av_id = 1_640_114_u64;
            let av = kernel.fvar(av_id);
            let body = inner_claim(kernel, av);
            lam_fv(kernel, av_id, nat_ty, body)
        };

        // a = 0: case on b.
        let a_zero = {
            let bb_claim = |kern: &mut crate::Kernel, bv: ExprId| -> ExprId {
                let hyp = {
                    let pab = pair_app(kern, c, zero, bv);
                    neq(kern, c, pab, zero)
                };
                let concl = {
                    let up = unpair_of(kern, zero);
                    let mk = pmk(kern, c, zero, bv);
                    peq(kern, c, up, mk)
                };
                arrow(kern, hyp, concl)
            };
            let bb_motive = {
                let bv_id = 1_640_115_u64;
                let bv = kernel.fvar(bv_id);
                let body = bb_claim(kernel, bv);
                lam_fv(kernel, bv_id, nat_ty, body)
            };
            // b = 0: `unpair 0` and `mk 0 0` are the same term after iota.
            let bb_base = {
                let mk00 = pmk(kernel, c, zero, zero);
                let refl = {
                    let one = kernel.level_succ(zero_lvl);
                    let cst = kernel.const_(logic.eq_refl, vec![one]);
                    apply_all(kernel, cst, &[pair_ty, mk00])
                };
                let hyp_ty = {
                    let p00 = pair_app(kernel, c, zero, zero);
                    neq(kernel, c, p00, zero)
                };
                lam_fv(kernel, h_id, hyp_ty, refl)
            };
            // b = succ k: `pair 0 (succ k) = succ (pair k 0)` refutes the hypothesis.
            let bb_step = {
                let k_id = 1_640_116_u64;
                let ihb_id = 1_640_117_u64;
                let k = kernel.fvar(k_id);
                let sk = nsucc(kernel, c, k);
                let hyp_ty = {
                    let p = pair_app(kernel, c, zero, sk);
                    neq(kernel, c, p, zero)
                };
                let h = kernel.fvar(h_id);
                let pk0 = pair_app(kernel, c, k, zero);
                let succ_pk0 = nsucc(kernel, c, pk0);
                let eqn = {
                    let cst = kernel.const_(pair_zero_succ, vec![]);
                    kernel.app(cst, k)
                };
                let lhs = pair_app(kernel, c, zero, sk);
                let back = gsymm(kernel, logic, nat_ty, lhs, succ_pk0, eqn, 1_640_118_u64);
                let chained = gtrans(
                    kernel,
                    logic,
                    nat_ty,
                    succ_pk0,
                    lhs,
                    zero,
                    back,
                    h,
                    1_640_119_u64,
                );
                let contra = succ_ne_zero_elim(kernel, c, pk0, chained);
                let goal = {
                    let up = unpair_of(kernel, zero);
                    let mk = pmk(kernel, c, zero, sk);
                    peq(kernel, c, up, mk)
                };
                let body = false_elim(kernel, c, goal, contra);
                let with_h = lam_fv(kernel, h_id, hyp_ty, body);
                let ih_ty = bb_claim(kernel, k);
                lams(kernel, &[(k_id, nat_ty), (ihb_id, ih_ty)], with_h)
            };
            let rec = kernel.const_(c.nat.rec, vec![zero_lvl]);
            let b = kernel.fvar(b_id);
            let applied = apply_all(kernel, rec, &[bb_motive, bb_base, bb_step, b]);
            lam_fv(kernel, b_id, nat_ty, applied)
        };

        // a = succ a': `pair (succ a') b = succ (pair a' (succ b))` refutes it.
        let a_step = {
            let ap_id = 1_640_121_u64;
            let iha_id = 1_640_122_u64;
            let ap = kernel.fvar(ap_id);
            let sap = nsucc(kernel, c, ap);
            let b = kernel.fvar(b_id);
            let h = kernel.fvar(h_id);
            let hyp_ty = {
                let p = pair_app(kernel, c, sap, b);
                neq(kernel, c, p, zero)
            };
            let sb = nsucc(kernel, c, b);
            let inner = pair_app(kernel, c, ap, sb);
            let succ_inner = nsucc(kernel, c, inner);
            let eqn = {
                let cst = kernel.const_(pair_succ, vec![]);
                apply_all(kernel, cst, &[ap, b])
            };
            let lhs = pair_app(kernel, c, sap, b);
            let back = gsymm(kernel, logic, nat_ty, lhs, succ_inner, eqn, 1_640_123_u64);
            let chained = gtrans(
                kernel,
                logic,
                nat_ty,
                succ_inner,
                lhs,
                zero,
                back,
                h,
                1_640_124_u64,
            );
            let contra = succ_ne_zero_elim(kernel, c, inner, chained);
            let goal = {
                let up = unpair_of(kernel, zero);
                let mk = pmk(kernel, c, sap, b);
                peq(kernel, c, up, mk)
            };
            let body = false_elim(kernel, c, goal, contra);
            let with_h = lam_fv(kernel, h_id, hyp_ty, body);
            let with_b = lam_fv(kernel, b_id, nat_ty, with_h);
            let ih_ty = inner_claim(kernel, ap);
            lams(kernel, &[(ap_id, nat_ty), (iha_id, ih_ty)], with_b)
        };

        let rec = kernel.const_(c.nat.rec, vec![zero_lvl]);
        let applied = apply_all(kernel, rec, &[inner_motive, a_zero, a_step, a]);
        lam_fv(kernel, a_id, nat_ty, applied)
    };

    // --- step : Π m, P m -> P (succ m) --------------------------------------
    let step_minor = {
        let m_id = 1_640_131_u64;
        let ih_id = 1_640_132_u64;
        let a_id = 1_640_133_u64;
        let b_id = 1_640_134_u64;
        let h_id = 1_640_135_u64;
        let m = kernel.fvar(m_id);
        let ih = kernel.fvar(ih_id);
        let sm = nsucc(kernel, c, m);
        let a = kernel.fvar(a_id);

        let inner_claim = |kern: &mut crate::Kernel, av: ExprId| -> ExprId {
            let b = kern.fvar(b_id);
            let hyp = {
                let pab = pair_app(kern, c, av, b);
                let smv = {
                    let mm = kern.fvar(m_id);
                    nsucc(kern, c, mm)
                };
                neq(kern, c, pab, smv)
            };
            let concl = {
                let smv = {
                    let mm = kern.fvar(m_id);
                    nsucc(kern, c, mm)
                };
                let up = unpair_of(kern, smv);
                let mk = pmk(kern, c, av, b);
                peq(kern, c, up, mk)
            };
            let with_h = arrow(kern, hyp, concl);
            pi_fv(kern, b_id, nat_ty, with_h)
        };
        let inner_motive = {
            let av_id = 1_640_136_u64;
            let av = kernel.fvar(av_id);
            let body = inner_claim(kernel, av);
            lam_fv(kernel, av_id, nat_ty, body)
        };

        // a = 0: case on b.
        let a_zero = {
            let bb_claim = |kern: &mut crate::Kernel, bv: ExprId| -> ExprId {
                let hyp = {
                    let pab = pair_app(kern, c, zero, bv);
                    neq(kern, c, pab, sm)
                };
                let concl = {
                    let up = unpair_of(kern, sm);
                    let mk = pmk(kern, c, zero, bv);
                    peq(kern, c, up, mk)
                };
                arrow(kern, hyp, concl)
            };
            let bb_motive = {
                let bv_id = 1_640_137_u64;
                let bv = kernel.fvar(bv_id);
                let body = bb_claim(kernel, bv);
                lam_fv(kernel, bv_id, nat_ty, body)
            };
            // b = 0: `pair 0 0` IS `Nat.zero`, so the hypothesis is `0 = succ m`.
            let bb_base = {
                let h = kernel.fvar(h_id);
                let hyp_ty = {
                    let p00 = pair_app(kernel, c, zero, zero);
                    neq(kernel, c, p00, sm)
                };
                let back = gsymm(kernel, logic, nat_ty, zero, sm, h, 1_640_138_u64);
                let contra = succ_ne_zero_elim(kernel, c, m, back);
                let goal = {
                    let up = unpair_of(kernel, sm);
                    let mk = pmk(kernel, c, zero, zero);
                    peq(kernel, c, up, mk)
                };
                let body = false_elim(kernel, c, goal, contra);
                lam_fv(kernel, h_id, hyp_ty, body)
            };
            // b = succ k: peel with `pair_zero_succ`, then the induction hypothesis
            // at `(k, 0)`; `step (mk k 0)` ι-reduces to `mk 0 (succ k)`.
            let bb_step = {
                let k_id = 1_640_139_u64;
                let ihb_id = 1_640_140_u64;
                let k = kernel.fvar(k_id);
                let sk = nsucc(kernel, c, k);
                let h = kernel.fvar(h_id);
                let hyp_ty = {
                    let p = pair_app(kernel, c, zero, sk);
                    neq(kernel, c, p, sm)
                };
                let pk0 = pair_app(kernel, c, k, zero);
                let succ_pk0 = nsucc(kernel, c, pk0);
                let eqn = {
                    let cst = kernel.const_(pair_zero_succ, vec![]);
                    kernel.app(cst, k)
                };
                let lhs = pair_app(kernel, c, zero, sk);
                let back = gsymm(kernel, logic, nat_ty, lhs, succ_pk0, eqn, 1_640_141_u64);
                let chained = gtrans(
                    kernel,
                    logic,
                    nat_ty,
                    succ_pk0,
                    lhs,
                    sm,
                    back,
                    h,
                    1_640_142_u64,
                );
                let peeled = succ_inj(kernel, c, pk0, m, chained);
                let from_ih = {
                    let applied = apply_all(kernel, ih, &[k, zero]);
                    kernel.app(applied, peeled)
                };
                let up_m = unpair_of(kernel, m);
                let mk_k0 = pmk(kernel, c, k, zero);
                let body = gcongr(
                    kernel,
                    logic,
                    pair_ty,
                    pair_ty,
                    up_m,
                    mk_k0,
                    from_ih,
                    &step_of,
                    1_640_143_u64,
                );
                let with_h = lam_fv(kernel, h_id, hyp_ty, body);
                let ih_ty = bb_claim(kernel, k);
                lams(kernel, &[(k_id, nat_ty), (ihb_id, ih_ty)], with_h)
            };
            let rec = kernel.const_(c.nat.rec, vec![zero_lvl]);
            let b = kernel.fvar(b_id);
            let applied = apply_all(kernel, rec, &[bb_motive, bb_base, bb_step, b]);
            lam_fv(kernel, b_id, nat_ty, applied)
        };

        // a = succ a': peel with `pair_succ`, then the induction hypothesis at
        // `(a', succ b)`; `step (mk a' (succ b))` ι-reduces to `mk (succ a') b`.
        let a_step = {
            let ap_id = 1_640_151_u64;
            let iha_id = 1_640_152_u64;
            let ap = kernel.fvar(ap_id);
            let sap = nsucc(kernel, c, ap);
            let b = kernel.fvar(b_id);
            let h = kernel.fvar(h_id);
            let hyp_ty = {
                let p = pair_app(kernel, c, sap, b);
                neq(kernel, c, p, sm)
            };
            let sb = nsucc(kernel, c, b);
            let inner = pair_app(kernel, c, ap, sb);
            let succ_inner = nsucc(kernel, c, inner);
            let eqn = {
                let cst = kernel.const_(pair_succ, vec![]);
                apply_all(kernel, cst, &[ap, b])
            };
            let lhs = pair_app(kernel, c, sap, b);
            let back = gsymm(kernel, logic, nat_ty, lhs, succ_inner, eqn, 1_640_153_u64);
            let chained = gtrans(
                kernel,
                logic,
                nat_ty,
                succ_inner,
                lhs,
                sm,
                back,
                h,
                1_640_154_u64,
            );
            let peeled = succ_inj(kernel, c, inner, m, chained);
            let from_ih = {
                let applied = apply_all(kernel, ih, &[ap, sb]);
                kernel.app(applied, peeled)
            };
            let up_m = unpair_of(kernel, m);
            let mk_ap_sb = pmk(kernel, c, ap, sb);
            let body = gcongr(
                kernel,
                logic,
                pair_ty,
                pair_ty,
                up_m,
                mk_ap_sb,
                from_ih,
                &step_of,
                1_640_155_u64,
            );
            let with_h = lam_fv(kernel, h_id, hyp_ty, body);
            let with_b = lam_fv(kernel, b_id, nat_ty, with_h);
            let ih_ty = inner_claim(kernel, ap);
            lams(kernel, &[(ap_id, nat_ty), (iha_id, ih_ty)], with_b)
        };

        let rec = kernel.const_(c.nat.rec, vec![zero_lvl]);
        let applied = apply_all(kernel, rec, &[inner_motive, a_zero, a_step, a]);
        let with_a = lam_fv(kernel, a_id, nat_ty, applied);
        let ih_ty = claim_at(kernel, m);
        lams(kernel, &[(m_id, nat_ty), (ih_id, ih_ty)], with_a)
    };

    // --- the theorem ---------------------------------------------------------
    let a_id = 1_640_161_u64;
    let b_id = 1_640_162_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let pab = pair_app(kernel, c, a, b);
    let rec = kernel.const_(c.nat.rec, vec![zero_lvl]);
    let induction = apply_all(kernel, rec, &[motive, base, step_minor, pab]);
    let refl = {
        let one = kernel.level_succ(zero_lvl);
        let cst = kernel.const_(logic.eq_refl, vec![one]);
        apply_all(kernel, cst, &[nat_ty, pab])
    };
    let applied = apply_all(kernel, induction, &[a, b, refl]);

    let concl = {
        let up = unpair_of(kernel, pab);
        let mk = pmk(kernel, c, a, b);
        peq(kernel, c, up, mk)
    };
    let binders = [(a_id, nat_ty), (b_id, nat_ty)];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, applied);
    let name = kernel.name_str(c.code_ns, "unpair_pair");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.Code.fst_pair : Π a b, Eq Nat (fst (pair a b)) a` and its `snd` twin —
/// `congrArg` of `Nat.Pair.fst`/`snd` along [`declare_unpair_pair`], with both
/// endpoints ι-reducing to the stated ones.
fn declare_projection_pair(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    unpair: NameId,
    unpair_pair: NameId,
    projection: NameId,
    left: bool,
) -> Result<NameId, KernelError> {
    let a_id = 1_640_171_u64;
    let b_id = 1_640_172_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let pab = pair_app(kernel, c, a, b);
    let up = {
        let f = kernel.const_(unpair, vec![]);
        kernel.app(f, pab)
    };
    let mk = pmk(kernel, c, a, b);
    let h = {
        let cst = kernel.const_(unpair_pair, vec![]);
        apply_all(kernel, cst, &[a, b])
    };
    let logic = c.logic;
    let proof = gcongr(
        kernel,
        logic,
        c.pair_ty,
        c.nat_ty,
        up,
        mk,
        h,
        &|kern, x| {
            if left {
                pfst(kern, c, x)
            } else {
                psnd(kern, c, x)
            }
        },
        1_640_173_u64,
    );

    let lhs = {
        let f = kernel.const_(projection, vec![]);
        kernel.app(f, pab)
    };
    let rhs = if left { a } else { b };
    let concl = neq(kernel, c, lhs, rhs);
    let binders = [(a_id, c.nat_ty), (b_id, c.nat_ty)];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, proof);
    let label = if left { "fst_pair" } else { "snd_pair" };
    let name = kernel.name_str(c.code_ns, label);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.Code.pair_inj_left : Π a b c d, Eq Nat (pair a b) (pair c d) -> Eq Nat a c`
/// and its `right` twin: read the component back off both sides with
/// [`declare_projection_pair`].
fn declare_pair_inj(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    projection: NameId,
    projection_pair: NameId,
    left: bool,
) -> Result<NameId, KernelError> {
    let a_id = 1_640_181_u64;
    let b_id = 1_640_182_u64;
    let x_id = 1_640_183_u64;
    let y_id = 1_640_184_u64;
    let h_id = 1_640_185_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let h = kernel.fvar(h_id);

    let pab = pair_app(kernel, c, a, b);
    let pxy = pair_app(kernel, c, x, y);
    let logic = c.logic;
    let nat_ty = c.nat_ty;

    let proj_of = |kern: &mut crate::Kernel, n: ExprId| -> ExprId {
        let f = kern.const_(projection, vec![]);
        kern.app(f, n)
    };

    let congr = gcongr(
        kernel,
        logic,
        nat_ty,
        nat_ty,
        pab,
        pxy,
        h,
        &proj_of,
        1_640_186_u64,
    );
    let lhs_val = if left { a } else { b };
    let rhs_val = if left { x } else { y };
    let proj_ab = proj_of(kernel, pab);
    let proj_xy = proj_of(kernel, pxy);
    let eq_ab = {
        let cst = kernel.const_(projection_pair, vec![]);
        apply_all(kernel, cst, &[a, b])
    };
    let eq_xy = {
        let cst = kernel.const_(projection_pair, vec![]);
        apply_all(kernel, cst, &[x, y])
    };
    let back = gsymm(
        kernel,
        logic,
        nat_ty,
        proj_ab,
        lhs_val,
        eq_ab,
        1_640_187_u64,
    );
    let tail = gtrans(
        kernel,
        logic,
        nat_ty,
        proj_ab,
        proj_xy,
        rhs_val,
        congr,
        eq_xy,
        1_640_188_u64,
    );
    let proof = gtrans(
        kernel,
        logic,
        nat_ty,
        lhs_val,
        proj_ab,
        rhs_val,
        back,
        tail,
        1_640_189_u64,
    );

    let hyp_ty = neq(kernel, c, pab, pxy);
    let concl = neq(kernel, c, lhs_val, rhs_val);
    let with_h = arrow(kernel, hyp_ty, concl);
    let binders = [
        (a_id, nat_ty),
        (b_id, nat_ty),
        (x_id, nat_ty),
        (y_id, nat_ty),
    ];
    let ty = pis(kernel, &binders, with_h);
    let value = {
        let inner = lam_fv(kernel, h_id, hyp_ty, proof);
        lams(kernel, &binders, inner)
    };
    let label = if left {
        "pair_inj_left"
    } else {
        "pair_inj_right"
    };
    let name = kernel.name_str(c.code_ns, label);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests;
