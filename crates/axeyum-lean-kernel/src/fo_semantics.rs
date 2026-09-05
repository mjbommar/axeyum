//! **Slice 2 of the first-order model theory group** (`fo_*.rs`, ADR-1636):
//! `FO.Structure`, term evaluation, **Tarski satisfaction** `FO.sat`, and one
//! concrete structure — ℕ with `0`, `succ`, `+`, `<` — together with two
//! sentences shown satisfied in it by kernel reduction.
//!
//! ## A structure is a record over a *parameter* carrier
//!
//! ```text
//! FO.Structure : Type -> Type                       -- one parameter, the carrier
//! FO.Structure.mk : Π (M : Type),
//!     (Nat -> M) ->                                 -- constant symbols
//!     (Nat -> M -> M) ->                            -- unary function symbols
//!     (Nat -> M -> M -> M) ->                       -- binary function symbols
//!     (Nat -> M -> Prop) ->                         -- unary relation symbols
//!     (Nat -> M -> M -> Prop) ->                    -- binary relation symbols
//!     FO.Structure M
//! ```
//!
//! The carrier is a **parameter**, not a field, and this is a deliberate
//! design choice with a cost attached to the alternative. A record carrying
//! its own carrier (`mk (M : Type) (fn0 : Nat -> M) …`) would need the
//! projection `Structure.carrier : Structure -> Type` — a *large* elimination
//! producing a sort — and then every one of the four inductions in
//! `fo_substitution.rs` and `fo_soundness.rs` would quantify over a term whose
//! **type** is a stuck projection `Structure.carrier S`. Making the carrier a
//! parameter, exactly as `Sigma.{u,v} : Π (α : Sort u), (α → Sort v) → Sort …`
//! does in `sigma_prelude.rs`, keeps every type in this group a syntactic
//! `Sort`, and loses nothing: `Π (M : Type) (S : FO.Structure M), …` is the
//! same quantification, spelled with the carrier out front.
//!
//! The carrier sits at `Type` (`Sort 1`), not at a universe parameter. Every
//! statement in this group is then universe-monomorphic, which is what keeps
//! the recursor applications below to a single explicit level. The concrete
//! structure this slice builds — and every structure a finite or countable
//! model needs — lives at `Type`.
//!
//! Equality is **not** one of the five interpreted families: `FO.Formula.eqf`
//! is a logical constructor, and `FO.sat` sends it to the kernel's own
//! `Eq M`. So `=` means equality in the carrier by construction, and no
//! structure can interpret it as anything else — which is exactly the standard
//! semantics of first-order logic *with* equality, and what makes the `eqf`
//! rules in `fo_provable.rs` sound without any congruence side conditions on
//! the structure.
//!
//! ## Satisfaction is `Prop`-valued and constructive
//!
//! ```text
//! FO.Term.eval : Π (M : Type), FO.Structure M -> FO.Term -> (Nat -> M) -> M
//! FO.sat       : Π (M : Type), FO.Structure M -> FO.Formula -> (Nat -> M) -> Prop
//! ```
//!
//! `FO.sat` is a `FO.Formula.rec` application at the motive
//! `fun _ => (Nat -> M) -> Prop`, and every clause is the kernel's own
//! connective at the same arity:
//!
//! | formula | `sat M S φ v` |
//! | --- | --- |
//! | `bot` | `False` |
//! | `eqf a b` | `Eq M (eval a v) (eval b v)` |
//! | `rel1 k t` | `S.rel1 k (eval t v)` |
//! | `rel2 k a b` | `S.rel2 k (eval a v) (eval b v)` |
//! | `and_ p q` | `And (sat p v) (sat q v)` |
//! | `or_ p q` | `Or (sat p v) (sat q v)` |
//! | `imp p q` | `sat p v -> sat q v` |
//! | `all p` | `Π (x : M), sat p (FO.Val.cons x v)` |
//! | `ex p` | `Exists M (fun x => sat p (FO.Val.cons x v))` |
//!
//! This is the Tarski definition verbatim, and it is **constructive**: the
//! clauses use `Or`, `Exists` and the kernel's own `Pi`, never
//! `Not (And (Not _) (Not _))` or a `Bool`-valued truth table. That matters
//! because this kernel has no `Classical.em`, no `propext` and no `funext`
//! (see `prelude.rs`'s module docs), so a classical reading was never
//! available — and it means `fo_soundness.rs` proves soundness of an
//! *intuitionistic* natural deduction calculus with respect to this semantics,
//! which is the honest pairing. Nothing here rules out a classical calculus
//! later; it would need a semantics with a matching classical structure, not a
//! change to this one.
//!
//! The `Prop`-valued semantics is a genuine step up from `ipc_soundness.rs`'s
//! 3-element Heyting chain, and it makes the propositional half of soundness
//! *cheaper*, not more expensive: `and_intro`'s soundness case, which needed a
//! lattice lemma over the chain, is `And.intro` here.
//!
//! ## Valuations and `FO.Val.cons`
//!
//! A valuation is a total function `Nat -> M`, and the quantifier clauses
//! extend it by
//!
//! ```text
//! FO.Val.cons : Π (M : Type), M -> (Nat -> M) -> Nat -> M
//!             := fun M a v n => Nat.rec.{1} (motive := fun _ => M) a (fun k _ => v k) n
//! ```
//!
//! so `Val.cons a v 0` ι-reduces to `a` and `Val.cons a v (succ k)` to `v k`.
//! It is the semantic twin of `FO.Subst.cons`, and the pair of ι-reductions is
//! what makes `fo_substitution.rs`'s `∀`/`∃` cases discharge their index-`0`
//! obligation by `Eq.refl`.
//!
//! One further consequence of the `Nat.rec` shape is worth stating because it
//! is what rescues this development from the absence of `funext`:
//! `fun m => FO.Val.cons a v (Nat.succ m)` is **definitionally** `v`. The
//! body ι-reduces to `v m` under the binder, and the kernel's η rule
//! (`tc.rs`'s `try_eta_expansion`) closes `fun m => v m` against `v`. So the
//! "shifting a valuation and then reading past the new slot gives the original
//! valuation" step, which in a `funext`-free kernel would otherwise need a
//! pointwise congruence lemma at every use, is free.
//!
//! ## The ℕ structure
//!
//! `FO.natStructure : FO.Structure Nat` interprets each symbol family as a
//! genuinely index-dependent family, not as a constant that ignores its index
//! (a structure that ignored the index would be a legitimate structure but a
//! degenerate test — the module tests would then pass for a `sat` that dropped
//! the symbol index):
//!
//! | family | interpretation | the named symbol |
//! | --- | --- | --- |
//! | `fn0 k` | the numeral `k` | `f0 0` is `0` |
//! | `fn1 k` | `x ↦ Nat.add x k` | `f1 1` is `Nat.succ` |
//! | `fn2 k` | `(x, y) ↦ Nat.add (Nat.add x y) k` | `f2 0` is `+` |
//! | `rel1 k` | `x ↦ Nat.lt k x` | — |
//! | `rel2 k` | `(x, y) ↦ Nat.lt (Nat.add x k) y` | `rel2 0` is `<` |
//!
//! `Nat.add` recurses on its **second** argument, so `Nat.add x Nat.zero` and
//! `Nat.add x (Nat.succ Nat.zero)` ι-reduce to `x` and `Nat.succ x`: the
//! "named symbol" column is definitional, not a lemma. That is what lets the
//! two satisfaction theorems below be proved by supplying a witness and a
//! `Nat` lemma, with the kernel doing the unfolding.
//!
//! Two sentences are landed as kernel `Theorem`s, each stated for **every**
//! valuation (they are sentences — no free index — so the valuation is inert,
//! and quantifying over it is the honest way to say so):
//!
//! ```text
//! FO.nat_sat_lt_irrefl : Π (v : Nat -> Nat),
//!   FO.sat Nat FO.natStructure (all (imp (rel2 0 (var 0) (var 0)) bot)) v
//!
//! FO.nat_sat_no_greatest : Π (v : Nat -> Nat),
//!   FO.sat Nat FO.natStructure (all (ex (rel2 0 (var 1) (var 0)))) v
//! ```
//!
//! i.e. `∀x, ¬(x < x)` and `∀x ∃y, x < y`. The second is the discriminating
//! one, and it is the reason it is here rather than something simpler: its two
//! nested binders read the valuation at indices `1` and `0`, so its
//! satisfaction reduces to `∀ x, ∃ y, Nat.lt x y` **only if** the `ex` clause
//! extends the valuation with the witness and the `all` clause did so before
//! it. A `sat` whose `ex` clause passed the *outer* valuation through would
//! reduce this to `∀ x, ∃ y, Nat.lt x (v 0)`, which is false in ℕ at
//! `v := fun _ => 0`; one that shifted in the wrong order would reduce it to
//! `∀ x, ∃ y, Nat.lt y y`, which is false outright. Neither is provable, so
//! the theorem is a real check on the valuation plumbing and not a formality.

use crate::FoSyntaxPrelude;
use crate::fo_syntax::SyntaxNames;
use crate::fo_syntax::{apply_all, arrow, lam_fv, lams, pi_fv, pis};
use crate::{BinderInfo, Declaration, ExprId, KernelError, LevelId, LogicPrelude, NameId};
use crate::{ReducibilityHint, build_fo_syntax_prelude};

/// Names produced by [`build_fo_semantics_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoSemanticsPrelude {
    /// `FO.Term`, `FO.Formula` and the substitution operations (slice 1).
    pub syntax: FoSyntaxPrelude,

    // --- FO.Structure --------------------------------------------------------
    /// `FO.Structure : Type -> Type`.
    pub structure: NameId,
    /// `FO.Structure.mk`, the five-field constructor.
    pub structure_mk: NameId,
    /// `FO.Structure.rec`, the generated recursor.
    pub structure_rec: NameId,
    /// `FO.Structure.fn0 : Π (M) (S : Structure M), Nat -> M`.
    pub fn0: NameId,
    /// `FO.Structure.fn1 : Π (M) (S : Structure M), Nat -> M -> M`.
    pub fn1: NameId,
    /// `FO.Structure.fn2 : Π (M) (S : Structure M), Nat -> M -> M -> M`.
    pub fn2: NameId,
    /// `FO.Structure.rel1 : Π (M) (S : Structure M), Nat -> M -> Prop`.
    pub rel1: NameId,
    /// `FO.Structure.rel2 : Π (M) (S : Structure M), Nat -> M -> M -> Prop`.
    pub rel2: NameId,

    // --- valuations and semantics -------------------------------------------
    /// `FO.Val.cons : Π (M : Type), M -> (Nat -> M) -> Nat -> M`.
    pub val_cons: NameId,
    /// `FO.Term.eval : Π (M) (S), FO.Term -> (Nat -> M) -> M`.
    pub term_eval: NameId,
    /// `FO.sat : Π (M) (S), FO.Formula -> (Nat -> M) -> Prop`.
    pub sat: NameId,

    // --- the concrete ℕ structure -------------------------------------------
    /// `FO.natStructure : FO.Structure Nat`.
    pub nat_structure: NameId,
    /// `FO.nat_sat_lt_irrefl` — `∀ x, ¬(x < x)` holds in `FO.natStructure`.
    pub nat_sat_lt_irrefl: NameId,
    /// `FO.nat_sat_no_greatest` — `∀ x ∃ y, x < y` holds in `FO.natStructure`.
    pub nat_sat_no_greatest: NameId,
}

/// Build the first-order semantics package on top of `fo_syntax.rs`.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_semantics_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoSemanticsPrelude, KernelError> {
    let syntax = build_fo_syntax_prelude(kernel)?;
    let syn = syntax.names(kernel);
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);

    let structure = kernel.name_str(syn.fo, "Structure");
    let structure_mk = kernel.name_str(structure, "mk");
    declare_structure(kernel, &syn, structure, structure_mk, one)?;
    let structure_rec = kernel.name_str(structure, "rec");

    let sem = StructureNames {
        structure,
        structure_mk,
        structure_rec,
    };

    let fn0 = declare_projection(kernel, &syn, &sem, Field::Fn0, one)?;
    let fn1 = declare_projection(kernel, &syn, &sem, Field::Fn1, one)?;
    let fn2 = declare_projection(kernel, &syn, &sem, Field::Fn2, one)?;
    let rel1 = declare_projection(kernel, &syn, &sem, Field::Rel1, one)?;
    let rel2 = declare_projection(kernel, &syn, &sem, Field::Rel2, one)?;

    let val_cons = declare_val_cons(kernel, &syn, one)?;

    let interp = Interp {
        structure,
        fn0,
        fn1,
        fn2,
        rel1,
        rel2,
        val_cons,
    };

    let term_eval = declare_term_eval(kernel, &syn, &interp, one)?;
    let sat = declare_sat(kernel, &syn, &interp, syntax.nat.logic, term_eval, one)?;

    let nat_structure = declare_nat_structure(kernel, &syntax, &sem, one)?;
    let nat_sat_lt_irrefl = declare_nat_sat_lt_irrefl(kernel, &syntax, &syn, sat, nat_structure)?;
    let nat_sat_no_greatest =
        declare_nat_sat_no_greatest(kernel, &syntax, &syn, sat, nat_structure, one)?;

    Ok(FoSemanticsPrelude {
        syntax,
        structure,
        structure_mk,
        structure_rec,
        fn0,
        fn1,
        fn2,
        rel1,
        rel2,
        val_cons,
        term_eval,
        sat,
        nat_structure,
        nat_sat_lt_irrefl,
        nat_sat_no_greatest,
    })
}

/// `FO.Structure`, its constructor and its recursor.
pub(crate) struct StructureNames {
    pub(crate) structure: NameId,
    pub(crate) structure_mk: NameId,
    pub(crate) structure_rec: NameId,
}

/// The interpretation names `FO.Term.eval` / `FO.sat` are built over.
pub(crate) struct Interp {
    pub(crate) structure: NameId,
    pub(crate) fn0: NameId,
    pub(crate) fn1: NameId,
    pub(crate) fn2: NameId,
    pub(crate) rel1: NameId,
    pub(crate) rel2: NameId,
    pub(crate) val_cons: NameId,
}

/// Which of `FO.Structure`'s five fields a projection selects.
#[derive(Clone, Copy)]
enum Field {
    Fn0,
    Fn1,
    Fn2,
    Rel1,
    Rel2,
}

impl Field {
    fn name(self) -> &'static str {
        match self {
            Field::Fn0 => "fn0",
            Field::Fn1 => "fn1",
            Field::Fn2 => "fn2",
            Field::Rel1 => "rel1",
            Field::Rel2 => "rel2",
        }
    }

    fn index(self) -> usize {
        match self {
            Field::Fn0 => 0,
            Field::Fn1 => 1,
            Field::Fn2 => 2,
            Field::Rel1 => 3,
            Field::Rel2 => 4,
        }
    }
}

/// The five field types of `FO.Structure M`, in declaration order, at the
/// given carrier expression.
fn field_types(kernel: &mut crate::Kernel, syn: &SyntaxNames, carrier: ExprId) -> [ExprId; 5] {
    let prop = kernel.sort_zero();
    // Nat -> M
    let t_fn0 = arrow(kernel, syn.nat_ty, carrier);
    // Nat -> M -> M
    let t_fn1 = {
        let inner = arrow(kernel, carrier, carrier);
        arrow(kernel, syn.nat_ty, inner)
    };
    // Nat -> M -> M -> M
    let t_fn2 = {
        let inner = arrow(kernel, carrier, carrier);
        let inner = arrow(kernel, carrier, inner);
        arrow(kernel, syn.nat_ty, inner)
    };
    // Nat -> M -> Prop
    let t_rel1 = {
        let inner = arrow(kernel, carrier, prop);
        arrow(kernel, syn.nat_ty, inner)
    };
    // Nat -> M -> M -> Prop
    let t_rel2 = {
        let inner = arrow(kernel, carrier, prop);
        let inner = arrow(kernel, carrier, inner);
        arrow(kernel, syn.nat_ty, inner)
    };
    [t_fn0, t_fn1, t_fn2, t_rel1, t_rel2]
}

/// Declare `FO.Structure : Type -> Type` (one parameter, the carrier) and its
/// single five-field constructor `FO.Structure.mk`.
fn declare_structure(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    structure: NameId,
    structure_mk: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let type_sort = kernel.sort(one);

    // FO.Structure : Type -> Type
    let ind_ty = arrow(kernel, type_sort, type_sort);

    // FO.Structure.mk : Π (M : Type) (fn0) (fn1) (fn2) (rel1) (rel2), Structure M
    let m_id = 1_636_501_u64;
    let m = kernel.fvar(m_id);
    let fields = field_types(kernel, syn, m);
    let structure_const = kernel.const_(structure, vec![]);
    let result = kernel.app(structure_const, m);
    let mk_ty = {
        let mut ty = result;
        for &field in fields.iter().rev() {
            ty = arrow(kernel, field, ty);
        }
        pi_fv(kernel, m_id, type_sort, ty)
    };

    kernel.add_inductive(structure, &[], 1, ind_ty, &[(structure_mk, mk_ty)])
}

/// Declare one of the five projections, e.g.
///
/// ```text
/// FO.Structure.rel2 : Π (M : Type) (S : FO.Structure M), Nat -> M -> M -> Prop
///   := fun M S => FO.Structure.rec.{1} M (fun _ => Nat -> M -> M -> Prop)
///                    (fun _ _ _ _ r2 => r2) S
/// ```
///
/// The recursor takes the inductive's parameters first, then the motive, then
/// one minor per constructor, then the major premise — the same order
/// `sigma_prelude.rs`'s `Sigma.fst` uses.
fn declare_projection(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    sem: &StructureNames,
    field: Field,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let type_sort = kernel.sort(one);
    let m_id = 1_636_511_u64;
    let s_id = 1_636_512_u64;
    let m = kernel.fvar(m_id);
    let s = kernel.fvar(s_id);

    let fields = field_types(kernel, syn, m);
    let selected = fields[field.index()];

    let structure_const = kernel.const_(sem.structure, vec![]);
    let struct_m = kernel.app(structure_const, m);

    let anon = kernel.anon();
    let motive = kernel.lam(anon, struct_m, selected, BinderInfo::Default);

    // The single minor: bind all five fields, return the selected one.
    let minor = {
        let base = 1_636_520_u64;
        let binders: Vec<(u64, ExprId)> = fields
            .iter()
            .enumerate()
            .map(|(i, &ty)| (base + i as u64, ty))
            .collect();
        let chosen = kernel.fvar(base + field.index() as u64);
        lams(kernel, &binders, chosen)
    };

    let rec_const = kernel.const_(sem.structure_rec, vec![one]);
    let body = apply_all(kernel, rec_const, &[m, motive, minor, s]);
    let value = pis_to_lams(kernel, &[(m_id, type_sort), (s_id, struct_m)], body);

    let ty = pis(kernel, &[(m_id, type_sort), (s_id, struct_m)], selected);

    let name = kernel.name_str(sem.structure, field.name());
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `lams` under a different name at the call sites that pair a `pis`-built
/// type with a `lams`-built value over the SAME binder list, so the two cannot
/// drift apart.
fn pis_to_lams(kernel: &mut crate::Kernel, binders: &[(u64, ExprId)], body: ExprId) -> ExprId {
    lams(kernel, binders, body)
}

/// `FO.Val.cons : Π (M : Type), M -> (Nat -> M) -> Nat -> M`, the semantic
/// twin of `FO.Subst.cons`. See the module docs for why the `Nat.rec` shape
/// (rather than a `Bool` test on the index) is load-bearing.
fn declare_val_cons(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let type_sort = kernel.sort(one);
    let m_id = 1_636_531_u64;
    let a_id = 1_636_532_u64;
    let v_id = 1_636_533_u64;
    let n_id = 1_636_534_u64;
    let k_id = 1_636_535_u64;
    let ih_id = 1_636_536_u64;

    let m = kernel.fvar(m_id);
    let a = kernel.fvar(a_id);
    let v = kernel.fvar(v_id);
    let n = kernel.fvar(n_id);
    let k = kernel.fvar(k_id);

    let val_ty = arrow(kernel, syn.nat_ty, m);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.nat_ty, m, BinderInfo::Default);

    let v_k = kernel.app(v, k);
    let step = lams(kernel, &[(k_id, syn.nat_ty), (ih_id, m)], v_k);

    let nat_rec = kernel.const_(syn.nat_rec, vec![one]);
    let body = apply_all(kernel, nat_rec, &[motive, a, step, n]);

    let binders = [
        (m_id, type_sort),
        (a_id, m),
        (v_id, val_ty),
        (n_id, syn.nat_ty),
    ];
    let value = lams(kernel, &binders, body);
    let ty = pis(kernel, &binders, m);

    let val_ns = kernel.name_str(syn.fo, "Val");
    let name = kernel.name_str(val_ns, "cons");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Term.eval : Π (M : Type) (S : FO.Structure M), FO.Term -> (Nat -> M) -> M`,
/// a `FO.Term.rec` application at the motive `fun _ => (Nat -> M) -> M`.
///
/// ```text
/// m_var := fun i v        => v i
/// m_f0  := fun k v        => S.fn0 k
/// m_f1  := fun k _ ih v   => S.fn1 k (ih v)
/// m_f2  := fun k _ _ a b v => S.fn2 k (a v) (b v)
/// ```
fn declare_term_eval(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    interp: &Interp,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let type_sort = kernel.sort(one);
    let m_id = 1_636_541_u64;
    let s_id = 1_636_542_u64;
    let m = kernel.fvar(m_id);
    let s = kernel.fvar(s_id);

    let structure_const = kernel.const_(interp.structure, vec![]);
    let struct_m = kernel.app(structure_const, m);

    let val_ty = arrow(kernel, syn.nat_ty, m);
    let codomain = arrow(kernel, val_ty, m);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.term_ty, codomain, BinderInfo::Default);

    // `FO.Structure.fnJ M S args…`
    let proj = |kernel: &mut crate::Kernel, name: NameId, args: &[ExprId]| -> ExprId {
        let c = kernel.const_(name, vec![]);
        let head = apply_all(kernel, c, &[m, s]);
        apply_all(kernel, head, args)
    };

    let m_var = {
        let i_id = 1_636_551_u64;
        let v_id = 1_636_552_u64;
        let i = kernel.fvar(i_id);
        let v = kernel.fvar(v_id);
        let body = kernel.app(v, i);
        lams(kernel, &[(i_id, syn.nat_ty), (v_id, val_ty)], body)
    };

    let m_f0 = {
        let k_id = 1_636_561_u64;
        let v_id = 1_636_562_u64;
        let k = kernel.fvar(k_id);
        let body = proj(kernel, interp.fn0, &[k]);
        lams(kernel, &[(k_id, syn.nat_ty), (v_id, val_ty)], body)
    };

    let m_f1 = {
        let k_id = 1_636_571_u64;
        let t_id = 1_636_572_u64;
        let ih_id = 1_636_573_u64;
        let v_id = 1_636_574_u64;
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let v = kernel.fvar(v_id);
        let ih_v = kernel.app(ih, v);
        let body = proj(kernel, interp.fn1, &[k, ih_v]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (t_id, syn.term_ty),
                (ih_id, codomain),
                (v_id, val_ty),
            ],
            body,
        )
    };

    let m_f2 = {
        let k_id = 1_636_581_u64;
        let a_id = 1_636_582_u64;
        let b_id = 1_636_583_u64;
        let ia_id = 1_636_584_u64;
        let ib_id = 1_636_585_u64;
        let v_id = 1_636_586_u64;
        let k = kernel.fvar(k_id);
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let v = kernel.fvar(v_id);
        let ia_v = kernel.app(ia, v);
        let ib_v = kernel.app(ib, v);
        let body = proj(kernel, interp.fn2, &[k, ia_v, ib_v]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (a_id, syn.term_ty),
                (b_id, syn.term_ty),
                (ia_id, codomain),
                (ib_id, codomain),
                (v_id, val_ty),
            ],
            body,
        )
    };

    let rec_const = kernel.const_(syn.term_rec, vec![one]);
    let applied = apply_all(kernel, rec_const, &[motive, m_var, m_f0, m_f1, m_f2]);

    let t_id = 1_636_591_u64;
    let t = kernel.fvar(t_id);
    let inner = kernel.app(applied, t);
    let with_term = lam_fv(kernel, t_id, syn.term_ty, inner);

    let binders = [(m_id, type_sort), (s_id, struct_m)];
    let value = lams(kernel, &binders, with_term);
    let cod = arrow(kernel, syn.term_ty, codomain);
    let ty = pis(kernel, &binders, cod);

    let name = kernel.name_str(syn.term, "eval");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.sat : Π (M : Type) (S : FO.Structure M), FO.Formula -> (Nat -> M) -> Prop`,
/// the Tarski definition as a `FO.Formula.rec` application. See the module
/// docs for the clause table.
#[allow(clippy::too_many_lines)]
fn declare_sat(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    interp: &Interp,
    logic: LogicPrelude,
    term_eval: NameId,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let type_sort = kernel.sort(one);
    let prop = kernel.sort_zero();

    let m_id = 1_636_601_u64;
    let s_id = 1_636_602_u64;
    let m = kernel.fvar(m_id);
    let s = kernel.fvar(s_id);

    let structure_const = kernel.const_(interp.structure, vec![]);
    let struct_m = kernel.app(structure_const, m);

    let val_ty = arrow(kernel, syn.nat_ty, m);
    let codomain = arrow(kernel, val_ty, prop);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.formula_ty, codomain, BinderInfo::Default);

    // `FO.Term.eval M S t v`
    let ev = |kernel: &mut crate::Kernel, t: ExprId, v: ExprId| -> ExprId {
        let c = kernel.const_(term_eval, vec![]);
        apply_all(kernel, c, &[m, s, t, v])
    };
    // `FO.Structure.relJ M S args…`
    let proj = |kernel: &mut crate::Kernel, name: NameId, args: &[ExprId]| -> ExprId {
        let c = kernel.const_(name, vec![]);
        let head = apply_all(kernel, c, &[m, s]);
        apply_all(kernel, head, args)
    };

    // m_bot := fun (v : Nat -> M) => False
    let m_bot = {
        let v_id = 1_636_611_u64;
        let false_ = kernel.const_(logic.false_, vec![]);
        lam_fv(kernel, v_id, val_ty, false_)
    };

    // m_eqf := fun (a b : Term) (v) => Eq.{1} M (eval a v) (eval b v)
    let m_eqf = {
        let a_id = 1_636_621_u64;
        let b_id = 1_636_622_u64;
        let v_id = 1_636_623_u64;
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let v = kernel.fvar(v_id);
        let a_v = ev(kernel, a, v);
        let b_v = ev(kernel, b, v);
        let eq = kernel.const_(logic.eq, vec![one]);
        let body = apply_all(kernel, eq, &[m, a_v, b_v]);
        lams(
            kernel,
            &[(a_id, syn.term_ty), (b_id, syn.term_ty), (v_id, val_ty)],
            body,
        )
    };

    // m_rel1 := fun (k : Nat) (t : Term) (v) => S.rel1 k (eval t v)
    let m_rel1 = {
        let k_id = 1_636_631_u64;
        let t_id = 1_636_632_u64;
        let v_id = 1_636_633_u64;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let v = kernel.fvar(v_id);
        let t_v = ev(kernel, t, v);
        let body = proj(kernel, interp.rel1, &[k, t_v]);
        lams(
            kernel,
            &[(k_id, syn.nat_ty), (t_id, syn.term_ty), (v_id, val_ty)],
            body,
        )
    };

    // m_rel2 := fun (k : Nat) (a b : Term) (v) => S.rel2 k (eval a v) (eval b v)
    let m_rel2 = {
        let k_id = 1_636_641_u64;
        let a_id = 1_636_642_u64;
        let b_id = 1_636_643_u64;
        let v_id = 1_636_644_u64;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let v = kernel.fvar(v_id);
        let a_v = ev(kernel, a, v);
        let b_v = ev(kernel, b, v);
        let body = proj(kernel, interp.rel2, &[k, a_v, b_v]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (a_id, syn.term_ty),
                (b_id, syn.term_ty),
                (v_id, val_ty),
            ],
            body,
        )
    };

    // The three binary connectives, each `fun p q ip iq v => OP (ip v) (iq v)`
    // where `OP` is `And`, `Or`, or the kernel's own non-dependent arrow.
    let binary = |kernel: &mut crate::Kernel, ctor: Option<NameId>, base: u64| -> ExprId {
        let p_id = base;
        let q_id = base + 1;
        let ip_id = base + 2;
        let iq_id = base + 3;
        let v_id = base + 4;
        let ip = kernel.fvar(ip_id);
        let iq = kernel.fvar(iq_id);
        let v = kernel.fvar(v_id);
        let ip_v = kernel.app(ip, v);
        let iq_v = kernel.app(iq, v);
        let body = match ctor {
            Some(name) => {
                let c = kernel.const_(name, vec![]);
                apply_all(kernel, c, &[ip_v, iq_v])
            }
            None => arrow(kernel, ip_v, iq_v),
        };
        lams(
            kernel,
            &[
                (p_id, syn.formula_ty),
                (q_id, syn.formula_ty),
                (ip_id, codomain),
                (iq_id, codomain),
                (v_id, val_ty),
            ],
            body,
        )
    };
    let m_and = binary(kernel, Some(logic.and), 1_636_651_u64);
    let m_or = binary(kernel, Some(logic.or), 1_636_661_u64);
    let m_imp = binary(kernel, None, 1_636_671_u64);

    // m_all := fun (p : Formula) (ip : C) (v) => Π (x : M), ip (Val.cons M x v)
    let m_all = {
        let p_id = 1_636_681_u64;
        let ip_id = 1_636_682_u64;
        let v_id = 1_636_683_u64;
        let x_id = 1_636_684_u64;
        let ip = kernel.fvar(ip_id);
        let v = kernel.fvar(v_id);
        let x = kernel.fvar(x_id);
        let cons_const = kernel.const_(interp.val_cons, vec![]);
        let extended = apply_all(kernel, cons_const, &[m, x, v]);
        let applied = kernel.app(ip, extended);
        let quantified = pi_fv(kernel, x_id, m, applied);
        lams(
            kernel,
            &[(p_id, syn.formula_ty), (ip_id, codomain), (v_id, val_ty)],
            quantified,
        )
    };

    // m_ex := fun (p : Formula) (ip : C) (v) => Exists.{1} M (fun x => ip (Val.cons M x v))
    let m_ex = {
        let p_id = 1_636_691_u64;
        let ip_id = 1_636_692_u64;
        let v_id = 1_636_693_u64;
        let x_id = 1_636_694_u64;
        let ip = kernel.fvar(ip_id);
        let v = kernel.fvar(v_id);
        let x = kernel.fvar(x_id);
        let cons_const = kernel.const_(interp.val_cons, vec![]);
        let extended = apply_all(kernel, cons_const, &[m, x, v]);
        let applied = kernel.app(ip, extended);
        let predicate = lam_fv(kernel, x_id, m, applied);
        let exists_const = kernel.const_(logic.exists_, vec![one]);
        let quantified = apply_all(kernel, exists_const, &[m, predicate]);
        lams(
            kernel,
            &[(p_id, syn.formula_ty), (ip_id, codomain), (v_id, val_ty)],
            quantified,
        )
    };

    let rec_const = kernel.const_(syn.formula_rec, vec![one]);
    let applied = apply_all(
        kernel,
        rec_const,
        &[
            motive, m_bot, m_eqf, m_rel1, m_rel2, m_and, m_or, m_imp, m_all, m_ex,
        ],
    );

    let f_id = 1_636_701_u64;
    let f = kernel.fvar(f_id);
    let inner = kernel.app(applied, f);
    let with_formula = lam_fv(kernel, f_id, syn.formula_ty, inner);

    let binders = [(m_id, type_sort), (s_id, struct_m)];
    let value = lams(kernel, &binders, with_formula);
    let cod = arrow(kernel, syn.formula_ty, codomain);
    let ty = pis(kernel, &binders, cod);

    let name = kernel.name_str(syn.fo, "sat");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.natStructure : FO.Structure Nat`. See the module docs for the symbol
/// table and for why every family is index-dependent.
fn declare_nat_structure(
    kernel: &mut crate::Kernel,
    syntax: &FoSyntaxPrelude,
    sem: &StructureNames,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let nat = syntax.nat;
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let add = |kernel: &mut crate::Kernel, x: ExprId, y: ExprId| -> ExprId {
        let c = kernel.const_(nat.add, vec![]);
        apply_all(kernel, c, &[x, y])
    };
    let lt = |kernel: &mut crate::Kernel, x: ExprId, y: ExprId| -> ExprId {
        let c = kernel.const_(nat.lt, vec![]);
        apply_all(kernel, c, &[x, y])
    };

    // fn0 := fun k => k
    let i_fn0 = {
        let k_id = 1_636_711_u64;
        let k = kernel.fvar(k_id);
        lam_fv(kernel, k_id, nat_ty, k)
    };
    // fn1 := fun k x => Nat.add x k
    let i_fn1 = {
        let k_id = 1_636_721_u64;
        let x_id = 1_636_722_u64;
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let body = add(kernel, x, k);
        lams(kernel, &[(k_id, nat_ty), (x_id, nat_ty)], body)
    };
    // fn2 := fun k x y => Nat.add (Nat.add x y) k
    let i_fn2 = {
        let k_id = 1_636_731_u64;
        let x_id = 1_636_732_u64;
        let y_id = 1_636_733_u64;
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let xy = add(kernel, x, y);
        let body = add(kernel, xy, k);
        lams(
            kernel,
            &[(k_id, nat_ty), (x_id, nat_ty), (y_id, nat_ty)],
            body,
        )
    };
    // rel1 := fun k x => Nat.lt k x
    let i_rel1 = {
        let k_id = 1_636_741_u64;
        let x_id = 1_636_742_u64;
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let body = lt(kernel, k, x);
        lams(kernel, &[(k_id, nat_ty), (x_id, nat_ty)], body)
    };
    // rel2 := fun k x y => Nat.lt (Nat.add x k) y
    let i_rel2 = {
        let k_id = 1_636_751_u64;
        let x_id = 1_636_752_u64;
        let y_id = 1_636_753_u64;
        let k = kernel.fvar(k_id);
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let xk = add(kernel, x, k);
        let body = lt(kernel, xk, y);
        lams(
            kernel,
            &[(k_id, nat_ty), (x_id, nat_ty), (y_id, nat_ty)],
            body,
        )
    };

    let mk = kernel.const_(sem.structure_mk, vec![]);
    let value = apply_all(kernel, mk, &[nat_ty, i_fn0, i_fn1, i_fn2, i_rel1, i_rel2]);

    let structure_const = kernel.const_(sem.structure, vec![]);
    let ty = kernel.app(structure_const, nat_ty);
    let _ = one;

    let anon = kernel.anon();
    let fo = kernel.name_str(anon, "FO");
    let name = kernel.name_str(fo, "natStructure");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Formula` builders for the two sentences below.
struct SentenceBuilder<'a> {
    syn: &'a SyntaxNames,
}

impl SentenceBuilder<'_> {
    fn num(&self, kernel: &mut crate::Kernel, n: u32) -> ExprId {
        let mut e = kernel.const_(self.syn.nat_zero, vec![]);
        let succ = kernel.const_(self.syn.nat_succ, vec![]);
        for _ in 0..n {
            e = kernel.app(succ, e);
        }
        e
    }

    fn var(&self, kernel: &mut crate::Kernel, i: u32) -> ExprId {
        let idx = self.num(kernel, i);
        let c = kernel.const_(self.syn.var, vec![]);
        kernel.app(c, idx)
    }

    fn rel2(&self, kernel: &mut crate::Kernel, k: u32, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.num(kernel, k);
        let c = kernel.const_(self.syn.rel2, vec![]);
        apply_all(kernel, c, &[idx, a, b])
    }

    fn imp(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let c = kernel.const_(self.syn.imp, vec![]);
        apply_all(kernel, c, &[a, b])
    }

    fn bot(&self, kernel: &mut crate::Kernel) -> ExprId {
        kernel.const_(self.syn.bot, vec![])
    }

    fn all(&self, kernel: &mut crate::Kernel, body: ExprId) -> ExprId {
        let c = kernel.const_(self.syn.all, vec![]);
        kernel.app(c, body)
    }

    fn ex(&self, kernel: &mut crate::Kernel, body: ExprId) -> ExprId {
        let c = kernel.const_(self.syn.ex, vec![]);
        kernel.app(c, body)
    }
}

/// `FO.natIrrefl : FO.Formula` — the sentence `∀ x, ¬ (x < x)`, i.e.
/// `all (imp (rel2 0 (var 0) (var 0)) bot)`.
pub(crate) fn nat_irrefl_sentence(kernel: &mut crate::Kernel, syn: &SyntaxNames) -> ExprId {
    let b = SentenceBuilder { syn };
    let x1 = b.var(kernel, 0);
    let x2 = b.var(kernel, 0);
    let atom = b.rel2(kernel, 0, x1, x2);
    let bot = b.bot(kernel);
    let body = b.imp(kernel, atom, bot);
    b.all(kernel, body)
}

/// `FO.natNoGreatest : FO.Formula` — the sentence `∀ x ∃ y, x < y`, i.e.
/// `all (ex (rel2 0 (var 1) (var 0)))`. Under two binders the outer variable
/// is de Bruijn index `1` and the inner one is `0`.
pub(crate) fn nat_no_greatest_sentence(kernel: &mut crate::Kernel, syn: &SyntaxNames) -> ExprId {
    let b = SentenceBuilder { syn };
    let outer = b.var(kernel, 1);
    let inner = b.var(kernel, 0);
    let atom = b.rel2(kernel, 0, outer, inner);
    let body = b.ex(kernel, atom);
    b.all(kernel, body)
}

/// `FO.nat_sat_lt_irrefl : Π (v : Nat -> Nat), FO.sat Nat FO.natStructure
/// (all (imp (rel2 0 (var 0) (var 0)) bot)) v`.
///
/// The stated type reduces, by ι on `FO.Formula.rec` and `FO.Term.rec` and by
/// ι on `Nat.add x Nat.zero`, to `Π v x, Nat.lt x x -> False` — which is
/// `Nat.lt_irrefl` applied pointwise. The proof term is
/// `fun v x h => Nat.lt_irrefl x h`; the kernel does the unfolding.
fn declare_nat_sat_lt_irrefl(
    kernel: &mut crate::Kernel,
    syntax: &FoSyntaxPrelude,
    syn: &SyntaxNames,
    sat: NameId,
    nat_structure: NameId,
) -> Result<NameId, KernelError> {
    let nat = syntax.nat;
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let val_ty = arrow(kernel, nat_ty, nat_ty);
    let sentence = nat_irrefl_sentence(kernel, syn);
    let structure = kernel.const_(nat_structure, vec![]);

    let v_id = 1_636_761_u64;
    let x_id = 1_636_762_u64;
    let h_id = 1_636_763_u64;
    let v = kernel.fvar(v_id);
    let x = kernel.fvar(x_id);
    let h = kernel.fvar(h_id);

    let sat_const = kernel.const_(sat, vec![]);
    let body = apply_all(kernel, sat_const, &[nat_ty, structure, sentence, v]);
    let ty = pi_fv(kernel, v_id, val_ty, body);

    // The hypothesis binder's type must be written in the SAME reduced form
    // the goal presents, so the kernel's defeq check has something to compare
    // against: `Nat.lt (Nat.add x 0) x`.
    let zero = kernel.const_(nat.zero, vec![]);
    let x_plus_zero = {
        let c = kernel.const_(nat.add, vec![]);
        apply_all(kernel, c, &[x, zero])
    };
    let hyp_ty = {
        let c = kernel.const_(nat.lt, vec![]);
        apply_all(kernel, c, &[x_plus_zero, x])
    };

    let irrefl = kernel.const_(nat.lt_irrefl, vec![]);
    let contradiction = apply_all(kernel, irrefl, &[x, h]);
    let value = {
        let inner = lam_fv(kernel, h_id, hyp_ty, contradiction);
        let inner = lam_fv(kernel, x_id, nat_ty, inner);
        lam_fv(kernel, v_id, val_ty, inner)
    };

    let name = kernel.name_str(syn.fo, "nat_sat_lt_irrefl");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.nat_sat_no_greatest : Π (v : Nat -> Nat), FO.sat Nat FO.natStructure
/// (all (ex (rel2 0 (var 1) (var 0)))) v`.
///
/// The stated type reduces to `Π v x, Exists Nat (fun y => Nat.lt (Nat.add x 0) y)`,
/// i.e. `∀ x ∃ y, x < y`, **provided** the `ex` clause of `FO.sat` extends the
/// valuation with the existential witness on top of the one the `all` clause
/// already extended. The witness is `Nat.succ x`, and
/// `Nat.lt x (Nat.succ x)` δ-unfolds to `Nat.le (Nat.succ x) (Nat.succ x)`,
/// which is `Nat.le_refl (Nat.succ x)`.
fn declare_nat_sat_no_greatest(
    kernel: &mut crate::Kernel,
    syntax: &FoSyntaxPrelude,
    syn: &SyntaxNames,
    sat: NameId,
    nat_structure: NameId,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let nat = syntax.nat;
    let logic = nat.logic;
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let val_ty = arrow(kernel, nat_ty, nat_ty);
    let sentence = nat_no_greatest_sentence(kernel, syn);
    let structure = kernel.const_(nat_structure, vec![]);

    let v_id = 1_636_771_u64;
    let x_id = 1_636_772_u64;
    let y_id = 1_636_773_u64;
    let v = kernel.fvar(v_id);
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);

    let sat_const = kernel.const_(sat, vec![]);
    let body = apply_all(kernel, sat_const, &[nat_ty, structure, sentence, v]);
    let ty = pi_fv(kernel, v_id, val_ty, body);

    // predicate := fun (y : Nat) => Nat.lt (Nat.add x 0) y — written in the
    // reduced form the goal presents.
    let zero = kernel.const_(nat.zero, vec![]);
    let x_plus_zero = {
        let c = kernel.const_(nat.add, vec![]);
        apply_all(kernel, c, &[x, zero])
    };
    let predicate = {
        let c = kernel.const_(nat.lt, vec![]);
        let applied = apply_all(kernel, c, &[x_plus_zero, y]);
        lam_fv(kernel, y_id, nat_ty, applied)
    };

    let succ_x = {
        let c = kernel.const_(nat.succ, vec![]);
        kernel.app(c, x)
    };
    let witness_proof = {
        let c = kernel.const_(nat.le_refl, vec![]);
        kernel.app(c, succ_x)
    };
    let intro = kernel.const_(logic.exists_intro, vec![one]);
    let existential = apply_all(kernel, intro, &[nat_ty, predicate, succ_x, witness_proof]);

    let value = {
        let inner = lam_fv(kernel, x_id, nat_ty, existential);
        lam_fv(kernel, v_id, val_ty, inner)
    };

    let name = kernel.name_str(syn.fo, "nat_sat_no_greatest");
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
