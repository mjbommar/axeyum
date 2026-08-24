//! `Str.isPrefix`, `Str.isSuffix`, `Str.contains` — the SMT-LIB string
//! predicates (`str.prefixof`, `str.suffixof`, `str.contains`, argument order
//! flipped to the mathematical `contains haystack needle` reading) — and the
//! laws tying them to `append` (`monoid.rs`), `take`/`drop`
//! (`take_drop.rs`), `substr` (`substr.rs`), and `reverse` (`reverse.rs`).
//!
//! # Design — `Prop`-valued existentials, not `Bool` predicates
//!
//! ```text
//! isPrefix p s := ∃ t, append p t = s
//! isSuffix s t := ∃ p, append p s = t
//! contains s u := ∃ p t, append (append p u) t = s
//! ```
//!
//! All three are `Str → Str → Prop`, built directly on [`LogicPrelude`]'s
//! `Exists`/`Exists.intro`/`Exists.rec` (already used the same way by
//! `int_prelude::dvd`'s `Int.dvd a b := ∃ c, b = a * c` and
//! `nat_prelude::modular`) — **not** a recursive `Bool`-valued decision
//! procedure. Two reasons, and they compound:
//!
//! - `Exists` is `Prop`-valued and (per this kernel's elimination rule, the
//!   same one `int_prelude::dvd::declare_dvd_trans` already relies on)
//!   eliminates into another `Prop`, never into `Str`/`Bool`/`Sort 1`. Every
//!   law below is a `Prop` **implication** or an existence claim, so nothing
//!   here ever needs to *compute* a witness at kernel ι-reduction time —
//!   `isPrefix_take`'s witness (`drop n s`) is supplied by the *proof*, not
//!   extracted from the proposition afterward. A `Type`-valued (`Str`-valued)
//!   alternative would need large elimination out of the predicate, which
//!   this development does not have and does not need.
//! - A `Bool`-valued `isPrefix : Str → Str → Bool` would need **decidable**
//!   `Char` equality to compare corresponding positions, and per
//!   `string_prelude.rs`'s own module doc, `Char` may have **zero**
//!   constructors (`num_chars == 0`, exercised by
//!   `tests::empty_alphabet_admits`). `char_eq_fn`/`char_lt_fn`
//!   (`string_prelude.rs`) already build such truth tables for the
//!   lexicographic comparator `lex_cmp_fn`, so a Boolean decision procedure
//!   *is* buildable the same way if a future reconstruction route needs one —
//!   but it is a separate design question (what to do with the truth table on
//!   an empty alphabet is not "false", it is "there is no `Char` to
//!   distinguish", a different failure mode than an ordinary `Bool.false`) and
//!   nothing below needs it: every law here is a `Prop` fact a reconstruction
//!   cites, not a value it evaluates.
//!
//! # Placement — base prelude, not opt-in
//!
//! Every proof here is built from **already-proved** free-monoid facts
//! (`nil_append`, `append_nil`, `append_assoc`, `take_append_drop`,
//! `reverse_append`, `reverse_reverse`) chained by `Eq.rec`-derived
//! congruence/symmetry/transitivity, plus `Exists.intro`/`Exists.rec` from
//! [`LogicPrelude`] — **no new `Str.rec`/`Nat.rec` induction is done in this
//! module**, and (unlike `length_append.rs`/`substr_arithmetic.rs`) nothing
//! here needs `nat_prelude`'s `Nat.add`/`Nat.sub`/`Nat.min` arithmetic, only
//! the bare `Nat` count type already in [`LogicPrelude`]. So these
//! declarations belong in [`super::build_string_prelude`] itself, not the
//! opt-in composition step — the same "no extra prelude needed" test
//! `take_drop.rs`/`substr.rs` already satisfy.
//!
//! # `Iff` — not used here
//!
//! [`LogicPrelude`] carries `Iff`/`Iff.intro`/`Iff.mp`/`Iff.mpr`, but as of
//! 2026-08-17 no `string_prelude` module cites them (confirmed by inspection:
//! the only occurrences of the string "iff" anywhere under `string_prelude/`
//! are inside English doc comments, e.g. `char_eq_fn`'s "ι-reduces to
//! `Bool.true` iff `i == j`"). `isSuffix_reverse`
//! (`isSuffix s t ↔ isPrefix (reverse s) (reverse t)`) is therefore stated as
//! two named implications, `isSuffix_reverse_mp` and `isSuffix_reverse_mpr`
//! (mirroring the `Iff.mp`/`Iff.mpr` naming [`LogicPrelude`] itself uses),
//! rather than a single `Iff`-valued theorem.
//!
//! # What is proved
//!
//! | law                     | statement                                                        | route |
//! |--------------------------|-------------------------------------------------------------------|-------|
//! | `isPrefix_nil`           | `∀ s, isPrefix nil s`                                              | witness `s`, `nil_append` |
//! | `isPrefix_refl`          | `∀ s, isPrefix s s`                                                | witness `nil`, `append_nil` |
//! | `isPrefix_append`        | `∀ p t, isPrefix p (append p t)`                                   | witness `t`, `Eq.refl` |
//! | `isPrefix_trans`         | `∀ p s u, isPrefix p s → isPrefix s u → isPrefix p u`              | witness composition, `append_assoc` |
//! | `isPrefix_take`          | `∀ n s, isPrefix (take n s) s`                                     | witness `drop n s`, `take_append_drop` |
//! | `isSuffix_nil`           | `∀ s, isSuffix nil s`                                              | witness `s`, `append_nil` |
//! | `isSuffix_refl`          | `∀ s, isSuffix s s`                                                | witness `nil`, `nil_append` |
//! | `isSuffix_drop`          | `∀ n s, isSuffix (drop n s) s`                                     | witness `take n s`, `take_append_drop` |
//! | `isSuffix_reverse_mp`    | `∀ s t, isSuffix s t → isPrefix (reverse s) (reverse t)`           | `reverse_append`, congruence on `reverse` |
//! | `isSuffix_reverse_mpr`   | `∀ s t, isPrefix (reverse s) (reverse t) → isSuffix s t`           | `reverse_append`, `reverse_reverse` |
//! | `contains_nil`           | `∀ s, contains s nil`                                              | witnesses `s`, `nil`, `append_nil` twice |
//! | `contains_refl`          | `∀ s, contains s s`                                                | witnesses `nil`, `nil`, `nil_append`/`append_nil` |
//! | `contains_of_isPrefix`   | `∀ p s, isPrefix p s → contains s p`                               | witnesses `nil`, the prefix witness |
//! | `contains_of_isSuffix`   | `∀ p s, isSuffix p s → contains s p`                               | witnesses the suffix witness, `nil` |
//! | `contains_substr`        | `∀ n m s, contains s (substr n m s)`                               | witnesses `take n s`, `drop m (drop n s)`, two `take_append_drop` applications, `append_assoc` |
//!
//! `isPrefix_trans`'s witness composition: from `append p t1 = s` and
//! `append s t2 = u`, `append p (append t1 t2) = u` via `append_assoc` and
//! substituting `s` for `append p t1`; the new witness is `append t1 t2`.
//! `contains_substr`'s witnesses come from applying `take_append_drop` at
//! `(n, s)` **and** at `(m, drop n s)`: the second application is exactly
//! `substr n m s`'s own splitting law, re-associated by `append_assoc` to land
//! on the first.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_predicates_and_laws`] declares into, plus the
/// already-admitted `Str`/`append`/`take`/`drop`/`substr`/`reverse` handles
/// its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct PredicateNames {
    pub logic: LogicPrelude,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub append: NameId,
    pub nil_append: NameId,
    pub append_nil: NameId,
    pub append_assoc: NameId,
    pub take: NameId,
    pub drop: NameId,
    pub take_append_drop: NameId,
    pub substr: NameId,
    pub reverse: NameId,
    pub reverse_append: NameId,
    pub reverse_reverse: NameId,
    pub is_prefix: NameId,
    pub is_prefix_nil: NameId,
    pub is_prefix_refl: NameId,
    pub is_prefix_append: NameId,
    pub is_prefix_trans: NameId,
    pub is_prefix_take: NameId,
    pub is_suffix: NameId,
    pub is_suffix_nil: NameId,
    pub is_suffix_refl: NameId,
    pub is_suffix_drop: NameId,
    pub is_suffix_reverse_mp: NameId,
    pub is_suffix_reverse_mpr: NameId,
    pub contains: NameId,
    pub contains_nil: NameId,
    pub contains_refl: NameId,
    pub contains_of_is_prefix: NameId,
    pub contains_of_is_suffix: NameId,
    pub contains_substr: NameId,
}

/// Declare `isPrefix`/`isSuffix`/`contains` as checked `Exists`-valued
/// definitions and prove their laws, in dependency order.
#[allow(clippy::too_many_lines)] // straight-line declaration sequence; see monoid.rs's same allow.
pub(super) fn declare_predicates_and_laws(
    kernel: &mut Kernel,
    // By reference: `PredicateNames` embeds `LogicPrelude` and so exceeds
    // clippy's 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`TakeDropNames`/`SubstrNames` already hit.
    names: &PredicateNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_is_prefix()?;
    dev.prove_is_prefix_nil()?;
    dev.prove_is_prefix_refl()?;
    dev.prove_is_prefix_append()?;
    dev.prove_is_prefix_trans()?;
    dev.prove_is_prefix_take()?;
    dev.define_is_suffix()?;
    dev.prove_is_suffix_nil()?;
    dev.prove_is_suffix_refl()?;
    dev.prove_is_suffix_drop()?;
    dev.prove_is_suffix_reverse_mp()?;
    dev.prove_is_suffix_reverse_mpr()?;
    dev.define_contains()?;
    dev.prove_contains_nil()?;
    dev.prove_contains_refl()?;
    dev.prove_contains_of_is_prefix()?;
    dev.prove_contains_of_is_suffix()?;
    dev.prove_contains_substr()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 10_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: PredicateNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &PredicateNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let nat_ty = k.const_(n.logic.nat, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            nat_ty,
            next_fvar: FVAR_BASE,
        }
    }

    // --- small builders -----------------------------------------------------

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn fvar(&mut self) -> (u64, ExprId) {
        let id = self.fresh();
        let e = self.k.fvar(id);
        (id, e)
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.k.app(e, a);
        }
        e
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.lam(self.anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.pi(self.anon, ty, b, BinderInfo::Default)
    }

    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        self.k.pi(self.anon, dom, cod, BinderInfo::Default)
    }

    fn nil(&mut self) -> ExprId {
        self.k.const_(self.n.str_nil, vec![])
    }

    /// `append a b` — the already-declared constant applied, not inlined.
    fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.append, vec![]);
        self.apply(f, &[a, b])
    }

    /// `take n s` — the already-declared constant applied, not inlined.
    fn take_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.take, vec![]);
        self.apply(f, &[count, s])
    }

    /// `drop n s` — the already-declared constant applied, not inlined.
    fn drop_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.drop, vec![]);
        self.apply(f, &[count, s])
    }

    /// `substr n m s` — the already-declared constant applied, not inlined.
    fn substr_of(&mut self, n_: ExprId, m: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.substr, vec![]);
        self.apply(f, &[n_, m, s])
    }

    /// `reverse a` — the already-declared constant applied, not inlined.
    fn reverse_of(&mut self, a: ExprId) -> ExprId {
        let f = self.k.const_(self.n.reverse, vec![]);
        self.k.app(f, a)
    }

    /// `Eq.{1} Str x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(eq, &[str_ty, x, y])
    }

    /// `Eq.refl.{1} Str x : Eq Str x x`.
    fn refl(&mut self, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(refl, &[str_ty, x])
    }

    /// `Eq.symm`-style transport: from `proof : Eq Str a b` build
    /// `Eq Str b a`. Mirrors `reverse::Dev::eq_symm`.
    fn eq_symm(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let motive = {
            let (x_fv, x) = self.fvar();
            let eq_x_a = self.eq(x, a);
            let eq_a_x = self.eq(a, x);
            let inner = self.k.lam(self.anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(x_fv, str_ty, inner)
        };
        let base = self.refl(a);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, a, motive, base, b, proof])
    }

    /// `Eq.trans`-style transport: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`. Mirrors `reverse::Dev::eq_trans`.
    fn eq_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq(a, z);
            let eq_b_z = self.eq(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, b, motive, h1, c, h2])
    }

    /// Congruence in the one-hole context `append · c` (the tail `c` fixed,
    /// the head argument varying): from `proof : Eq Str x y` build
    /// `Eq Str (append x c) (append y c)`. Mirrors `reverse::Dev::congr_append_left`.
    fn congr_append_left(&mut self, x: ExprId, y: ExprId, c: ExprId, proof: ExprId) -> ExprId {
        let ax = self.append(x, c);
        let motive = {
            let (z_fv, z) = self.fvar();
            let az = self.append(z, c);
            let conclusion = self.eq(ax, az);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(ax);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// Congruence in the one-hole context `append a ·` (the head `a` fixed,
    /// the tail argument varying): from `proof : Eq Str x y` build
    /// `Eq Str (append a x) (append a y)`.
    fn congr_append_right(&mut self, a: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let ax = self.append(a, x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let az = self.append(a, z);
            let conclusion = self.eq(ax, az);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(ax);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// Congruence under `reverse`: from `proof : Eq Str x y` build
    /// `Eq Str (reverse x) (reverse y)`.
    fn reverse_congr(&mut self, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let rx = self.reverse_of(x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let rz = self.reverse_of(z);
            let conclusion = self.eq(rx, rz);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(rx);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    // --- `Exists` builders ----------------------------------------------------

    /// `Exists.{1} Str pred`.
    fn exists_str(&mut self, pred: ExprId) -> ExprId {
        let ex = self.k.const_(self.n.logic.exists_, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(ex, &[str_ty, pred])
    }

    /// `Exists.intro.{1} Str pred witness proof : Exists Str pred`.
    fn exists_intro_str(&mut self, pred: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
        let intro = self.k.const_(self.n.logic.exists_intro, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(intro, &[str_ty, pred, witness, proof])
    }

    /// `Exists.rec.{1} Str pred motive minor major`, with the **non-dependent**
    /// motive `λ _ : Exists Str pred, result` — i.e. `Exists.elim` specialized
    /// to `Str`. `minor` receives the witness and the predicate proof (both
    /// fresh `FVar`s) and must return a proof of `result`.
    fn exists_elim_str(
        &mut self,
        pred: ExprId,
        result: ExprId,
        minor: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        major: ExprId,
    ) -> ExprId {
        let str_ty = self.str_ty;
        let ex_ty = self.exists_str(pred);
        let motive = self.k.lam(self.anon, ex_ty, result, BinderInfo::Default);
        let minor_term = {
            let (w_fv, w) = self.fvar();
            let pred_w = self.k.app(pred, w);
            let (h_fv, h) = self.fvar();
            let body = minor(self, w, h);
            let inner = self.lam_fv(h_fv, pred_w, body);
            self.lam_fv(w_fv, str_ty, inner)
        };
        let rec = self.k.const_(self.n.logic.exists_rec, vec![self.one]);
        self.apply(rec, &[str_ty, pred, motive, minor_term, major])
    }

    fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    }

    // --- isPrefix ---------------------------------------------------------

    /// `λ (t : Str), Eq Str (append p t) s` — the predicate `isPrefix p s`
    /// existentially quantifies.
    fn is_prefix_pred(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let (t_fv, t) = self.fvar();
        let apt = self.append(p, t);
        let body = self.eq(apt, s);
        let str_ty = self.str_ty;
        self.lam_fv(t_fv, str_ty, body)
    }

    /// `isPrefix p s` — the declared constant applied, not inlined.
    fn is_prefix_of(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_prefix, vec![]);
        self.apply(f, &[p, s])
    }

    /// `isPrefix : Str → Str → Prop := λ p s, ∃ t, append p t = s`.
    fn define_is_prefix(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let pred = self.is_prefix_pred(p, s);
        let body = self.exists_str(pred);
        let value = {
            let inner = self.lam_fv(s_fv, str_ty, body);
            self.lam_fv(p_fv, str_ty, inner)
        };
        let prop = self.k.sort_zero();
        let ty = {
            let inner = self.arrow(str_ty, prop);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.is_prefix,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `isPrefix_nil : ∀ (s : Str), isPrefix nil s` — witness `s`, via
    /// `nil_append`.
    fn prove_is_prefix_nil(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let nil = self.nil();
        let pred = self.is_prefix_pred(nil, s);
        let witness_proof = {
            let lemma = self.k.const_(self.n.nil_append, vec![]);
            self.k.app(lemma, s)
        };
        let proof = self.exists_intro_str(pred, s, witness_proof);
        let stmt = self.is_prefix_of(nil, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.is_prefix_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `isPrefix_refl : ∀ (s : Str), isPrefix s s` — witness `nil`, via
    /// `append_nil`.
    fn prove_is_prefix_refl(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let pred = self.is_prefix_pred(s, s);
        let nil = self.nil();
        let witness_proof = {
            let lemma = self.k.const_(self.n.append_nil, vec![]);
            self.k.app(lemma, s)
        };
        let proof = self.exists_intro_str(pred, nil, witness_proof);
        let stmt = self.is_prefix_of(s, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.is_prefix_refl;
        self.declare_theorem(name, ty, value)
    }

    /// `isPrefix_append : ∀ (p t : Str), isPrefix p (append p t)` — witness
    /// `t`, via `Eq.refl`.
    fn prove_is_prefix_append(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let (t_fv, t) = self.fvar();
        let apt = self.append(p, t);
        let pred = self.is_prefix_pred(p, apt);
        let witness_proof = self.refl(apt);
        let proof = self.exists_intro_str(pred, t, witness_proof);
        let stmt = self.is_prefix_of(p, apt);
        let str_ty = self.str_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(p_fv, str_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(p_fv, str_ty, over_t)
        };
        let name = self.n.is_prefix_append;
        self.declare_theorem(name, ty, value)
    }

    /// `isPrefix_trans : ∀ (p s u : Str), isPrefix p s → isPrefix s u → isPrefix p u`.
    ///
    /// From `h1 : append p t1 = s` and `h2 : append s t2 = u`,
    /// `append p (append t1 t2) = u` via `append_assoc` and rewriting
    /// `append p t1` to `s` through `h1`; the new witness is `append t1 t2`.
    fn prove_is_prefix_trans(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let (u_fv, u) = self.fvar();
        let hab_ty = self.is_prefix_of(p, s);
        let hbc_ty = self.is_prefix_of(s, u);
        let target = self.is_prefix_of(p, u);
        let str_ty = self.str_ty;

        let (hab_fv, hab) = self.fvar();
        let (hbc_fv, hbc) = self.fvar();

        let pred_ps = self.is_prefix_pred(p, s);

        let body = self.exists_elim_str(
            pred_ps,
            target,
            &|d, t1, h1| {
                let pred_su = d.is_prefix_pred(s, u);
                d.exists_elim_str(
                    pred_su,
                    target,
                    &|d, t2, h2| {
                        let ap_t1 = d.append(p, t1);
                        let t1_t2 = d.append(t1, t2);
                        let p_app = d.append(p, t1_t2);
                        let ap_t1_t2 = d.append(ap_t1, t2);
                        let assoc = {
                            let lemma = d.k.const_(d.n.append_assoc, vec![]);
                            let e = d.k.app(lemma, p);
                            let e = d.k.app(e, t1);
                            d.k.app(e, t2)
                        }; // Eq Str (append (append p t1) t2) (append p (append t1 t2))
                        let assoc_symm = d.eq_symm(ap_t1_t2, p_app, assoc);
                        let s_t2 = d.append(s, t2);
                        let step_congr = d.congr_append_left(ap_t1, s, t2, h1);
                        let chain1 = d.eq_trans(p_app, ap_t1_t2, s_t2, assoc_symm, step_congr);
                        let chain2 = d.eq_trans(p_app, s_t2, u, chain1, h2);
                        let pred_pu = d.is_prefix_pred(p, u);
                        d.exists_intro_str(pred_pu, t1_t2, chain2)
                    },
                    hbc,
                )
            },
            hab,
        );

        let value = {
            let with_hbc = self.lam_fv(hbc_fv, hbc_ty, body);
            let with_hab = self.lam_fv(hab_fv, hab_ty, with_hbc);
            let with_u = self.lam_fv(u_fv, str_ty, with_hab);
            let with_s = self.lam_fv(s_fv, str_ty, with_u);
            self.lam_fv(p_fv, str_ty, with_s)
        };
        let ty = {
            let inner = self.arrow(hbc_ty, target);
            let with_hyps = self.arrow(hab_ty, inner);
            let with_u = self.pi_fv(u_fv, str_ty, with_hyps);
            let with_s = self.pi_fv(s_fv, str_ty, with_u);
            self.pi_fv(p_fv, str_ty, with_s)
        };
        let name = self.n.is_prefix_trans;
        self.declare_theorem(name, ty, value)
    }

    /// `isPrefix_take : ∀ (n : Nat) (s : Str), isPrefix (take n s) s` — witness
    /// `drop n s`, exactly `take_append_drop`. The bridge from the existential
    /// predicate to the computable `take`/`drop`.
    fn prove_is_prefix_take(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let (s_fv, s) = self.fvar();
        let tk = self.take_of(n, s);
        let dr = self.drop_of(n, s);
        let pred = self.is_prefix_pred(tk, s);
        let witness_proof = {
            let lemma = self.k.const_(self.n.take_append_drop, vec![]);
            let e = self.k.app(lemma, n);
            self.k.app(e, s)
        };
        let proof = self.exists_intro_str(pred, dr, witness_proof);
        let stmt = self.is_prefix_of(tk, s);
        let str_ty = self.str_ty;
        let nat_ty = self.nat_ty;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(n_fv, nat_ty, over_s)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(n_fv, nat_ty, over_s)
        };
        let name = self.n.is_prefix_take;
        self.declare_theorem(name, ty, value)
    }

    // --- isSuffix -----------------------------------------------------------

    /// `λ (p : Str), Eq Str (append p s) t` — the predicate `isSuffix s t`
    /// existentially quantifies.
    fn is_suffix_pred(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let (p_fv, p) = self.fvar();
        let aps = self.append(p, s);
        let body = self.eq(aps, t);
        let str_ty = self.str_ty;
        self.lam_fv(p_fv, str_ty, body)
    }

    /// `isSuffix s t` — the declared constant applied, not inlined.
    fn is_suffix_of(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_suffix, vec![]);
        self.apply(f, &[s, t])
    }

    /// `isSuffix : Str → Str → Prop := λ s t, ∃ p, append p s = t`.
    fn define_is_suffix(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let pred = self.is_suffix_pred(s, t);
        let body = self.exists_str(pred);
        let value = {
            let inner = self.lam_fv(t_fv, str_ty, body);
            self.lam_fv(s_fv, str_ty, inner)
        };
        let prop = self.k.sort_zero();
        let ty = {
            let inner = self.arrow(str_ty, prop);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.is_suffix,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `isSuffix_nil : ∀ (s : Str), isSuffix nil s` — witness `s`, via
    /// `append_nil`.
    fn prove_is_suffix_nil(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let nil = self.nil();
        let pred = self.is_suffix_pred(nil, s);
        let witness_proof = {
            let lemma = self.k.const_(self.n.append_nil, vec![]);
            self.k.app(lemma, s)
        };
        let proof = self.exists_intro_str(pred, s, witness_proof);
        let stmt = self.is_suffix_of(nil, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.is_suffix_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `isSuffix_refl : ∀ (s : Str), isSuffix s s` — witness `nil`, via
    /// `nil_append`.
    fn prove_is_suffix_refl(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let pred = self.is_suffix_pred(s, s);
        let nil = self.nil();
        let witness_proof = {
            let lemma = self.k.const_(self.n.nil_append, vec![]);
            self.k.app(lemma, s)
        };
        let proof = self.exists_intro_str(pred, nil, witness_proof);
        let stmt = self.is_suffix_of(s, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.is_suffix_refl;
        self.declare_theorem(name, ty, value)
    }

    /// `isSuffix_drop : ∀ (n : Nat) (s : Str), isSuffix (drop n s) s` —
    /// witness `take n s`, exactly `take_append_drop`.
    fn prove_is_suffix_drop(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let (s_fv, s) = self.fvar();
        let dr = self.drop_of(n, s);
        let tk = self.take_of(n, s);
        let pred = self.is_suffix_pred(dr, s);
        let witness_proof = {
            let lemma = self.k.const_(self.n.take_append_drop, vec![]);
            let e = self.k.app(lemma, n);
            self.k.app(e, s)
        };
        let proof = self.exists_intro_str(pred, tk, witness_proof);
        let stmt = self.is_suffix_of(dr, s);
        let str_ty = self.str_ty;
        let nat_ty = self.nat_ty;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(n_fv, nat_ty, over_s)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(n_fv, nat_ty, over_s)
        };
        let name = self.n.is_suffix_drop;
        self.declare_theorem(name, ty, value)
    }

    /// `isSuffix_reverse_mp : ∀ (s t : Str),
    ///     isSuffix s t → isPrefix (reverse s) (reverse t)`.
    ///
    /// From `h : append p s = t`: `reverse (append p s) = reverse t`, and
    /// `reverse_append p s : reverse (append p s) = append (reverse s) (reverse p)`,
    /// so `append (reverse s) (reverse p) = reverse t`. Witness `reverse p`.
    fn prove_is_suffix_reverse_mp(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let hyp_ty = self.is_suffix_of(s, t);
        let rs = self.reverse_of(s);
        let rt = self.reverse_of(t);
        let target = self.is_prefix_of(rs, rt);
        let str_ty = self.str_ty;

        let (h_fv, h) = self.fvar();
        let pred_st = self.is_suffix_pred(s, t);

        let body = self.exists_elim_str(
            pred_st,
            target,
            &|d, p, hp| {
                let aps = d.append(p, s);
                let step1 = d.reverse_congr(aps, t, hp); // Eq Str (reverse (append p s)) (reverse t)
                let rp = d.reverse_of(p);
                let rs_rp = d.append(rs, rp);
                let raps = d.reverse_of(aps);
                let step2 = {
                    let lemma = d.k.const_(d.n.reverse_append, vec![]);
                    let e = d.k.app(lemma, p);
                    d.k.app(e, s)
                }; // Eq Str (reverse (append p s)) (append (reverse s) (reverse p))
                let step2_symm = d.eq_symm(raps, rs_rp, step2);
                let chain = d.eq_trans(rs_rp, raps, rt, step2_symm, step1);
                let pred_pu = d.is_prefix_pred(rs, rt);
                d.exists_intro_str(pred_pu, rp, chain)
            },
            h,
        );

        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_h);
            self.lam_fv(s_fv, str_ty, with_t)
        };
        let ty = {
            let with_hyp = self.arrow(hyp_ty, target);
            let with_t = self.pi_fv(t_fv, str_ty, with_hyp);
            self.pi_fv(s_fv, str_ty, with_t)
        };
        let name = self.n.is_suffix_reverse_mp;
        self.declare_theorem(name, ty, value)
    }

    /// `isSuffix_reverse_mpr : ∀ (s t : Str),
    ///     isPrefix (reverse s) (reverse t) → isSuffix s t`.
    ///
    /// From `h : append (reverse s) t' = reverse t`: reverse both sides,
    /// `reverse_append (reverse s) t'` gives
    /// `append (reverse t') (reverse (reverse s)) = reverse (reverse t)`, and
    /// `reverse_reverse` rewrites both `reverse (reverse s)` (to `s`) and
    /// `reverse (reverse t)` (to `t`). Witness `reverse t'`.
    fn prove_is_suffix_reverse_mpr(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let rs = self.reverse_of(s);
        let rt = self.reverse_of(t);
        let hyp_ty = self.is_prefix_of(rs, rt);
        let target = self.is_suffix_of(s, t);
        let str_ty = self.str_ty;

        let (h_fv, h) = self.fvar();
        let pred_rs_rt = self.is_prefix_pred(rs, rt);

        let body = self.exists_elim_str(
            pred_rs_rt,
            target,
            &|d, tp, hpp| {
                // hpp : Eq Str (append (reverse s) tp) (reverse t)
                let rs_tp = d.append(rs, tp);
                let rrt = d.reverse_of(rt);
                let step1 = d.reverse_congr(rs_tp, rt, hpp); // Eq Str (reverse (append rs tp)) (reverse (reverse t))
                let rtp = d.reverse_of(tp);
                let rrs = d.reverse_of(rs);
                let rtp_rrs = d.append(rtp, rrs);
                let r_rs_tp = d.reverse_of(rs_tp);
                let step2 = {
                    let lemma = d.k.const_(d.n.reverse_append, vec![]);
                    let e = d.k.app(lemma, rs);
                    d.k.app(e, tp)
                }; // Eq Str (reverse (append rs tp)) (append (reverse tp) (reverse rs))
                let step2_symm = d.eq_symm(r_rs_tp, rtp_rrs, step2);
                let chain_a = d.eq_trans(rtp_rrs, r_rs_tp, rrt, step2_symm, step1);
                let step3 = {
                    let lemma = d.k.const_(d.n.reverse_reverse, vec![]);
                    d.k.app(lemma, t)
                }; // Eq Str (reverse (reverse t)) t
                let chain_b = d.eq_trans(rtp_rrs, rrt, t, chain_a, step3);
                let step4 = {
                    let lemma = d.k.const_(d.n.reverse_reverse, vec![]);
                    d.k.app(lemma, s)
                }; // Eq Str (reverse (reverse s)) s
                let rtp_s = d.append(rtp, s);
                let congr_r = d.congr_append_right(rtp, rrs, s, step4); // Eq Str (append rtp rrs) (append rtp s)
                let congr_r_symm = d.eq_symm(rtp_rrs, rtp_s, congr_r);
                let chain_c = d.eq_trans(rtp_s, rtp_rrs, t, congr_r_symm, chain_b);
                let pred_st = d.is_suffix_pred(s, t);
                d.exists_intro_str(pred_st, rtp, chain_c)
            },
            h,
        );

        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_h);
            self.lam_fv(s_fv, str_ty, with_t)
        };
        let ty = {
            let with_hyp = self.arrow(hyp_ty, target);
            let with_t = self.pi_fv(t_fv, str_ty, with_hyp);
            self.pi_fv(s_fv, str_ty, with_t)
        };
        let name = self.n.is_suffix_reverse_mpr;
        self.declare_theorem(name, ty, value)
    }

    // --- contains -------------------------------------------------------------

    /// `λ (t : Str), Eq Str (append (append p u) t) s` — the INNER predicate
    /// `contains s u` existentially quantifies (over `t`, for a fixed outer
    /// witness `p`).
    fn contains_inner_pred(&mut self, p: ExprId, u: ExprId, s: ExprId) -> ExprId {
        let (t_fv, t) = self.fvar();
        let pu = self.append(p, u);
        let put = self.append(pu, t);
        let body = self.eq(put, s);
        let str_ty = self.str_ty;
        self.lam_fv(t_fv, str_ty, body)
    }

    /// `λ (p : Str), Exists Str (contains_inner_pred p u s)` — the OUTER
    /// predicate `contains s u` existentially quantifies.
    fn contains_outer_pred(&mut self, s: ExprId, u: ExprId) -> ExprId {
        let (p_fv, p) = self.fvar();
        let inner_pred = self.contains_inner_pred(p, u, s);
        let body = self.exists_str(inner_pred);
        let str_ty = self.str_ty;
        self.lam_fv(p_fv, str_ty, body)
    }

    /// `contains s u` — the declared constant applied, not inlined.
    fn contains_of(&mut self, s: ExprId, u: ExprId) -> ExprId {
        let f = self.k.const_(self.n.contains, vec![]);
        self.apply(f, &[s, u])
    }

    /// Build a full `contains s u` witness from an explicit outer witness
    /// `p0`, inner witness `t0`, and a proof `e0 : append (append p0 u) t0 = s`.
    fn contains_witness(
        &mut self,
        s: ExprId,
        u: ExprId,
        p0: ExprId,
        t0: ExprId,
        e0: ExprId,
    ) -> ExprId {
        let inner_pred = self.contains_inner_pred(p0, u, s);
        let inner_exists = self.exists_intro_str(inner_pred, t0, e0);
        let outer_pred = self.contains_outer_pred(s, u);
        self.exists_intro_str(outer_pred, p0, inner_exists)
    }

    /// `contains : Str → Str → Prop := λ s u, ∃ p t, append (append p u) t = s`.
    fn define_contains(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (u_fv, u) = self.fvar();
        let outer_pred = self.contains_outer_pred(s, u);
        let body = self.exists_str(outer_pred);
        let value = {
            let inner = self.lam_fv(u_fv, str_ty, body);
            self.lam_fv(s_fv, str_ty, inner)
        };
        let prop = self.k.sort_zero();
        let ty = {
            let inner = self.arrow(str_ty, prop);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.contains,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `contains_nil : ∀ (s : Str), contains s nil` — witnesses `s`, `nil`,
    /// via `append_nil` twice.
    fn prove_contains_nil(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let nil = self.nil();
        let step1 = {
            let lemma = self.k.const_(self.n.append_nil, vec![]);
            self.k.app(lemma, s)
        }; // Eq Str (append s nil) s
        let as_nil = self.append(s, nil);
        let congrl = self.congr_append_left(as_nil, s, nil, step1); // Eq Str (append (append s nil) nil) (append s nil)
        let as_nil_nil = self.append(as_nil, nil);
        let e0 = self.eq_trans(as_nil_nil, as_nil, s, congrl, step1);
        let proof = self.contains_witness(s, nil, s, nil, e0);
        let stmt = self.contains_of(s, nil);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.contains_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `contains_refl : ∀ (s : Str), contains s s` — witnesses `nil`, `nil`,
    /// via `nil_append` then `append_nil`.
    fn prove_contains_refl(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let nil = self.nil();
        let step1 = {
            let lemma = self.k.const_(self.n.nil_append, vec![]);
            self.k.app(lemma, s)
        }; // Eq Str (append nil s) s
        let an_s = self.append(nil, s);
        let congrl = self.congr_append_left(an_s, s, nil, step1); // Eq Str (append (append nil s) nil) (append s nil)
        let step2 = {
            let lemma = self.k.const_(self.n.append_nil, vec![]);
            self.k.app(lemma, s)
        }; // Eq Str (append s nil) s
        let an_s_nil = self.append(an_s, nil);
        let s_nil = self.append(s, nil);
        let e0 = self.eq_trans(an_s_nil, s_nil, s, congrl, step2);
        let proof = self.contains_witness(s, s, nil, nil, e0);
        let stmt = self.contains_of(s, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.contains_refl;
        self.declare_theorem(name, ty, value)
    }

    /// `contains_of_isPrefix : ∀ (p s : Str), isPrefix p s → contains s p` —
    /// witness `nil` outer, the prefix witness inner, via `nil_append`.
    fn prove_contains_of_is_prefix(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let hyp_ty = self.is_prefix_of(p, s);
        let target = self.contains_of(s, p);
        let str_ty = self.str_ty;

        let (h_fv, h) = self.fvar();
        let pred_ps = self.is_prefix_pred(p, s);

        let body = self.exists_elim_str(
            pred_ps,
            target,
            &|d, t, ht| {
                let nil = d.nil();
                let step1 = {
                    let lemma = d.k.const_(d.n.nil_append, vec![]);
                    d.k.app(lemma, p)
                }; // Eq Str (append nil p) p
                let an_p = d.append(nil, p);
                let congrl = d.congr_append_left(an_p, p, t, step1); // Eq Str (append (append nil p) t) (append p t)
                let an_p_t = d.append(an_p, t);
                let p_t = d.append(p, t);
                let e0 = d.eq_trans(an_p_t, p_t, s, congrl, ht);
                d.contains_witness(s, p, nil, t, e0)
            },
            h,
        );

        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_s = self.lam_fv(s_fv, str_ty, with_h);
            self.lam_fv(p_fv, str_ty, with_s)
        };
        let ty = {
            let with_hyp = self.arrow(hyp_ty, target);
            let with_s = self.pi_fv(s_fv, str_ty, with_hyp);
            self.pi_fv(p_fv, str_ty, with_s)
        };
        let name = self.n.contains_of_is_prefix;
        self.declare_theorem(name, ty, value)
    }

    /// `contains_of_isSuffix : ∀ (p s : Str), isSuffix p s → contains s p` —
    /// the suffix witness outer, `nil` inner, via `append_nil`.
    fn prove_contains_of_is_suffix(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let hyp_ty = self.is_suffix_of(p, s);
        let target = self.contains_of(s, p);
        let str_ty = self.str_ty;

        let (h_fv, h) = self.fvar();
        let pred_qp = self.is_suffix_pred(p, s);

        let body = self.exists_elim_str(
            pred_qp,
            target,
            &|d, q, hq| {
                let qp = d.append(q, p);
                let nil = d.nil();
                let step1 = {
                    let lemma = d.k.const_(d.n.append_nil, vec![]);
                    d.k.app(lemma, qp)
                }; // Eq Str (append (append q p) nil) (append q p)
                let qp_nil = d.append(qp, nil);
                let e0 = d.eq_trans(qp_nil, qp, s, step1, hq);
                d.contains_witness(s, p, q, nil, e0)
            },
            h,
        );

        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_s = self.lam_fv(s_fv, str_ty, with_h);
            self.lam_fv(p_fv, str_ty, with_s)
        };
        let ty = {
            let with_hyp = self.arrow(hyp_ty, target);
            let with_s = self.pi_fv(s_fv, str_ty, with_hyp);
            self.pi_fv(p_fv, str_ty, with_s)
        };
        let name = self.n.contains_of_is_suffix;
        self.declare_theorem(name, ty, value)
    }

    /// `contains_substr : ∀ (n m : Nat) (s : Str), contains s (substr n m s)`.
    ///
    /// Witnesses `take n s` (outer) and `drop m (drop n s)` (inner), from two
    /// applications of `take_append_drop` — at `(n, s)` and at
    /// `(m, drop n s)` — re-associated by `append_assoc`. The stated type uses
    /// `substr n m s`; the proof is built against its `δ`-unfolded shape
    /// `take m (drop n s)`, exactly `substr_arithmetic.rs`'s established
    /// pattern.
    fn prove_contains_substr(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let (m_fv, m) = self.fvar();
        let (s_fv, s) = self.fvar();
        let a = self.take_of(n, s);
        let dn = self.drop_of(n, s);
        let b = self.take_of(m, dn);
        let c = self.drop_of(m, dn);

        let law1 = {
            let lemma = self.k.const_(self.n.take_append_drop, vec![]);
            let e = self.k.app(lemma, n);
            self.k.app(e, s)
        }; // Eq Str (append a dn) s
        let law2 = {
            let lemma = self.k.const_(self.n.take_append_drop, vec![]);
            let e = self.k.app(lemma, m);
            self.k.app(e, dn)
        }; // Eq Str (append b c) dn

        let step1 = {
            let lemma = self.k.const_(self.n.append_assoc, vec![]);
            let e = self.k.app(lemma, a);
            let e = self.k.app(e, b);
            self.k.app(e, c)
        }; // Eq Str (append (append a b) c) (append a (append b c))
        let bc = self.append(b, c);
        let step2 = self.congr_append_right(a, bc, dn, law2); // Eq Str (append a bc) (append a dn)
        let ab = self.append(a, b);
        let abc = self.append(ab, c);
        let a_bc = self.append(a, bc);
        let a_dn = self.append(a, dn);
        let chain = self.eq_trans(abc, a_bc, a_dn, step1, step2);
        let e0 = self.eq_trans(abc, a_dn, s, chain, law1);

        let u = self.substr_of(n, m, s);
        let proof = self.contains_witness(s, b, a, c, e0);
        let stmt = self.contains_of(s, u);
        let nat_ty = self.nat_ty;
        let str_ty = self.str_ty;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            let over_m = self.pi_fv(m_fv, nat_ty, over_s);
            self.pi_fv(n_fv, nat_ty, over_m)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            let over_m = self.lam_fv(m_fv, nat_ty, over_s);
            self.lam_fv(n_fv, nat_ty, over_m)
        };
        let name = self.n.contains_substr;
        self.declare_theorem(name, ty, value)
    }
}
