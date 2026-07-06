//! The **free-monoid (string) prelude** (P3.7 strings fragment): the word-clash
//! reconstruction's kernel foundation, declared into a [`Kernel`]'s environment
//! through the trusted `add_inductive` / `add_recursive_datatype_family` /
//! `add_declaration` gates — **no new kernel axioms**.
//!
//! # Design — strings as `List` over a finite code-point alphabet
//!
//! A word-level (string/sequence) refutation reasons in the **free monoid** over
//! an alphabet of code points. This prelude models that monoid the way the
//! word-clash certificate needs it — with the *minimal* representation that makes
//! the clash statement provable by **kernel ι-computation** rather than an assumed
//! axiom:
//!
//! - **`Char : Type`** — a finite enum with one **nullary** constructor
//!   `Char.c<i>` per **distinct code point** that appears in the certificate's
//!   constant literals. Distinct code points are therefore distinct *constructors*,
//!   so their inequality is a `Bool`-valued **is-tester** ι-fold
//!   (`is_c (Char.c_i) ↝ true`, `is_c (Char.c_j) ↝ false` for `i ≠ j`) — no
//!   numeric magnitude is ever encoded (a 21-bit Unicode scalar costs one nullary
//!   constructor, not a unary `Nat`), and constructor distinctness gives the
//!   "two different constants cannot be equal" contradiction for free.
//! - **`Str : Type`** — the **recursive** inductive `Str.nil | Str.cons (Char) (Str)`
//!   (i.e. `List Char`), declared through
//!   [`Kernel::add_recursive_datatype_family`]. Its recursor ι-computes the `head`
//!   and `tail` selectors, so a concrete constant block `"abc"` is the closed term
//!   `cons c_a (cons c_b (cons c_c nil))`, and projecting position `k` of it is a
//!   fixed `head ∘ tailᵏ` recursor application that ι-reduces to a concrete `Char`.
//! - **`append : Str → Str → Str`** — declared as an **opaque** constant (an
//!   `Axiom` of that function type). The word-clash reconstruction never reduces
//!   `append`: the equality-joining chain that connects two clashing members is a
//!   pure `Eq`-congruence over whole (opaque) terms, so `str.++` needs only to be a
//!   binary function symbol, never a computed one. (Length/cancellation reasoning —
//!   which *would* need `append`'s recursive definition and monoid lemmas — is the
//!   deferred follow-up; see the solver-side `word_reconstruct` module.)
//!
//! Every declaration is admitted through the **trusted** gates, which type-check
//! it; a malformed prelude would be rejected there (a green build is its
//! well-formedness proof). The same `infer` / `whnf` / `def_eq` machinery then
//! checks the reconstructed proof term on top of it, so a wrong reconstruction is
//! rejected by the kernel — never trusted.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::{LogicPrelude, RecField};
use crate::{BinderInfo, Kernel};

/// The interned names produced by [`build_string_prelude`]: the `Char` alphabet
/// enum, the recursive `Str = List Char` inductive, and the opaque `append`
/// constant, plus the shared [`LogicPrelude`] used to build the `Bool`
/// discriminators and `Eq` transports.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms.
#[derive(Debug, Clone)]
pub struct StringPrelude {
    /// The logical prelude (`Eq`, `Bool`, `False`, …) these declarations ride on.
    pub logic: LogicPrelude,

    /// `Char : Type` (`Sort 1`) — the code-point alphabet enum.
    pub char_ind: NameId,
    /// `Char.c<i> : Char` — one nullary constructor per distinct code point, in
    /// the order passed to [`build_string_prelude`].
    pub char_ctors: Vec<NameId>,
    /// `Char.rec` — the alphabet eliminator (used to build the is-testers).
    pub char_rec: NameId,

    /// `Str : Type` (`Sort 1`) — the recursive `List Char` inductive.
    pub str_ind: NameId,
    /// `Str.nil : Str`.
    pub str_nil: NameId,
    /// `Str.cons : Char → Str → Str`.
    pub str_cons: NameId,
    /// `Str.rec` — the list eliminator (used to build `head` / `tail`).
    pub str_rec: NameId,

    /// `append : Str → Str → Str` — the opaque monoid multiplication.
    pub append: NameId,

    /// The universe level `1` (so `Char`/`Str : Sort 1 = Type`).
    one: LevelId,
}

/// Declare the free-monoid string prelude into `kernel`'s environment over a
/// `num_chars`-symbol alphabet, returning the [`StringPrelude`] of interned names.
///
/// `logic` must already be built in the same `kernel` (its `Bool`/`Eq`/`False`
/// names are reused). `num_chars` is the number of **distinct code points** the
/// caller will model (each becomes one nullary `Char` constructor `Char.c<i>`);
/// it may be `0` for a pure equality/disequality reconstruction that never needs a
/// concrete character.
///
/// # Panics
///
/// Panics if any declaration fails to type-check, which would indicate a kernel
/// regression rather than a caller error — the declarations are fixed and valid.
#[must_use]
pub fn build_string_prelude(
    kernel: &mut Kernel,
    logic: LogicPrelude,
    num_chars: usize,
) -> StringPrelude {
    let anon = kernel.anon();
    let one = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };

    // --- Char : Type, Char.c0 | Char.c1 | … (all nullary) ----------------
    let char_ind = kernel.fresh_string_name("Char");
    let char_ctors: Vec<NameId> = (0..num_chars)
        .map(|i| kernel.name_str(char_ind, format!("c{i}")))
        .collect();
    {
        let char_ty = kernel.sort(one);
        let char_const = kernel.const_(char_ind, vec![]);
        // Each nullary constructor has type `Char` (the bare inductive).
        let ctor_decls: Vec<(NameId, ExprId)> =
            char_ctors.iter().map(|&c| (c, char_const)).collect();
        kernel
            .add_inductive(char_ind, &[], 0, char_ty, &ctor_decls)
            .expect("Char alphabet enum should admit");
    }
    let char_rec = kernel.name_str(char_ind, "rec");

    // --- Str : Type, Str.nil | Str.cons (Char) (Str) ---------------------
    // The recursive `List Char`: `cons` has a carrier field (`head : Char`) and a
    // direct recursive field (`tail : Str`), exactly the slice-5 shape the
    // recursive-datatype gate admits with an induction hypothesis per tail.
    let str_ind = kernel.fresh_string_name("Str");
    let char_carrier = kernel.const_(char_ind, vec![]);
    let str_nil = kernel.name_str(str_ind, "nil");
    let str_cons = kernel.name_str(str_ind, "cons");
    let family = {
        let ctors = [
            (str_nil, vec![]),
            (str_cons, vec![RecField::Carrier, RecField::Recursive]),
        ];
        kernel
            .add_recursive_datatype_family(str_ind, char_carrier, one, &ctors)
            .expect("Str = List Char recursive inductive should admit")
    };
    let str_rec = family.rec;

    // --- append : Str → Str → Str (opaque) -------------------------------
    let append = kernel.fresh_string_name("append");
    {
        let str_const = kernel.const_(str_ind, vec![]);
        let inner = kernel.pi(anon, str_const, str_const, BinderInfo::Default);
        let append_ty = kernel.pi(anon, str_const, inner, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Axiom {
                name: append,
                uparams: vec![],
                ty: append_ty,
            })
            .expect("append : Str → Str → Str axiom should admit");
    }

    StringPrelude {
        logic,
        char_ind,
        char_ctors,
        char_rec,
        str_ind,
        str_nil,
        str_cons,
        str_rec,
        append,
        one,
    }
}

impl Kernel {
    /// A fresh name under the reserved `axeyum.string` namespace for a string
    /// prelude declaration, so its inductives/recursors never clash with the
    /// logical prelude's fixed names across repeated reconstructions.
    fn fresh_string_name(&mut self, base: &str) -> NameId {
        let anon = self.anon();
        let ns = self.name_str(anon, "axeyum.string");
        self.name_str(ns, base)
    }
}

impl StringPrelude {
    /// `Char : Type` as a `Sort 1` expression's inductive constant.
    #[must_use]
    pub fn char_const(&self, kernel: &mut Kernel) -> ExprId {
        kernel.const_(self.char_ind, vec![])
    }

    /// `Str : Type` inductive constant.
    #[must_use]
    pub fn str_const(&self, kernel: &mut Kernel) -> ExprId {
        kernel.const_(self.str_ind, vec![])
    }

    /// `Str.nil`.
    #[must_use]
    pub fn nil(&self, kernel: &mut Kernel) -> ExprId {
        kernel.const_(self.str_nil, vec![])
    }

    /// `Str.cons head tail`.
    #[must_use]
    pub fn cons(&self, kernel: &mut Kernel, head: ExprId, tail: ExprId) -> ExprId {
        let c = kernel.const_(self.str_cons, vec![]);
        let e = kernel.app(c, head);
        kernel.app(e, tail)
    }

    /// The `idx`-th alphabet character `Char.c<idx>`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of the declared alphabet range.
    #[must_use]
    pub fn char(&self, kernel: &mut Kernel, idx: usize) -> ExprId {
        kernel.const_(self.char_ctors[idx], vec![])
    }

    /// `append a b` (opaque).
    #[must_use]
    pub fn append_app(&self, kernel: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        let f = kernel.const_(self.append, vec![]);
        let e = kernel.app(f, a);
        kernel.app(e, b)
    }

    /// The `tail : Str → Str` selector, a closed `Str.rec` application:
    /// `λ (t : Str), Str.rec.{1} (motive := λ _ => Str) nil (λ h t ih => t) t`.
    /// `tail (cons h r)` ι-reduces to `r`; `tail nil` ι-reduces to `nil`.
    #[must_use]
    pub fn tail_fn(&self, kernel: &mut Kernel) -> ExprId {
        let anon = kernel.anon();
        let str_const = kernel.const_(self.str_ind, vec![]);
        let motive = kernel.lam(anon, str_const, str_const, BinderInfo::Default);
        let rec = kernel.const_(self.str_rec, vec![self.one]);
        // minor for nil : Str  = nil.
        let nil = kernel.const_(self.str_nil, vec![]);
        // minor for cons : Char → Str → Str(ih) → Str  = the tail field (BVar 1).
        let cons_minor = {
            let body = kernel.bvar(1);
            // binders innermost-first: ih (Str), then tail (Str), then head (Char).
            let m = kernel.lam(anon, str_const, body, BinderInfo::Default); // ih
            let char_const = kernel.const_(self.char_ind, vec![]);
            let m = kernel.lam(anon, str_const, m, BinderInfo::Default); // tail
            kernel.lam(anon, char_const, m, BinderInfo::Default) // head
        };
        let e = kernel.app(rec, motive);
        let e = kernel.app(e, nil);
        let e = kernel.app(e, cons_minor);
        let t = kernel.bvar(0);
        let body = kernel.app(e, t);
        kernel.lam(anon, str_const, body, BinderInfo::Default)
    }

    /// The `head : Str → Char` selector, a closed `Str.rec` application:
    /// `λ (t : Str), Str.rec.{1} (motive := λ _ => Char) default (λ h t ih => h) t`.
    /// `head (cons h r)` ι-reduces to `h`; `head nil` ι-reduces to `default`
    /// (`Char.c0`, only reached on `nil` and never in a concrete-clash projection,
    /// which always lands on a `cons`). Requires a non-empty alphabet.
    ///
    /// # Panics
    ///
    /// Panics if the alphabet is empty (`num_chars == 0`).
    #[must_use]
    pub fn head_fn(&self, kernel: &mut Kernel) -> ExprId {
        let anon = kernel.anon();
        let str_const = kernel.const_(self.str_ind, vec![]);
        let char_const = kernel.const_(self.char_ind, vec![]);
        let motive = kernel.lam(anon, str_const, char_const, BinderInfo::Default);
        let rec = kernel.const_(self.str_rec, vec![self.one]);
        let default = kernel.const_(self.char_ctors[0], vec![]);
        // minor for cons : Char → Str → Char(ih) → Char = the head field (BVar 2).
        let cons_minor = {
            let body = kernel.bvar(2);
            let m = kernel.lam(anon, char_const, body, BinderInfo::Default); // ih : Char
            let m = kernel.lam(anon, str_const, m, BinderInfo::Default); // tail : Str
            kernel.lam(anon, char_const, m, BinderInfo::Default) // head : Char
        };
        let e = kernel.app(rec, motive);
        let e = kernel.app(e, default);
        let e = kernel.app(e, cons_minor);
        let t = kernel.bvar(0);
        let body = kernel.app(e, t);
        kernel.lam(anon, str_const, body, BinderInfo::Default)
    }

    /// The is-tester `is_c<idx> : Char → Bool` for the `idx`-th alphabet
    /// character, a closed `Char.rec` application: `is_c<idx> (Char.c_j)`
    /// ι-reduces to `Bool.true` when `j == idx` and `Bool.false` otherwise, so a
    /// character equality `Eq Char c_i c_j` (`i ≠ j`) folds to `Eq Bool true false`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of the declared alphabet range.
    #[must_use]
    pub fn char_is_tester(&self, kernel: &mut Kernel, idx: usize) -> ExprId {
        assert!(idx < self.char_ctors.len(), "is-tester index out of range");
        let anon = kernel.anon();
        let char_const = kernel.const_(self.char_ind, vec![]);
        let bool_const = kernel.const_(self.logic.bool_, vec![]);
        let motive = kernel.lam(anon, char_const, bool_const, BinderInfo::Default);
        let rec = kernel.const_(self.char_rec, vec![self.one]);
        let mut e = kernel.app(rec, motive);
        for j in 0..self.char_ctors.len() {
            let value = if j == idx {
                self.logic.bool_true
            } else {
                self.logic.bool_false
            };
            let minor = kernel.const_(value, vec![]);
            e = kernel.app(e, minor);
        }
        let c = kernel.bvar(0);
        let body = kernel.app(e, c);
        kernel.lam(anon, char_const, body, BinderInfo::Default)
    }
}

#[cfg(test)]
mod tests;
