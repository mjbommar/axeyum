//! The **free-monoid (string) prelude** (P3.7 strings fragment): the word-clash
//! reconstruction's kernel foundation, declared into a [`Kernel`]'s environment
//! through the trusted `add_inductive` / `add_recursive_datatype_family` /
//! `add_declaration` gates. The inductives compute in the kernel; `append` is
//! one explicit opaque kernel axiom and is tracked in the prelude-axiom ledger.
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
//! it; a malformed prelude would be rejected there (a green build proves only
//! well-formedness, not the truth of the opaque `append` assumption). The same
//! `infer` / `whnf` / `def_eq` machinery then checks the reconstructed proof term
//! relative to that explicit assumption, so a wrong reconstruction is rejected
//! by the kernel rather than silently trusted.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::{LogicPrelude, RecField};
use crate::{BinderInfo, Kernel, KernelError, PreludeKey, PreludeValue};

/// The interned names produced by [`build_string_prelude`]: the `Char` alphabet
/// enum, the recursive `Str = List Char` inductive, and the opaque `append`
/// constant, plus the shared [`LogicPrelude`] used to build the `Bool`
/// discriminators and `Eq` transports.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms.
#[derive(Debug, Clone, PartialEq, Eq)]
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
/// Each alphabet size uses a deterministic `axeyum.string.<size>` namespace.
/// Repeated construction validates and returns the exact registered package;
/// any failure is returned as [`KernelError`] and rolls back this invocation.
///
/// # Errors
///
/// Returns a logic-package mismatch, alphabet-key overflow, trusted-gate
/// rejection, or exact-package conflict. A failed string build leaves the
/// pre-call environment unchanged.
pub fn build_string_prelude(
    kernel: &mut Kernel,
    logic: LogicPrelude,
    num_chars: usize,
) -> Result<StringPrelude, KernelError> {
    match kernel.cached_prelude(PreludeKey::Logic)? {
        Some(PreludeValue::Logic(expected)) if expected == logic => {}
        _ => return Err(KernelError::PreludePackageConflict { name: logic.true_ }),
    }
    let alphabet_size = u64::try_from(num_chars)
        .map_err(|_| KernelError::StringAlphabetSizeOverflow { num_chars })?;
    let key = PreludeKey::String(alphabet_size);
    if let Some(PreludeValue::String(prelude)) = kernel.cached_prelude(key)? {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<StringPrelude, KernelError> {
        let anon = kernel.anon();
        let one = {
            let z = kernel.level_zero();
            kernel.level_succ(z)
        };

        // --- Char : Type, Char.c0 | Char.c1 | … (all nullary) ----------------
        let axeyum = kernel.name_str(anon, "axeyum");
        let string = kernel.name_str(axeyum, "string");
        let namespace = kernel.name_num(string, alphabet_size);
        let char_ind = kernel.name_str(namespace, "Char");
        let char_ctors: Vec<NameId> = (0..num_chars)
            .map(|i| kernel.name_str(char_ind, format!("c{i}")))
            .collect();
        {
            let char_ty = kernel.sort(one);
            let char_const = kernel.const_(char_ind, vec![]);
            // Each nullary constructor has type `Char` (the bare inductive).
            let ctor_decls: Vec<(NameId, ExprId)> =
                char_ctors.iter().map(|&c| (c, char_const)).collect();
            kernel.add_inductive(char_ind, &[], 0, char_ty, &ctor_decls)?;
        }
        let char_rec = kernel.name_str(char_ind, "rec");

        // --- Str : Type, Str.nil | Str.cons (Char) (Str) ---------------------
        // The recursive `List Char`: `cons` has a carrier field (`head : Char`) and a
        // direct recursive field (`tail : Str`), exactly the slice-5 shape the
        // recursive-datatype gate admits with an induction hypothesis per tail.
        let str_ind = kernel.name_str(namespace, "Str");
        let char_carrier = kernel.const_(char_ind, vec![]);
        let str_nil = kernel.name_str(str_ind, "nil");
        let str_cons = kernel.name_str(str_ind, "cons");
        let family = {
            let ctors = [
                (str_nil, vec![]),
                (str_cons, vec![RecField::Carrier, RecField::Recursive]),
            ];
            kernel.add_recursive_datatype_family(str_ind, char_carrier, one, &ctors)?
        };
        let str_rec = family.rec;

        // --- append : Str → Str → Str (opaque) -------------------------------
        let append = kernel.name_str(namespace, "append");
        {
            let str_const = kernel.const_(str_ind, vec![]);
            let inner = kernel.pi(anon, str_const, str_const, BinderInfo::Default);
            let append_ty = kernel.pi(anon, str_const, inner, BinderInfo::Default);
            kernel.add_declaration(Declaration::Axiom {
                name: append,
                uparams: vec![],
                ty: append_ty,
            })?;
        }

        Ok(StringPrelude {
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
        })
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(key, PreludeValue::String(prelude.clone()), checkpoint);
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
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

    /// A closed `Char → Char → Bool` **truth table** for a binary predicate
    /// `f(i, j)` over the alphabet indices: `table (Char.c_i) (Char.c_j)`
    /// ι-reduces to `Bool.true` iff `f(i, j)` (and `Bool.false` otherwise). Built
    /// as a nested `Char.rec`: the outer eliminator selects the row `i`, the inner
    /// one the cell `j`, both folding to a concrete `Bool` constructor — no
    /// numeric magnitude is ever encoded (the order lives entirely in the
    /// constructor-index table). Used to build the code-point ordering
    /// (`char_lt_fn`) and equality (`char_eq_fn`) the lexicographic comparison
    /// needs.
    fn char_table_fn(&self, kernel: &mut Kernel, f: impl Fn(usize, usize) -> bool) -> ExprId {
        let anon = kernel.anon();
        let char_const = kernel.const_(self.char_ind, vec![]);
        let bool_const = kernel.const_(self.logic.bool_, vec![]);
        // Outer motive: `λ _ : Char, Char → Bool`.
        let char_to_bool = kernel.pi(anon, char_const, bool_const, BinderInfo::Default);
        let outer_motive = kernel.lam(anon, char_const, char_to_bool, BinderInfo::Default);
        let outer_rec = kernel.const_(self.char_rec, vec![self.one]);
        let mut outer = kernel.app(outer_rec, outer_motive);
        let n = self.char_ctors.len();
        for i in 0..n {
            // Row `i`: `λ (b : Char), Char.rec (λ _, Bool) [f(i,0) … f(i,n-1)] b`.
            let inner_motive = kernel.lam(anon, char_const, bool_const, BinderInfo::Default);
            let inner_rec = kernel.const_(self.char_rec, vec![self.one]);
            let mut inner = kernel.app(inner_rec, inner_motive);
            for j in 0..n {
                let value = if f(i, j) {
                    self.logic.bool_true
                } else {
                    self.logic.bool_false
                };
                let minor = kernel.const_(value, vec![]);
                inner = kernel.app(inner, minor);
            }
            let b = kernel.bvar(0);
            let inner_body = kernel.app(inner, b);
            let row = kernel.lam(anon, char_const, inner_body, BinderInfo::Default);
            outer = kernel.app(outer, row);
        }
        let a = kernel.bvar(0);
        let outer_body = kernel.app(outer, a);
        kernel.lam(anon, char_const, outer_body, BinderInfo::Default)
    }

    /// The alphabet **equality** `char_eq : Char → Char → Bool`;
    /// `char_eq (Char.c_i) (Char.c_j)` ι-reduces to `Bool.true` iff `i == j`.
    #[must_use]
    pub fn char_eq_fn(&self, kernel: &mut Kernel) -> ExprId {
        self.char_table_fn(kernel, |i, j| i == j)
    }

    /// The alphabet **strict code-point order** `char_lt : Char → Char → Bool`;
    /// `char_lt (Char.c_i) (Char.c_j)` ι-reduces to `Bool.true` iff `i < j`. The
    /// alphabet is interned in ascending code-point order, so the constructor
    /// index order *is* the Unicode code-point order (ADR-0051).
    #[must_use]
    pub fn char_lt_fn(&self, kernel: &mut Kernel) -> ExprId {
        self.char_table_fn(kernel, |i, j| i < j)
    }

    /// `cond c t e : Bool` — the `Bool` if-then-else via `Bool.rec`
    /// (`cond Bool.true t e ↝ t`, `cond Bool.false t e ↝ e`).
    fn bool_cond(&self, kernel: &mut Kernel, c: ExprId, t: ExprId, e: ExprId) -> ExprId {
        let anon = kernel.anon();
        let bool_const = kernel.const_(self.logic.bool_, vec![]);
        let motive = kernel.lam(anon, bool_const, bool_const, BinderInfo::Default);
        let rec = kernel.const_(self.logic.bool_rec, vec![self.one]);
        let e0 = kernel.app(rec, motive);
        let e0 = kernel.app(e0, t); // minor for Bool.true
        let e0 = kernel.app(e0, e); // minor for Bool.false
        kernel.app(e0, c)
    }

    /// The lexicographic comparison `lex : Str → Str → Bool` (`strict = false` for
    /// `str.<=`, `strict = true` for `str.<`), a closed double `Str.rec` term over
    /// the free monoid `Str = List Char`:
    ///
    /// ```text
    /// lex nil          u            = if strict then (u ≠ nil) else true
    /// lex (cons a s')  nil          = false
    /// lex (cons a s')  (cons b t')  = if char_eq a b then lex s' t' else char_lt a b
    /// ```
    ///
    /// It ι-computes: on two concrete `cons`-prefixes that first differ at a
    /// determined position `k` (equal code points before `k`), `lex A B` reduces —
    /// through exactly `k` `char_eq`-true steps — to `char_lt (A[k]) (B[k])`, a
    /// constant `Bool`, **without forcing any tail past `k`** (so opaque variable
    /// tails are irrelevant to a first-clash refutation). The `strict`/`≤` variants
    /// coincide on that differing-position branch (`char_lt a b`); they differ only
    /// in the `nil` base cases, which such a refutation never reaches.
    #[must_use]
    pub fn lex_cmp_fn(&self, kernel: &mut Kernel, strict: bool) -> ExprId {
        let anon = kernel.anon();
        let str_const = kernel.const_(self.str_ind, vec![]);
        let char_const = kernel.const_(self.char_ind, vec![]);
        let bool_const = kernel.const_(self.logic.bool_, vec![]);
        let bool_true = kernel.const_(self.logic.bool_true, vec![]);
        let bool_false = kernel.const_(self.logic.bool_false, vec![]);
        let char_eq = self.char_eq_fn(kernel);
        let char_lt = self.char_lt_fn(kernel);

        // Outer motive: `λ _ : Str, Str → Bool`.
        let str_to_bool = kernel.pi(anon, str_const, bool_const, BinderInfo::Default);
        let outer_motive = kernel.lam(anon, str_const, str_to_bool, BinderInfo::Default);

        // Outer `nil` minor: `λ (u : Str), <nil-case>`.
        let outer_nil_minor = if strict {
            // `lt nil u = (u ≠ nil)`: `Str.rec (λ _, Bool) false (λ _ _ _, true) u`.
            let inner_motive = kernel.lam(anon, str_const, bool_const, BinderInfo::Default);
            let inner_rec = kernel.const_(self.str_rec, vec![self.one]);
            let cons_minor = {
                let m = kernel.lam(anon, bool_const, bool_true, BinderInfo::Default); // ih
                let m = kernel.lam(anon, str_const, m, BinderInfo::Default); // tail
                kernel.lam(anon, char_const, m, BinderInfo::Default) // head
            };
            let e0 = kernel.app(inner_rec, inner_motive);
            let e0 = kernel.app(e0, bool_false); // nil
            let e0 = kernel.app(e0, cons_minor); // cons
            let u = kernel.bvar(0);
            let body = kernel.app(e0, u);
            kernel.lam(anon, str_const, body, BinderInfo::Default)
        } else {
            // `le nil u = true`.
            kernel.lam(anon, str_const, bool_true, BinderInfo::Default)
        };

        // Outer `cons` minor: `λ (a : Char)(s' : Str)(ih : Str → Bool)(u : Str), …`.
        // Binder stack (outermost→innermost): a, s', ih, u, then inner b, t', ih2.
        let outer_cons_minor = {
            let inner_motive = kernel.lam(anon, str_const, bool_const, BinderInfo::Default);
            let inner_rec = kernel.const_(self.str_rec, vec![self.one]);
            // Inner `cons` minor body (deepest): stack indices —
            //   ih2=0, t'=1, b=2, u=3, ih=4, s'=5, a=6.
            let inner_cons_minor = {
                let a = kernel.bvar(6);
                let b = kernel.bvar(2);
                let ih = kernel.bvar(4);
                let tp = kernel.bvar(1);
                let cheq = {
                    let e0 = kernel.app(char_eq, a);
                    kernel.app(e0, b)
                };
                let chlt = {
                    let e0 = kernel.app(char_lt, a);
                    kernel.app(e0, b)
                };
                let ih_tp = kernel.app(ih, tp);
                let condv = self.bool_cond(kernel, cheq, ih_tp, chlt);
                let m = kernel.lam(anon, bool_const, condv, BinderInfo::Default); // ih2 : Bool
                let m = kernel.lam(anon, str_const, m, BinderInfo::Default); // t' : Str
                kernel.lam(anon, char_const, m, BinderInfo::Default) // b : Char
            };
            let e0 = kernel.app(inner_rec, inner_motive);
            let e0 = kernel.app(e0, bool_false); // inner nil: (cons a s') vs nil = false
            let e0 = kernel.app(e0, inner_cons_minor);
            let u = kernel.bvar(0); // u at the `λ u` body level
            let inner_applied = kernel.app(e0, u);
            let m = kernel.lam(anon, str_const, inner_applied, BinderInfo::Default); // u : Str
            let m = kernel.lam(anon, str_to_bool, m, BinderInfo::Default); // ih : Str → Bool
            let m = kernel.lam(anon, str_const, m, BinderInfo::Default); // s' : Str
            kernel.lam(anon, char_const, m, BinderInfo::Default) // a : Char
        };

        let outer_rec = kernel.const_(self.str_rec, vec![self.one]);
        let outer = kernel.app(outer_rec, outer_motive);
        let outer = kernel.app(outer, outer_nil_minor);
        let outer = kernel.app(outer, outer_cons_minor);
        let s = kernel.bvar(0);
        let body = kernel.app(outer, s);
        kernel.lam(anon, str_const, body, BinderInfo::Default)
    }
}

#[cfg(test)]
mod tests;
