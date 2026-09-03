//! The **list prelude**: `List.{u}` as an ordinary universe-polymorphic
//! inductive (`nil`/`cons`), admitted through the same trusted
//! `add_inductive` gate as `Nat`, `Bool`, `Exists`, and `Acc` in
//! [`build_logic_prelude`](crate::build_logic_prelude) — see ADR-1495 (the
//! constructor-field universe guard this inductive is checked against) and
//! ADR-1579 (this carrier's own design note).
//!
//! ADR-1310 declined to add `List`, on the measured ground that every use
//! cited as needing it actually only needed a **fold** over a finite index
//! set, which `Int.sumMaps` already gave without an aggregate. That finding
//! stands and is not revisited here. What changed is ADR-1520/ADR-1577:
//! `Nat.Multiset` and `Nat.Finset` each landed as a ℕ-only **computed**
//! carrier (a function-plus-bound pair) specifically to avoid the
//! permutation quotient a real `List` would otherwise need — and each ADR
//! records, in its own "what this deliberately does not provide" section,
//! that order is never represented and nothing is quotiented. `List` is the
//! third piece: it needs **no quotient at all**, because nothing about it
//! claims two permutations of the same elements are equal. It is an
//! ordinary inductive with an ordinary structurally-recursive eliminator,
//! exactly like `Nat`, `Nat.Fin`, `Nat.Pair`, `Nat.Multiset` and
//! `Nat.Finset` before it. ADR-1310's own alternatives section already says
//! so: "Nothing about it \[`List`\] cannot be declared (it can; it costs
//! zero axioms)."
//!
//! # Universe
//!
//! `List.{u} : Type u → Type u`, exactly Lean's own polymorphic list, with
//! one type parameter (`num_params = 1`) and two constructors:
//!
//! ```text
//! inductive List.{u} (α : Type u) : Type u
//!   | nil  : List α
//!   | cons : α → List α → List α
//! ```
//!
//! admitted with the identical shape `tests/support/lean_shaped_string.rs`
//! already builds for the string-literal bootstrap fixtures (`List.{u} Char`
//! at `u := 0` for the ordinary case, `u := 1` under the `CharAtUniverseOne`
//! mutation) — this module is the first place that shape lands as *prelude*
//! surface rather than test-only scaffolding.
//!
//! ADR-1495's constructor-field universe guard
//! (`KernelError::ConstructorFieldUniverseTooBig`) is exactly what pins this
//! shape down: `cons : α → List α → List α` has its `α` field at `Sort
//! (u+1)` (since `α : Type u = Sort (u+1)`), and the family's own result
//! universe is also `Sort (u+1)` (`List.{u} α : Type u`), so the field sits
//! **at, not above**, the result universe and the guard accepts it. Every
//! definition below fixes `u := 0` (`List.{0} α` for `α : Type 0`, matching
//! `Nat : Type 0` and every other carrier this prelude builds), so nothing
//! downstream needs to reason about `u` symbolically — but the inductive
//! itself stays genuinely universe-polymorphic, so a later consumer that
//! needs `List.{1}` (e.g. a list of `Prop`-quantified propositions) is not
//! blocked by this module's own choice to specialize at `u := 0`.
//!
//! # What is declared
//!
//! Structural recursion via the generated `List.rec`, following exactly the
//! recursion-argument discipline `nat_prelude` documents for `Nat.add`
//! et al.: **`append` recurses on its FIRST (left) argument**, so
//! `nil_append`-shaped equations at the right operand are real theorems and
//! `append_nil`-shaped equations at the left operand are the ones that
//! reduce for a literal `nil`/`cons` skeleton.
//!
//! | name | type | recurses on |
//! | --- | --- | --- |
//! | `List.length` | `{α} → List α → Nat` | the list |
//! | `List.append` | `{α} → List α → List α → List α` | the first list |
//! | `List.map` | `{α β} → (α → β) → List α → List β` | the list |
//! | `List.foldr` | `{α β} → (α → β → β) → β → List α → β` | the list |
//! | `List.reverse` | `{α} → List α → List α` | the list, via `append` |
//!
//! `List.sum` (`List Nat → Nat`, via `List.foldr Nat.add 0`) and every
//! theorem that mentions `Nat.add` are declared in
//! [`build_list_nat_bridge`], **after** `build_nat_prelude`, precisely
//! because they need the real named `Nat.add` (and its `zero_add`/
//! `succ_add`/`add_assoc` theorems) rather than reinventing arithmetic
//! inline. Everything in *this* module needs nothing beyond
//! [`crate::build_logic_prelude`] — no named `Nat.add` exists yet at the
//! point `build_list_prelude` runs (it is declared later, inside
//! `build_nat_prelude`), which is also why this module sits **before**
//! `nat` in the prelude chain rather than after it: `List Nat` only needs
//! the `Nat` *type* (an ordinary inductive, from `build_logic_prelude`), not
//! its arithmetic.
//!
//! Every `Definition` below is exercised at concrete, small, discriminating
//! arguments in `list_prelude_tests`, each paired with a negative control
//! that a plausible wrong implementation would fail (the kernel's trusted
//! gate cannot tell a `Definition` is wrong — see
//! `docs/contributor-guide/kernel-proof-engineering.md`).

use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, PreludeKey, PreludeValue};

mod bridge;
mod ops;
mod theorems;

pub use bridge::{ListNatBridge, build_list_nat_bridge};

use ops::{declare_append, declare_foldr, declare_length, declare_map, declare_reverse};

/// The interned names produced by [`build_list_prelude`]: the inductive
/// `List` and its constructors/recursor, plus every operation and theorem
/// declared without needing `Nat`'s arithmetic. See [`build_list_nat_bridge`]
/// for `List.sum` and the theorems that do need it.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms
/// (`k.const_(list.length, vec![])`) directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListPrelude {
    /// `List.{u} : Type u → Type u`.
    pub list: NameId,
    /// `List.nil.{u} : {α : Type u} → List α`.
    pub nil: NameId,
    /// `List.cons.{u} : {α : Type u} → α → List α → List α`.
    pub cons: NameId,
    /// `List.rec` — the generated eliminator.
    pub rec: NameId,
    /// The universe parameter name `List` was declared with (`u`).
    pub u_param: NameId,

    /// `List.length : {α : Type 0} → List α → Nat`.
    pub length: NameId,
    /// `List.append : {α : Type 0} → List α → List α → List α`, recursing on
    /// the FIRST list argument.
    pub append: NameId,
    /// `List.map : {α β : Type 0} → (α → β) → List α → List β`.
    pub map: NameId,
    /// `List.foldr : {α β : Type 0} → (α → β → β) → β → List α → β`.
    pub foldr: NameId,
    /// `List.reverse : {α : Type 0} → List α → List α`.
    pub reverse: NameId,

    /// `List.append_nil : ∀ {α} l, append l nil = l`.
    pub append_nil: NameId,
    /// `List.append_assoc : ∀ {α} l1 l2 l3, append (append l1 l2) l3 = append l1 (append l2 l3)`.
    pub append_assoc: NameId,
    /// `List.reverse_append : ∀ {α} a b, reverse (append a b) = append (reverse b) (reverse a)`.
    pub reverse_append: NameId,
    /// `List.reverse_reverse : ∀ {α} l, reverse (reverse l) = l`.
    pub reverse_reverse: NameId,
    /// `List.length_map : ∀ {α β} f l, length (map f l) = length l`.
    pub length_map: NameId,
    /// `List.foldr_append : ∀ {α β} f z l1 l2, foldr f z (append l1 l2) = foldr f (foldr f z l2) l1`.
    pub foldr_append: NameId,
}

/// Declare [`ListPrelude`] into `kernel`'s environment, building
/// [`crate::LogicPrelude`] first if it is not already present.
///
/// Repeated construction validates and returns the exact registered package.
/// Any trusted-gate rejection is returned as [`KernelError`] and rolls back
/// all declarations admitted by this invocation.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A
/// failed build leaves the pre-call environment unchanged.
pub fn build_list_prelude(kernel: &mut Kernel) -> Result<ListPrelude, KernelError> {
    if let Some(PreludeValue::List(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::List)
    {
        return Ok(prelude);
    }
    build_list_prelude_uncached(kernel)
}

/// [`build_list_prelude`] without the process-wide template fast path (there
/// is none for `List` yet — see `prelude_cache::slot`).
pub(crate) fn build_list_prelude_uncached(kernel: &mut Kernel) -> Result<ListPrelude, KernelError> {
    let logic = crate::build_logic_prelude(kernel)?;
    if let Some(PreludeValue::List(prelude)) = kernel.cached_prelude(PreludeKey::List)? {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<ListPrelude, KernelError> {
        let anon = kernel.anon();
        let zero_lvl = kernel.level_zero();
        let one_lvl = kernel.level_succ(zero_lvl);
        // `Type 0 = Sort 1`, the universe every carrier this prelude touches
        // (`Nat`, `Bool`, …) already lives at.
        let type0 = kernel.sort(one_lvl);

        // --- List.{u} (α : Type u) : Type u, nil | cons -----------------
        let u_param = kernel.name_str(anon, "u");
        let list = kernel.name_str(anon, "List");
        let nil = kernel.name_str(list, "nil");
        let cons = kernel.name_str(list, "cons");
        {
            let u_lvl = kernel.level_param(u_param);
            let u_succ = kernel.level_succ(u_lvl);
            let type_u = kernel.sort(u_succ);
            let alpha_name = kernel.name_str(anon, "α");
            let list_ty = kernel.pi(alpha_name, type_u, type_u, BinderInfo::Default);

            let list_const = kernel.const_(list, vec![u_lvl]);
            let nil_ty = {
                let a0 = kernel.bvar(0);
                let list_a = kernel.app(list_const, a0);
                kernel.pi(alpha_name, type_u, list_a, BinderInfo::Default)
            };
            let cons_ty = {
                let a2 = kernel.bvar(2);
                let result = kernel.app(list_const, a2);
                let a1 = kernel.bvar(1);
                let tail_ty = kernel.app(list_const, a1);
                let tail_name = kernel.name_str(anon, "tail");
                let inner = kernel.pi(tail_name, tail_ty, result, BinderInfo::Default);
                let a0 = kernel.bvar(0);
                let head_name = kernel.name_str(anon, "head");
                let inner = kernel.pi(head_name, a0, inner, BinderInfo::Default);
                kernel.pi(alpha_name, type_u, inner, BinderInfo::Default)
            };
            kernel.add_inductive(
                list,
                &[u_param],
                1,
                list_ty,
                &[(nil, nil_ty), (cons, cons_ty)],
            )?;
        }
        let rec = kernel.name_str(list, "rec");

        let length = declare_length(kernel, list, rec, zero_lvl, one_lvl, type0, &logic)?;
        let append = declare_append(kernel, list, nil, cons, rec, zero_lvl, one_lvl, type0)?;
        let map = declare_map(kernel, list, nil, cons, rec, zero_lvl, one_lvl, type0)?;
        let foldr = declare_foldr(kernel, list, rec, zero_lvl, one_lvl, type0)?;
        let reverse = declare_reverse(
            kernel, list, nil, cons, rec, append, zero_lvl, one_lvl, type0,
        )?;

        let names = ListNames {
            list,
            nil,
            cons,
            rec,
            u_param,
            length,
            append,
            map,
            foldr,
            reverse,
        };
        let (append_assoc, append_nil, reverse_append, reverse_reverse, length_map, foldr_append) =
            theorems::declare_list_theorems(kernel, &logic, &names, zero_lvl, one_lvl, type0)?;

        Ok(ListPrelude {
            list,
            nil,
            cons,
            rec,
            u_param,
            length,
            append,
            map,
            foldr,
            reverse,
            append_nil,
            append_assoc,
            reverse_append,
            reverse_reverse,
            length_map,
            foldr_append,
        })
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(PreludeKey::List, PreludeValue::List(prelude), checkpoint);
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

/// The handful of interned names `ops`/`theorems` need to build further
/// terms, without exposing every field of [`ListPrelude`] before it exists.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ListNames {
    pub list: NameId,
    pub nil: NameId,
    pub cons: NameId,
    pub rec: NameId,
    #[allow(dead_code)]
    pub u_param: NameId,
    pub length: NameId,
    pub append: NameId,
    pub map: NameId,
    pub foldr: NameId,
    pub reverse: NameId,
}

#[cfg(test)]
mod list_prelude_tests;
