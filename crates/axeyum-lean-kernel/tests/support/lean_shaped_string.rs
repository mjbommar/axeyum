//! A Lean-shaped `Nat`/`List`/`Char`/`String` environment for the primitive
//! `String` literal rules, with one clause of the checked bootstrap optionally
//! mutated.
//!
//! # Why the environment here is built rather than imported
//!
//! Lean 4.30's `String` is `structure String where ofByteArray :: (toByteArray :
//! ByteArray) (isValidUTF8 : ByteArray.IsValidUTF8 toByteArray)`, and reaching
//! that shape by hand means modelling `ByteArray`, `Array`, `UInt8` and a UTF-8
//! validity predicate -- hundreds of lines that test the *fixture*, not the
//! rule. This module therefore declares a `String` with the same **checked
//! shape** (parameter-free, index-free, non-recursive, sole constructor
//! `String.ofByteArray`) over a simpler field type, so the rules actually
//! compute and every mutation is one line.
//!
//! That is exactly as much as the gate inspects, and deliberately so: the
//! expansion's well-typedness comes from `String.ofList`'s **declared type**,
//! not from what its field contains. The claim that any of this matches *Lean*
//! is not made here -- it is made by `real_lean_string_literal_crosscheck`,
//! which hands official Lean 4.30 obligations generated from this kernel's own
//! answers.
#![allow(dead_code)]

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, Lit, NameId, ReducibilityHint};

/// One clause of the checked bootstrap, removed or corrupted.
///
/// A negative test that passes because the rule was never enabled proves
/// nothing, so every control below is paired with `Mutation::None` in the same
/// test — the positive assertion runs first, in the same shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutation {
    /// Lean's shape, unmodified.
    None,
    /// `String.ofList` absent.
    NoOfList,
    /// `String.ofList` present as an `Axiom` of the right type.
    OfListIsAxiom,
    /// `String.ofList : List Char -> List Char`.
    OfListWrongCodomain,
    /// `String.ofList.{v} : List Char -> String`, universe-polymorphic.
    OfListIsPolymorphic,
    /// `Char.ofNat` absent.
    NoCharOfNat,
    /// `Char.ofNat : Char -> Char` (wrong domain).
    CharOfNatWrongDomain,
    /// `Char.ofNat` present as an `Axiom` of the right type.
    CharOfNatIsAxiom,
    /// `List` declared with its constructors in the order `[cons, nil]`.
    ListConstructorsReordered,
    /// `String`'s sole constructor named `String.mk`.
    StringConstructorRenamed,
    /// `Char`'s sole constructor named `Char.make`.
    CharConstructorRenamed,
    /// `Char : Type 1`, so `String.ofList`'s domain is `List.{1} Char`.
    ///
    /// The whole tower moves with it: a `Type 1` field forces `String : Type 1`
    /// in Lean and here (ADR-1495), so this mutation changes the LIST LEVEL and
    /// nothing else the bootstrap looks at.
    CharAtUniverseOne,
}

/// Every handle the tests need out of a built environment.
pub struct Env {
    pub string: NameId,
    pub string_ctor: NameId,
    pub string_type: ExprId,
    pub of_list: NameId,
    pub char_of_nat: NameId,
    pub list_nil: NameId,
    pub list_cons: NameId,
    pub char_type: ExprId,
    pub list_char: ExprId,
    pub list_level: axeyum_lean_kernel::LevelId,
}

/// A Lean-shaped `Nat`/`List`/`Char`/`String` environment, with one clause of the
/// bootstrap optionally mutated.
#[allow(clippy::too_many_lines)]
pub fn lean_shaped_kernel(mutation: Mutation) -> (Kernel, Env) {
    let mut kernel = Kernel::new();
    let logic = axeyum_lean_kernel::build_logic_prelude(&mut kernel)
        .expect("the logic prelude carries the canonical Nat bootstrap");
    let anon = kernel.anon();
    let nat_type = kernel.const_(logic.nat, vec![]);

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let two = kernel.level_succ(one);

    // --- Char : Type (or Type 1 under the universe mutation) ----------------
    let char_name = kernel.name_str(anon, "Char");
    let char_ctor = if mutation == Mutation::CharConstructorRenamed {
        kernel.name_str(char_name, "make")
    } else {
        kernel.name_str(char_name, "mk")
    };
    let char_sort = if mutation == Mutation::CharAtUniverseOne {
        kernel.sort(two)
    } else {
        kernel.sort(one)
    };
    let char_type = kernel.const_(char_name, vec![]);
    {
        let mk_ty = kernel.pi(anon, nat_type, char_type, BinderInfo::Default);
        kernel
            .add_inductive(char_name, &[], 0, char_sort, &[(char_ctor, mk_ty)])
            .expect("Char admits");
    }

    // --- List.{u} : Type u -> Type u ----------------------------------------
    // At `u := 0` this is Lean's `List Char`, which is the only instance the
    // string rules ever build.
    let list_name = kernel.name_str(anon, "List");
    let list_nil = kernel.name_str(list_name, "nil");
    let list_cons = kernel.name_str(list_name, "cons");
    let u = kernel.name_str(anon, "u");
    {
        let u_level = kernel.level_param(u);
        let u_succ = kernel.level_succ(u_level);
        let type_u = kernel.sort(u_succ);
        let alpha = kernel.name_str(anon, "α");
        let list_ty = kernel.pi(alpha, type_u, type_u, BinderInfo::Default);
        let list_const = kernel.const_(list_name, vec![u_level]);

        let nil_ty = {
            let a0 = kernel.bvar(0);
            let list_a = kernel.app(list_const, a0);
            kernel.pi(alpha, type_u, list_a, BinderInfo::Default)
        };
        let cons_ty = {
            let a2 = kernel.bvar(2);
            let result = kernel.app(list_const, a2);
            let a1 = kernel.bvar(1);
            let tail_ty = kernel.app(list_const, a1);
            let tail = kernel.name_str(anon, "tail");
            let inner = kernel.pi(tail, tail_ty, result, BinderInfo::Default);
            let a0 = kernel.bvar(0);
            let head = kernel.name_str(anon, "head");
            let inner = kernel.pi(head, a0, inner, BinderInfo::Default);
            kernel.pi(alpha, type_u, inner, BinderInfo::Default)
        };
        let ctors = if mutation == Mutation::ListConstructorsReordered {
            [(list_cons, cons_ty), (list_nil, nil_ty)]
        } else {
            [(list_nil, nil_ty), (list_cons, cons_ty)]
        };
        kernel
            .add_inductive(list_name, &[u], 1, list_ty, &ctors)
            .expect("List admits");
    }

    // `List Char` at the universe `Char` actually lives at.
    let list_level = if mutation == Mutation::CharAtUniverseOne {
        one
    } else {
        zero
    };
    let list_char = {
        let head = kernel.const_(list_name, vec![list_level]);
        kernel.app(head, char_type)
    };

    // --- String : Type, sole constructor `String.ofByteArray (List Char)` ----
    let string = kernel.name_str(anon, "String");
    let string_ctor = if mutation == Mutation::StringConstructorRenamed {
        kernel.name_str(string, "mk")
    } else {
        kernel.name_str(string, "ofByteArray")
    };
    let string_type = kernel.const_(string, vec![]);
    {
        // `String` sits at the universe its sole field FORCES, which under
        // `CharAtUniverseOne` is one higher: `Char : Type 1` makes
        // `List.{1} Char : Type 1`, and a `Type 1` field cannot be stored in a
        // `Type 0` structure. Lean 4.30 refuses that shape verbatim — "Invalid
        // universe level in constructor `String.ofByteArray`: Parameter has
        // type List Char at universe level 2 which is not less than or equal
        // to the inductive type's resulting universe level 1" — and accepts it
        // at `Type 1`; this kernel enforces the same constraint as
        // `KernelError::ConstructorFieldUniverseTooBig` (ADR-1495).
        //
        // The mutation still measures exactly what it names. The string-literal
        // bootstrap never inspects `String`'s own sort; it requires
        // `String.ofList`'s domain to be `List.{0} Char` and rejects any other
        // level (`build_string_literal_bootstrap` in `src/tc.rs`). So a
        // `String` admitted one universe up leaves the literal rejected for the
        // list level, which is the clause under test.
        let string_sort = if mutation == Mutation::CharAtUniverseOne {
            kernel.sort(two)
        } else {
            kernel.sort(one)
        };
        let ctor_ty = kernel.pi(anon, list_char, string_type, BinderInfo::Default);
        kernel
            .add_inductive(string, &[], 0, string_sort, &[(string_ctor, ctor_ty)])
            .expect("String admits");
    }

    // --- Char.ofNat : Nat -> Char -------------------------------------------
    let char_of_nat = kernel.name_str(char_name, "ofNat");
    if mutation != Mutation::NoCharOfNat {
        let domain = if mutation == Mutation::CharOfNatWrongDomain {
            char_type
        } else {
            nat_type
        };
        let ty = kernel.pi(anon, domain, char_type, BinderInfo::Default);
        let value = {
            let mk = kernel.const_(char_ctor, vec![]);
            let argument = if mutation == Mutation::CharOfNatWrongDomain {
                // `Char.mk` still wants a `Nat`, so the body projects one back
                // out; only the declared *type* is the mutation.
                kernel.lit(Lit::nat(0_u8))
            } else {
                kernel.bvar(0)
            };
            let body = kernel.app(mk, argument);
            kernel.lam(anon, domain, body, BinderInfo::Default)
        };
        let declaration = if mutation == Mutation::CharOfNatIsAxiom {
            Declaration::Axiom {
                name: char_of_nat,
                uparams: vec![],
                ty,
            }
        } else {
            Declaration::Definition {
                name: char_of_nat,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(0),
            }
        };
        kernel
            .add_declaration(declaration)
            .expect("Char.ofNat admits");
    }

    // --- String.ofList : List Char -> String ---------------------------------
    let of_list = kernel.name_str(string, "ofList");
    if mutation != Mutation::NoOfList {
        let codomain = if mutation == Mutation::OfListWrongCodomain {
            list_char
        } else {
            string_type
        };
        let ty = kernel.pi(anon, list_char, codomain, BinderInfo::Default);
        let value = if mutation == Mutation::OfListWrongCodomain {
            let body = kernel.bvar(0);
            kernel.lam(anon, list_char, body, BinderInfo::Default)
        } else {
            let ctor = kernel.const_(string_ctor, vec![]);
            let arg = kernel.bvar(0);
            let body = kernel.app(ctor, arg);
            kernel.lam(anon, list_char, body, BinderInfo::Default)
        };
        let declaration = match mutation {
            Mutation::OfListIsAxiom => Declaration::Axiom {
                name: of_list,
                uparams: vec![],
                ty,
            },
            Mutation::OfListIsPolymorphic => {
                let v = kernel.name_str(anon, "v");
                Declaration::Definition {
                    name: of_list,
                    uparams: vec![v],
                    ty,
                    value,
                    hint: ReducibilityHint::Regular(0),
                }
            }
            _ => Declaration::Definition {
                name: of_list,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(0),
            },
        };
        kernel
            .add_declaration(declaration)
            .expect("String.ofList admits");
    }

    let env = Env {
        string,
        string_ctor,
        string_type,
        of_list,
        char_of_nat,
        list_nil,
        list_cons,
        char_type,
        list_char,
        list_level,
    };
    (kernel, env)
}

/// `String.ofList (List.cons Char c₀ (… (List.nil Char)))` for the given scalars,
/// written out by hand — the term the kernel's expansion is checked *against*.
pub fn of_list_of_scalars(kernel: &mut Kernel, env: &Env, scalars: &[u32]) -> ExprId {
    let list = list_of_scalars(kernel, env, scalars);
    let of_list = kernel.const_(env.of_list, vec![]);
    kernel.app(of_list, list)
}

pub fn list_of_scalars(kernel: &mut Kernel, env: &Env, scalars: &[u32]) -> ExprId {
    let nil = kernel.const_(env.list_nil, vec![env.list_level]);
    let mut list = kernel.app(nil, env.char_type);
    let cons = kernel.const_(env.list_cons, vec![env.list_level]);
    let cons = kernel.app(cons, env.char_type);
    let of_nat = kernel.const_(env.char_of_nat, vec![]);
    for &scalar in scalars.iter().rev() {
        let code = kernel.lit(Lit::nat(scalar));
        let character = kernel.app(of_nat, code);
        let step = kernel.app(cons, character);
        list = kernel.app(step, list);
    }
    list
}
