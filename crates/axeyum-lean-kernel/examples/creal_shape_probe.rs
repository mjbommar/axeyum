//! Probe: **is a setoid ℝ expressible in this kernel, and does it cost an
//! axiom?** (ADR-0512.)
//!
//! ADR-0456 measured that the two textbook routes to `ℝ` are both closed here:
//! a Cauchy **quotient** needs `Quot.sound`, which the four-declaration
//! quotient package does not contain, and a **Dedekind** cut needs `propext`
//! and `funext`, neither of which exists in this intuitionistic, zero-axiom
//! logic prelude. ADR-0512 takes the third route — a Bishop-style *setoid*: a
//! carrier of regular representatives (no quotient) with equality carried by a
//! **defined** relation `Equiv` rather than by `Eq`.
//!
//! That route is only worth planning if the kernel can actually admit its
//! carrier, so this probe admits the carrier and measures the cost. It answers
//! four structural questions, all of which had to hold before ADR-0512 could
//! name a plan:
//!
//! 1. an inductive in `Type 0` may carry a **function field** `Nat → Rat`
//!    (`CReal` is not recursive, so strict positivity is not at issue, but the
//!    result universe is: `Nat → Rat` lives in `Type 0`, so no universe bump);
//! 2. it may carry a **dependent `Prop` field** whose type mentions the earlier
//!    function field (`Rat` already shows this for non-function fields);
//! 3. the generated recursor supports **large elimination** back out to
//!    `Nat → Rat`, so the representative projection is a definition, not a
//!    field access we would have to assume; and
//! 4. a relation over the carrier, defined through that projection, checks in
//!    `Prop` — the shape every `Equiv` and every congruence lemma will take.
//!
//! # What this probe does NOT measure
//!
//! It does **not** state Bishop regularity, and it does not define `Equiv`'s
//! closeness relation. Both need `ℚ`'s **order** development (`Rat.le`,
//! `Rat.sub`, `Rat.abs`), which does not exist yet — `int_prelude/rat.rs` has
//! <!-- was-absent: Rat.sub, Rat.abs -->
//! the carrier, `normalize`, `add`, `mul` and `neg` and no order at all. So the
//! carrier here is admitted **parametrically in its regularity predicate**:
//!
//! ```text
//! CReal.Of (reg : (Nat → Rat) → Prop) : Type
//! CReal.Of.mk : (f : Nat → Rat) → reg f → CReal.Of reg
//! ```
//!
//! and the relation is parametric in its closeness predicate. When `ℚ`'s order
//! lands, `CReal := CReal.Of Rat.Regular` is one definition and nothing here
//! changes shape. Reporting this probe as "ℝ is constructed" would be exactly
//! the failure mode this repository keeps hitting: a tool that ran, exited 0,
//! and answered a question nobody asked. It measures **expressibility and
//! cost**, and that is all it claims.
//!
//! # The finding the exit status depends on
//!
//! Every declaration this probe admits must have an **empty**
//! `Kernel::axiom_footprint`, and the environment's trusted surface (`Axiom` +
//! `Opaque` + `Quotient`) must still be **empty** afterwards. Either failing
//! exits non-zero: the whole point of the route is that it is free, so a probe
//! that could not report "not free" would be worthless.
//!
//! A zero from a measurement that cannot report anything else is not evidence,
//! so the probe carries a **negative control** in a second kernel: the exact
//! monomorphic instance of `funext` a Dedekind construction would need,
//!
//! ```text
//! Control.funext_seq : ∀ (f g : Nat → Rat),
//!   (∀ (n : Nat), Eq.{1} Rat (f n) (g n)) → Eq.{1} (Nat → Rat) f g
//! ```
//!
//! declared as an `Axiom` and consumed by a theorem. That theorem's footprint
//! must come back **non-empty and naming it**. If it does not, the footprint
//! machinery is blind and this probe's zeros mean nothing — so that also
//! exits non-zero.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example creal_shape_probe
//! ```

#![allow(clippy::similar_names, clippy::too_many_lines)]

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, ReducibilityHint, build_int_prelude,
};

fn main() {
    let mut kernel = Kernel::new();
    let int = build_int_prelude(&mut kernel).expect("the Int/Rat development must build");
    let anon = kernel.anon();

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let prop = kernel.sort(zero);
    let type0 = kernel.sort(one);

    let nat_ty = kernel.const_(int.nat.nat, vec![]);
    let rat_ty = kernel.const_(int.rat, vec![]);
    // `Nat → Rat`, the representative type. Its own sort is `Type 0`, which is
    // question (1): a field of this type does not push the carrier up a level.
    let seq_ty = kernel.pi(anon, nat_ty, rat_ty, BinderInfo::Default);
    // `(Nat → Rat) → Prop`, the regularity predicate's type: `Type 0` as well.
    let reg_ty = kernel.pi(anon, seq_ty, prop, BinderInfo::Default);

    let creal_root = kernel.name_str(anon, "CReal");
    let of = kernel.name_str(creal_root, "Of");
    let of_mk = kernel.name_str(of, "mk");
    let of_rec = kernel.name_str(of, "rec");
    let of_seq = kernel.name_str(of, "seq");
    let of_equiv_by = kernel.name_str(of, "EquivBy");

    // --- (1) + (2): the carrier ---------------------------------------------
    //
    //   CReal.Of (reg : (Nat → Rat) → Prop) : Type
    //   CReal.Of.mk : (f : Nat → Rat) → reg f → CReal.Of reg
    //
    // One parameter, one constructor, a function field and a dependent `Prop`
    // field over it. `Rat` itself is this same shape with `Int`/`Nat` fields.
    let of_ty = kernel.pi(anon, reg_ty, type0, BinderInfo::Default);
    let mk_ty = {
        // Under binders `reg` (BVar 1 at the field) and `f` (BVar 0):
        //   result `CReal.Of reg`
        let of_reg_2 = {
            let head = kernel.const_(of, vec![]);
            let reg = kernel.bvar(2);
            kernel.app(head, reg)
        };
        let reg_f = {
            let reg = kernel.bvar(1);
            let f = kernel.bvar(0);
            kernel.app(reg, f)
        };
        let after_proof = kernel.pi(anon, reg_f, of_reg_2, BinderInfo::Default);
        let after_seq = kernel.pi(anon, seq_ty, after_proof, BinderInfo::Default);
        kernel.pi(anon, reg_ty, after_seq, BinderInfo::Default)
    };
    kernel
        .add_inductive(of, &[], 1, of_ty, &[(of_mk, mk_ty)])
        .expect("(1)+(2) the regular-representative carrier must be admissible");

    // --- (3): the representative projection, by large elimination ------------
    //
    //   CReal.Of.seq (reg) (x : CReal.Of reg) : Nat → Rat
    //     := CReal.Of.rec reg (fun _ => Nat → Rat) (fun f _ => f) x
    //
    // The motive lands in `Type 0` while the carrier has a `Prop` field, so
    // this is the large-elimination question. `CReal.Of` is a `Type`-valued
    // inductive, so it should be allowed; a `Prop`-valued one would not be.
    let seq_ty_decl = {
        let of_reg = {
            let head = kernel.const_(of, vec![]);
            let reg = kernel.bvar(0);
            kernel.app(head, reg)
        };
        let body = kernel.pi(anon, of_reg, seq_ty, BinderInfo::Default);
        kernel.pi(anon, reg_ty, body, BinderInfo::Default)
    };
    let seq_value = {
        // fun (reg) (x) => CReal.Of.rec reg (fun _ => Nat → Rat) (fun f _ => f) x
        let rec_head = kernel.const_(of_rec, vec![one]);
        let reg = kernel.bvar(1);
        let applied_reg = kernel.app(rec_head, reg);
        let motive = {
            let of_reg = {
                let head = kernel.const_(of, vec![]);
                let reg = kernel.bvar(1);
                kernel.app(head, reg)
            };
            kernel.lam(anon, of_reg, seq_ty, BinderInfo::Default)
        };
        let applied_motive = kernel.app(applied_reg, motive);
        let minor = {
            let reg_f = {
                let reg = kernel.bvar(2);
                let f = kernel.bvar(0);
                kernel.app(reg, f)
            };
            let inner = {
                let f = kernel.bvar(1);
                kernel.lam(anon, reg_f, f, BinderInfo::Default)
            };
            kernel.lam(anon, seq_ty, inner, BinderInfo::Default)
        };
        let applied_minor = kernel.app(applied_motive, minor);
        let x = kernel.bvar(0);
        let applied = kernel.app(applied_minor, x);
        let of_reg = {
            let head = kernel.const_(of, vec![]);
            let reg = kernel.bvar(0);
            kernel.app(head, reg)
        };
        let inner = kernel.lam(anon, of_reg, applied, BinderInfo::Default);
        kernel.lam(anon, reg_ty, inner, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Definition {
            name: of_seq,
            uparams: vec![],
            ty: seq_ty_decl,
            value: seq_value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("(3) the representative projection must check by large elimination");

    // --- (4): the setoid relation over the projection -------------------------
    //
    //   CReal.Of.EquivBy (reg) (close : Rat → Rat → Nat → Prop)
    //                    (x y : CReal.Of reg) : Prop
    //     := ∀ (n : Nat), close (seq reg x n) (seq reg y n) n
    //
    // This is the shape `Equiv` takes once `ℚ`'s order supplies `close`, and
    // the shape every congruence obligation (`add`, `mul`, `neg`, `le`, `lt`
    // respect `Equiv`) is stated against. `close` is a parameter here for
    // <!-- was-absent: Rat.le -->
    // exactly the reason `reg` is: `Rat.le` does not exist yet.
    let close_ty = {
        let n = kernel.pi(anon, nat_ty, prop, BinderInfo::Default);
        let b = kernel.pi(anon, rat_ty, n, BinderInfo::Default);
        kernel.pi(anon, rat_ty, b, BinderInfo::Default)
    };
    let equiv_ty = {
        let of_reg = |k: &mut Kernel, depth: u32| {
            let head = k.const_(of, vec![]);
            let reg = k.bvar(depth);
            k.app(head, reg)
        };
        let x_ty = of_reg(&mut kernel, 1);
        let y_ty = of_reg(&mut kernel, 2);
        let after_y = kernel.pi(anon, y_ty, prop, BinderInfo::Default);
        let after_x = kernel.pi(anon, x_ty, after_y, BinderInfo::Default);
        let after_close = kernel.pi(anon, close_ty, after_x, BinderInfo::Default);
        kernel.pi(anon, reg_ty, after_close, BinderInfo::Default)
    };
    let equiv_value = {
        // under reg(4) close(3) x(2) y(1) n(0)
        let sample = |k: &mut Kernel, arg: u32| {
            let head = k.const_(of_seq, vec![]);
            let reg = k.bvar(4);
            let applied = k.app(head, reg);
            let point = k.bvar(arg);
            let at_point = k.app(applied, point);
            let n = k.bvar(0);
            k.app(at_point, n)
        };
        let xs = sample(&mut kernel, 2);
        let ys = sample(&mut kernel, 1);
        let close = kernel.bvar(3);
        let a = kernel.app(close, xs);
        let b = kernel.app(a, ys);
        let n = kernel.bvar(0);
        let body = kernel.app(b, n);
        let forall_n = kernel.pi(anon, nat_ty, body, BinderInfo::Default);

        let of_reg = |k: &mut Kernel, depth: u32| {
            let head = k.const_(of, vec![]);
            let reg = k.bvar(depth);
            k.app(head, reg)
        };
        let y_ty = of_reg(&mut kernel, 2);
        let l_y = kernel.lam(anon, y_ty, forall_n, BinderInfo::Default);
        let x_ty = of_reg(&mut kernel, 1);
        let l_x = kernel.lam(anon, x_ty, l_y, BinderInfo::Default);
        let l_close = kernel.lam(anon, close_ty, l_x, BinderInfo::Default);
        kernel.lam(anon, reg_ty, l_close, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Definition {
            name: of_equiv_by,
            uparams: vec![],
            ty: equiv_ty,
            value: equiv_value,
            hint: ReducibilityHint::Regular(2),
        })
        .expect("(4) the setoid relation over the projection must check in Prop");

    // --- the finding ----------------------------------------------------------
    let admitted = [of, of_mk, of_rec, of_seq, of_equiv_by];
    let mut failed = false;
    println!("declaration\tfootprint");
    for name in admitted {
        let footprint = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|a| kernel.display_name(a).to_string())
            .collect::<Vec<_>>();
        println!(
            "{}\t{}",
            kernel.display_name(name),
            if footprint.is_empty() {
                "-".to_owned()
            } else {
                footprint.join(",")
            }
        );
        if !footprint.is_empty() {
            failed = true;
        }
    }

    // --- the negative control -------------------------------------------------
    //
    // The same measurement, run where the answer must NOT be zero.
    let (control_name, control_footprint) = funext_control();
    println!("{control_name}\t{}", control_footprint.join(","));
    if control_footprint.is_empty() {
        eprintln!(
            "FAIL: the negative control ({control_name}) reported an EMPTY footprint. \
             The footprint measurement is blind, so the zeros above are not evidence."
        );
        std::process::exit(1);
    }

    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    if !trusted.is_empty() {
        failed = true;
    }

    eprintln!(
        "CReal.Of over the constructed Rat: {} declarations admitted, \
         trusted surface = {} ({})",
        admitted.len(),
        trusted.len(),
        if trusted.is_empty() {
            "empty".to_owned()
        } else {
            trusted.join(",")
        }
    );
    if failed {
        eprintln!(
            "FAIL: the setoid carrier is NOT free — see the footprints above. \
             ADR-0512's cost claim does not hold."
        );
        std::process::exit(1);
    }
    eprintln!(
        "the setoid carrier for ℝ costs ZERO trusted declarations \
         (control: {} = {}); regularity and closeness are parameters pending \
         ℚ's order development",
        control_name,
        control_footprint.join(",")
    );
}

/// The negative control: `funext` at `Nat → Rat` — the axiom a **Dedekind**
/// construction needs to prove two cuts with the same members equal, and which
/// the setoid route is chosen to avoid — declared and then consumed, so its
/// footprint is measured rather than assumed.
///
/// Returns the consuming theorem's name and its measured footprint. A
/// non-empty footprint naming the axiom is the expected result; an empty one
/// means [`Kernel::axiom_footprint`] cannot see through this shape and the
/// probe's zeros are worthless.
fn funext_control() -> (String, Vec<String>) {
    let mut kernel = Kernel::new();
    let int = build_int_prelude(&mut kernel).expect("the Int/Rat development must build");
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);

    let nat_ty = kernel.const_(int.nat.nat, vec![]);
    let rat_ty = kernel.const_(int.rat, vec![]);
    let seq_ty = kernel.pi(anon, nat_ty, rat_ty, BinderInfo::Default);

    // `Eq.{1} α a b` and `Eq.refl.{1} α a`.
    let eq3 = |k: &mut Kernel, ty: ExprId, a: ExprId, b: ExprId| {
        let head = k.const_(int.logic.eq, vec![one]);
        let at_ty = k.app(head, ty);
        let at_a = k.app(at_ty, a);
        k.app(at_a, b)
    };

    let control = kernel.name_str(anon, "Control");
    let funext = kernel.name_str(control, "funext_seq");
    let consumer = kernel.name_str(control, "seq_eq_self");

    // funext_seq : ∀ (f g : Nat → Rat),
    //                (∀ (n : Nat), Eq.{1} Rat (f n) (g n)) → Eq.{1} (Nat → Rat) f g
    let funext_ty = {
        let pointwise = {
            let fn_ = kernel.bvar(2);
            let gn = kernel.bvar(1);
            let n = kernel.bvar(0);
            let f_at = kernel.app(fn_, n);
            let g_at = kernel.app(gn, n);
            let body = eq3(&mut kernel, rat_ty, f_at, g_at);
            kernel.pi(anon, nat_ty, body, BinderInfo::Default)
        };
        let conclusion = {
            let f = kernel.bvar(2);
            let g = kernel.bvar(1);
            eq3(&mut kernel, seq_ty, f, g)
        };
        let after_h = kernel.pi(anon, pointwise, conclusion, BinderInfo::Default);
        let after_g = kernel.pi(anon, seq_ty, after_h, BinderInfo::Default);
        kernel.pi(anon, seq_ty, after_g, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Axiom {
            name: funext,
            uparams: vec![],
            ty: funext_ty,
        })
        .expect("the control axiom must check");

    // seq_eq_self : ∀ (f : Nat → Rat), Eq.{1} (Nat → Rat) f f
    //   := fun f => funext_seq f f (fun n => Eq.refl.{1} Rat (f n))
    let consumer_ty = {
        let f = kernel.bvar(0);
        let body = eq3(&mut kernel, seq_ty, f, f);
        kernel.pi(anon, seq_ty, body, BinderInfo::Default)
    };
    let consumer_value = {
        let witness = {
            let refl = kernel.const_(int.logic.eq_refl, vec![one]);
            let at_ty = kernel.app(refl, rat_ty);
            let f = kernel.bvar(1);
            let n = kernel.bvar(0);
            let f_at = kernel.app(f, n);
            let applied = kernel.app(at_ty, f_at);
            kernel.lam(anon, nat_ty, applied, BinderInfo::Default)
        };
        let head = kernel.const_(funext, vec![]);
        let f = kernel.bvar(0);
        let a = kernel.app(head, f);
        let f = kernel.bvar(0);
        let b = kernel.app(a, f);
        let applied = kernel.app(b, witness);
        kernel.lam(anon, seq_ty, applied, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Theorem {
            name: consumer,
            uparams: vec![],
            ty: consumer_ty,
            value: consumer_value,
        })
        .expect("the control consumer must check against the axiom");

    let footprint = kernel
        .axiom_footprint(consumer)
        .into_iter()
        .map(|a| kernel.display_name(a).to_string())
        .collect();
    (kernel.display_name(consumer).to_string(), footprint)
}
