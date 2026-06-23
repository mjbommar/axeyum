//! Alethe proof **emission** for the array (`QF_ABV`) read-over-write-same
//! disequality fragment (Track 3, phase P3.5) — the producer counterpart to the
//! `QF_BV`/EUF/LRA emitters ([`crate::prove_qf_bv_unsat_alethe`] /
//! [`crate::prove_qf_uf_unsat_alethe`] / [`crate::prove_lra_unsat_alethe`]).
//!
//! [`prove_qf_abv_unsat_alethe`] builds a complete, **in-tree-checkable** Alethe
//! refutation closing to the empty clause `(cl)` for a `QF_ABV` conjunction that
//! contains at least one asserted **read-over-write-same disequality**:
//!
//! ```text
//! (not (= (select (store a i v) i) v))      ; or the symmetric
//! (not (= v (select (store a i v) i)))
//! ```
//!
//! Such an assertion is UNSAT *on its own* — `select(store(a, i, v), i) = v` is the
//! read-over-write axiom's same-index instance (the `i = j` case), valid for **all**
//! `a`, `i`, `v` — so if any assertion in the conjunction has that shape the whole
//! problem is unsat. A binary `(distinct sel v)` lowers to exactly the same
//! `(not (= sel v))` IR (the [`crate::distinct`] helper builds `(not (= …))` for two
//! operands), so it is covered by the same matcher.
//!
//! The emitted proof is the three-step refutation
//!
//! ```text
//! (assume h  (not (= (select (store a i v) i) v)))
//! (step    rw   (cl (= (select (store a i v) i) v)) :rule read_over_write_same)
//! (step    done (cl) :rule resolution :premises (rw h))
//! ```
//!
//! where `read_over_write_same` is an **axeyum-internal** Alethe rule (Alethe/Carcara
//! has no array theory rules; see
//! `docs/research/07-verification/array-elimination-alethe-proofs.md`), structurally
//! checked by the in-tree [`axeyum_cnf::check_alethe`]. The emitter is
//! **self-validating**: it returns `Some(proof)` only after `check_alethe` accepts the
//! proof, so a returned certificate is always genuinely checkable.

use axeyum_cnf::{
    AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe, check_alethe_with,
};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// Emits a complete, in-tree-checkable Alethe refutation for a `QF_ABV`
/// conjunction containing a **read-over-write-same disequality**, or [`None`] when
/// no assertion matches that fragment (or the built proof fails self-validation).
///
/// An assertion matches when it is `(not (= sel rhs))` or `(not (= rhs sel))` (the
/// symmetric form), where
///
/// - `sel == (select (store a i v) j)` — a `select` of a `store`, with the read
///   index `j` **structurally identical** to the write index `i` (same [`TermId`],
///   since the arena hash-conses), and
/// - `rhs == v` — structurally identical to the stored value.
///
/// A binary `(distinct sel rhs)` is also matched: the [`crate::distinct`] builder
/// lowers it to the very same `(not (= sel rhs))` IR.
///
/// The returned proof is the three-command refutation `assume`/`read_over_write_same`/
/// `resolution` closing to the empty clause `(cl)`, with deterministic step ids. It is
/// returned only after [`axeyum_cnf::check_alethe`] accepts it.
///
/// Returns [`None`] when no assertion is a read-over-write-same disequality, when the
/// matched terms render outside the small array fragment (`select`/`store`/symbol/
/// bit-vector-constant), or — defensively — when self-validation fails.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_abv_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Scan for the first assertion that is a read-over-write-same disequality.
    // If none, fall back to the congruence/extensionality route: `select`/`store`
    // are treated as uninterpreted functions, so the EUF congruence emitter proves
    // e.g. `a = b ∧ select(a, k) ≠ select(b, k)` (array extensionality). That
    // emitter is itself self-validating against `check_alethe`.
    let Some((sel, rhs)) = assertions
        .iter()
        .find_map(|&assertion| match_row_same_diseq(arena, assertion))
    else {
        return crate::prove_qf_uf_unsat_alethe(arena, assertions);
    };

    // Render `(= sel rhs)` exactly as the `read_over_write_same` rule expects.
    let sel_alethe = array_term_to_alethe(arena, sel)?;
    let rhs_alethe = array_term_to_alethe(arena, rhs)?;
    let equality = AletheTerm::App("=".to_owned(), vec![sel_alethe, rhs_alethe]);

    // (assume h (not (= sel rhs))) — the assumed disequality, a negated equality.
    let assume_clause: AletheClause = vec![AletheLit {
        atom: equality.clone(),
        negated: true,
    }];
    // (step rw (cl (= sel rhs)) :rule read_over_write_same)
    let rw_clause: AletheClause = vec![AletheLit {
        atom: equality,
        negated: false,
    }];

    let proof = vec![
        AletheCommand::Assume {
            id: "h".to_owned(),
            clause: assume_clause,
        },
        AletheCommand::Step {
            id: "rw".to_owned(),
            clause: rw_clause,
            rule: "read_over_write_same".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        },
        // (step done (cl) :rule resolution :premises (rw h)) — resolve the axiom
        // equality against its negation to the empty clause.
        AletheCommand::Step {
            id: "done".to_owned(),
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: vec!["rw".to_owned(), "h".to_owned()],
            args: Vec::new(),
        },
    ];

    // Self-validate: only hand back a certificate the in-tree checker accepts.
    // If the read-over-write-same proof did not validate (e.g. a subterm outside
    // the rendered fragment), still try the congruence/extensionality route.
    match check_alethe(&proof) {
        Ok(true) => Some(proof),
        _ => crate::prove_qf_uf_unsat_alethe(arena, assertions),
    }
}

/// If `assertion` is `(not (= sel rhs))` or `(not (= rhs sel))` where `sel` is a
/// read-over-write-same select `(select (store a i v) i)` and `rhs` is the stored
/// value `v`, returns `(sel, rhs)`; otherwise [`None`].
fn match_row_same_diseq(arena: &TermArena, assertion: TermId) -> Option<(TermId, TermId)> {
    // Peel a single `not`.
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let &[inner] = &args[..] else {
        return None;
    };
    // The inner term must be a binary equality `(= x y)`.
    let TermNode::App {
        op: Op::Eq,
        args: eq_args,
    } = arena.node(inner)
    else {
        return None;
    };
    let &[x, y] = &eq_args[..] else {
        return None;
    };
    // Either operand may be the ROW-same select; the other is then the stored value.
    if let Some(v) = row_same_value(arena, x)
        && v == y
    {
        return Some((x, y));
    }
    if let Some(v) = row_same_value(arena, y)
        && v == x
    {
        return Some((y, x));
    }
    None
}

/// If `term` is a read-over-write-same select `(select (store a i v) i)` — the read
/// index structurally identical to the write index — returns the stored value `v`;
/// otherwise [`None`].
fn row_same_value(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::Select,
        args: sel_args,
    } = arena.node(term)
    else {
        return None;
    };
    let &[inner, read_idx] = &sel_args[..] else {
        return None;
    };
    let TermNode::App {
        op: Op::Store,
        args: store_args,
    } = arena.node(inner)
    else {
        return None;
    };
    let &[_array, write_idx, value] = &store_args[..] else {
        return None;
    };
    // The read index must be structurally identical to the write index (same
    // hash-consed `TermId`).
    if read_idx == write_idx {
        Some(value)
    } else {
        None
    }
}

/// Renders an array-fragment IR term to [`AletheTerm`]: a symbol becomes
/// `Const(name)`; a bit-vector constant becomes its `#b…`/`#x…` literal; a `select`
/// becomes `(select arr idx)`; a `store` becomes `(store arr idx val)`. Any other
/// node yields [`None`].
fn array_term_to_alethe(arena: &TermArena, term: TermId) -> Option<AletheTerm> {
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            let (name, _sort) = arena.symbol(*symbol);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(bv_const_literal(*width, *value)))
        }
        TermNode::App { op, args } => {
            let head = match op {
                Op::Select => "select",
                Op::Store => "store",
                _ => return None,
            };
            let rendered = args
                .iter()
                .map(|&arg| array_term_to_alethe(arena, arg))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(head.to_owned(), rendered))
        }
        _ => None,
    }
}

/// The SMT-LIB bit-vector-constant binary literal `#b…` for `value` at `width`,
/// MSB-first. Mirrors the renderer in [`crate::bitblast_alethe`] verbatim so a
/// rendered constant matches the rest of the proof stack byte-for-byte.
fn bv_const_literal(width: u32, value: u128) -> String {
    let mut out = String::with_capacity(2 + width as usize);
    out.push_str("#b");
    // MSB-first: bit (width-1) down to bit 0.
    for i in (0..width).rev() {
        let bit = (value >> i) & 1;
        out.push(if bit == 1 { '1' } else { '0' });
    }
    out
}

/// Emits a **Carcara-checkable** refutation of a `QF_ABV` read-over-write-same
/// disequality, deriving `select(store(a, i, v), i) = v` from the *general*
/// read-over-write rewrite instance through Carcara's own `eq_simplify`,
/// `cong`, `ite_simplify`, and `trans` rules — instead of the axeyum-internal
/// premise-free `read_over_write_same` rule used by [`prove_qf_abv_unsat_alethe`].
///
/// ## Why this is a tighter certificate than `read_over_write_same`
///
/// [`prove_qf_abv_unsat_alethe`] discharges the same-index read with a single
/// premise-free `read_over_write_same` step, an **axeyum-internal** Alethe rule:
/// Alethe/Carcara has no array theory rules, so that step is checkable only by
/// the in-tree [`axeyum_cnf::check_alethe`], never by Carcara. The trusted
/// surface is the whole collapsed equality `(= (select (store a i v) i) v)`.
///
/// This emitter shrinks that surface to a *more primitive* premise — the
/// **read-over-write rewrite instance**
///
/// ```text
/// (= (select (store a i v) i) (ite (= i i) v (select a i)))
/// ```
///
/// — and then derives the same-index collapse `(ite (= i i) v _) = v` with
/// rules Carcara checks in full:
///
/// ```text
/// (assume rw (= (select (store a i v) i) (ite (= i i) v (select a i))))
/// (assume h  (not (= (select (store a i v) i) v)))
/// (step s1 (cl (= (= i i) true)) :rule eq_simplify)
/// (step s2 (cl (= (ite (= i i) v (select a i)) (ite true v (select a i)))) :rule cong :premises (s1))
/// (step s3 (cl (= (ite true v (select a i)) v)) :rule ite_simplify)
/// (step s4 (cl (= (ite (= i i) v (select a i)) v)) :rule trans :premises (s2 s3))
/// (step s5 (cl (= (select (store a i v) i) v)) :rule trans :premises (rw s4))
/// (step s6 (cl) :rule resolution :premises (s5 h))
/// ```
///
/// **Honest boundary.** This certifies the *same-index collapse reasoning*
/// externally; the read-over-write rewrite *instance* (`rw`) is still an array
/// fact, asserted as a premise in the `QF_AUFBV` problem. It is strictly more
/// primitive than the in-tree rule (the general select-of-store rewrite, the one
/// axiom every array solver rests on), and the `(= i i) → true` / `ite true`
/// folding that turns it into the same-index equality is now Carcara-checked
/// rather than baked into a trusted rule. This does **not** certify the array
/// axiom itself, and it does not replace [`prove_qf_abv_unsat_alethe`] in the
/// solving path — it is an additional, externally-anchored certificate.
///
/// Returns the `assume rw` premise term alongside the proof so the caller can
/// emit the matching `QF_AUFBV` problem (the `rw` `assume` must match a problem
/// premise for Carcara). Returns [`None`] when no assertion is a
/// read-over-write-same disequality or the matched terms render outside the
/// array fragment.
///
/// Self-validation uses [`axeyum_cnf::check_alethe_with`] with a narrow hook that
/// accepts `eq_simplify` only for `(= (= t t) true)` and `ite_simplify` only for
/// `(= (ite true x _) x)` — the exact two shapes emitted; Carcara is the trust
/// anchor for them. The proof is returned only after that re-check passes.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_abv_row_same_alethe_carcara(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Vec<AletheCommand>, AletheTerm)> {
    // Find the first read-over-write-same disequality and recover (a, i, v).
    let (a, i, v) = assertions
        .iter()
        .find_map(|&assertion| match_row_same_parts(arena, assertion))?;

    // Render the array-fragment subterms.
    let a_t = array_term_to_alethe(arena, a)?;
    let i_t = array_term_to_alethe(arena, i)?;
    let v_t = array_term_to_alethe(arena, v)?;

    // `(select (store a i v) i)`, `(select a i)`, `(= i i)`, `(ite (= i i) v (select a i))`.
    let store_t = AletheTerm::App(
        "store".to_owned(),
        vec![a_t.clone(), i_t.clone(), v_t.clone()],
    );
    let sel_store = AletheTerm::App("select".to_owned(), vec![store_t, i_t.clone()]);
    let sel_a = AletheTerm::App("select".to_owned(), vec![a_t, i_t.clone()]);
    let eq_ii = AletheTerm::App("=".to_owned(), vec![i_t.clone(), i_t]);
    let true_t = AletheTerm::Const("true".to_owned());
    let ite_cond = AletheTerm::App(
        "ite".to_owned(),
        vec![eq_ii.clone(), v_t.clone(), sel_a.clone()],
    );
    let ite_true = AletheTerm::App("ite".to_owned(), vec![true_t.clone(), v_t.clone(), sel_a]);

    // The read-over-write rewrite instance, the `rw` premise (returned for the problem).
    let rw_atom = eq(sel_store.clone(), ite_cond.clone());
    // The refuted disequality `(not (= (select (store a i v) i) v))`.
    let goal_eq = eq(sel_store.clone(), v_t.clone());

    let proof = vec![
        AletheCommand::Assume {
            id: "rw".to_owned(),
            clause: vec![pos(rw_atom.clone())],
        },
        AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![neg(goal_eq.clone())],
        },
        // s1: (= (= i i) true) by eq_simplify.
        step(
            "s1",
            vec![pos(eq(eq_ii.clone(), true_t))],
            "eq_simplify",
            &[],
        ),
        // s2: cong lifting `(= i i) = true` under the `ite` head.
        step(
            "s2",
            vec![pos(eq(ite_cond.clone(), ite_true.clone()))],
            "cong",
            &["s1"],
        ),
        // s3: (= (ite true v (select a i)) v) by ite_simplify.
        step(
            "s3",
            vec![pos(eq(ite_true, v_t.clone()))],
            "ite_simplify",
            &[],
        ),
        // s4: (= (ite (= i i) v (select a i)) v) by trans s2,s3.
        step(
            "s4",
            vec![pos(eq(ite_cond, v_t.clone()))],
            "trans",
            &["s2", "s3"],
        ),
        // s5: (= (select (store a i v) i) v) by trans rw,s4.
        step("s5", vec![pos(goal_eq)], "trans", &["rw", "s4"]),
        // s6: empty clause by resolving s5 against the assumed disequality.
        step("s6", Vec::new(), "resolution", &["s5", "h"]),
    ];

    // Self-validate with the narrow simplify hook; Carcara is the trust anchor.
    let accepted = matches!(check_alethe_with(&proof, &row_same_simplify_hook), Ok(true));
    accepted.then_some((proof, rw_atom))
}

/// If `assertion` is a read-over-write-same disequality, returns the array `a`,
/// the (shared read/write) index `i`, and the stored value `v` as [`TermId`]s.
fn match_row_same_parts(arena: &TermArena, assertion: TermId) -> Option<(TermId, TermId, TermId)> {
    let (sel, _rhs) = match_row_same_diseq(arena, assertion)?;
    // `sel == (select (store a i v) i)`; recover (a, i, v) from the store.
    let TermNode::App {
        op: Op::Select,
        args: sel_args,
    } = arena.node(sel)
    else {
        return None;
    };
    let &[inner, idx] = &sel_args[..] else {
        return None;
    };
    let TermNode::App {
        op: Op::Store,
        args: store_args,
    } = arena.node(inner)
    else {
        return None;
    };
    let &[array, write_idx, value] = &store_args[..] else {
        return None;
    };
    debug_assert!(
        idx == write_idx,
        "match_row_same_diseq guarantees read == write index"
    );
    Some((array, write_idx, value))
}

/// The narrow self-validation hook for [`prove_qf_abv_row_same_alethe_carcara`]:
/// accepts `eq_simplify` only when the clause is the unit `(= (= t t) true)`, and
/// `ite_simplify` only when it is the unit `(= (ite true x _) x)`. Every other
/// rule defers (`None`). These are the two exact shapes the emitter produces and
/// are precisely the simplifications Carcara independently checks.
fn row_same_simplify_hook(rule: &str, clause: &[AletheLit]) -> Option<bool> {
    let [lit] = clause else {
        return Some(false);
    };
    if lit.negated {
        return Some(false);
    }
    match rule {
        // (= (= t t) true)
        "eq_simplify" => {
            let AletheTerm::App(head, args) = &lit.atom else {
                return Some(false);
            };
            if head != "=" || args.len() != 2 {
                return Some(false);
            }
            let inner_is_self_eq = matches!(
                &args[0],
                AletheTerm::App(h, a) if h == "=" && a.len() == 2 && a[0] == a[1]
            );
            let rhs_is_true = matches!(&args[1], AletheTerm::Const(c) if c == "true");
            Some(inner_is_self_eq && rhs_is_true)
        }
        // (= (ite true x _) x)
        "ite_simplify" => {
            let AletheTerm::App(head, args) = &lit.atom else {
                return Some(false);
            };
            if head != "=" || args.len() != 2 {
                return Some(false);
            }
            let AletheTerm::App(ite_head, ite_args) = &args[0] else {
                return Some(false);
            };
            let well_formed = ite_head == "ite"
                && ite_args.len() == 3
                && matches!(&ite_args[0], AletheTerm::Const(c) if c == "true");
            Some(well_formed && ite_args[1] == args[1])
        }
        _ => None,
    }
}

/// `(= a b)`.
fn eq(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![a, b])
}

/// A positive literal.
fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

/// A negated literal.
fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

/// A `step` command with the given id, clause, rule, and premise ids (no args).
fn step(id: &str, clause: AletheClause, rule: &str, premises: &[&str]) -> AletheCommand {
    AletheCommand::Step {
        id: id.to_owned(),
        clause,
        rule: rule.to_owned(),
        premises: premises.iter().map(|p| (*p).to_owned()).collect(),
        args: Vec::new(),
    }
}
