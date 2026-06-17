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

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
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
    let (sel, rhs) = assertions
        .iter()
        .find_map(|&assertion| match_row_same_diseq(arena, assertion))?;

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
    match check_alethe(&proof) {
        Ok(true) => Some(proof),
        _ => None,
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
