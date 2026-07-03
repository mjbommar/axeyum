//! Hand-built equivalence-class cases for the T-B.2 flat/normal-form slice:
//! two-variable concat alignment, the cvc5 running decomposition example,
//! constant-prefix agreement, ε-collapse, a containment cycle (must *decline*,
//! not hang), an unreconcilable constant clash, and a byte-for-byte determinism
//! check.

mod common;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{Classes, Declined, NormalForm, Unreconciled};
use common::{cat, ch, empty, seq_sort, unit};

/// Declares a `Seq(BitVec 8)` variable, returning `(symbol, term)` so tests can
/// bind it in an assignment.
fn svar(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, seq_sort()).expect("declare seq var");
    (s, arena.var(s))
}

/// A concrete `Seq(Bv 8)` value from raw bytes.
fn seqval(bytes: &[u8]) -> Value {
    Value::Seq(
        bytes
            .iter()
            .map(|&b| Value::Bv {
                width: 8,
                value: u128::from(b),
            })
            .collect(),
    )
}

/// Concatenates the normal-form components into one sequence term (ε when
/// empty) and evaluates it under `asg`.
fn eval_nf(arena: &mut TermArena, nf: &NormalForm, asg: &Assignment) -> Value {
    let term = if nf.components.is_empty() {
        empty(arena)
    } else {
        // Right-associate to match the canonical spine.
        let parts = &nf.components;
        let mut acc = *parts.last().expect("non-empty");
        for &p in parts[..parts.len() - 1].iter().rev() {
            acc = cat(arena, p, acc);
        }
        acc
    };
    eval(arena, term, asg).expect("eval nf concat")
}

// ----- two-variable concat equality, lengths force alignment -----------------

#[test]
fn two_variable_concat_alignment() {
    // (x ++ y) = (a ++ b), with x = a and y = b so the two decompositions align
    // position-for-position.
    let mut arena = TermArena::new();
    let (xs, x) = svar(&mut arena, "x");
    let (ys, y) = svar(&mut arena, "y");
    let (as_, a) = svar(&mut arena, "a");
    let (bs, b) = svar(&mut arena, "b");
    let xy = cat(&mut arena, x, y);
    let ab = cat(&mut arena, a, b);

    let eqs = [(xy, ab), (x, a), (y, b)];
    let classes = Classes::new(&eqs);
    let forms = classes.normal_forms(&mut arena).expect("no decline");

    // The class of xy/ab has a two-component normal form [rep{x,a}, rep{y,b}].
    let rep = classes.representative(xy);
    let nf = forms.get(rep).expect("normal form for the concat class");
    assert_eq!(nf.components.len(), 2, "aligned concat has two components");
    assert_eq!(nf.components[0], classes.representative(x));
    assert_eq!(nf.components[1], classes.representative(y));

    // It evaluates to the same sequence as either member under any assignment.
    let mut asg = Assignment::new();
    asg.set(xs, seqval(b"foo"));
    asg.set(ys, seqval(b"bar"));
    asg.set(as_, seqval(b"foo"));
    asg.set(bs, seqval(b"bar"));
    let member = eval(&arena, xy, &asg).expect("eval member");
    let via_nf = eval_nf(&mut arena, nf, &asg);
    assert_eq!(member, via_nf, "normal form denotes the member");
}

// ----- the cvc5 running example: bottom-up decomposition ----------------------

#[test]
#[allow(clippy::many_single_char_names)] // deliberately mirrors the paper's x,y,z,u,v
fn cvc5_running_example_decomposes_bottom_up() {
    // { x = y, y = z, y = u ++ v, u = u1 ++ u2 }  ⇒  nf([x]) = (u1, u2, v)
    let mut arena = TermArena::new();
    let (xs, x) = svar(&mut arena, "x");
    let (ys, y) = svar(&mut arena, "y");
    let (zs, z) = svar(&mut arena, "z");
    let (u1s, u1) = svar(&mut arena, "u1");
    let (u2s, u2) = svar(&mut arena, "u2");
    let (vs, v) = svar(&mut arena, "v");
    let (us, u) = svar(&mut arena, "u");
    let uv = cat(&mut arena, u, v);
    let u1u2 = cat(&mut arena, u1, u2);

    let eqs = [(x, y), (y, z), (y, uv), (u, u1u2)];
    let classes = Classes::new(&eqs);
    let forms = classes.normal_forms(&mut arena).expect("no decline");

    let rep = classes.representative(x);
    let nf = forms.get(rep).expect("nf of [x]");
    assert_eq!(
        nf.components,
        vec![
            classes.representative(u1),
            classes.representative(u2),
            classes.representative(v)
        ],
        "nf([x]) must be (u1, u2, v)"
    );

    // The premise set is sufficient: only y=u++v (idx 2) and u=u1++u2 (idx 3)
    // plus the link x=y (idx 0) are cited; x=z / y=z are not needed.
    assert!(nf.premises.contains(&2), "cites y = u ++ v");
    assert!(nf.premises.contains(&3), "cites u = u1 ++ u2");
    assert!(!nf.premises.contains(&1), "does not need y = z");

    // Evaluates correctly.
    let mut asg = Assignment::new();
    asg.set(u1s, seqval(b"AB"));
    asg.set(u2s, seqval(b"C"));
    asg.set(vs, seqval(b"DE"));
    asg.set(us, seqval(b"ABC"));
    asg.set(xs, seqval(b"ABCDE"));
    asg.set(ys, seqval(b"ABCDE"));
    asg.set(zs, seqval(b"ABCDE"));
    let via_nf = eval_nf(&mut arena, nf, &asg);
    assert_eq!(via_nf, seqval(b"ABCDE"));
}

// ----- constant-prefix agreement ---------------------------------------------

#[test]
fn constant_prefix_agreement() {
    // x = "ab" ++ y  and  x = "ab" ++ w  with y = w: both members share the
    // constant prefix and a common tail class, so they reconcile.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_ys, y) = svar(&mut arena, "y");
    let (_ws, w) = svar(&mut arena, "w");
    let ca = ch(&mut arena, b'a'.into());
    let cb = ch(&mut arena, b'b'.into());
    let ua = unit(&mut arena, ca);
    let ub = unit(&mut arena, cb);
    let ab1 = cat(&mut arena, ua, ub);
    let pre_y = cat(&mut arena, ab1, y);
    let ab2 = cat(&mut arena, ua, ub);
    let pre_w = cat(&mut arena, ab2, w);

    let eqs = [(x, pre_y), (x, pre_w), (y, w)];
    let classes = Classes::new(&eqs);
    let forms = classes.normal_forms(&mut arena).expect("no decline");

    let nf = forms.get(classes.representative(x)).expect("nf of [x]");
    assert_eq!(nf.components.len(), 2, "[const-block, tail]");
    assert_eq!(
        eval(&arena, nf.components[0], &Assignment::new()).expect("const"),
        seqval(b"ab"),
        "constant prefix is 'ab'"
    );
    assert_eq!(nf.components[1], classes.representative(y));
}

// ----- ε-collapse -------------------------------------------------------------

#[test]
fn epsilon_collapses_out_of_normal_form() {
    // z = ε, x = z ++ y  ⇒  nf([x]) = (rep(y)),  the ε drops out.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_ys, y) = svar(&mut arena, "y");
    let (_zs, z) = svar(&mut arena, "z");
    let eps = empty(&mut arena);
    let zy = cat(&mut arena, z, y);

    let eqs = [(z, eps), (x, zy)];
    let classes = Classes::new(&eqs);
    let forms = classes.normal_forms(&mut arena).expect("no decline");

    // z's class normalizes to the empty vector.
    let nf_z = forms.get(classes.representative(z)).expect("nf of [z]");
    assert!(nf_z.components.is_empty(), "[z] is the ε class");

    // x's class drops the ε and keeps only y.
    let nf_x = forms.get(classes.representative(x)).expect("nf of [x]");
    assert_eq!(nf_x.components, vec![classes.representative(y)]);
}

// ----- containment cycle: decline, never hang --------------------------------

#[test]
fn self_containment_is_declined_as_cycle() {
    // x = x ++ y is a loop the later F-Loop device handles; T-B.2 declines.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_ys, y) = svar(&mut arena, "y");
    let xy = cat(&mut arena, x, y);

    let eqs = [(x, xy)];
    let classes = Classes::new(&eqs);
    match classes.normal_forms(&mut arena) {
        Err(Declined::Cycle { classes: cyc }) => {
            assert!(
                cyc.contains(&classes.representative(x)),
                "cycle names the offending class"
            );
        }
        other => panic!("expected Declined::Cycle, got {other:?}"),
    }
}

#[test]
fn two_class_cycle_is_declined() {
    // x = a ++ p, a = x ++ q : a mutual containment cycle.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_as, a) = svar(&mut arena, "a");
    let (_ps, p) = svar(&mut arena, "p");
    let (_qs, q) = svar(&mut arena, "q");
    let ap = cat(&mut arena, a, p);
    let xq = cat(&mut arena, x, q);

    let eqs = [(x, ap), (a, xq)];
    let classes = Classes::new(&eqs);
    assert!(
        matches!(
            classes.normal_forms(&mut arena),
            Err(Declined::Cycle { .. })
        ),
        "mutual containment must decline as a cycle"
    );
}

// ----- unreconcilable constant clash -----------------------------------------

#[test]
fn constant_clash_is_unreconciled() {
    // x = "a" and x = "b": two distinct constants in one class.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let ca = ch(&mut arena, b'a'.into());
    let cb = ch(&mut arena, b'b'.into());
    let ua = unit(&mut arena, ca);
    let ub = unit(&mut arena, cb);

    let eqs = [(x, ua), (x, ub)];
    let classes = Classes::new(&eqs);
    match classes.normal_forms(&mut arena) {
        Err(Declined::Unreconciled {
            class,
            kind: Unreconciled::ConstantClash,
        }) => {
            assert_eq!(class, classes.representative(x));
        }
        other => panic!("expected Unreconciled::ConstantClash, got {other:?}"),
    }
}

#[test]
fn shape_mismatch_is_unreconciled() {
    // x = a ++ b  and  x = "cd" (a constant), with a, b free variables: aligning
    // these needs arrangement splitting (T-B.4), so T-B.2 declines by shape.
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_as, a) = svar(&mut arena, "a");
    let (_bs, b) = svar(&mut arena, "b");
    let cc = ch(&mut arena, b'c'.into());
    let cd = ch(&mut arena, b'd'.into());
    let uc = unit(&mut arena, cc);
    let ud = unit(&mut arena, cd);
    let ab = cat(&mut arena, a, b);
    let cdblk = cat(&mut arena, uc, ud);

    let eqs = [(x, ab), (x, cdblk)];
    let classes = Classes::new(&eqs);
    assert!(
        matches!(
            classes.normal_forms(&mut arena),
            Err(Declined::Unreconciled {
                kind: Unreconciled::ShapeMismatch,
                ..
            })
        ),
        "variable-vs-constant shape needs T-B.4, must decline"
    );
}

// ----- explanation queries ----------------------------------------------------

#[test]
fn explain_returns_sufficient_premises() {
    let mut arena = TermArena::new();
    let (_xs, x) = svar(&mut arena, "x");
    let (_ys, y) = svar(&mut arena, "y");
    let (_zs, z) = svar(&mut arena, "z");
    let (_ws, w) = svar(&mut arena, "w");
    // x=y (0), y=z (1); w is unrelated.
    let eqs = [(x, y), (y, z)];
    let classes = Classes::new(&eqs);

    assert_eq!(classes.explain(x, x), Some([].into_iter().collect()));
    // x≈z needs both edges.
    let xz = classes.explain(x, z).expect("x and z related");
    assert_eq!(xz, [0usize, 1].into_iter().collect());
    // x≈y needs only edge 0.
    assert_eq!(classes.explain(x, y), Some([0usize].into_iter().collect()));
    // Unrelated terms have no explanation.
    assert_eq!(classes.explain(x, w), None);
}

// ----- determinism ------------------------------------------------------------

#[test]
#[allow(clippy::many_single_char_names)] // deliberately mirrors the paper's x,y,z,u,v
fn normal_forms_are_byte_identical_across_runs() {
    fn run() -> Vec<(TermId, NormalForm)> {
        let mut arena = TermArena::new();
        let (_xs, x) = svar(&mut arena, "x");
        let (_ys, y) = svar(&mut arena, "y");
        let (_zs, z) = svar(&mut arena, "z");
        let (_u1s, u1) = svar(&mut arena, "u1");
        let (_u2s, u2) = svar(&mut arena, "u2");
        let (_vs, v) = svar(&mut arena, "v");
        let (_us, u) = svar(&mut arena, "u");
        let uv = cat(&mut arena, u, v);
        let u1u2 = cat(&mut arena, u1, u2);
        let eqs = [(x, y), (y, z), (y, uv), (u, u1u2)];
        let classes = Classes::new(&eqs);
        let forms = classes.normal_forms(&mut arena).expect("no decline");
        forms.iter().map(|(r, nf)| (r, nf.clone())).collect()
    }

    let first = run();
    let second = run();
    assert_eq!(first, second, "normal-form output must be deterministic");
}
