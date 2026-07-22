//! Correctness tests for the data-structure slice: interning, level
//! `leq`/equiv (translated from nanoda's `tests/level.rs`), and the de Bruijn
//! operations (the soundness backbone of later type checking).
//!
//! These tests use short mathematical binding names (`p`, `q`, `a`, `b`, `m`,
//! `ss`, `sm`, …) matching the universe-algebra literature and nanoda's own
//! test names, so the relevant naming lints are relaxed module-wide.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::{BinderInfo, Kernel, Lit};

// ---------------------------------------------------------------------------
// Interning + determinism
// ---------------------------------------------------------------------------

#[test]
fn inference_caches_only_closed_successes() {
    let mut k = Kernel::new();
    let sort = k.sort_zero();
    let inferred = k.infer(sort).expect("closed sort infers");
    assert_eq!(k.infer_closed_cache.get(&sort), Some(&inferred));
    assert_eq!(k.infer(sort).unwrap(), inferred);

    let free = k.fvar(17);
    assert!(k.infer(free).is_err());
    assert!(!k.infer_closed_cache.contains_key(&free));

    let loose = k.bvar(0);
    assert!(k.infer(loose).is_err());
    assert!(!k.infer_closed_cache.contains_key(&loose));
}

#[test]
fn names_intern_structurally() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let a1 = k.name_str(anon, "a");
    let a2 = k.name_str(anon, "a");
    let b = k.name_str(anon, "b");
    assert_eq!(a1, a2);
    assert_ne!(a1, b);

    let a_1 = k.name_num(a1, 1);
    let a_1b = k.name_num(a2, 1);
    assert_eq!(a_1, a_1b);
}

#[test]
fn name_display_dotted() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let a = k.name_str(anon, "a");
    let ab = k.name_str(a, "b");
    let ab1 = k.name_num(ab, 1);
    assert_eq!(format!("{}", k.display_name(ab1)), "a.b.1");
    assert_eq!(format!("{}", k.display_name(anon)), "[anonymous]");
    assert_eq!(format!("{}", k.display_name(a)), "a");
}

#[test]
fn levels_intern_structurally() {
    let mut k = Kernel::new();
    let z1 = k.level_zero();
    let z2 = k.level_zero();
    assert_eq!(z1, z2);
    let s1 = k.level_succ(z1);
    let s2 = k.level_succ(z2);
    assert_eq!(s1, s2);
    let m1 = k.level_max(s1, z1);
    let m2 = k.level_max(s2, z2);
    assert_eq!(m1, m2);
    assert_ne!(m1, s1);
}

#[test]
fn exprs_intern_structurally() {
    let mut k = Kernel::new();
    let n = k.anon();
    let ty = k.sort_zero();
    let b1 = k.bvar(0);
    let b2 = k.bvar(0);
    assert_eq!(b1, b2);
    let lam1 = k.lam(n, ty, b1, BinderInfo::Default);
    let lam2 = k.lam(n, ty, b2, BinderInfo::Default);
    assert_eq!(lam1, lam2);

    let other = k.lam(n, ty, b1, BinderInfo::Implicit);
    assert_ne!(lam1, other);
}

#[test]
fn determinism_same_ids() {
    fn build() -> (usize, usize) {
        let mut k = Kernel::new();
        let n = k.anon();
        let a = k.name_str(n, "f");
        let c = k.const_(a, vec![]);
        let b = k.bvar(0);
        let ty = k.sort_zero();
        let lam = k.lam(n, ty, b, BinderInfo::Default);
        let app = k.app(lam, c);
        (app.index(), lam.index())
    }
    assert_eq!(build(), build());
}

// ---------------------------------------------------------------------------
// Level tests — translated from nanoda_lib/src/tests/level.rs
// ---------------------------------------------------------------------------

#[test]
fn leq_test0() {
    // max(succ 0, succ 0) is equivalent to succ 0.
    let mut k = Kernel::new();
    let z = k.level_zero();
    let s = k.level_succ(z);
    let m = k.level_max(s, s);
    assert!(k.level_leq(s, m));
    assert!(k.level_leq(m, s));
    assert!(k.level_is_equiv(s, m));
}

#[test]
fn leq_test1() {
    // imax (succ succ 0) 0 == 0.
    let mut k = Kernel::new();
    let z = k.level_zero();
    let s = k.level_succ(z);
    let ss = k.level_succ(s);
    let im = k.level_imax(ss, z);
    assert!(k.level_leq(im, z));
    assert!(k.level_is_equiv(z, im));
}

#[test]
fn leq_test_params_incomparable() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let na = k.name_str(anon, "a");
    let nb = k.name_str(anon, "b");
    let a = k.level_param(na);
    let b = k.level_param(nb);
    assert!(!k.level_leq(a, b));
    assert!(!k.level_leq(b, a));
}

#[test]
fn leq_test_imax_imax() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let na = k.name_str(anon, "a");
    let nb = k.name_str(anon, "b");
    let a = k.level_param(na);
    let b = k.level_param(nb);
    let imax_a_b = k.level_imax(a, b);
    let s_imax = k.level_succ(imax_a_b);
    let ss_imax = k.level_succ(s_imax);
    assert!(k.level_leq(imax_a_b, imax_a_b));
    assert!(k.level_leq(imax_a_b, s_imax));
    assert!(k.level_leq(imax_a_b, ss_imax));
    assert!(k.level_leq(s_imax, ss_imax));
    assert!(!k.level_leq(ss_imax, imax_a_b));
    assert!(!k.level_leq(ss_imax, s_imax));
}

#[test]
fn leq_test_succ_monotone() {
    // p + small <= p + large for small <= large.
    let mut k = Kernel::new();
    let anon = k.anon();
    let np = k.name_str(anon, "p");
    let p = k.level_param(np);
    for small in 0u64..20 {
        for large in small..20 {
            let a = k.level_offset(p, small);
            let b = k.level_offset(p, large);
            assert!(k.level_leq(a, b), "p+{small} <= p+{large}");
        }
    }
}

#[test]
fn leq_test_max_offsets() {
    // (max(p+small, q+small)) + small <= (max(p+large, q+large)) + large.
    let mut k = Kernel::new();
    let anon = k.anon();
    let np = k.name_str(anon, "p");
    let nq = k.name_str(anon, "q");
    let p = k.level_param(np);
    let q = k.level_param(nq);
    for small in 0u64..10 {
        for large in small..10 {
            let lhs = {
                let ps = k.level_offset(p, small);
                let qs = k.level_offset(q, small);
                let m = k.level_max(ps, qs);
                k.level_offset(m, small)
            };
            let rhs = {
                let pl = k.level_offset(p, large);
                let ql = k.level_offset(q, large);
                let m = k.level_max(pl, ql);
                k.level_offset(m, large)
            };
            assert!(k.level_leq(lhs, rhs));
        }
    }
}

#[test]
fn leq_test_imax_offsets() {
    // imax variant of the max-offset test.
    let mut k = Kernel::new();
    let anon = k.anon();
    let np = k.name_str(anon, "p");
    let nq = k.name_str(anon, "q");
    let p = k.level_param(np);
    let q = k.level_param(nq);
    for small in 0u64..10 {
        for large in small..10 {
            let lhs = {
                let ps = k.level_offset(p, small);
                let qs = k.level_offset(q, small);
                let m = k.level_imax(ps, qs);
                k.level_offset(m, small)
            };
            let rhs = {
                let pl = k.level_offset(p, large);
                let ql = k.level_offset(q, large);
                let m = k.level_imax(pl, ql);
                k.level_offset(m, large)
            };
            assert!(k.level_leq(lhs, rhs));
        }
    }
}

#[test]
fn leq_test_imax_eq_max_when_rhs_nonzero() {
    // nanoda leq_test7: when q has at least a successor, imax(p, q+1) ~ max(p, q+1).
    let mut k = Kernel::new();
    let anon = k.anon();
    let np = k.name_str(anon, "p");
    let nq = k.name_str(anon, "q");
    let p = k.level_param(np);
    let q = k.level_param(nq);
    for u in 0u64..8 {
        for v in 0u64..8 {
            for w in 0u64..6 {
                let p_ = k.level_offset(p, u);
                let q_ = k.level_offset(q, v + 1);
                let lhs = {
                    let im = k.level_imax(p_, q_);
                    k.level_offset(im, w)
                };
                let rhs = {
                    let m = k.level_max(p_, q_);
                    k.level_offset(m, w)
                };
                assert!(k.level_is_equiv(lhs, rhs), "u={u} v={v} w={w}");
            }
        }
    }
}

#[test]
fn eq_test_max_simplify() {
    // nanoda eq_test1: succ succ 0 == succ (max(succ 0, succ 0)).
    let mut k = Kernel::new();
    let z = k.level_zero();
    let s = k.level_succ(z);
    let ss = k.level_succ(s);
    let m = k.level_max(s, s);
    let sm = k.level_succ(m);
    assert!(k.level_is_equiv(ss, sm));
}

#[test]
fn simplify_idempotent_and_level_succs() {
    // nanoda debug_test1: simplify is idempotent; level_succs peels.
    let mut k = Kernel::new();
    let z = k.level_zero();
    let s = k.level_succ(z);
    let m = k.level_max(s, s);
    let sm = k.level_succ(m);
    let simp = k.simplify(sm);
    let simp2 = k.simplify(simp);
    assert_eq!(simp, simp2);
    // succ(max(1,1)) simplifies to succ(succ 0) == 2.
    let (inner, n) = k.level_succs(simp);
    assert_eq!(inner, z);
    assert_eq!(n, 2);
}

#[test]
fn max_zero_left_identity() {
    // max(0, x) ~ x and max(x, 0) ~ x.
    let mut k = Kernel::new();
    let anon = k.anon();
    let nx = k.name_str(anon, "x");
    let z = k.level_zero();
    let x = k.level_param(nx);
    let m1 = k.level_max(z, x);
    let m2 = k.level_max(x, z);
    assert!(k.level_is_equiv(m1, x));
    assert!(k.level_is_equiv(m2, x));
}

#[test]
fn substitute_level_params() {
    // Substitute p := succ 0 in max(p, q), check result.
    let mut k = Kernel::new();
    let anon = k.anon();
    let np = k.name_str(anon, "p");
    let nq = k.name_str(anon, "q");
    let p = k.level_param(np);
    let q = k.level_param(nq);
    let z = k.level_zero();
    let one = k.level_succ(z);
    let m = k.level_max(p, q);
    let out = k.substitute_level(m, &[(np, one)]);
    let expected = k.level_max(one, q);
    assert_eq!(out, expected);
}

// ---------------------------------------------------------------------------
// De Bruijn operations — the soundness backbone
// ---------------------------------------------------------------------------

#[test]
fn instantiate_closed_is_identity() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let cn = k.name_str(anon, "c");
    let c = k.const_(cn, vec![]);
    let ty = k.sort_zero();
    // (fun x => c) is closed.
    let lam = k.lam(anon, ty, c, BinderInfo::Default);
    let arg = k.const_(cn, vec![]);
    assert_eq!(k.num_loose_bvars(lam), 0);
    assert_eq!(k.instantiate(lam, &[arg]), lam);
}

#[test]
fn instantiate_identity_body_yields_arg() {
    // (fun x. #0) body instantiated with arg -> arg.
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let body = k.bvar(0);
    let _id_fn = k.lam(anon, ty, body, BinderInfo::Default);
    let cn = k.name_str(anon, "c");
    let arg = k.const_(cn, vec![]);
    assert_eq!(k.instantiate(body, &[arg]), arg);
}

#[test]
fn instantiate_nested_binders_right_index() {
    // (lam (lam #1)) — the inner body is #1, referring to the OUTER binder.
    // Instantiating the whole double-lambda body region: take the outer lambda's
    // body (lam #1), then instantiate with [arg]: #1 -> still bound? Let's test
    // by instantiating the doubly-loose body directly.
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    // body = #1 (loose by 2), under one binder it refers to the next-out binder.
    let b1 = k.bvar(1);
    let inner = k.lam(anon, ty, b1, BinderInfo::Default); // lam #1, loose-range 1
    assert_eq!(k.num_loose_bvars(inner), 1);
    let cn = k.name_str(anon, "c");
    let arg = k.const_(cn, vec![]);
    // Instantiating `inner` (lam #1) with [arg]: offset under binder = 1, the #1
    // resolves to subst index 0 -> arg, producing (lam c).
    let out = k.instantiate(inner, &[arg]);
    let expected = k.lam(anon, ty, arg, BinderInfo::Default);
    assert_eq!(out, expected);
}

#[test]
fn instantiate_multi_subst_order() {
    // App(#0, #1) instantiated with [a, b]: #0 -> last = b, #1 -> b'... check
    // nanoda's rev() convention: subst.rev().nth(idx). idx 0 -> b, idx 1 -> a.
    let mut k = Kernel::new();
    let anon = k.anon();
    let na = k.name_str(anon, "a");
    let nb = k.name_str(anon, "b");
    let a = k.const_(na, vec![]);
    let b = k.const_(nb, vec![]);
    let v0 = k.bvar(0);
    let v1 = k.bvar(1);
    let app = k.app(v0, v1);
    let out = k.instantiate(app, &[a, b]);
    // #0 -> rev[0] = b ; #1 -> rev[1] = a
    let expected = k.app(b, a);
    assert_eq!(out, expected);
}

#[test]
fn abstract_instantiate_roundtrip() {
    // abstract a free var, then instantiate with the same arg -> original-with-arg.
    let mut k = Kernel::new();
    let anon = k.anon();
    let fv_id = 42u64;
    let fv = k.fvar(fv_id);
    let na = k.name_str(anon, "g");
    let g = k.const_(na, vec![]);
    // term = g fv   (application of a const to the free var)
    let term = k.app(g, fv);
    assert!(k.has_fvars(term));
    // abstract fv -> g #0
    let abstracted = k.abstract_fvars(term, &[fv_id]);
    let v0 = k.bvar(0);
    let expected_abstr = k.app(g, v0);
    assert_eq!(abstracted, expected_abstr);
    assert_eq!(k.num_loose_bvars(abstracted), 1);
    // instantiate #0 -> arg yields g arg
    let arg = k.const_(na, vec![]);
    let reinst = k.instantiate(abstracted, &[arg]);
    let expected = k.app(g, arg);
    assert_eq!(reinst, expected);
    // round-trip with the original fvar recovers the original term.
    let back = k.instantiate(abstracted, &[fv]);
    assert_eq!(back, term);
}

#[test]
fn abstract_under_binder_uses_offset() {
    // term = fun (_ : Sort 0) => g fv ; abstracting fv must produce #1 under the
    // lambda (offset 1), since #0 is the lambda's own binder.
    let mut k = Kernel::new();
    let anon = k.anon();
    let fv_id = 7u64;
    let fv = k.fvar(fv_id);
    let gn = k.name_str(anon, "g");
    let g = k.const_(gn, vec![]);
    let body = k.app(g, fv);
    let ty = k.sort_zero();
    let lam = k.lam(anon, ty, body, BinderInfo::Default);
    let abstracted = k.abstract_fvars(lam, &[fv_id]);
    let v1 = k.bvar(1);
    let expected_body = k.app(g, v1);
    let expected = k.lam(anon, ty, expected_body, BinderInfo::Default);
    assert_eq!(abstracted, expected);
}

#[test]
fn abstract_fvars_visits_shared_expression_dag_once() {
    let mut k = Kernel::new();
    let fvar_id = 19u64;
    let mut shared = k.fvar(fvar_id);
    for _ in 0..30 {
        shared = k.app(shared, shared);
    }
    let abstracted = k.abstract_fvars(shared, &[fvar_id]);

    let mut expected = k.bvar(0);
    for _ in 0..30 {
        expected = k.app(expected, expected);
    }
    assert_eq!(abstracted, expected);
}

#[test]
fn scoped_fvar_closure_binds_nested_marked_lambdas_once() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let outer_id = 71_u64;
    let inner_id = 72_u64;
    let outer = k.fvar(outer_id);
    let inner = k.fvar(inner_id);
    let body = k.app(outer, inner);
    let inner_lam = k.lam(anon, ty, body, BinderInfo::Default);
    let outer_lam = k.lam(anon, ty, inner_lam, BinderInfo::Default);

    let closed = k.close_scoped_fvars(outer_lam, &[(outer_lam, outer_id), (inner_lam, inner_id)]);
    let outer_bvar = k.bvar(1);
    let inner_bvar = k.bvar(0);
    let expected_body = k.app(outer_bvar, inner_bvar);
    let expected_inner = k.lam(anon, ty, expected_body, BinderInfo::Default);
    let expected = k.lam(anon, ty, expected_inner, BinderInfo::Default);
    assert_eq!(closed, expected);
    assert!(!k.has_fvars(closed));
}

#[test]
fn scoped_fvar_closure_accounts_for_unmarked_binders() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let local_id = 81_u64;
    let local = k.fvar(local_id);
    let ordinary = k.lam(anon, ty, local, BinderInfo::Default);
    let marked = k.lam(anon, ty, ordinary, BinderInfo::Default);

    let closed = k.close_scoped_fvars(marked, &[(marked, local_id)]);
    let shifted = k.bvar(1);
    let expected_ordinary = k.lam(anon, ty, shifted, BinderInfo::Default);
    let expected = k.lam(anon, ty, expected_ordinary, BinderInfo::Default);
    assert_eq!(closed, expected);
}

#[test]
fn scoped_fvar_inference_checks_and_closes_the_same_lambda() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let prop = k.sort_zero();
    let local_id = 91_u64;
    let local = k.fvar(local_id);
    let open = k.lam(anon, prop, local, BinderInfo::Default);

    let (closed, inferred) = k
        .infer_and_close_scoped_fvars(open, &[(open, local_id)])
        .expect("scoped identity should infer");
    let body = k.bvar(0);
    let expected_closed = k.lam(anon, prop, body, BinderInfo::Default);
    let expected_type = k.pi(anon, prop, prop, BinderInfo::Default);
    assert_eq!(closed, expected_closed);
    assert!(k.def_eq(inferred, expected_type));
    assert_eq!(k.infer(closed).unwrap(), expected_type);
}

#[test]
fn scoped_fvar_inference_rejects_an_escape_outside_its_lambda() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let prop = k.sort_zero();
    let local_id = 92_u64;
    let local = k.fvar(local_id);
    let open = k.lam(anon, prop, local, BinderInfo::Default);
    let escaped = k.app(open, local);

    assert!(
        k.infer_and_close_scoped_fvars(escaped, &[(open, local_id)])
            .is_err()
    );
}

#[test]
fn instantiate_visits_shared_expression_dag_once() {
    let mut k = Kernel::new();
    let mut shared = k.bvar(0);
    for _ in 0..30 {
        shared = k.app(shared, shared);
    }
    let replacement = k.fvar(31);
    let instantiated = k.instantiate(shared, &[replacement]);

    let mut expected = replacement;
    for _ in 0..30 {
        expected = k.app(expected, expected);
    }
    assert_eq!(instantiated, expected);
}

#[test]
fn substitute_expr_levels_visits_shared_dag_once() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let universe_name = k.name_str(anon, "u_shared");
    let universe = k.level_param(universe_name);
    let constant_name = k.name_str(anon, "shared_constant");
    let mut shared = k.const_(constant_name, vec![universe]);
    for _ in 0..30 {
        shared = k.app(shared, shared);
    }
    let zero = k.level_zero();
    let substituted = k.substitute_expr_levels(shared, &[(universe_name, zero)]);

    let mut expected = k.const_(constant_name, vec![zero]);
    for _ in 0..30 {
        expected = k.app(expected, expected);
    }
    assert_eq!(substituted, expected);
}

#[test]
fn infer_open_shared_expression_dag_once_per_local_context() {
    let mut k = Kernel::new();
    let prelude = crate::build_logic_prelude(&mut k);
    let prop = k.sort_zero();
    let fvar_id = 23u64;
    let mut shared = k.fvar(fvar_id);
    for _ in 0..24 {
        let and = k.const_(prelude.and, vec![]);
        let and = k.app(and, shared);
        shared = k.app(and, shared);
    }
    let body = k.abstract_fvars(shared, &[fvar_id]);
    let anon = k.anon();
    let function = k.lam(anon, prop, body, BinderInfo::Default);
    let inferred = k.infer(function).expect("shared open DAG infers");
    let result = k.pi(anon, prop, prop, BinderInfo::Default);
    assert!(k.def_eq(inferred, result));
}

#[test]
fn loose_bvar_range_through_binders() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    // #0 alone has loose range 1.
    let v0 = k.bvar(0);
    assert_eq!(k.loose_bvar_range(v0), 0..1);
    assert!(k.has_loose_bvars(v0));
    // lam #0 is closed.
    let lam = k.lam(anon, ty, v0, BinderInfo::Default);
    assert_eq!(k.num_loose_bvars(lam), 0);
    assert!(!k.has_loose_bvars(lam));
    // #2 has loose range 3; under two binders it becomes 1.
    let v2 = k.bvar(2);
    assert_eq!(k.num_loose_bvars(v2), 3);
    let l1 = k.lam(anon, ty, v2, BinderInfo::Default);
    assert_eq!(k.num_loose_bvars(l1), 2);
    let l2 = k.lam(anon, ty, l1, BinderInfo::Default);
    assert_eq!(k.num_loose_bvars(l2), 1);
}

#[test]
fn lift_loose_bvars_shifts_above_cutoff() {
    let mut k = Kernel::new();
    // App(#0, #1) lifted by 2 with cutoff 0 -> App(#2, #3).
    let v0 = k.bvar(0);
    let v1 = k.bvar(1);
    let app = k.app(v0, v1);
    let lifted = k.lift_loose_bvars(app, 0, 2);
    let v2 = k.bvar(2);
    let v3 = k.bvar(3);
    let expected = k.app(v2, v3);
    assert_eq!(lifted, expected);

    // With cutoff 1: #0 stays, #1 -> #3.
    let lifted2 = k.lift_loose_bvars(app, 1, 2);
    let expected2 = k.app(v0, v3);
    assert_eq!(lifted2, expected2);
}

#[test]
fn lift_respects_binder_cutoff() {
    // fun => #0 (bound) #1 (loose) ; lift by 5 cutoff 0:
    // under the lambda the inner cutoff is 1, so #0 (bound) stays, #1 -> #6.
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let v0 = k.bvar(0);
    let v1 = k.bvar(1);
    let body = k.app(v0, v1);
    let lam = k.lam(anon, ty, body, BinderInfo::Default);
    let lifted = k.lift_loose_bvars(lam, 0, 5);
    let v6 = k.bvar(6);
    let expected_body = k.app(v0, v6);
    let expected = k.lam(anon, ty, expected_body, BinderInfo::Default);
    assert_eq!(lifted, expected);
}

#[test]
fn lit_nodes_are_closed() {
    let mut k = Kernel::new();
    let n = k.lit(Lit::nat(123_u8));
    let s = k.lit(Lit::Str("hi".into()));
    assert_eq!(k.num_loose_bvars(n), 0);
    assert!(!k.has_fvars(s));
    let n2 = k.lit(Lit::nat(123_u8));
    assert_eq!(n, n2);
    assert_ne!(n, s);
}

#[test]
#[should_panic(expected = "kernel was finalized for read-only export")]
fn export_finalization_rejects_further_construction() {
    let mut k = Kernel::new();
    let _ = k.sort_zero();
    k.release_transient_tables_for_export();
    let _ = k.sort_zero();
}
