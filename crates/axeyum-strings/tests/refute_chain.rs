//! Slice-2 refutation: **inference-dependent** `unsat` behind re-checked
//! derivations. The concrete tests pin the shapes that now certify; the adversarial
//! property confirms every cited premise set is genuinely unsatisfiable by
//! brute-force small-model enumeration (a wrong `unsat` is impossible because each
//! appended fact is `check_fact`-certified).
#![allow(clippy::many_single_char_names, clippy::similar_names)]

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};
use common::{cat, seq_sort, seq_var, unit};

fn budget() -> SearchBudget {
    SearchBudget::new(1_000_000)
}

/// `"a"` / `"b"` as length-1 constant sequences.
fn ab(arena: &mut TermArena) -> (TermId, TermId) {
    let a = {
        let e = arena.bv_const(8, u128::from(b'a')).expect("a");
        unit(arena, e)
    };
    let b = {
        let e = arena.bv_const(8, u128::from(b'b')).expect("b");
        unit(arena, e)
    };
    (a, b)
}

fn refute(arena: &mut TermArena, eqs: &[(TermId, TermId)]) -> RefuteOutcome {
    refute_word_equations(arena, eqs, &[], &budget())
}

fn cited_is_unsat(arena: &TermArena, eqs: &[(TermId, TermId)], premises: &BTreeSet<usize>) {
    assert!(
        !premises.is_empty(),
        "an unsat must cite at least one premise"
    );
    let cited: Vec<(TermId, TermId)> = premises.iter().map(|&i| eqs[i]).collect();
    assert!(
        brute_force_unsat(arena, &cited),
        "cited premises {premises:?} are NOT unsat by brute force (wrong refutation)"
    );
}

// ----- self-loop constant contradictions -------------------------------------

#[test]
fn self_loop_prefix_constant_is_unsat() {
    // x = "a" ++ x  (|x| = 1 + |x|).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let (a, _) = ab(&mut arena);
    let rhs = cat(&mut arena, a, x);
    let eqs = [(x, rhs)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("x = \"a\" ++ x must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
}

#[test]
fn self_loop_suffix_constant_is_unsat() {
    // x = x ++ "a".
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let (a, _) = ab(&mut arena);
    let rhs = cat(&mut arena, x, a);
    let eqs = [(x, rhs)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("x = x ++ \"a\" must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
}

#[test]
fn self_loop_interior_constant_is_unsat() {
    // x = y ++ "a" ++ x  with the cycle continuation x; the constant "a" is off-cycle.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let (a, _) = ab(&mut arena);
    let ya = cat(&mut arena, y, a);
    let yax = cat(&mut arena, ya, x);
    let eqs = [(x, yax)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("x = y ++ \"a\" ++ x must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
}

// ----- augmented constant clash (variable-cycle then constant) ---------------

#[test]
fn var_cycle_then_constant_is_unsat() {
    // x = y ++ x forces y ≈ ε; y = "a" then clashes ("a" ≈ ε).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let (a, _) = ab(&mut arena);
    let yx = cat(&mut arena, y, x);
    let eqs = [(x, yx), (y, a)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("x = y ++ x ∧ y = \"a\" must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
    // Both premises are needed and cited.
    assert_eq!(premises, BTreeSet::from([0, 1]));
}

// ----- chained conflict (clash closes only through a derived fact) -----------

#[test]
fn endpoint_eq_chained_constant_clash_is_unsat() {
    // x = y ++ z1, x = y ++ z2  ⇒  z1 ≈ z2 (endpoint-eq); with z1 = "a", z2 = "b"
    // the derived merge exposes a constant clash the DIRECT checker cannot see.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z1 = seq_var(&mut arena, "z1");
    let z2 = seq_var(&mut arena, "z2");
    let (a, b) = ab(&mut arena);
    let yz1 = cat(&mut arena, y, z1);
    let yz2 = cat(&mut arena, y, z2);
    let eqs = [(x, yz1), (x, yz2), (z1, a), (z2, b)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("the endpoint-eq chained clash must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
}

#[test]
fn multi_char_chained_clash_is_unsat() {
    // x = y ++ z1, x = y ++ z2, z1 = "ab", z2 = "aa": z1 ≈ z2 then "ab" ≠ "aa".
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z1 = seq_var(&mut arena, "z1");
    let z2 = seq_var(&mut arena, "z2");
    let (a, b) = ab(&mut arena);
    let ab_block = cat(&mut arena, a, b); // "ab"
    let aa_block = cat(&mut arena, a, a); // "aa"
    let yz1 = cat(&mut arena, y, z1);
    let yz2 = cat(&mut arena, y, z2);
    let eqs = [(x, yz1), (x, yz2), (z1, ab_block), (z2, aa_block)];
    let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
        panic!("the multi-char chained clash must refute to unsat");
    };
    cited_is_unsat(&arena, &eqs, &premises);
}

// ----- soundness: satisfiable cycle shapes are never refuted ------------------

#[test]
fn satisfiable_variable_self_loop_is_not_refuted() {
    // x = y ++ x is satisfiable (y = ε, x anything) — must NOT refute.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let yx = cat(&mut arena, y, x);
    let eqs = [(x, yx)];
    assert_eq!(
        refute(&mut arena, &eqs),
        RefuteOutcome::Unknown,
        "x = y ++ x is SAT (y = ε); refuting it would be a wrong unsat"
    );
}

#[test]
fn satisfiable_endpoint_shape_is_not_refuted() {
    // x = "a" ++ z, x = "a" ++ w is satisfiable (z = w); must NOT refute.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let z = seq_var(&mut arena, "z");
    let w = seq_var(&mut arena, "w");
    let (a, _) = ab(&mut arena);
    let az = cat(&mut arena, a, z);
    let aw = cat(&mut arena, a, w);
    let eqs = [(x, az), (x, aw)];
    assert_eq!(refute(&mut arena, &eqs), RefuteOutcome::Unknown);
}

// ----- adversarial property: certified inference-dependent unsats -------------

/// Deterministic LCG (house constant).
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        (self.next_u64() >> 33) % n
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & (1 << 40) != 0
    }
}

/// Builds a random *inference-dependent* UNSAT seed (a self-loop constant, a
/// variable cycle forced to ε then pinned to a constant, or an endpoint-eq chained
/// clash), optionally plus a satisfiable noise equality among fresh variables.
fn adversarial_seed(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Vec<(TermId, TermId)> {
    let mkvar = |arena: &mut TermArena, tag: &str| {
        let s = arena
            .declare(&format!("s{id}_{tag}"), seq_sort())
            .expect("var");
        arena.var(s)
    };
    let (a, b) = ab(arena);
    let mut eqs = Vec::new();
    match rng.below(4) {
        0 => {
            // x = "a" ++ x  (or suffix).
            let x = mkvar(arena, "x");
            let rhs = if rng.coin() {
                cat(arena, a, x)
            } else {
                cat(arena, x, a)
            };
            eqs.push((x, rhs));
        }
        1 => {
            // x = y ++ x ∧ y = "a".
            let x = mkvar(arena, "x");
            let y = mkvar(arena, "y");
            let yx = cat(arena, y, x);
            eqs.push((x, yx));
            eqs.push((y, a));
        }
        2 => {
            // x = z ++ x ∧ z = "b" (suffix cycle continuation).
            let x = mkvar(arena, "x");
            let z = mkvar(arena, "z");
            let xz = cat(arena, x, z);
            eqs.push((x, xz));
            eqs.push((z, b));
        }
        _ => {
            // x = y ++ z1, x = y ++ z2, z1 = "a", z2 = "b".
            let x = mkvar(arena, "x");
            let y = mkvar(arena, "y");
            let z1 = mkvar(arena, "z1");
            let z2 = mkvar(arena, "z2");
            let yz1 = cat(arena, y, z1);
            let yz2 = cat(arena, y, z2);
            eqs.push((x, yz1));
            eqs.push((x, yz2));
            eqs.push((z1, a));
            eqs.push((z2, b));
        }
    }
    if rng.coin() {
        let n0 = mkvar(arena, "n0");
        let n1 = mkvar(arena, "n1");
        eqs.push((n0, n1)); // satisfiable noise
    }
    eqs
}

#[test]
fn certified_inference_dependent_unsats_are_brute_force_unsat() {
    let mut rng = Lcg(0xF00D_CAFE_5151_9999);
    let mut refuted = 0u64;
    for id in 0..1400 {
        let mut arena = TermArena::new();
        let eqs = adversarial_seed(&mut arena, &mut rng, id);
        let RefuteOutcome::Unsat { premises } = refute(&mut arena, &eqs) else {
            continue; // conservative decline is allowed; a wrong unsat is not
        };
        cited_is_unsat(&arena, &eqs, &premises);
        refuted += 1;
    }
    assert!(
        refuted >= 1000,
        "expected ≥1000 certified inference-dependent refutations (did {refuted})"
    );
}

// ----- brute-force small-model enumeration -----------------------------------

fn brute_force_unsat(arena: &TermArena, eqs: &[(TermId, TermId)]) -> bool {
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for &(a, b) in eqs {
        collect_vars(arena, a, &mut vars);
        collect_vars(arena, b, &mut vars);
    }
    let vars: Vec<SymbolId> = vars.into_iter().collect();

    let alphabet = *b"ab";
    let mut values: Vec<Value> = Vec::new();
    for len in 0..=2usize {
        enumerate_strings(&alphabet, len, &mut Vec::new(), &mut values);
    }
    let base = values.len();
    let Some(total) = base.checked_pow(u32::try_from(vars.len()).expect("few vars")) else {
        return false;
    };
    for combo in 0..total {
        let mut asg = Assignment::new();
        let mut rem = combo;
        for &v in &vars {
            asg.set(v, values[rem % base].clone());
            rem /= base;
        }
        let sat = eqs.iter().all(|&(a, b)| {
            matches!(
                (eval(arena, a, &asg), eval(arena, b, &asg)),
                (Ok(va), Ok(vb)) if va == vb
            )
        });
        if sat {
            return false;
        }
    }
    true
}

fn collect_vars(arena: &TermArena, t: TermId, out: &mut BTreeSet<SymbolId>) {
    use axeyum_ir::TermNode;
    match arena.node(t) {
        TermNode::Symbol(s) => {
            if matches!(arena.sort_of(t), axeyum_ir::Sort::Seq(_)) {
                out.insert(*s);
            }
        }
        TermNode::App { args, .. } => {
            for &a in args {
                collect_vars(arena, a, out);
            }
        }
        _ => {}
    }
}

fn enumerate_strings(alphabet: &[u8], len: usize, acc: &mut Vec<Value>, out: &mut Vec<Value>) {
    if len == 0 {
        out.push(Value::Seq(acc.clone()));
        return;
    }
    for &c in alphabet {
        acc.push(Value::Bv {
            width: 8,
            value: u128::from(c),
        });
        enumerate_strings(alphabet, len - 1, acc, out);
        acc.pop();
    }
}
