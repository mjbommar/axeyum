//! The trust anchor for T-B.3. Three properties over the house LCG:
//!
//! 1. **soundness on model-consistent input** — from a random ground assignment
//!    we build an equality set that HOLDS under it; the inference pass must then
//!    produce **no `Conflict`**, and every derived `Fact` must evaluate true
//!    under the same assignment;
//! 2. **explanation sufficiency** — re-running the pass with *only* a fact's
//!    cited premises re-derives that equality (or the premises already put its
//!    two sides in one class);
//! 3. **adversarial conflicts** — from UNSAT seeds (a variable forced to two
//!    distinct constants through a chain) the pass must emit a `Conflict`, and
//!    the cited premise subset is checked **jointly unsatisfiable by brute-force
//!    small-model enumeration** (short strings, tiny alphabet). A wrong Conflict
//!    fails this.

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{Classes, infer};
use common::{cat, seq_sort, unit};

/// Deterministic linear-congruential generator (the repo's house constant).
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

/// The shared term pool: seq variables plus random concatenations and a couple
/// of constants.
struct Pool {
    seq_vars: Vec<(SymbolId, TermId)>,
    terms: Vec<TermId>,
}

impl Pool {
    fn new(arena: &mut TermArena, rng: &mut Lcg) -> Self {
        let seq_vars: Vec<(SymbolId, TermId)> = (0..4)
            .map(|i| {
                let s = arena
                    .declare(&format!("s{i}"), seq_sort())
                    .expect("declare seq var");
                (s, arena.var(s))
            })
            .collect();
        let chars: Vec<TermId> = b"ab"
            .iter()
            .map(|&c| {
                let ce = arena.bv_const(8, u128::from(c)).expect("char const");
                unit(arena, ce)
            })
            .collect();

        let mut terms: Vec<TermId> = seq_vars.iter().map(|&(_, t)| t).collect();
        terms.extend_from_slice(&chars);
        for _ in 0..7 {
            let a = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            let b = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            terms.push(cat(arena, a, b));
        }
        Self { seq_vars, terms }
    }
}

fn gen_assignment(rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    for &(s, _) in &pool.seq_vars {
        let len = rng.below(3);
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: u128::from(b'a') + u128::from(rng.below(2)),
            })
            .collect();
        asg.set(s, Value::Seq(elems));
    }
    asg
}

/// The model-consistent equality set: pool pairs that evaluate equal under
/// `asg`, each kept with probability ~1/2.
fn consistent_equalities(
    arena: &TermArena,
    pool: &Pool,
    asg: &Assignment,
    rng: &mut Lcg,
) -> Vec<(TermId, TermId)> {
    let vals: Vec<Value> = pool
        .terms
        .iter()
        .map(|&t| eval(arena, t, asg).expect("closed pool term"))
        .collect();
    let mut eqs = Vec::new();
    for i in 0..pool.terms.len() {
        for j in (i + 1)..pool.terms.len() {
            if vals[i] == vals[j] && rng.coin() {
                eqs.push((pool.terms[i], pool.terms[j]));
            }
        }
    }
    eqs
}

// ----- (1)+(2) soundness + explanation sufficiency ---------------------------

#[test]
fn inferences_are_sound_and_explanations_sufficient() {
    let mut rng = Lcg(0x0BAD_F00D_1234_5678);
    let mut verified_facts = 0u64;
    let mut iters = 0u64;

    for _ in 0..6000 {
        let mut arena = TermArena::new();
        let pool = Pool::new(&mut arena, &mut rng);
        let asg = gen_assignment(&mut rng, &pool);
        let eqs = consistent_equalities(&arena, &pool, &asg, &mut rng);
        if eqs.is_empty() {
            continue;
        }
        iters += 1;

        let inf = infer(&mut arena, &eqs);

        // (1a) A model-consistent input can never be a conflict.
        assert!(
            !inf.is_conflict(),
            "conflict reported on a model-consistent equality set"
        );

        // (1b) Every derived fact holds under the witness assignment.
        let facts: Vec<_> = inf.facts().cloned().collect();
        for f in &facts {
            let (a, b) = f.equality;
            let va = eval(&arena, a, &asg).expect("closed fact lhs");
            let vb = eval(&arena, b, &asg).expect("closed fact rhs");
            assert_eq!(va, vb, "derived fact is false under the witness model");
        }

        // (2) Explanation sufficiency: re-derive each fact from its premises.
        for f in &facts {
            let cited: Vec<(TermId, TermId)> = f
                .premises
                .iter()
                .map(|&i| eqs[i])
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let (a, b) = f.equality;
            let want = (a.min(b), a.max(b));

            let sub_classes = Classes::new(&cited);
            let already = sub_classes.representative(a) == sub_classes.representative(b);
            let sub_inf = infer(&mut arena, &cited);
            let rederived = sub_inf.facts().any(|g| g.equality == want);
            assert!(
                already || rederived,
                "cited premises {:?} are insufficient to re-derive {want:?}",
                f.premises
            );
            verified_facts += 1;
        }
    }

    assert!(
        iters >= 1000,
        "expected at least 1000 non-empty iterations (did {iters})"
    );
    assert!(
        verified_facts >= 1000,
        "expected at least 1000 verified facts (did {verified_facts})"
    );
}

// ----- (3) adversarial conflicts ---------------------------------------------

/// Builds an UNSAT seed: a variable chain forcing one class to contain two
/// distinct constants, plus consistent noise equalities among fresh variables.
/// Returns `(equalities, involved-seq-vars)`.
fn adversarial_seed(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Vec<(TermId, TermId)> {
    // Two distinct single-char constants.
    let ca = {
        let e = arena.bv_const(8, u128::from(b'a')).expect("a");
        unit(arena, e)
    };
    let cb = {
        let e = arena.bv_const(8, u128::from(b'b')).expect("b");
        unit(arena, e)
    };

    // A chain x0 = x1 = … = xk, with x0 = "a" and xk = "b".
    let k = 1 + rng.below(3); // 1..3 links
    let vars: Vec<TermId> = (0..=k)
        .map(|i| {
            let s = arena
                .declare(&format!("c{id}_{i}"), seq_sort())
                .expect("var");
            arena.var(s)
        })
        .collect();

    let mut eqs = Vec::new();
    eqs.push((vars[0], ca));
    for w in vars.windows(2) {
        eqs.push((w[0], w[1]));
    }
    eqs.push((*vars.last().expect("nonempty"), cb));

    // Consistent noise: two fresh vars asserted equal to each other (satisfiable,
    // unrelated to the clash).
    if rng.coin() {
        let s1 = arena.declare(&format!("n{id}_0"), seq_sort()).expect("n0");
        let s2 = arena.declare(&format!("n{id}_1"), seq_sort()).expect("n1");
        eqs.push((arena.var(s1), arena.var(s2)));
    }
    eqs
}

/// Brute-force check that `eqs` (a subset of asserted equalities) is
/// unsatisfiable over strings of length ≤ 3 in the alphabet {a, b}. Enumerates
/// all assignments of the free sequence variables; asserts none satisfies all.
fn brute_force_unsat(arena: &TermArena, eqs: &[(TermId, TermId)]) -> bool {
    // Collect the free sequence variables appearing in the equalities.
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for &(a, b) in eqs {
        collect_vars(arena, a, &mut vars);
        collect_vars(arena, b, &mut vars);
    }
    let vars: Vec<SymbolId> = vars.into_iter().collect();

    // All short strings over {a, b}: lengths 0..=2 (enough to expose any model
    // of these structurally-unsat premises).
    let alphabet = *b"ab";
    let mut values: Vec<Value> = Vec::new();
    for len in 0..=2usize {
        enumerate_strings(&alphabet, len, &mut Vec::new(), &mut values);
    }

    // Odometer over `vars`, each ranging over `values`.
    let base = values.len();
    let total = base.checked_pow(u32::try_from(vars.len()).expect("few vars"));
    let Some(total) = total else {
        // Too many combinations to enumerate — treat as "not shown unsat".
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
            return false; // found a model ⇒ NOT unsat
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

#[test]
fn adversarial_conflicts_have_unsatisfiable_premises() {
    let mut rng = Lcg(0xC0FF_EE00_DEAD_BEEF);
    let mut conflicts = 0u64;

    for id in 0..1400 {
        let mut arena = TermArena::new();
        let eqs = adversarial_seed(&mut arena, &mut rng, id);

        let inf = infer(&mut arena, &eqs);
        let conflict = inf
            .conflict()
            .expect("a variable forced to two distinct constants must conflict");

        // The cited premise subset must be genuinely unsatisfiable.
        let cited: Vec<(TermId, TermId)> = conflict.premises.iter().map(|&i| eqs[i]).collect();
        assert!(
            !cited.is_empty(),
            "a conflict must cite at least one premise"
        );
        assert!(
            brute_force_unsat(&arena, &cited),
            "cited premises {:?} are NOT unsat by brute force (wrong conflict); reason {:?}",
            conflict.premises,
            conflict.reason
        );
        conflicts += 1;
    }

    assert!(
        conflicts >= 1000,
        "expected at least 1000 adversarial conflicts checked (did {conflicts})"
    );
}
