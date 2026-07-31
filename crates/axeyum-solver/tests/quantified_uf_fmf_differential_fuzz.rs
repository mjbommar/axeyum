//! Oracle-free differential fuzz for **quantified pure-UF finite model
//! finding** (the `uf_fmf` route and its independent certificate checker).
//!
//! Reference implementation: a brute-force finite-structure enumerator local
//! to this test. For each generated instance it enumerates *every* structure
//! with carrier size 1..=3 (constants x functions x predicates) and evaluates
//! the assertions exactly (quantifiers by enumeration). It shares no code
//! with the solver's expansion, ground engines, or checker.
//!
//! Soundness contract per instance:
//! - brute force finds a model ∧ axeyum answers `Unsat` → **PANIC** (wrong
//!   unsat — the worst bug).
//! - axeyum answers `Sat` with recorded cardinalities ≤ 3 ∧ brute force found
//!   no model up to size 3 → **PANIC** (wrong sat).
//! - axeyum answers `Sat` → the returned model is re-evaluated here with the
//!   test's own evaluator over its recorded cardinalities; any assertion
//!   evaluating false → **PANIC** (unsound model).
//! - `Unknown` is always acceptable.
//!
//! The generator deliberately emits the degenerate shapes the hard rule
//! demands: size-1 carriers, exact-upper-bound formulas (`forall x y. x = y`
//! plus distinct constants — unsat only through the cardinality interaction),
//! `exists` under `forall`, `Bool`-sorted binders, and 0-ary functions.

#![cfg(feature = "full")]

use std::collections::HashMap;
use std::time::Duration;

use axeyum_ir::{FuncId, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

const INSTANCES: u64 = 150;
const AXEYUM_TIMEOUT: Duration = Duration::from_millis(750);
const MAX_BRUTE_SIZE: usize = 3;

struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
    fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

/// One generated instance over a single uninterpreted sort `S`: two constants
/// `c0 c1 : S`, a unary function `f : S -> S`, a unary predicate `p : S ->
/// Bool`, and (sometimes) a free Bool symbol. Terms and formulas are tiny
/// trees the brute-force reference can evaluate exactly.
struct Instance {
    arena: TermArena,
    assertions: Vec<TermId>,
    constants: [SymbolId; 2],
    function: FuncId,
    predicate: FuncId,
    sort_id: axeyum_ir::SortId,
}

/// Test-local term AST mirrored into the arena, so the brute-force evaluator
/// never touches arena evaluation.
#[derive(Clone, Debug)]
enum T {
    Const(usize),
    Bound(usize),
    App(Box<T>),
}

#[derive(Clone, Debug)]
enum F {
    EqT(T, T),
    Pred(T),
    BoolVar(usize),
    Not(Box<F>),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
    Implies(Box<F>, Box<F>),
    Forall(usize, Box<F>),
    Exists(usize, Box<F>),
    ForallBool(usize, Box<F>),
}

fn gen_term(rng: &mut Lcg, depth: usize, bound: &[usize]) -> T {
    match rng.below(if depth == 0 { 2 } else { 3 }) {
        1 if !bound.is_empty() => T::Bound(bound[rng.below(bound.len() as u64)]),
        0 | 1 => T::Const(rng.below(2)),
        _ => T::App(Box::new(gen_term(rng, depth - 1, bound))),
    }
}

fn gen_formula(
    rng: &mut Lcg,
    depth: usize,
    bound: &mut Vec<usize>,
    bool_bound: &mut Vec<usize>,
    next_binder: &mut usize,
) -> F {
    let choice = rng.below(if depth == 0 { 3 } else { 8 });
    match choice {
        0 => F::EqT(gen_term(rng, 1, bound), gen_term(rng, 1, bound)),
        1 => F::Pred(gen_term(rng, 1, bound)),
        2 => {
            if bool_bound.is_empty() {
                F::Pred(gen_term(rng, 1, bound))
            } else {
                F::BoolVar(bool_bound[rng.below(bool_bound.len() as u64)])
            }
        }
        3 => F::Not(Box::new(gen_formula(
            rng,
            depth - 1,
            bound,
            bool_bound,
            next_binder,
        ))),
        4 | 5 => {
            let left = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
            let right = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
            if choice == 4 {
                F::And(Box::new(left), Box::new(right))
            } else {
                F::Or(Box::new(left), Box::new(right))
            }
        }
        6 => {
            let left = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
            let right = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
            F::Implies(Box::new(left), Box::new(right))
        }
        _ => {
            let binder = *next_binder;
            *next_binder += 1;
            // Degenerate corner: an occasional Bool-sorted binder.
            if rng.below(5) == 0 {
                bool_bound.push(binder);
                let body = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
                bool_bound.pop();
                F::ForallBool(binder, Box::new(body))
            } else {
                bound.push(binder);
                let body = gen_formula(rng, depth - 1, bound, bool_bound, next_binder);
                bound.pop();
                if rng.flip() {
                    F::Forall(binder, Box::new(body))
                } else {
                    F::Exists(binder, Box::new(body))
                }
            }
        }
    }
}

/// A finite structure: carrier `0..size`, constant values, `f` table, `p`
/// table.
struct Structure {
    size: usize,
    constants: [usize; 2],
    function: Vec<usize>,
    predicate: Vec<bool>,
}

fn eval_term(term: &T, structure: &Structure, env: &HashMap<usize, usize>) -> usize {
    match term {
        T::Const(index) => structure.constants[*index],
        T::Bound(binder) => env[binder],
        T::App(inner) => structure.function[eval_term(inner, structure, env)],
    }
}

fn eval_formula(
    formula: &F,
    structure: &Structure,
    env: &mut HashMap<usize, usize>,
    bool_env: &mut HashMap<usize, bool>,
) -> bool {
    match formula {
        F::EqT(left, right) => eval_term(left, structure, env) == eval_term(right, structure, env),
        F::Pred(term) => structure.predicate[eval_term(term, structure, env)],
        F::BoolVar(binder) => bool_env[binder],
        F::Not(inner) => !eval_formula(inner, structure, env, bool_env),
        F::And(left, right) => {
            eval_formula(left, structure, env, bool_env)
                && eval_formula(right, structure, env, bool_env)
        }
        F::Or(left, right) => {
            eval_formula(left, structure, env, bool_env)
                || eval_formula(right, structure, env, bool_env)
        }
        F::Implies(left, right) => {
            !eval_formula(left, structure, env, bool_env)
                || eval_formula(right, structure, env, bool_env)
        }
        F::Forall(binder, body) => (0..structure.size).all(|value| {
            env.insert(*binder, value);
            let holds = eval_formula(body, structure, env, bool_env);
            env.remove(binder);
            holds
        }),
        F::Exists(binder, body) => (0..structure.size).any(|value| {
            env.insert(*binder, value);
            let holds = eval_formula(body, structure, env, bool_env);
            env.remove(binder);
            holds
        }),
        F::ForallBool(binder, body) => [false, true].into_iter().all(|value| {
            bool_env.insert(*binder, value);
            let holds = eval_formula(body, structure, env, bool_env);
            bool_env.remove(binder);
            holds
        }),
    }
}

/// Whether some structure of carrier size `1..=MAX_BRUTE_SIZE` satisfies every
/// formula — the independent reference decision (complete for "has a model of
/// size <= 3", silent beyond).
fn brute_force_has_small_model(formulas: &[F]) -> bool {
    for size in 1..=MAX_BRUTE_SIZE {
        let mut constants = [0usize; 2];
        loop {
            let mut function = vec![0usize; size];
            'function: loop {
                for predicate_bits in 0..(1u32 << size) {
                    let predicate: Vec<bool> =
                        (0..size).map(|i| predicate_bits & (1 << i) != 0).collect();
                    let structure = Structure {
                        size,
                        constants,
                        function: function.clone(),
                        predicate,
                    };
                    if formulas.iter().all(|formula| {
                        eval_formula(
                            formula,
                            &structure,
                            &mut HashMap::new(),
                            &mut HashMap::new(),
                        )
                    }) {
                        return true;
                    }
                }
                // Next function table (odometer).
                for slot in &mut function {
                    *slot += 1;
                    if *slot < size {
                        continue 'function;
                    }
                    *slot = 0;
                }
                break;
            }
            // Next constant tuple (odometer).
            let mut carried = true;
            for slot in &mut constants {
                *slot += 1;
                if *slot < size {
                    carried = false;
                    break;
                }
                *slot = 0;
            }
            if carried {
                break;
            }
        }
    }
    false
}

/// Mirrors the test AST into the arena.
fn build_instance(formulas: &[F]) -> Instance {
    let mut arena = TermArena::new();
    let sort_id = arena.declare_uninterpreted_sort("FuzzS");
    let sort = Sort::Uninterpreted(sort_id);
    let constants = [
        arena.declare("fuzz_c0", sort).unwrap(),
        arena.declare("fuzz_c1", sort).unwrap(),
    ];
    let function = arena.declare_fun("fuzz_f", &[sort], sort).unwrap();
    let predicate = arena.declare_fun("fuzz_p", &[sort], Sort::Bool).unwrap();

    let mut binder_symbols: HashMap<usize, SymbolId> = HashMap::new();
    let mut assertions = Vec::new();
    for formula in formulas {
        let term = mirror_formula(
            &mut arena,
            formula,
            constants,
            function,
            predicate,
            sort,
            &mut binder_symbols,
        );
        assertions.push(term);
    }
    Instance {
        arena,
        assertions,
        constants,
        function,
        predicate,
        sort_id,
    }
}

#[allow(clippy::too_many_arguments)]
fn mirror_term(
    arena: &mut TermArena,
    term: &T,
    constants: [SymbolId; 2],
    function: FuncId,
    binder_symbols: &HashMap<usize, SymbolId>,
) -> TermId {
    match term {
        T::Const(index) => arena.var(constants[*index]),
        T::Bound(binder) => arena.var(binder_symbols[binder]),
        T::App(inner) => {
            let argument = mirror_term(arena, inner, constants, function, binder_symbols);
            arena.apply(function, &[argument]).unwrap()
        }
    }
}

fn mirror_formula(
    arena: &mut TermArena,
    formula: &F,
    constants: [SymbolId; 2],
    function: FuncId,
    predicate: FuncId,
    sort: Sort,
    binder_symbols: &mut HashMap<usize, SymbolId>,
) -> TermId {
    match formula {
        F::EqT(left, right) => {
            let left = mirror_term(arena, left, constants, function, binder_symbols);
            let right = mirror_term(arena, right, constants, function, binder_symbols);
            arena.eq(left, right).unwrap()
        }
        F::Pred(term) => {
            let argument = mirror_term(arena, term, constants, function, binder_symbols);
            arena.apply(predicate, &[argument]).unwrap()
        }
        F::BoolVar(binder) => arena.var(binder_symbols[binder]),
        F::Not(inner) => {
            let inner = mirror_formula(
                arena,
                inner,
                constants,
                function,
                predicate,
                sort,
                binder_symbols,
            );
            arena.not(inner).unwrap()
        }
        F::And(left, right) | F::Or(left, right) | F::Implies(left, right) => {
            let left_term = mirror_formula(
                arena,
                left,
                constants,
                function,
                predicate,
                sort,
                binder_symbols,
            );
            let right_term = mirror_formula(
                arena,
                right,
                constants,
                function,
                predicate,
                sort,
                binder_symbols,
            );
            match formula {
                F::And(..) => arena.and(left_term, right_term).unwrap(),
                F::Or(..) => arena.or(left_term, right_term).unwrap(),
                _ => arena.implies(left_term, right_term).unwrap(),
            }
        }
        F::Forall(binder, body) | F::Exists(binder, body) => {
            let symbol = arena.declare(&format!("fuzz_x{binder}"), sort).unwrap();
            binder_symbols.insert(*binder, symbol);
            let body = mirror_formula(
                arena,
                body,
                constants,
                function,
                predicate,
                sort,
                binder_symbols,
            );
            match formula {
                F::Forall(..) => arena.forall(symbol, body).unwrap(),
                _ => arena.exists(symbol, body).unwrap(),
            }
        }
        F::ForallBool(binder, body) => {
            let symbol = arena
                .declare(&format!("fuzz_b{binder}"), Sort::Bool)
                .unwrap();
            binder_symbols.insert(*binder, symbol);
            let body = mirror_formula(
                arena,
                body,
                constants,
                function,
                predicate,
                sort,
                binder_symbols,
            );
            arena.forall(symbol, body).unwrap()
        }
    }
}

/// Re-evaluates a returned `Sat` model with the test's own evaluator: builds
/// a [`Structure`] from the recorded cardinality and the model's tables and
/// checks every formula. `None` when the model does not carry the pieces this
/// independent replay needs (then the test cannot judge it).
fn model_satisfies(
    instance: &Instance,
    model: &axeyum_solver::Model,
    formulas: &[F],
) -> Option<bool> {
    let cardinality = model.uninterpreted_cardinality(instance.sort_id)? as usize;
    let token = |value: Value| -> Option<usize> {
        match value {
            Value::Uninterpreted { sort, value } if sort == instance.sort_id => {
                usize::try_from(value).ok()
            }
            _ => None,
        }
    };
    let mut constants = [0usize; 2];
    for (index, symbol) in instance.constants.into_iter().enumerate() {
        constants[index] = token(model.get(symbol)?)?;
        if constants[index] >= cardinality {
            return Some(false);
        }
    }
    let function_interp = model.function(instance.function)?;
    let predicate_interp = model.function(instance.predicate)?;
    let mut function = Vec::with_capacity(cardinality);
    let mut predicate = Vec::with_capacity(cardinality);
    for value in 0..cardinality {
        let input = Value::Uninterpreted {
            sort: instance.sort_id,
            value: value as u128,
        };
        let output = token(function_interp.apply_value(std::slice::from_ref(&input)))?;
        if output >= cardinality {
            return Some(false);
        }
        function.push(output);
        match predicate_interp.apply_value(&[input]) {
            Value::Bool(holds) => predicate.push(holds),
            _ => return None,
        }
    }
    let structure = Structure {
        size: cardinality,
        constants,
        function,
        predicate,
    };
    Some(formulas.iter().all(|formula| {
        eval_formula(
            formula,
            &structure,
            &mut HashMap::new(),
            &mut HashMap::new(),
        )
    }))
}

fn run_instance(formulas: &[F], seed: u64) {
    let mut instance = build_instance(formulas);
    let has_small_model = brute_force_has_small_model(formulas);
    let config = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let assertions = instance.assertions.clone();
    // An operational error is not a wrong verdict; skip.
    let Ok(verdict) = solve(&mut instance.arena, &assertions, &config) else {
        return;
    };
    match verdict {
        CheckResult::Unsat => {
            assert!(
                !has_small_model,
                "seed {seed}: WRONG UNSAT — brute force found a model of size <= \
                 {MAX_BRUTE_SIZE} for {formulas:?}"
            );
        }
        CheckResult::Sat(model) => {
            if let Some(cardinality) = model.uninterpreted_cardinality(instance.sort_id)
                && cardinality as usize <= MAX_BRUTE_SIZE
            {
                assert!(
                    has_small_model,
                    "seed {seed}: WRONG SAT — axeyum reports a size-{cardinality} model but \
                     brute force finds none up to {MAX_BRUTE_SIZE} for {formulas:?}"
                );
            }
            if let Some(replayed) = model_satisfies(&instance, &model, formulas) {
                assert!(
                    replayed,
                    "seed {seed}: UNSOUND MODEL — the returned model does not satisfy the \
                     assertions under the test evaluator for {formulas:?}"
                );
            }
        }
        CheckResult::Unknown(_) => {}
    }
}

/// Whether the generated formula tree contains any quantifier.
fn quantified(formula: &F) -> bool {
    match formula {
        F::Forall(..) | F::Exists(..) | F::ForallBool(..) => true,
        F::Not(inner) => quantified(inner),
        F::And(left, right) | F::Or(left, right) | F::Implies(left, right) => {
            quantified(left) || quantified(right)
        }
        F::EqT(..) | F::Pred(..) | F::BoolVar(..) => false,
    }
}

#[test]
fn quantified_pure_uf_matches_brute_force_reference() {
    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed);
        let count = 1 + rng.below(3);
        let mut formulas = Vec::with_capacity(count);
        let mut next_binder = 0usize;
        for _ in 0..count {
            let depth = 2 + rng.below(2);
            formulas.push(gen_formula(
                &mut rng,
                depth,
                &mut Vec::new(),
                &mut Vec::new(),
                &mut next_binder,
            ));
        }
        // At least one quantifier so the finite-model route is exercised.
        if !formulas.iter().any(quantified) {
            let binder = next_binder;
            formulas.push(F::Forall(
                binder,
                Box::new(F::Or(
                    Box::new(F::Pred(T::Bound(binder))),
                    Box::new(F::Not(Box::new(F::Pred(T::Bound(binder))))),
                )),
            ));
        }
        run_instance(&formulas, seed);
    }
}

/// The deterministic degenerate seed shapes the hard rule demands, pinned so
/// no generator drift can stop emitting them.
#[test]
fn degenerate_shapes_are_decided_soundly() {
    // Exact upper bound through cardinality: `forall x y. x = y` plus
    // `c0 != c1` is unsatisfiable ONLY because the universal forces a
    // one-element carrier. A bounded expansion that emitted `unsat` from a
    // single size would get this wrong in reverse; the solver must never
    // answer `sat`.
    let forced_singleton = vec![
        F::Forall(
            0,
            Box::new(F::Forall(1, Box::new(F::EqT(T::Bound(0), T::Bound(1))))),
        ),
        F::Not(Box::new(F::EqT(T::Const(0), T::Const(1)))),
    ];
    run_instance(&forced_singleton, u64::MAX);

    // The same universal with equal constants is satisfiable at size one.
    let singleton = vec![
        F::Forall(
            0,
            Box::new(F::Forall(1, Box::new(F::EqT(T::Bound(0), T::Bound(1))))),
        ),
        F::EqT(T::Const(0), T::Const(1)),
    ];
    run_instance(&singleton, u64::MAX - 1);

    // Exists-under-forall with the function: `forall x. exists y. f(x) = y`.
    let nested = vec![F::Forall(
        0,
        Box::new(F::Exists(
            1,
            Box::new(F::EqT(T::App(Box::new(T::Bound(0))), T::Bound(1))),
        )),
    )];
    run_instance(&nested, u64::MAX - 2);

    // Complementary exists/forall pair: unsat at every size.
    let complementary = vec![
        F::Exists(0, Box::new(F::Pred(T::Bound(0)))),
        F::Forall(1, Box::new(F::Not(Box::new(F::Pred(T::Bound(1)))))),
    ];
    run_instance(&complementary, u64::MAX - 3);

    // A Bool-sorted binder over a body that also quantifies the carrier.
    let bool_binder = vec![F::ForallBool(
        0,
        Box::new(F::Or(
            Box::new(F::BoolVar(0)),
            Box::new(F::Exists(1, Box::new(F::EqT(T::Bound(1), T::Bound(1))))),
        )),
    )];
    run_instance(&bool_binder, u64::MAX - 4);
}
