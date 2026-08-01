//! Encoding uninterpreted sorts as bit-vectors by the **finite model property**,
//! so the pure-Rust BV backend can decide `UF`.
//!
//! # Why this exists
//!
//! After the quantifier-reachability work (`fdfb910b`), 51 of the 159
//! declared-status files in the 300-file UF slice — **32 % of the
//! parity-relevant set, the largest single bucket** — reach the backend and are
//! turned away with `term #N has sort (Uninterpreted k) that the pure-Rust BV
//! backend cannot bit-blast`. These are `UF` benchmarks: uninterpreted functions
//! over uninterpreted sorts, no bit-vectors anywhere. Bit-blasting is simply
//! being handed a sort it has no encoding for.
//!
//! # The encoding
//!
//! An EUF formula containing `n` distinct terms of an uninterpreted sort is
//! satisfiable iff it is satisfiable over a domain of size `≤ n` — nothing in the
//! formula can distinguish more elements than it can name. So each uninterpreted
//! sort is given a domain of exactly its symbol count and its elements are
//! encoded as `BitVec(w)` with `2^w ≥ n`. Equality becomes bit-vector equality,
//! which is what congruence reasoning needs and all it needs.
//!
//! This runs **after** function abstraction, and that ordering is not incidental:
//!
//! - Running it first would leave every function declaration with uninterpreted
//!   parameter/result sorts, so applying one to a bit-vector argument is an
//!   immediate sort error.
//! - Running it after means there is nothing left to do but rename leaves.
//!   `abstract_functions` replaces every application with a fresh variable, so no
//!   `Op::Apply` node of uninterpreted sort survives and the only remaining terms
//!   of that sort are **free symbols**. Every other operator that can carry them
//!   — `=`, `distinct`, `ite` — is sort-polymorphic and rebuilds unchanged over
//!   the new arguments.
//!
//! # Soundness
//!
//! The domain must be **at least** the number of distinct symbols. Too small a
//! domain forces two symbols to share a value, which can manufacture a
//! contradiction and produce a **wrong `unsat`** — the one error class this
//! project treats as unacceptable. The width is therefore computed from an actual
//! count, never assumed, and `encoding_is_wide_enough` pins the relationship in a
//! test that fails if the width is shrunk by one.
//!
//! Because the domain is large enough to keep every symbol distinct, the encoding
//! is *equisatisfiable*, so `unsat` transfers. The caller still declines to return
//! `sat` from it: such a model assigns bit-vector values to symbols the original
//! query holds at an uninterpreted sort, so it could not be replayed against the
//! original term, and this project requires every `sat` to replay.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Sort, SortId, SymbolId, TermArena, TermId, TermNode, Value};

use crate::backend::SolverError;
use crate::model::Model;

/// One round's uninterpreted-sort → bit-vector encoding: the rewritten
/// assertions plus the symbol correspondence needed to translate the backend's
/// model **back** into the original vocabulary.
///
/// The correspondence is load-bearing for the lazy CEGAR loop
/// ([`crate::euf::check_qf_ufbv_lazy`]): the loop's candidate-model inspectors
/// (`args_tuples_equal` / `results_differ`) and the final replay all reason over
/// ORIGINAL terms, while the backend's assignment is keyed by the fresh encoded
/// `!us*` symbols. Without translating the assignment back, every original
/// uninterpreted symbol keeps the backend's *distinct-by-construction*
/// completion default, no argument tuples ever compare equal, zero congruence
/// lemmas are produced, and the loop declines — the measured
/// `pair_checks=22197, equal_arg_pairs=0` completeness gap.
pub(crate) struct UninterpretedEncoding {
    /// The assertions with every uninterpreted-sort symbol replaced by its
    /// bit-vector encoding.
    pub(crate) assertions: Vec<TermId>,
    /// `(original symbol, encoded bit-vector symbol, uninterpreted sort)` for
    /// every replaced symbol, in deterministic first-encounter order.
    pub(crate) symbols: Vec<(SymbolId, SymbolId, SortId)>,
}

/// Translates a backend model over the ENCODED vocabulary back onto the
/// ORIGINAL uninterpreted-sort symbols: each original symbol receives
/// `Value::Uninterpreted` whose token is its encoded symbol's bit-vector value.
///
/// Equality is the only operation on an uninterpreted carrier, and the token map
/// is value-preserving on equality (equal bit-vector values ⇔ equal tokens), so
/// evaluating an original term under the translated assignment agrees with
/// evaluating its encoding under the backend's assignment. Symbols the backend
/// left without a scalar value are skipped (conservative: the CEGAR loop treats
/// an unresolved argument as *not provably equal* and adds no lemma).
pub(crate) fn lift_encoded_model(model: &Model, encoding: &UninterpretedEncoding) -> Model {
    let mut out = model.clone();
    for &(original, encoded, sort) in &encoding.symbols {
        let token = match model.get(encoded) {
            Some(Value::Bv { value, .. }) => value,
            Some(Value::Bool(b)) => u128::from(b),
            _ => continue,
        };
        out.set(original, Value::Uninterpreted { sort, value: token });
    }
    out
}

/// Encodes every uninterpreted-sort symbol in `assertions` as a bit-vector.
///
/// Returns `Ok(None)` when no uninterpreted sort occurs, so callers can keep
/// their existing path untouched.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if declaring a replacement symbol or
/// rebuilding a term fails in the arena.
pub(crate) fn encode_uninterpreted_symbols(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Option<UninterpretedEncoding>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());

    // Group the uninterpreted-sort symbols by sort, in first-encounter order so
    // the assigned widths and names are deterministic.
    let mut order: Vec<Sort> = Vec::new();
    let mut by_sort: HashMap<Sort, Vec<SymbolId>> = HashMap::new();
    let mut seen_symbol: HashSet<SymbolId> = HashSet::new();
    for &assertion in assertions {
        for term in subterms(arena, assertion) {
            let TermNode::Symbol(symbol) = *arena.node(term) else {
                continue;
            };
            let sort = arena.symbol(symbol).1;
            if !matches!(sort, Sort::Uninterpreted(_)) {
                continue;
            }
            if !seen_symbol.insert(symbol) {
                continue;
            }
            if !by_sort.contains_key(&sort) {
                order.push(sort);
            }
            by_sort.entry(sort).or_default().push(symbol);
        }
    }
    if order.is_empty() {
        return Ok(None);
    }

    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut symbol_map: Vec<(SymbolId, SymbolId, SortId)> = Vec::new();
    for sort in &order {
        let symbols = &by_sort[sort];
        let width = domain_width(symbols.len());
        let Sort::Uninterpreted(sort_id) = *sort else {
            unreachable!("only uninterpreted sorts are collected above");
        };
        for (index, &symbol) in symbols.iter().enumerate() {
            let name = fresh_name(arena, &format!("!us{}_{index}_", sort_index(*sort)));
            let encoded = arena
                .declare_internal(&name, Sort::BitVec(width))
                .map_err(err)?;
            let original = arena.var(symbol);
            let replacement = arena.var(encoded);
            replacements.insert(original, replacement);
            symbol_map.push((symbol, encoded, sort_id));
        }
    }

    let mut memo = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        out.push(
            axeyum_rewrite::replace_subterms(arena, assertion, &replacements, &mut memo)
                .map_err(err)?,
        );
    }
    Ok(Some(UninterpretedEncoding {
        assertions: out,
        symbols: symbol_map,
    }))
}

/// The bit width whose domain holds `count` distinct elements: the smallest `w`
/// with `2^w ≥ count`, and at least 1.
///
/// Never round this down. A domain smaller than the symbol count forces two
/// symbols to collide, which can produce a wrong `unsat` (module docs).
fn domain_width(count: usize) -> u32 {
    let mut width = 1_u32;
    while (1_u128 << width) < count as u128 {
        width += 1;
    }
    width
}

fn sort_index(sort: Sort) -> usize {
    match sort {
        Sort::Uninterpreted(id) => id.index(),
        _ => 0,
    }
}

/// A name not already present in the arena's **internal** namespace.
///
/// Symbols persist for the arena's lifetime while this pass runs once per
/// refinement round, so a plain counter would reuse a name — either erroring on
/// a sort clash or, worse, silently making two distinct symbols share one
/// encoding.
///
/// It must be [`TermArena::find_internal_symbol`], not `find_symbol`: the user
/// and internal namespaces are disjoint, so `find_symbol` never sees anything
/// `declare_internal` minted and every probe would report "free". That mistake
/// produced 228 `symbol ... already declared with sort (_ BitVec 1), requested
/// (_ BitVec 2)` failures across the UF slice, and its quiet form — a reuse where
/// the sorts happen to agree — is worse than the loud one.
fn fresh_name(arena: &TermArena, prefix: &str) -> String {
    let mut suffix = 0_u32;
    loop {
        let candidate = format!("{prefix}{suffix}");
        if arena.find_internal_symbol(&candidate).is_none() {
            return candidate;
        }
        suffix += 1;
    }
}

/// Every subterm of `term`, each visited once.
fn subterms(arena: &TermArena, term: TermId) -> Vec<TermId> {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut out = Vec::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        out.push(current);
        if let TermNode::App { args, .. } = arena.node(current) {
            stack.extend(args.iter().copied());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn uninterpreted_symbol_count(arena: &TermArena, assertions: &[TermId]) -> usize {
        let mut count = 0;
        for &assertion in assertions {
            for term in subterms(arena, assertion) {
                if let TermNode::Symbol(symbol) = *arena.node(term)
                    && matches!(arena.symbol(symbol).1, Sort::Uninterpreted(_))
                {
                    count += 1;
                }
            }
        }
        count
    }

    #[test]
    fn encoding_is_wide_enough_for_every_symbol() {
        // The soundness property. A domain smaller than the symbol count forces a
        // collision, which can manufacture a contradiction and yield a wrong
        // `unsat`. This fails if `domain_width` is ever shrunk by one.
        for count in 1_usize..=64 {
            let width = domain_width(count);
            assert!(
                (1_u128 << width) >= count as u128,
                "width {width} cannot hold {count} distinct elements"
            );
            assert!(width >= 1);
        }
    }

    #[test]
    fn width_is_minimal_so_the_encoding_stays_small() {
        assert_eq!(domain_width(1), 1);
        assert_eq!(domain_width(2), 1);
        assert_eq!(domain_width(3), 2);
        assert_eq!(domain_width(4), 2);
        assert_eq!(domain_width(5), 3);
        assert_eq!(domain_width(8), 3);
        assert_eq!(domain_width(9), 4);
    }

    #[test]
    fn a_query_without_uninterpreted_sorts_is_left_alone() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let assertion = arena.eq(xv, xv).unwrap();

        assert!(
            encode_uninterpreted_symbols(&mut arena, &[assertion])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn uninterpreted_symbols_become_bit_vectors() {
        let mut arena = TermArena::new();
        let sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("S"));
        let a = arena.declare("a", sort).unwrap();
        let b = arena.declare("b", sort).unwrap();
        let (av, bv) = (arena.var(a), arena.var(b));
        let assertion = arena.eq(av, bv).unwrap();

        let encoding = encode_uninterpreted_symbols(&mut arena, &[assertion])
            .unwrap()
            .expect("an uninterpreted sort is present");
        let encoded = &encoding.assertions;

        assert_eq!(uninterpreted_symbol_count(&arena, encoded), 0);
        // Two symbols need a domain of 2, i.e. one bit.
        assert_eq!(arena.sort_of(encoded[0]), Sort::Bool); // `=` is still Bool
        // The symbol correspondence covers exactly the replaced symbols, so a
        // backend model can be translated back.
        let mut originals = encoding
            .symbols
            .iter()
            .map(|&(original, _, _)| original)
            .collect::<Vec<_>>();
        originals.sort();
        let mut expected = vec![a, b];
        expected.sort();
        assert_eq!(originals, expected);
    }

    #[test]
    fn distinct_symbols_get_distinct_encodings() {
        // Collapsing two symbols onto one variable would make `distinct a b`
        // unsatisfiable and hand back a wrong `unsat`.
        let mut arena = TermArena::new();
        let sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("S"));
        let a = arena.declare("a", sort).unwrap();
        let b = arena.declare("b", sort).unwrap();
        let (av, bv) = (arena.var(a), arena.var(b));
        let assertion = arena.eq(av, bv).unwrap();

        let encoded = encode_uninterpreted_symbols(&mut arena, &[assertion])
            .unwrap()
            .unwrap()
            .assertions;

        let TermNode::App { args, .. } = arena.node(encoded[0]).clone() else {
            panic!("expected an equality application");
        };
        assert_ne!(args[0], args[1], "distinct symbols must not be conflated");
    }

    #[test]
    fn two_uninterpreted_sorts_are_sized_independently() {
        let mut arena = TermArena::new();
        let first = Sort::Uninterpreted(arena.declare_uninterpreted_sort("S"));
        let second = Sort::Uninterpreted(arena.declare_uninterpreted_sort("T"));
        let a = arena.declare("a", first).unwrap();
        let b = arena.declare("b", first).unwrap();
        let c = arena.declare("c", second).unwrap();
        let (av, bv, cv) = (arena.var(a), arena.var(b), arena.var(c));
        let left = arena.eq(av, bv).unwrap();
        let right = arena.eq(cv, cv).unwrap();

        let encoded = encode_uninterpreted_symbols(&mut arena, &[left, right])
            .unwrap()
            .unwrap()
            .assertions;

        assert_eq!(uninterpreted_symbol_count(&arena, &encoded), 0);
        assert_eq!(encoded.len(), 2);
    }

    #[test]
    fn running_twice_over_one_arena_does_not_reuse_names() {
        // Symbols outlive a single call, so a plain counter would collide.
        let mut arena = TermArena::new();
        let sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("S"));
        let a = arena.declare("a", sort).unwrap();
        let b = arena.declare("b", sort).unwrap();
        let (av, bv) = (arena.var(a), arena.var(b));
        let assertion = arena.eq(av, bv).unwrap();

        let first = encode_uninterpreted_symbols(&mut arena, &[assertion])
            .unwrap()
            .unwrap();
        let second = encode_uninterpreted_symbols(&mut arena, &[assertion])
            .unwrap()
            .unwrap();

        assert_eq!(uninterpreted_symbol_count(&arena, &first.assertions), 0);
        assert_eq!(uninterpreted_symbol_count(&arena, &second.assertions), 0);
    }

    #[test]
    fn lift_encoded_model_translates_tokens_back_to_original_symbols() {
        // The completeness anchor for the lazy CEGAR loop: the backend's model is
        // keyed by the encoded `!us*` symbols, and the loop inspects ORIGINAL
        // symbols. The lift must carry the backend's equality structure back:
        // equal bit-vector values become equal tokens, distinct stay distinct.
        let mut arena = TermArena::new();
        let sort_id = arena.declare_uninterpreted_sort("S");
        let sort = Sort::Uninterpreted(sort_id);
        let a = arena.declare("a", sort).unwrap();
        let b = arena.declare("b", sort).unwrap();
        let c = arena.declare("c", sort).unwrap();
        let (av, bv, cv) = (arena.var(a), arena.var(b), arena.var(c));
        let ab = arena.eq(av, bv).unwrap();
        let bc = arena.eq(bv, cv).unwrap();

        let encoding = encode_uninterpreted_symbols(&mut arena, &[ab, bc])
            .unwrap()
            .unwrap();
        assert_eq!(encoding.symbols.len(), 3);

        // A backend model that identifies a and b but separates c.
        let mut backend_model = Model::new();
        let width = match arena.symbol(encoding.symbols[0].1).1 {
            Sort::BitVec(w) => w,
            other => panic!("encoded symbol must be a bit-vector, got {other}"),
        };
        backend_model.set(encoding.symbols[0].1, Value::Bv { width, value: 1 });
        backend_model.set(encoding.symbols[1].1, Value::Bv { width, value: 1 });
        backend_model.set(encoding.symbols[2].1, Value::Bv { width, value: 0 });

        let lifted = lift_encoded_model(&backend_model, &encoding);
        let token = |symbol| match lifted.get(symbol) {
            Some(Value::Uninterpreted { sort, value }) => {
                assert_eq!(sort, sort_id);
                value
            }
            other => panic!("expected an uninterpreted token, got {other:?}"),
        };
        assert_eq!(token(a), token(b), "equal encodings must lift equal");
        assert_ne!(token(a), token(c), "distinct encodings must stay distinct");
    }
}
