//! Models: satisfying assignments keyed by Axeyum symbols.

use axeyum_ir::{Assignment, ConstructorId, FuncId, FuncValue, Rational, SortId, SymbolId, Value};

// Certificate DATA only, and from ONE module. Importing these through the
// crate-root facade resolved them to their five CHECKER modules; two of those
// reach the dispatcher, the theory solvers and back to here, which put `Model`
// -- the crate's base value type -- inside a dependency cycle of 65 modules and
// 115,840 lines, half the crate. Naming the data module directly leaves a
// largest cycle of 24. A value type may depend on the SHAPE of a certificate,
// never on the search or checker that produces it. Measured and gated by
// `scripts/analyze_solver_module_graph.py`.
#[cfg(feature = "full")]
use crate::quant_sat_certificates::{
    QuantifiedBoolModelSatCertificate, QuantifiedBvModelSatCertificate,
    QuantifiedGuardSatCertificate, QuantifiedSkolemSatCertificate, QuantifiedUfModelSatCertificate,
};

#[cfg(feature = "full")]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct QuantifiedSatCertificates {
    skolem: Vec<QuantifiedSkolemSatCertificate>,
    bool_model: Vec<QuantifiedBoolModelSatCertificate>,
    guard: Vec<QuantifiedGuardSatCertificate>,
    bv_model: Vec<QuantifiedBvModelSatCertificate>,
    uf_model: Vec<QuantifiedUfModelSatCertificate>,
}

/// A satisfying assignment produced by a backend, keyed by Axeyum
/// [`SymbolId`]s — never by backend AST handles (backend-model note).
///
/// Entries are kept sorted by symbol ID so iteration order is deterministic.
/// Uninterpreted-function interpretations (ADR-0013), when present, are kept in
/// a separate list sorted by [`FuncId`]. Restricted quantified results may
/// additionally carry checked Skolem certificates (ADR-0096/0121), checked
/// free-Boolean universal models (ADR-0107), or checked finite-profile UF models
/// (ADR-0357/0358); use the full-profile `check_model` entry point rather than
/// evaluator-only replay when quantifiers are possible.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Model {
    entries: Vec<(SymbolId, Value)>,
    functions: Vec<(FuncId, FuncValue)>,
    /// Model-chosen interpretation of real division-by-zero, keyed by the
    /// numerator value (P2.5 free-division witnesses). SMT-LIB leaves real
    /// `(/ x 0)` unspecified; the solver's chosen value for each forced `x/0` is
    /// carried here so the `sat` replay (which re-evaluates the original
    /// division term) accepts the witness. Kept sorted by numerator for
    /// deterministic iteration; an empty map is exactly the total `x/0 = 0`
    /// evaluator convention. Mirrors [`Assignment::set_real_div_zero`].
    real_div_zero: Vec<(Rational, Rational)>,
    /// Model-chosen interpretation of a **wrong-constructor selector**, keyed by
    /// `(the selector's constructor, field index, the operand's value)`
    /// (ADR-1930). SMT-LIB leaves `sel_{c,i}(t)` unspecified when `t` was not
    /// built by `c`; the value the search chose is carried here so the `sat`
    /// replay (which re-evaluates the original selector term) accepts the
    /// witness. Kept in insertion order, which is deterministic: entries are
    /// appended by a single traversal of the query's selector sites in
    /// ascending `TermId`. An empty list is exactly the total
    /// `well_founded_default` evaluator convention. Mirrors
    /// [`Assignment::set_dt_select_witness`].
    dt_select_wrong_ctor: Vec<(ConstructorId, u32, Value, Value)>,
    /// Declared finite carrier size per uninterpreted sort (finite model
    /// finding, pure UF). An entry `(s, k)` asserts this model is a structure
    /// whose carrier for `s` is exactly the canonical token domain `0..k`;
    /// every [`Value::Uninterpreted`] token this model carries for `s` must
    /// then be `< k` (the independent quantified-UF checker enforces this and
    /// fails closed otherwise). Kept sorted by [`SortId`] for deterministic
    /// iteration.
    uninterpreted_cardinalities: Vec<(SortId, u32)>,
    /// Lazily allocated checked quantified certificates, grouped behind one
    /// pointer so adding a certificate family does not inflate every model.
    #[cfg(feature = "full")]
    quantified: Option<Box<QuantifiedSatCertificates>>,
}

impl Model {
    /// Creates an empty model.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts or replaces the value for `symbol`.
    pub fn set(&mut self, symbol: SymbolId, value: Value) {
        match self.entries.binary_search_by_key(&symbol, |&(s, _)| s) {
            Ok(i) => self.entries[i].1 = value,
            Err(i) => self.entries.insert(i, (symbol, value)),
        }
    }

    /// The value assigned to `symbol`, if present.
    pub fn get(&self, symbol: SymbolId) -> Option<Value> {
        self.entries
            .binary_search_by_key(&symbol, |(s, _)| *s)
            .ok()
            .map(|i| self.entries[i].1.clone())
    }

    /// Iterates over `(symbol, value)` pairs in symbol order.
    pub fn iter(&self) -> impl Iterator<Item = (SymbolId, Value)> + '_ {
        self.entries.iter().cloned()
    }

    /// Inserts or replaces the interpretation for uninterpreted function
    /// `func` (ADR-0013).
    pub fn set_function(&mut self, func: FuncId, value: FuncValue) {
        match self.functions.binary_search_by_key(&func, |(f, _)| *f) {
            Ok(i) => self.functions[i].1 = value,
            Err(i) => self.functions.insert(i, (func, value)),
        }
    }

    /// The interpretation assigned to `func`, if present.
    pub fn function(&self, func: FuncId) -> Option<&FuncValue> {
        self.functions
            .binary_search_by_key(&func, |(f, _)| *f)
            .ok()
            .map(|i| &self.functions[i].1)
    }

    /// Iterates over `(func, interpretation)` pairs in function order.
    pub fn functions(&self) -> impl Iterator<Item = (FuncId, &FuncValue)> + '_ {
        self.functions.iter().map(|(f, v)| (*f, v))
    }

    /// Records the model-chosen value of `(/ numerator 0)` (P2.5 free-division
    /// witness), replacing any previous entry for the same numerator. Entries
    /// are kept in a deterministic, overflow-free order (lexicographic on the
    /// normalized `(numerator, denominator)` representation — a stable total
    /// order, not the numeric one, which suffices for reproducible output and
    /// avoids the `Rational` `Ord` overflow panic on large model values).
    pub fn set_real_div_zero(&mut self, numerator: Rational, quotient: Rational) {
        match self
            .real_div_zero
            .binary_search_by_key(&div_zero_key(numerator), |&(n, _)| div_zero_key(n))
        {
            Ok(i) => self.real_div_zero[i].1 = quotient,
            Err(i) => self.real_div_zero.insert(i, (numerator, quotient)),
        }
    }

    /// The model-chosen value of `(/ numerator 0)`, if the model fixes one.
    pub fn real_div_zero(&self, numerator: Rational) -> Option<Rational> {
        self.real_div_zero
            .binary_search_by_key(&div_zero_key(numerator), |&(n, _)| div_zero_key(n))
            .ok()
            .map(|i| self.real_div_zero[i].1)
    }

    /// Iterates over the recorded real division-by-zero interpretations
    /// (`numerator -> quotient`) in the deterministic key order.
    pub fn real_div_zeros(&self) -> impl Iterator<Item = (Rational, Rational)> + '_ {
        self.real_div_zero.iter().copied()
    }

    /// Records the model-chosen value of `sel_{constructor,index}(operand)` for
    /// an operand built by a **different** constructor (ADR-1930).
    ///
    /// Returns `false` — and changes nothing — when a *different* value is
    /// already recorded for the same key, which is a congruence violation the
    /// caller must reject. Mirrors [`Assignment::set_dt_select_witness`].
    pub fn set_dt_select_witness(
        &mut self,
        constructor: ConstructorId,
        index: u32,
        operand: Value,
        value: Value,
    ) -> bool {
        for (c, i, key, recorded) in &self.dt_select_wrong_ctor {
            if *c == constructor && *i == index && *key == operand {
                return *recorded == value;
            }
        }
        self.dt_select_wrong_ctor
            .push((constructor, index, operand, value));
        true
    }

    /// Iterates the recorded wrong-constructor selector interpretations in
    /// insertion order (deterministic — see the field docs).
    pub fn dt_select_witnesses(
        &self,
    ) -> impl Iterator<Item = (ConstructorId, u32, &Value, &Value)> + '_ {
        self.dt_select_wrong_ctor
            .iter()
            .map(|(c, i, key, value)| (*c, *i, key, value))
    }

    /// Declares the finite carrier size of uninterpreted sort `sort` as the
    /// canonical token domain `0..cardinality` (finite model finding). A zero
    /// cardinality is meaningless (an empty carrier is not a first-order
    /// structure) and is ignored.
    pub fn set_uninterpreted_cardinality(&mut self, sort: SortId, cardinality: u32) {
        if cardinality == 0 {
            return;
        }
        match self
            .uninterpreted_cardinalities
            .binary_search_by_key(&sort, |&(s, _)| s)
        {
            Ok(i) => self.uninterpreted_cardinalities[i].1 = cardinality,
            Err(i) => self
                .uninterpreted_cardinalities
                .insert(i, (sort, cardinality)),
        }
    }

    /// The declared finite carrier size for `sort`, if this model records one.
    pub fn uninterpreted_cardinality(&self, sort: SortId) -> Option<u32> {
        self.uninterpreted_cardinalities
            .binary_search_by_key(&sort, |&(s, _)| s)
            .ok()
            .map(|i| self.uninterpreted_cardinalities[i].1)
    }

    /// Iterates over `(sort, cardinality)` entries in sort order.
    pub fn uninterpreted_cardinalities(&self) -> impl Iterator<Item = (SortId, u32)> + '_ {
        self.uninterpreted_cardinalities.iter().copied()
    }

    /// Inserts or replaces the checked Skolem certificate for its original
    /// quantified assertion. Entries stay in assertion-ID order.
    #[cfg(feature = "full")]
    pub fn set_quantified_sat_certificate(&mut self, cert: QuantifiedSkolemSatCertificate) {
        let certificates = &mut self.quantified.get_or_insert_with(Default::default).skolem;
        match certificates.binary_search_by_key(&cert.assertion, |candidate| candidate.assertion) {
            Ok(index) => certificates[index] = cert,
            Err(index) => certificates.insert(index, cert),
        }
    }

    /// The quantified-SAT certificate for `assertion`, if present.
    #[cfg(feature = "full")]
    pub fn quantified_sat_certificate(
        &self,
        assertion: axeyum_ir::TermId,
    ) -> Option<&QuantifiedSkolemSatCertificate> {
        let certificates = self
            .quantified
            .as_deref()
            .map_or(&[][..], |certificates| certificates.skolem.as_slice());
        certificates
            .binary_search_by_key(&assertion, |candidate| candidate.assertion)
            .ok()
            .map(|index| &certificates[index])
    }

    /// Iterates over quantified-SAT certificates in original assertion order.
    #[cfg(feature = "full")]
    pub fn quantified_sat_certificates(
        &self,
    ) -> impl Iterator<Item = &QuantifiedSkolemSatCertificate> {
        self.quantified
            .as_deref()
            .into_iter()
            .flat_map(|certificates| &certificates.skolem)
    }

    /// Inserts or replaces a checked free-Boolean certificate.
    #[cfg(feature = "full")]
    pub fn set_quantified_bool_model_sat_certificate(
        &mut self,
        cert: QuantifiedBoolModelSatCertificate,
    ) {
        let certificates = &mut self
            .quantified
            .get_or_insert_with(Default::default)
            .bool_model;
        match certificates.binary_search_by_key(&cert.assertion, |candidate| candidate.assertion) {
            Ok(index) => certificates[index] = cert,
            Err(index) => certificates.insert(index, cert),
        }
    }

    /// Returns the checked free-Boolean certificate for `assertion`.
    #[cfg(feature = "full")]
    pub fn quantified_bool_model_sat_certificate(
        &self,
        assertion: axeyum_ir::TermId,
    ) -> Option<&QuantifiedBoolModelSatCertificate> {
        let certificates = self
            .quantified
            .as_deref()
            .map_or(&[][..], |certificates| certificates.bool_model.as_slice());
        certificates
            .binary_search_by_key(&assertion, |candidate| candidate.assertion)
            .ok()
            .map(|index| &certificates[index])
    }

    /// Iterates over checked free-Boolean certificates in assertion order.
    #[cfg(feature = "full")]
    pub fn quantified_bool_model_sat_certificates(
        &self,
    ) -> impl Iterator<Item = &QuantifiedBoolModelSatCertificate> {
        self.quantified
            .as_deref()
            .into_iter()
            .flat_map(|certificates| &certificates.bool_model)
    }

    /// Inserts or replaces a checked outer-BV guard certificate.
    #[cfg(feature = "full")]
    pub fn set_quantified_guard_sat_certificate(&mut self, cert: QuantifiedGuardSatCertificate) {
        let certificates = &mut self.quantified.get_or_insert_with(Default::default).guard;
        match certificates.binary_search_by_key(&cert.assertion, |candidate| candidate.assertion) {
            Ok(index) => certificates[index] = cert,
            Err(index) => certificates.insert(index, cert),
        }
    }

    /// Returns the checked outer-BV guard certificate for `assertion`.
    #[cfg(feature = "full")]
    pub fn quantified_guard_sat_certificate(
        &self,
        assertion: axeyum_ir::TermId,
    ) -> Option<&QuantifiedGuardSatCertificate> {
        let certificates = self
            .quantified
            .as_deref()
            .map_or(&[][..], |certificates| certificates.guard.as_slice());
        certificates
            .binary_search_by_key(&assertion, |candidate| candidate.assertion)
            .ok()
            .map(|index| &certificates[index])
    }

    /// Iterates over checked outer-BV guard certificates in assertion order.
    #[cfg(feature = "full")]
    pub fn quantified_guard_sat_certificates(
        &self,
    ) -> impl Iterator<Item = &QuantifiedGuardSatCertificate> {
        self.quantified
            .as_deref()
            .into_iter()
            .flat_map(|certificates| &certificates.guard)
    }

    /// Inserts or replaces a checked quantified-BV model certificate.
    #[cfg(feature = "full")]
    pub fn set_quantified_bv_model_sat_certificate(
        &mut self,
        cert: QuantifiedBvModelSatCertificate,
    ) {
        let certificates = &mut self
            .quantified
            .get_or_insert_with(Default::default)
            .bv_model;
        match certificates.binary_search_by_key(&cert.assertion, |candidate| candidate.assertion) {
            Ok(index) => certificates[index] = cert,
            Err(index) => certificates.insert(index, cert),
        }
    }

    /// Returns the checked quantified-BV model certificate for `assertion`.
    #[cfg(feature = "full")]
    pub fn quantified_bv_model_sat_certificate(
        &self,
        assertion: axeyum_ir::TermId,
    ) -> Option<&QuantifiedBvModelSatCertificate> {
        let certificates = self
            .quantified
            .as_deref()
            .map_or(&[][..], |certificates| certificates.bv_model.as_slice());
        certificates
            .binary_search_by_key(&assertion, |candidate| candidate.assertion)
            .ok()
            .map(|index| &certificates[index])
    }

    /// Iterates over checked quantified-BV model certificates in assertion order.
    #[cfg(feature = "full")]
    pub fn quantified_bv_model_sat_certificates(
        &self,
    ) -> impl Iterator<Item = &QuantifiedBvModelSatCertificate> {
        self.quantified
            .as_deref()
            .into_iter()
            .flat_map(|certificates| &certificates.bv_model)
    }

    /// Inserts or replaces a checked finite-profile quantified-UF certificate.
    #[cfg(feature = "full")]
    pub fn set_quantified_uf_model_sat_certificate(
        &mut self,
        cert: QuantifiedUfModelSatCertificate,
    ) {
        let certificates = &mut self
            .quantified
            .get_or_insert_with(Default::default)
            .uf_model;
        match certificates.binary_search_by_key(&cert.assertion, |candidate| candidate.assertion) {
            Ok(index) => certificates[index] = cert,
            Err(index) => certificates.insert(index, cert),
        }
    }

    /// Returns the checked finite-profile quantified-UF certificate for `assertion`.
    #[cfg(feature = "full")]
    pub fn quantified_uf_model_sat_certificate(
        &self,
        assertion: axeyum_ir::TermId,
    ) -> Option<&QuantifiedUfModelSatCertificate> {
        let certificates = self
            .quantified
            .as_deref()
            .map_or(&[][..], |certificates| certificates.uf_model.as_slice());
        certificates
            .binary_search_by_key(&assertion, |candidate| candidate.assertion)
            .ok()
            .map(|index| &certificates[index])
    }

    /// Iterates over checked finite-profile quantified-UF certificates.
    #[cfg(feature = "full")]
    pub fn quantified_uf_model_sat_certificates(
        &self,
    ) -> impl Iterator<Item = &QuantifiedUfModelSatCertificate> {
        self.quantified
            .as_deref()
            .into_iter()
            .flat_map(|certificates| &certificates.uf_model)
    }

    /// Number of assigned symbols.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the model assigns no symbols.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Drops every symbol entry `keep` rejects, leaving **every other component
    /// of the model untouched**.
    ///
    /// This is how a solver route narrows a model to the caller's vocabulary
    /// (roadmap 2.11). It exists because the obvious alternative — build a fresh
    /// [`Model`] and copy the fields you remember — is a defect generator: it
    /// silently drops whatever the author did not list, and the SOUND-1 family
    /// is three separate instances of exactly that
    /// (`c41dd4264` dropped `real_div_zero`, `9b259f7c2` dropped `functions`,
    /// and an audit of eleven more sites found five dropping `functions` and
    /// most dropping `real_div_zero`).
    ///
    /// The distinction that makes this a *fix* rather than a *check*: a re-replay
    /// against [`Self::to_assignment`] — SOUND-1's guard 2 — can only ever see
    /// the three components an [`Assignment`] can hold. It is structurally blind
    /// to [`Self::uninterpreted_cardinalities`] and to the quantified
    /// certificates, so at a site whose only loss is one of those, guard 2 is a
    /// check that cannot fail on the defect the site has. Narrowing through this
    /// method instead means no component *can* be lost, including components
    /// added to `Model` after this was written — a rebuild-and-copy would have
    /// to be edited to keep carrying them, and this does not.
    pub fn retain_symbols(&mut self, mut keep: impl FnMut(SymbolId) -> bool) {
        self.entries.retain(|&(symbol, _)| keep(symbol));
    }

    /// Copies into this model every component of `assignment` that is **not** a
    /// symbol binding: uninterpreted-function interpretations and the chosen
    /// real division-at-zero interpretation.
    ///
    /// The companion to [`Self::retain_symbols`] for the routes that build a
    /// model out of an [`Assignment`] rather than out of another `Model`, and
    /// which therefore choose their symbol set with their own loop. Those are
    /// precisely the two components such a route replays against and then
    /// forgets to emit: `functions` is the `9b259f7c2` defect (the caller's
    /// replay returned `Err(UnboundFunction(..))`) and `real_div_zero` is the
    /// `c41dd4264` one.
    ///
    /// `Assignment` holds exactly three things — bindings, functions, and the
    /// division-at-zero map — so together with the caller's own symbol loop this
    /// carries all of it.
    pub fn carry_assignment_components(&mut self, assignment: &Assignment) {
        for (func, interpretation) in assignment.functions() {
            self.set_function(func, interpretation.clone());
        }
        for (numerator, quotient) in assignment.real_div_zeros() {
            self.set_real_div_zero(numerator, quotient);
        }
        for (constructor, index, operand, value) in assignment.dt_select_witnesses() {
            self.set_dt_select_witness(constructor, index, operand.clone(), value.clone());
        }
    }

    /// Converts to an evaluator [`Assignment`] for check-by-evaluation —
    /// the level-1 evidence check (evidence-and-checking note).
    pub fn to_assignment(&self) -> Assignment {
        let mut asg = Assignment::new();
        for (s, v) in self.iter() {
            asg.set(s, v);
        }
        for (f, v) in &self.functions {
            asg.set_function(*f, v.clone());
        }
        for &(n, q) in &self.real_div_zero {
            asg.set_real_div_zero(n, q);
        }
        for (constructor, index, operand, value) in &self.dt_select_wrong_ctor {
            asg.set_dt_select_witness(*constructor, *index, operand.clone(), value.clone());
        }
        asg
    }
}

/// A deterministic, overflow-free sort key for a `Rational`: the lexicographic
/// pair of its normalized numerator and denominator. This is a stable total
/// order (distinct rationals get distinct keys because the representation is in
/// lowest terms with a positive denominator), used only to order the
/// division-by-zero entries reproducibly — it deliberately avoids the numeric
/// `Rational` `Ord`, which cross-multiplies and can overflow-panic on the large
/// values a model may assign.
fn div_zero_key(r: Rational) -> (i128, i128) {
    (r.numerator(), r.denominator())
}

#[cfg(test)]
mod tests {
    use super::Model;

    #[test]
    fn quantified_certificate_families_do_not_bloat_every_model() {
        assert!(
            std::mem::size_of::<Model>() <= 128,
            "Model grew beyond the result-size lint boundary"
        );
    }
}

/// Roadmap 2.11 — the two narrowing helpers, and the property that makes them a
/// fix rather than a check.
///
/// The audit behind item 2.11 found eleven sites emitting a `Model` narrower
/// than the state their replay ran against, in three different ways (five
/// dropped `functions`, most dropped `real_div_zero`, two dropped
/// `uninterpreted_cardinalities` and the quantified certificates). Every one was
/// a hand-written "build a fresh `Model` and copy the fields you remember".
///
/// The tests below pin the property that removes that whole class:
/// [`Model::retain_symbols`] changes the symbol entries and **provably nothing
/// else**, checked by `PartialEq` on the whole `Model` rather than by a list of
/// accessors this file would have to remember to extend.
#[cfg(test)]
mod sound2_narrowing_tests {
    use super::Model;
    use crate::quant_sat_certificates::{AffineSkolemWitness, QuantifiedSkolemSatCertificate};
    use axeyum_ir::{Assignment, FuncValue, Rational, Sort, SymbolId, TermArena, Value};

    /// A model with **every** component populated, over a real arena.
    /// `retain_symbols` is only interesting as a test subject against one of
    /// these: a component that is empty in the fixture cannot be observed to
    /// survive.
    fn fully_populated() -> (Model, SymbolId) {
        let mut arena = TermArena::new();
        let kept = arena.declare("kept", Sort::Int).expect("declare kept");
        let hidden = arena.declare("hidden", Sort::Int).expect("declare hidden");
        let func = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .expect("declare f");
        let opaque = arena.declare_uninterpreted_sort("U");
        let assertion = arena.var(kept);

        let mut model = Model::new();
        model.set(kept, Value::Int(7));
        model.set(hidden, Value::Int(9));
        model.set_function(
            func,
            FuncValue::constant(vec![Sort::BitVec(8)], Sort::BitVec(8), 4).define(&[1], 2),
        );
        model.set_real_div_zero(Rational::integer(5), Rational::integer(100));
        model.set_uninterpreted_cardinality(opaque, 3);
        model.set_quantified_sat_certificate(QuantifiedSkolemSatCertificate {
            assertion,
            universals: vec![kept],
            existential: hidden,
            witness: AffineSkolemWitness {
                terms: Vec::new(),
                constant: Rational::integer(1),
            },
        });
        (model, hidden)
    }

    /// The fixture's own control. Without it, a component silently arriving
    /// empty would make the test below pass for the wrong reason — the audit
    /// this fixes is precisely a family of components nobody noticed were
    /// missing.
    #[test]
    fn the_fixture_populates_every_component_of_model() {
        let (model, _) = fully_populated();
        assert_eq!(model.len(), 2, "symbol entries");
        assert_eq!(model.functions().count(), 1, "function interpretations");
        assert_eq!(model.real_div_zeros().count(), 1, "real division-at-zero");
        assert_eq!(
            model.uninterpreted_cardinalities().count(),
            1,
            "uninterpreted carrier cardinalities"
        );
        assert_eq!(
            model.quantified_sat_certificates().count(),
            1,
            "quantified sat certificates"
        );
    }

    /// The whole point of the helper. Narrowing drops the symbol entry it was
    /// told to drop, and putting that one entry back reproduces the original
    /// model **exactly** — so nothing else moved.
    ///
    /// This assertion is `PartialEq` on `Model`, not a list of accessors: a
    /// component added to `Model` after today is covered the moment the fixture
    /// populates it, and a reimplementation of `retain_symbols` as
    /// rebuild-and-copy fails here rather than shipping a narrower certificate.
    ///
    /// DIES ON: reimplementing `retain_symbols` as anything that does not start
    /// from the whole model (a field-by-field rebuild that forgets one).
    #[test]
    fn retain_symbols_changes_the_symbol_entries_and_nothing_else() {
        let (original, hidden) = fully_populated();
        let mut narrowed = original.clone();
        narrowed.retain_symbols(|symbol| symbol != hidden);
        assert_eq!(narrowed.get(hidden), None, "the hidden symbol must be gone");
        assert_eq!(narrowed.len(), 1, "the other symbol must survive");

        narrowed.set(hidden, Value::Int(9));
        assert_eq!(
            narrowed, original,
            "retain_symbols altered a component other than the symbol entries"
        );
    }

    /// DIES ON: deleting the `functions` loop in `carry_assignment_components`.
    #[test]
    fn carry_assignment_components_carries_function_interpretations() {
        let mut arena = TermArena::new();
        let func = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .expect("declare f");
        let interpretation =
            FuncValue::constant(vec![Sort::BitVec(8)], Sort::BitVec(8), 4).define(&[1], 2);
        let mut assignment = Assignment::new();
        assignment.set_function(func, interpretation.clone());

        let mut model = Model::new();
        model.carry_assignment_components(&assignment);
        assert_eq!(
            model.function(func),
            Some(&interpretation),
            "a replay that consulted this interpretation emitted a model without it \
             — the caller's replay then fails with UnboundFunction (9b259f7c2)"
        );
    }

    /// DIES ON: deleting the `real_div_zeros` loop in
    /// `carry_assignment_components`.
    #[test]
    fn carry_assignment_components_carries_the_real_div_zero_witness() {
        let mut assignment = Assignment::new();
        assignment.set_real_div_zero(Rational::integer(5), Rational::integer(100));

        let mut model = Model::new();
        model.carry_assignment_components(&assignment);
        assert_eq!(
            model.real_div_zero(Rational::integer(5)),
            Some(Rational::integer(100)),
            "a replay that chose (/ 5 0) = 100 emitted a model without it, so the \
             caller's replay falls back to the total x/0 = 0 convention (c41dd4264)"
        );
    }

    /// The negative control: the helper must not invent components. Without
    /// this, "set every function to a default" would pass the two tests above.
    #[test]
    fn carry_assignment_components_of_an_empty_assignment_adds_nothing() {
        let mut model = Model::new();
        model.carry_assignment_components(&Assignment::new());
        assert_eq!(model, Model::new());
    }
}
