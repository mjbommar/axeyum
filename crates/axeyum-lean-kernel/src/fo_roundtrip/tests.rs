//! Tests for `fo_roundtrip.rs`.
//!
//! `FO.Term.size` and `FO.Formula.size` are `Definition`s, so admission proves
//! nothing about them: `FO.Formula -> Nat` is `FO.Formula -> Nat` whatever the
//! body computes, and a `size` that returned the constant `1` would type-check
//! identically (and would break the round trip below, which is the point). So
//! every `size` is pinned by `def_eq` at concrete, small, DISCRIMINATING
//! arguments — a formula whose two children have different sizes, so a body
//! that read the wrong child is caught.
//!
//! `FO.Term.decode_code` and `FO.Formula.decode_code` are `Theorem`s, so the
//! trusted gate DID check them; what the tests add is (a) the axiom footprint,
//! (b) the rendered type, so a silently weakened statement is a failure here,
//! and (c) the two obstruction measurements the module doc rests on.

use super::*;
use crate::Kernel;
use crate::fo_code::numeral;

struct Fixture {
    kernel: Kernel,
    p: FoRoundTripPrelude,
    c: CodeNames,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_roundtrip_prelude(&mut kernel).expect("FO round-trip prelude must build");
        let c = CodeNames::rebuild(&mut kernel, p.decode.numbering.code.syntax.nat);
        Self { kernel, p, c }
    }

    fn num(&mut self, n: u32) -> ExprId {
        numeral(&mut self.kernel, &self.c, n)
    }

    fn ctor(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let head = self.kernel.const_(name, vec![]);
        apply_all(&mut self.kernel, head, args)
    }

    fn var(&mut self, i: u32) -> ExprId {
        let idx = self.num(i);
        let name = self.p.decode.numbering.code.syntax.var;
        self.ctor(name, &[idx])
    }

    fn tsize(&mut self, t: ExprId) -> ExprId {
        size_app(&mut self.kernel, self.p.term_size, t)
    }

    fn fsize(&mut self, p: ExprId) -> ExprId {
        size_app(&mut self.kernel, self.p.formula_size, p)
    }

    fn tcode(&mut self, t: ExprId) -> ExprId {
        code_app(&mut self.kernel, self.p.decode.numbering.term_code, t)
    }

    fn fcode(&mut self, p: ExprId) -> ExprId {
        code_app(&mut self.kernel, self.p.decode.numbering.formula_code, p)
    }

    fn assert_eq_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            self.kernel.def_eq(got, want),
            "{what}: got {}, want {}",
            self.kernel.render_lean(got),
            self.kernel.render_lean(want)
        );
    }

    fn assert_ne_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            !self.kernel.def_eq(got, want),
            "{what}: expected these NOT to be definitionally equal, but {} = {}",
            self.kernel.render_lean(got),
            self.kernel.render_lean(want)
        );
    }

    /// An empty footprint is also what a MISSING name returns, so the
    /// membership assertion comes first.
    fn assert_axiom_free(&mut self, name: NameId, label: &str) {
        assert!(
            self.kernel.environment().contains(name),
            "{label} must be declared before its footprint means anything"
        );
        let footprint = self.kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, but rests on {:?}",
            footprint
                .iter()
                .map(|id| self.kernel.display_name(*id).to_string())
                .collect::<Vec<_>>()
        );
    }
}

// ============================================================================
// FO.Term.size and FO.Formula.size, at discriminating arguments.
// ============================================================================

#[test]
fn term_size_counts_every_node() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;

    // size (var 0) = 1, size (f0 0) = 1.
    let v0 = f.var(0);
    let got = f.tsize(v0);
    let want = f.num(1);
    f.assert_eq_expr(got, want, "size (var 0)");

    let zero = f.num(0);
    let c0 = f.ctor(syntax.f0, &[zero]);
    let got = f.tsize(c0);
    let want = f.num(1);
    f.assert_eq_expr(got, want, "size (f0 0)");

    // size (f1 0 (var 0)) = 2 -- the Nat field must NOT be counted, so a body
    // that added the symbol index would give 2 here as well; the f1 at symbol
    // index 3 below is what discriminates that.
    let inner = f.ctor(syntax.f1, &[zero, v0]);
    let got = f.tsize(inner);
    let want = f.num(2);
    f.assert_eq_expr(got, want, "size (f1 0 (var 0))");

    let three = f.num(3);
    let wide = f.ctor(syntax.f1, &[three, v0]);
    let got = f.tsize(wide);
    let want = f.num(2);
    f.assert_eq_expr(got, want, "size (f1 3 (var 0)) ignores the symbol index");

    // size (f2 0 (var 0) (f1 0 (var 0))) = 1 + 1 + 2 = 4, and the two children
    // have DIFFERENT sizes, so reading one child twice is caught.
    let both = f.ctor(syntax.f2, &[zero, v0, inner]);
    let got = f.tsize(both);
    let want = f.num(4);
    f.assert_eq_expr(got, want, "size (f2 0 (var 0) (f1 0 (var 0)))");
}

#[test]
fn formula_size_counts_its_term_fields_too() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;
    let zero = f.num(0);
    let v0 = f.var(0);
    let inner = f.ctor(syntax.f1, &[zero, v0]);

    // size bot = 1.
    let bot = f.ctor(syntax.bot, &[]);
    let got = f.fsize(bot);
    let want = f.num(1);
    f.assert_eq_expr(got, want, "size bot");

    // size (eqf (var 0) (f1 0 (var 0))) = 1 + 1 + 2 = 4; the two term fields
    // have different sizes.
    let atom = f.ctor(syntax.eqf, &[v0, inner]);
    let got = f.fsize(atom);
    let want = f.num(4);
    f.assert_eq_expr(got, want, "size (eqf (var 0) (f1 0 (var 0)))");

    // size (rel1 2 (f1 0 (var 0))) = 1 + 2 = 3.
    let two = f.num(2);
    let rel = f.ctor(syntax.rel1, &[two, inner]);
    let got = f.fsize(rel);
    let want = f.num(3);
    f.assert_eq_expr(got, want, "size (rel1 2 (f1 0 (var 0)))");

    // size (all (eqf (var 0) (f1 0 (var 0)))) = 1 + 4 = 5.
    let quantified = f.ctor(syntax.all, &[atom]);
    let got = f.fsize(quantified);
    let want = f.num(5);
    f.assert_eq_expr(got, want, "size (all (eqf …))");

    // size (imp bot (all …)) = 1 + 1 + 5 = 7; asymmetric children again.
    let implication = f.ctor(syntax.imp, &[bot, quantified]);
    let got = f.fsize(implication);
    let want = f.num(7);
    f.assert_eq_expr(got, want, "size (imp bot (all …))");
}

// ============================================================================
// The round trip, as a statement.
// ============================================================================

#[test]
fn the_round_trip_theorems_have_the_stated_types() {
    let f = Fixture::new();
    for (name, want) in [
        (
            f.p.term_decode_code,
            "((x0 : FO.Term) -> ((x1 : AxNat) -> Eq.{1} FO.Term \
             (FO.Term.decodeAux (AxNat.add x1 (FO.Term.size x0)) (FO.Term.code x0)) x0))",
        ),
        (
            f.p.formula_decode_code,
            "((x0 : FO.Formula) -> ((x1 : AxNat) -> Eq.{1} FO.Formula \
             (FO.Formula.decodeAux (AxNat.add x1 (FO.Formula.size x0)) \
             (FO.Formula.code x0)) x0))",
        ),
        (
            f.p.term_decode_code_at_size,
            "((x0 : FO.Term) -> Eq.{1} FO.Term \
             (FO.Term.decodeAux (FO.Term.size x0) (FO.Term.code x0)) x0)",
        ),
        (
            f.p.formula_decode_code_at_size,
            "((x0 : FO.Formula) -> Eq.{1} FO.Formula \
             (FO.Formula.decodeAux (FO.Formula.size x0) (FO.Formula.code x0)) x0)",
        ),
    ] {
        let declaration = f
            .kernel
            .environment()
            .get(name)
            .expect("the theorem must be declared");
        let ty = declaration.ty();
        let rendered = f.kernel.render_lean(ty);
        assert_eq!(
            rendered,
            want,
            "{} has the wrong statement",
            f.kernel.display_name(name)
        );
    }
}

/// The round trip is a `Π`-statement about ALL terms, but an instance at a
/// concrete code is still worth pinning: it ties the theorem to the same
/// numerals `fo_decode/tests.rs` checks the decoder against, so a theorem
/// about some OTHER `decodeAux` would fail here.
#[test]
fn the_round_trip_instantiates_at_a_concrete_term() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;
    let zero = f.num(0);
    let v0 = f.var(0);
    let t = f.ctor(syntax.f1, &[zero, v0]);

    let size = f.tsize(t);
    let code = f.tcode(t);
    let decoded = decode_at(&mut f.kernel, f.p.decode.term_decode_aux, size, code);
    f.assert_eq_expr(
        decoded,
        t,
        "decodeAux (size t) (code t) = t at f1 0 (var 0)",
    );
}

#[test]
fn the_round_trip_instantiates_at_a_concrete_formula() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;
    let v0 = f.var(0);
    let p = f.ctor(syntax.eqf, &[v0, v0]);

    let size = f.fsize(p);
    let code = f.fcode(p);
    let decoded = decode_at(&mut f.kernel, f.p.decode.formula_decode_aux, size, code);
    f.assert_eq_expr(
        decoded,
        p,
        "decodeAux (size p) (code p) = p at eqf (var 0) (var 0)",
    );
}

// ============================================================================
// The obstruction the module doc rests on.
// ============================================================================

/// `Nat.le (size x) (code x)` — what the SELF-fuelled `decode n := decodeAux n
/// n` would need — is FALSE, and this is the measurement rather than the
/// claim: `FO.Term.code (FO.Term.var 0)` and `FO.Formula.code
/// FO.Formula.bot` are both `Nat.zero`, while both sizes are `1`.
#[test]
fn size_is_not_bounded_by_the_code() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;

    let v0 = f.var(0);
    let code = f.tcode(v0);
    let zero = f.num(0);
    f.assert_eq_expr(code, zero, "FO.Term.code (var 0)");
    let size = f.tsize(v0);
    let one = f.num(1);
    f.assert_eq_expr(size, one, "FO.Term.size (var 0)");
    f.assert_ne_expr(size, code, "size (var 0) vs code (var 0)");

    let bot = f.ctor(syntax.bot, &[]);
    let code = f.fcode(bot);
    let zero = f.num(0);
    f.assert_eq_expr(code, zero, "FO.Formula.code bot");
    let size = f.fsize(bot);
    let one = f.num(1);
    f.assert_eq_expr(size, one, "FO.Formula.size bot");
    f.assert_ne_expr(size, code, "size bot vs code bot");
}

// ============================================================================
// The commuting lemma.
// ============================================================================

#[test]
fn the_commuting_lemma_and_the_image_lemma_have_the_stated_types() {
    let f = Fixture::new();
    for (name, want) in [
        (
            f.p.subst_code_aux_commutes,
            "((x0 : FO.Formula) -> ((x1 : FO.Term) -> ((x2 : AxNat) -> ((x3 : AxNat) -> \
             Eq.{1} AxNat (FO.Code.substCodeAux (AxNat.add x2 (FO.Formula.size x0)) \
             (AxNat.add x3 (FO.Term.size x1)) (FO.Formula.code x0) (FO.Term.code x1)) \
             (FO.Formula.code (FO.Formula.subst x0 (FO.Subst.cons x1 FO.Subst.id)))))))",
        ),
        (
            f.p.is_formula_code_aux_code,
            "((x0 : FO.Formula) -> ((x1 : AxNat) -> Eq.{1} Bool \
             (FO.Code.isFormulaCodeAux (AxNat.add x1 (FO.Formula.size x0)) \
             (FO.Formula.code x0)) Bool.true))",
        ),
    ] {
        let declaration = f
            .kernel
            .environment()
            .get(name)
            .expect("the theorem must be declared");
        let ty = declaration.ty();
        let rendered = f.kernel.render_lean(ty);
        assert_eq!(
            rendered,
            want,
            "{} has the wrong statement",
            f.kernel.display_name(name)
        );
    }
}

/// `FO.Code.substCodeAux` is a `Definition`, so its admission proves nothing:
/// a body that dropped the substitution, or substituted at the wrong index,
/// has the same type. Pinned at a concrete, two-symbol instance:
/// substituting `FO.Term.f0 0` for de Bruijn index `0` in
/// `FO.Formula.eqf (var 0) (var 0)` must give the code of
/// `FO.Formula.eqf (f0 0) (f0 0)`, which is a DIFFERENT numeral.
#[test]
fn subst_code_aux_actually_substitutes() {
    let mut f = Fixture::new();
    let syntax = f.p.decode.numbering.code.syntax;
    let zero = f.num(0);
    let v0 = f.var(0);
    let symbol = f.ctor(syntax.f0, &[zero]);
    let before = f.ctor(syntax.eqf, &[v0, v0]);
    let after = f.ctor(syntax.eqf, &[symbol, symbol]);

    let fp = f.fsize(before);
    let ft = f.tsize(symbol);
    let cp = f.fcode(before);
    let ct = f.tcode(symbol);
    let got = {
        let head = f.kernel.const_(f.p.subst_code_aux, vec![]);
        apply_all(&mut f.kernel, head, &[fp, ft, cp, ct])
    };
    let want = f.fcode(after);
    f.assert_eq_expr(got, want, "substCodeAux at eqf (var 0) (var 0) := f0 0");

    // …and the two codes really are different, so the check above is not
    // satisfied by an identity function.
    let unchanged = f.fcode(before);
    f.assert_ne_expr(want, unchanged, "the substituted code differs");
}

// ============================================================================
// The every-declaration sweep.
// ============================================================================

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.term_size, "FO.Term.size"),
        (p.formula_size, "FO.Formula.size"),
        (p.term_decode_code, "FO.Term.decode_code"),
        (p.formula_decode_code, "FO.Formula.decode_code"),
        (p.term_decode_code_at_size, "FO.Term.decode_code_at_size"),
        (
            p.formula_decode_code_at_size,
            "FO.Formula.decode_code_at_size",
        ),
        (p.subst_code_aux, "FO.Code.substCodeAux"),
        (p.subst_code_aux_commutes, "FO.Code.substCodeAux_commutes"),
        (p.is_formula_code_aux, "FO.Code.isFormulaCodeAux"),
        (p.is_formula_code_aux_code, "FO.Code.isFormulaCodeAux_code"),
    ] {
        f.assert_axiom_free(name, label);
    }
}

/// The number of declarations `build_fo_roundtrip_prelude` adds on top of
/// `build_nat_prelude`: the whole `fo_syntax` + `fo_code` + `fo_numbering` +
/// `fo_decode` chain (48, pinned in `fo_decode/tests.rs`) plus this slice's
/// six. Pinned so drift in EITHER direction is a failure.
const FO_ARITHMETIZATION_WITH_ROUND_TRIP: usize = 58;

/// The every-declaration sweep for the arithmetization package including the
/// round trip, derived from the environment rather than from a list, with a
/// coverage control so it cannot pass vacuously.
#[test]
fn the_whole_round_trip_package_is_axiom_free() {
    use std::collections::{BTreeMap, BTreeSet};

    let baseline: BTreeSet<String> = {
        let mut kernel = Kernel::new();
        let _ = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        kernel
            .environment()
            .iter()
            .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
            .collect()
    };

    let mut kernel = Kernel::new();
    let _ = build_fo_roundtrip_prelude(&mut kernel).expect("FO round-trip prelude must build");
    let added: BTreeMap<String, NameId> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| {
            let id = declaration.name();
            (kernel.display_name(id).to_string(), id)
        })
        .filter(|(name, _)| !baseline.contains(name))
        .collect();

    for control in [
        "FO.Term.size",
        "FO.Formula.size",
        "FO.Term.decode_code",
        "FO.Formula.decode_code",
        "FO.Term.decode_code_at_size",
        "FO.Formula.decode_code_at_size",
        "FO.Formula.decodeAux",
        "FO.Formula.code_injective",
        "FO.Code.substCodeAux_commutes",
        "FO.Code.isFormulaCodeAux_code",
    ] {
        assert!(
            added.contains_key(control),
            "coverage control: {control} must be IN the set difference, or the \
             sweep below passes vacuously; the difference has {} rows",
            added.len()
        );
    }

    let assuming: Vec<&String> = added
        .iter()
        .filter(|(_, id)| !kernel.axiom_footprint(**id).is_empty())
        .map(|(name, _)| name)
        .collect();
    assert!(
        assuming.is_empty(),
        "these declarations rest on axioms: {assuming:?}"
    );

    assert_eq!(
        added.len(),
        FO_ARITHMETIZATION_WITH_ROUND_TRIP,
        "declaration count drifted; the names are {:?}",
        added.keys().collect::<Vec<_>>()
    );
}
