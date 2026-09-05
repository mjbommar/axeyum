//! Evaluation tests for `fo_decode.rs`.
//!
//! Every declaration here is a `Definition`, and a decoder is the worst case
//! for "admission proves nothing": `Nat -> FO.Formula` is `Nat -> FO.Formula`
//! whatever the body computes, and a tag tree with two arms swapped, or a
//! payload projection taken from the wrong side, type-checks identically.
//!
//! So every check below is a **round trip at a concrete code**: encode a small
//! term or formula with `FO.Term.code`/`FO.Formula.code`, hand the resulting
//! numeral to the decoder with enough fuel, and require `def_eq` back to the
//! original. That is the strongest available discriminator, because it ties
//! the decoder to a function whose own evaluation test already passed
//! (`fo_numbering/tests.rs` pins those codes against hand-computed numerals).
//!
//! It is NOT the round-trip THEOREM: these are eleven instances, not a
//! statement about all terms. See the module doc for what the theorem costs.

use super::*;
use crate::Kernel;
use crate::fo_code::{nsucc, numeral};

struct Fixture {
    kernel: Kernel,
    p: FoDecodePrelude,
    c: CodeNames,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_decode_prelude(&mut kernel).expect("FO decode prelude must build");
        let c = CodeNames::rebuild(&mut kernel, p.numbering.code.syntax.nat);
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
        let name = self.p.numbering.code.syntax.var;
        self.ctor(name, &[idx])
    }

    fn tcode(&mut self, t: ExprId) -> ExprId {
        let f = self.kernel.const_(self.p.numbering.term_code, vec![]);
        self.kernel.app(f, t)
    }

    fn fcode(&mut self, p: ExprId) -> ExprId {
        let f = self.kernel.const_(self.p.numbering.formula_code, vec![]);
        self.kernel.app(f, p)
    }

    /// `FO.Term.decodeAux <fuel> <code>`.
    fn tdecode_aux(&mut self, fuel: u32, code: ExprId) -> ExprId {
        let f = self.num(fuel);
        let d = self.kernel.const_(self.p.term_decode_aux, vec![]);
        apply_all(&mut self.kernel, d, &[f, code])
    }

    /// `FO.Formula.decodeAux <fuel> <code>`.
    fn fdecode_aux(&mut self, fuel: u32, code: ExprId) -> ExprId {
        let f = self.num(fuel);
        let d = self.kernel.const_(self.p.formula_decode_aux, vec![]);
        apply_all(&mut self.kernel, d, &[f, code])
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
            "{what}: expected these to DIFFER, both are {}",
            self.kernel.render_lean(got)
        );
    }

    fn assert_axiom_free(&mut self, name: NameId, what: &str) {
        assert!(
            self.kernel.environment().contains(name),
            "{what}: not in the environment at all"
        );
        let footprint = self.kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{what}: axiom footprint must be empty, got {footprint:?}"
        );
    }
}

/// `FO.Term.decodeAux` inverts `FO.Term.code` at every constructor, given
/// enough fuel. Each of the four is present, so a swapped tag arm shows up.
#[test]
fn term_decode_aux_inverts_the_code_at_every_constructor() {
    let mut f = Fixture::new();

    let cases: Vec<(&str, ExprId)> = {
        let v0 = f.var(0);
        let v2 = f.var(2);
        let c0 = {
            let k = f.num(0);
            let name = f.p.numbering.code.syntax.f0;
            f.ctor(name, &[k])
        };
        let u1 = {
            let k = f.num(0);
            let inner = f.var(0);
            let name = f.p.numbering.code.syntax.f1;
            f.ctor(name, &[k, inner])
        };
        let u2 = {
            let k = f.num(0);
            let a = f.var(0);
            let b = f.var(0);
            let name = f.p.numbering.code.syntax.f2;
            f.ctor(name, &[k, a, b])
        };
        vec![
            ("var 0", v0),
            ("var 2", v2),
            ("f0 0", c0),
            ("f1 0 (var 0)", u1),
            ("f2 0 (var 0) (var 0)", u2),
        ]
    };

    for (label, term) in cases {
        let code = f.tcode(term);
        let back = f.tdecode_aux(4, code);
        f.assert_eq_expr(back, term, &format!("decodeAux 4 (code ({label}))"));
    }
}

/// `FO.Formula.decodeAux` inverts `FO.Formula.code` at every constructor.
/// `all` versus `ex` is the pair a swapped arm would collapse, and `ex` is the
/// CATCH-ALL arm, so it is also the one an off-by-one in the tag tree lands in.
#[test]
fn formula_decode_aux_inverts_the_code_at_every_constructor() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.numbering.code.syntax.bot, vec![]);

    let cases: Vec<(&str, ExprId)> = {
        let eq = {
            let a = f.var(0);
            let b = f.var(0);
            let name = f.p.numbering.code.syntax.eqf;
            f.ctor(name, &[a, b])
        };
        let r1 = {
            let k = f.num(0);
            let t = f.var(0);
            let name = f.p.numbering.code.syntax.rel1;
            f.ctor(name, &[k, t])
        };
        let r2 = {
            let k = f.num(0);
            let a = f.var(0);
            let b = f.var(0);
            let name = f.p.numbering.code.syntax.rel2;
            f.ctor(name, &[k, a, b])
        };
        let mut out = vec![("bot", bot), ("eqf (var 0) (var 0)", eq)];
        out.push(("rel1 0 (var 0)", r1));
        out.push(("rel2 0 (var 0) (var 0)", r2));
        for (label, name) in [
            ("and_ bot bot", f.p.numbering.code.syntax.and_),
            ("or_ bot bot", f.p.numbering.code.syntax.or_),
            ("imp bot bot", f.p.numbering.code.syntax.imp),
        ] {
            let e = f.ctor(name, &[bot, bot]);
            out.push((label, e));
        }
        for (label, name) in [
            ("all bot", f.p.numbering.code.syntax.all),
            ("ex bot", f.p.numbering.code.syntax.ex),
        ] {
            let e = f.ctor(name, &[bot]);
            out.push((label, e));
        }
        out
    };

    for (label, formula) in cases {
        let code = f.fcode(formula);
        let back = f.fdecode_aux(4, code);
        f.assert_eq_expr(back, formula, &format!("decodeAux 4 (code ({label}))"));
    }
}

/// The tag tree's catch-all is reachable, and it is `FO.Formula.ex`. A code
/// whose tag is 9 -- one past the last real constructor -- decodes to `ex`,
/// which is what "the last arm is the catch-all" means. Asserting this rather
/// than assuming it is what keeps the tree's shape honest.
#[test]
fn an_out_of_range_tag_falls_into_the_catch_all_arm() {
    let mut f = Fixture::new();
    let nine = f.num(9);
    let zero = f.num(0);
    let bogus = {
        let pair = f.kernel.const_(f.c.pair, vec![]);
        apply_all(&mut f.kernel, pair, &[nine, zero])
    };
    let got = f.fdecode_aux(3, bogus);
    let bot = f.kernel.const_(f.p.numbering.code.syntax.bot, vec![]);
    let want = {
        let name = f.p.numbering.code.syntax.ex;
        f.ctor(name, &[bot])
    };
    f.assert_eq_expr(got, want, "decodeAux 3 (pair 9 0)");
}

/// Zero fuel returns the DEFAULT, not the right answer. This is the control
/// that says the fuel argument is load-bearing rather than decorative: at
/// fuel 0 a code that decodes correctly at fuel 4 does not.
#[test]
fn zero_fuel_returns_the_default_not_the_answer() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.numbering.code.syntax.bot, vec![]);
    let formula = {
        let name = f.p.numbering.code.syntax.all;
        f.ctor(name, &[bot])
    };
    let code = f.fcode(formula);

    let starved = f.fdecode_aux(0, code);
    f.assert_eq_expr(starved, bot, "decodeAux 0 (code (all bot)) is the default");
    f.assert_ne_expr(starved, formula, "decodeAux 0 must NOT decode all bot");

    let fed = f.fdecode_aux(2, code);
    f.assert_eq_expr(fed, formula, "decodeAux 2 (code (all bot))");
}

/// `FO.Code.substCode (code (all bot)) (code (var 0))` is `code (all bot)`:
/// substituting into a closed formula changes nothing, so the code comes back
/// unchanged. `Formula.subst (all bot) s` reduces to `all (subst bot (lift s))`
/// = `all bot`, so the expected value is hand-computable and is 35.
#[test]
fn subst_code_round_trips_a_closed_formula() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.numbering.code.syntax.bot, vec![]);
    let formula = {
        let name = f.p.numbering.code.syntax.all;
        f.ctor(name, &[bot])
    };
    let cp = f.fcode(formula);
    let term = f.var(0);
    let ct = f.tcode(term);

    let got = {
        let s = f.kernel.const_(f.p.subst_code, vec![]);
        apply_all(&mut f.kernel, s, &[cp, ct])
    };
    let want = f.num(35);
    f.assert_eq_expr(got, want, "substCode (code (all bot)) (code (var 0))");
}

/// `FO.Code.substCode` at a formula that actually has a free index: `all`
/// binds index 0, so `imp bot bot` is the interesting closed case and
/// `eqf (var 0) (var 0)` is where the substitution reaches. Substituting
/// `var 0` for index 0 is the identity there, so the code is unchanged (2),
/// while substituting `f0 0` changes it -- the discriminating pair.
#[test]
fn subst_code_sees_the_substituted_term() {
    let mut f = Fixture::new();
    let formula = {
        let a = f.var(0);
        let b = f.var(0);
        let name = f.p.numbering.code.syntax.eqf;
        f.ctor(name, &[a, b])
    };
    let cp = f.fcode(formula);

    let identity_case = {
        let term = f.var(0);
        let ct = f.tcode(term);
        let s = f.kernel.const_(f.p.subst_code, vec![]);
        apply_all(&mut f.kernel, s, &[cp, ct])
    };
    let unchanged = f.num(2);
    f.assert_eq_expr(
        identity_case,
        unchanged,
        "substCode (code (eqf (var 0) (var 0))) (code (var 0))",
    );

    let changed_case = {
        let k = f.num(0);
        let name = f.p.numbering.code.syntax.f0;
        let term = f.ctor(name, &[k]);
        let ct = f.tcode(term);
        let s = f.kernel.const_(f.p.subst_code, vec![]);
        apply_all(&mut f.kernel, s, &[cp, ct])
    };
    f.assert_ne_expr(
        changed_case,
        unchanged,
        "substituting f0 0 must change the code",
    );
}

/// `FO.Code.isFormulaCode` is `Bool.true` on a code and `Bool.false` on a
/// natural that is not one. `1` is the discriminating negative: it decodes to
/// `bot` (its tag is 0) and `bot` re-encodes to `0`, not `1`.
#[test]
fn is_formula_code_separates_codes_from_non_codes() {
    let mut f = Fixture::new();
    let bool_true = f.kernel.const_(f.c.logic.bool_true, vec![]);
    let bool_false = f.kernel.const_(f.c.logic.bool_false, vec![]);

    let call = |f: &mut Fixture, n: u32| -> ExprId {
        let arg = f.num(n);
        let d = f.kernel.const_(f.p.is_formula_code, vec![]);
        f.kernel.app(d, arg)
    };

    // 0 = code bot, 2 = code (eqf (var 0) (var 0)), 27 = code (imp bot bot).
    for n in [0_u32, 2, 27] {
        let got = call(&mut f, n);
        f.assert_eq_expr(got, bool_true, &format!("isFormulaCode {n}"));
    }
    // 1 decodes to bot, and code bot is 0, not 1.
    let got = call(&mut f, 1);
    f.assert_eq_expr(got, bool_false, "isFormulaCode 1");
}

/// `FO.Term.decode`/`FO.Formula.decode` are the self-fuelled wrappers, and at
/// a code big enough to pay for its own decoding they agree with `decodeAux`.
/// `code (all bot) = 35`, and 35 is far more fuel than `all bot` needs.
#[test]
fn the_self_fuelled_wrappers_agree_where_the_code_pays_for_itself() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.numbering.code.syntax.bot, vec![]);
    let formula = {
        let name = f.p.numbering.code.syntax.all;
        f.ctor(name, &[bot])
    };
    let code = f.fcode(formula);
    let got = {
        let d = f.kernel.const_(f.p.formula_decode, vec![]);
        f.kernel.app(d, code)
    };
    f.assert_eq_expr(got, formula, "FO.Formula.decode (code (all bot))");

    let term = {
        let k = f.num(0);
        let name = f.p.numbering.code.syntax.f0;
        f.ctor(name, &[k])
    };
    let tcode = f.tcode(term);
    let tgot = {
        let d = f.kernel.const_(f.p.term_decode, vec![]);
        f.kernel.app(d, tcode)
    };
    f.assert_eq_expr(tgot, term, "FO.Term.decode (code (f0 0))");
}

/// `succ` is used only to build the numerals above; this pins that the helper
/// this file imports is the one `fo_code.rs` exports, so a rename there is a
/// compile error here rather than a silent divergence.
#[test]
fn the_numeral_helper_is_the_shared_one() {
    let mut f = Fixture::new();
    let two = f.num(2);
    let built = {
        let one = f.num(1);
        nsucc(&mut f.kernel, &f.c, one)
    };
    f.assert_eq_expr(built, two, "succ 1 = 2");
}

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.term_decode_aux, "FO.Term.decodeAux"),
        (p.term_decode, "FO.Term.decode"),
        (p.formula_decode_aux, "FO.Formula.decodeAux"),
        (p.formula_decode, "FO.Formula.decode"),
        (p.subst_code, "FO.Code.substCode"),
        (p.is_formula_code, "FO.Code.isFormulaCode"),
    ] {
        f.assert_axiom_free(name, label);
    }
}

/// The number of declarations `build_fo_decode_prelude` adds on top of
/// `build_nat_prelude` — the whole `fo_syntax` + `fo_code` + `fo_numbering` +
/// `fo_decode` chain. Pinned so drift in EITHER direction is a failure.
const FO_ARITHMETIZATION_WITH_DECODER: usize = 48;

/// The every-declaration sweep for the full arithmetization package, derived
/// from the environment rather than from a list, with a coverage control so it
/// cannot pass vacuously. This is the same set difference
/// `examples/fo_code_inventory.rs` reports.
#[test]
fn the_whole_arithmetization_package_is_axiom_free() {
    use std::collections::BTreeMap;

    let baseline: std::collections::BTreeSet<String> = {
        let mut kernel = Kernel::new();
        let _ = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        kernel
            .environment()
            .iter()
            .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
            .collect()
    };

    let mut kernel = Kernel::new();
    let _ = build_fo_decode_prelude(&mut kernel).expect("FO decode prelude must build");
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
        "FO.Formula.decode",
        "FO.Formula.decodeAux",
        "FO.Term.decode",
        "FO.Term.decodeAux",
        "FO.Code.substCode",
        "FO.Code.isFormulaCode",
        "FO.Formula.code_injective",
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
        FO_ARITHMETIZATION_WITH_DECODER,
        "declaration count drifted; the names are {:?}",
        added.keys().collect::<Vec<_>>()
    );
}
