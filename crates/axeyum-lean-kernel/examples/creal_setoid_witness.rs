//! **ℝ, constructed, at trusted cost zero** — the finding, with the exit status
//! depending on it (ADR-0468 phase R1).
//!
//! `creal_shape_probe` answered the *expressibility*
//! question before `ℚ` had an order, by admitting the carrier parametrically in
//! its regularity predicate. This is the same measurement on the real thing:
//! `CReal` over the constructed `Rat`, with regularity and closeness as
//! definitions, and with the three setoid laws — reflexivity, symmetry and
//! **transitivity** — proved.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness
//! ```
//!
//! # What the exit status depends on
//!
//! Four things, and the last two are what stop this being a green light on a
//! vacuous claim:
//!
//! 1. every declaration is a **checked** `Definition`/`Theorem` — never an
//!    `Axiom`, never an `Opaque`;
//! 2. every one has an **empty** `Kernel::axiom_footprint`, and the whole
//!    environment's trusted surface (`Axiom` + `Opaque` + `Quotient`) is still
//!    empty afterwards;
//! 3. `CReal.ofRat` is present, so `CReal.Regular` has a **solution** and the
//!    carrier is inhabited. Without it, `refl`/`symm`/`trans` could all hold
//!    for the empty type with empty footprints; and
//! 4. `CReal.Equiv.not_zero_one` is present, so `CReal.Equiv` is **not** the
//!    total relation. An equivalence relation that relates everything is still
//!    an equivalence relation; and
//! 5. `CReal.not_le_one_zero` is present, so `CReal.le` is not the total
//!    relation either. `le_refl`, `le_trans` and `add_le_add` all hold, with
//!    empty footprints, of the order that relates every pair; and
//! 6. `CReal.zero_lt_one` **and** `CReal.lt_irrefl` are both present, so
//!    `CReal.lt` is neither empty nor total. Six of the seven strict-order laws
//!    only *consume* a `lt`, so all six hold — footprint-free — of the relation
//!    that relates nothing at all; `zero_lt_one` is the only one that exhibits
//!    an inhabitant and `lt_irrefl` the only one that refuses a pair; and
//! 7. `CReal.ofRat_mul` **and** `CReal.not_equiv_mul_one_one_zero` are both
//!    present, so `CReal.mul` is the product and not a degenerate binary
//!    operation. `mul_zero`, `mul_comm` and `sq_nonneg` all hold —
//!    footprint-free — of `fun _ _ => zero`. `ofRat_mul` pins the *operation*
//!    on the whole embedded `ℚ` rather than asserting a property of it, and
//!    `not_equiv_mul_one_one_zero` refuses the constant-zero product by
//!    computation; and
//! 8. `CRealPrelude::ordered_ring_laws` names **22 distinct** declarations and
//!    every one of them is a checked, footprint-empty `Theorem`. The headline
//!    count is read out of the kernel through that list and nowhere else, so a
//!    dropped or duplicated law flips the exit status rather than shrinking a
//!    sentence in a document.
//!
//! 9. `CReal.apart_zero_one` **and** `CReal.no_total_inverse` are both
//!    present. The first exhibits a pair `CReal.Apart` separates —
//!    `apart_symm`, `apart_irrefl` and `apart_congr` all hold, footprint-free,
//!    of the relation that separates nothing — and the second refutes every
//!    total multiplicative inverse, so "the inverse is partial" is a proved
//!    obstruction rather than a scoping note (ADR-0474).
//!
//! # How far the ordered-field structure gets (ADR-0468 phase R2, partial)
//!
//! `zero`, `one`, `neg` and `add` are built, with `neg` and `add` each carrying
//! its `Equiv`-congruence — two of the five congruence obligations ADR-0468
//! counts as the setoid's real tax. `add` is where Bishop's index shift
//! `(x+y)_n := x_{2n+1} + y_{2n+1}` earns its keep: adding two regular
//! sequences doubles the error, and sampling twice as deep halves each modulus
//! back, exactly, with no slack.
//!
//! Of the 22 ordered-ring laws, **14 hold** here: four in `Equiv` form — the
//! whole additive group: `add_comm`, `add_neg`, `add_zero`,
//! `add_assoc` — and ten verbatim: `le_refl`, `le_trans`, `add_le_add`,
//! `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`,
//! `zero_lt_one` and `add_lt_add_of_le_of_lt`. The
//! first two are *pointwise*: their two sides sample at the same index, so
//! `Equiv.of_pointwise` reduces each to one `Rat` law. The other two are not,
//! and are the reason `Equiv` had to be an equivalence relation first —
//! `add x zero` samples `x` at `2n+1` where `x` samples it at `n`, and
//! `(x+y)+z` samples `x` at `2(2n+1)+1` where `x+(y+z)` samples it at `2n+1`.
//! Both close on regularity plus one inequality, `1/(2n+2) + 1/(n+1) ≤
//! 2/(n+1)`, read at the common denominator `2n+2` as `3 ≤ 4`. Monotonicity of
//! `Rat.natDivSucc` in its *index* is not needed and was not built. The other
//! three are the order laws below, which restate verbatim.
//!
//! # The product (ADR-0468 phase R2, continued)
//!
//! `CReal.mul` samples at `(c+1)·n + c` with `c := bound x + bound y + 1`, and
//! `CReal.bound x := |num (x_0)| + 1`. The usual story is that this bound is the
//! expensive part, because Bishop — and Mathlib's `CauSeq` after him — reads it
//! off an *existential* modulus and has to extract it. With ADR-0468's **fixed**
//! modulus there is nothing to extract: regularity at index `0` gives
//! `|x_m| ≤ |x_0| + 2` for every `m` outright, and the one genuinely missing
//! piece was an ℕ-valued magnitude, which is `Rat.bounds_num` — two `Int` facts
//! about `Int.natAbs` and one cross-multiplication.
//!
//! The estimate then closes **exactly**. The four terms
//! `Kx/(A+1) + Kx/(B+1) + Ky/(A+1) + Ky/(B+1)` fuse in the numerator, and
//! `Rat.natDivSucc_scale` reads `(c+1)/((c+1)·n + c + 1)` as `1/(n+1)` — so the
//! product bound *is* the regularity bound, with no slack and no weakening
//! step. `Rat.natDivSucc` is still never needed antitone in its index: every
//! comparison here happens at one denominator.
//!
//! `mul_comm` and `mul_zero` are *pointwise*. `mul_one` is not — `mul x one`
//! samples `x` at `(c+1)·n + c` where `x` samples it at `n` — and `mul_nonneg`
//! is the one that is genuinely about the order: `0 ≤ x` over the reals does
//! **not** say any sample of `x` is non-negative, only that each sits above
//! `−2/(j+1)`, so the product's lower bound trades that residue against the
//! other factor's canonical magnitude.
//!
//! # `mul_assoc`, `left_distrib`, `mul_congr`: the constant is free
//!
//! Those three, and `mul_le_mul_of_nonneg_left` behind them, compare two
//! products whose sampling indices **differ** — `mul x (add y z)` and
//! `add (mul x y) (mul x z)` agree at no index and their shifts are not equal
//! as naturals — so `CReal.mul`'s own exact estimate is unavailable and the
//! naive bound is `C/(n+1)` for some `C > 2`. `CReal.Equiv.of_bounded` is what
//! makes that enough: `Equiv` only needs the difference to be `O(1/n)`, and the
//! Archimedean lemma's numerator is a `Nat` **parameter**, so a symbolic
//! constant built from the factors' `CReal.bound`s is as acceptable as a
//! literal. It is `Equiv.trans`'s argument with one term deleted, and it is the
//! Archimedean property's third consumer.
//!
//! The other half is `Rat.nat_index_compose`: a product index *of* a product
//! index is a product index, and Bishop's additive shift `2n+1` is the `c = 1`
//! case — so every nested sampling index in sight reads back at `n` through one
//! lemma. `mul_le_mul_of_nonneg_left` then needs no estimate at all: `z − y ≥ 0`
//! gives `x·(z − y) ≥ 0` by `mul_nonneg`, and `left_distrib` plus `mul_congr`
//! say `x·z` is `Equiv`-equal to `x·y + x·(z − y)`.
//!
//! # The order (ADR-0468 phase R2, continued)
//!
//! `CReal.le` is Bishop's order, `∀ n, x_n − y_n ≤ 2/(n+1)` — the one-sided
//! reading of `Equiv`, which is why `le_trans` is `Equiv.trans` with the lower
//! half deleted: the same four-term estimate at an arbitrary index, sharing
//! `telescope_four` and `six_term_bound` with it verbatim, and the same
//! Archimedean lemma. `le_refl`, `le_trans` and `add_le_add` are the `Real`
//! package's statements **unchanged**: none of them mentions `Eq`, so unlike
//! the additive laws they needed no `Equiv` restatement.
//!
//! `le_of_equiv` and `equiv_of_le_le` pin it down: `Equiv` is the two-sided
//! bound, `le` its upper half, and having both halves is having `Equiv` back.
//! A `le` weakened to `≤ 100/(n+1)` would satisfy all three order laws and
//! close neither.
//!
//! `le_total` is **absent on purpose**. It holds for `ℚ` and does not lift —
//! `∀ x y, le x y ∨ le y x` over the reals is not constructively provable —
//! and nothing here assumes it.
//!
//! # The strict order, and why it quantifies over a rational gap
//!
//! `CReal.lt x y := ∃ (q : Rat), 0 < q ∧ le (add x (ofRat q)) y`. Two other
//! shapes were tried and are closed:
//!
//! - `lt := Not (le y x)` makes `le_of_lt` **non-constructive**, and there is no
//!   `le_total` over ℝ to recover it from — `Rat.le_total` holds for ℚ and does
//!   not lift, exactly as above.
//! - `∃ (n : Nat), y_n − x_n > 2/(n+1)` — the shape a Bishop transcription
//!   suggests — does not give `lt_trans`. Composing two such witnesses needs a
//!   *new* index, and the two regularity round trips that reach it consume
//!   precisely the margin the two hypotheses supply: chaining at an arbitrary
//!   third index leaves `z_k − x_k > −2/(k+1) − 1/(m+1) − 1/(n+1)`, which is
//!   negative. Closing that needs a quantitative gap lemma the fixed modulus
//!   does not supply.
//!
//! Quantifying over the **gap itself** removes the recomputation: `lt_trans`
//! carries `q₁` through untouched and uses the second hypothesis only via
//! `le_of_lt`. The one analytic step left is `le_add_of_nonneg`
//! (`0 ≤ q → x ≤ x + q`), which is analytic only because of the index shift —
//! and it closes on `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)`, the same inequality
//! `add_zero` and `add_assoc` reduce to. `lt_irrefl` is where the Archimedean
//! property is consumed a second time: a witness for `x < x` forces
//! `q ≤ 4/(n+1)` at every `n`, hence `q ≤ 0`, contradicting `0 < q`. **No
//! proof by contradiction is involved** — `¬¬P → P` does not exist in this
//! logic prelude and is not needed.
//!
//! `le_congr` and `lt_congr` are not among the 22: they are two of the nine
//! equality-slot binders the setoid ring telescope takes (ADR-0468 phase R3).
//!
//! # What this does NOT claim
//!
//! `Eq CReal` is not the equality of real numbers — `CReal.Equiv` is, and every
//! statement about reals will say so. Nine of the 22 are therefore **not** the
//! `Real` package's statements: they mention `Eq` there and `CReal.Equiv` here.
//! That is the substitution ADR-0468 phase R4 has to make good, by
//! instantiating the generalized telescope's equality slot — this example does
//! not claim it has been made.
//! Completeness, division, `inv` and `√` are each a separate ADR; none of them
//! is one of the 22. And the `Real` package's 30 axioms are **unchanged** by
//! this: ADR-0468 retires them by *deletion* in phase R4, once consumers are
//! generalized, not by exhibiting a model.

#![allow(clippy::too_many_lines)]

use axeyum_lean_kernel::{Declaration, Kernel, build_creal_prelude};

fn main() {
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("the CReal development must build");

    let admitted = [
        ("CReal.Within", p.within),
        ("CReal.Regular", p.regular_pred),
        ("CReal", p.creal),
        ("CReal.mk", p.mk),
        ("CReal.rec", p.rec),
        ("CReal.seq", p.seq),
        ("CReal.regular", p.regular),
        ("CReal.Equiv", p.equiv),
        ("CReal.Equiv.refl", p.equiv_refl),
        ("CReal.Equiv.symm", p.equiv_symm),
        ("CReal.Equiv.trans", p.equiv_trans),
        ("CReal.ofRat", p.of_rat),
        ("CReal.Equiv.not_zero_one", p.not_zero_one),
        ("CReal.zero", p.zero),
        ("CReal.one", p.one),
        ("CReal.Equiv.of_pointwise", p.equiv_of_pointwise),
        ("CReal.neg", p.neg),
        ("CReal.neg_congr", p.neg_congr),
        ("CReal.add", p.add),
        ("CReal.add_congr", p.add_congr),
        ("CReal.add_comm", p.add_comm),
        ("CReal.add_neg", p.add_neg),
        ("CReal.add_zero", p.add_zero),
        ("CReal.add_assoc", p.add_assoc),
        ("CReal.le", p.le),
        ("CReal.le_refl", p.le_refl),
        ("CReal.le_trans", p.le_trans),
        ("CReal.add_le_add", p.add_le_add),
        ("CReal.le_of_equiv", p.le_of_equiv),
        ("CReal.equiv_of_le_le", p.equiv_of_le_le),
        ("CReal.not_le_one_zero", p.not_le_one_zero),
        ("CReal.le_add_of_nonneg", p.le_add_of_nonneg),
        ("CReal.lt", p.lt),
        ("CReal.lt_irrefl", p.lt_irrefl),
        ("CReal.lt_trans", p.lt_trans),
        ("CReal.lt_of_lt_of_le", p.lt_of_lt_of_le),
        ("CReal.lt_of_le_of_lt", p.lt_of_le_of_lt),
        ("CReal.le_of_lt", p.le_of_lt),
        ("CReal.zero_lt_one", p.zero_lt_one),
        ("CReal.add_lt_add_of_le_of_lt", p.add_lt_add_of_le_of_lt),
        ("CReal.le_congr", p.le_congr),
        ("CReal.lt_congr", p.lt_congr),
        ("CReal.bound", p.bound),
        ("CReal.bound_within", p.bound_within),
        ("CReal.mulShift", p.mul_shift),
        ("CReal.mul", p.mul),
        ("CReal.ofRat_mul", p.of_rat_mul),
        ("CReal.mul_comm", p.mul_comm),
        ("CReal.mul_one", p.mul_one),
        ("CReal.mul_zero", p.mul_zero),
        ("CReal.mul_nonneg", p.mul_nonneg),
        ("CReal.sq_nonneg", p.sq_nonneg),
        (
            "CReal.not_equiv_mul_one_one_zero",
            p.not_equiv_mul_one_one_zero,
        ),
        ("CReal.Equiv.of_bounded", p.equiv_of_bounded),
        ("CReal.mul_congr", p.mul_congr),
        ("CReal.left_distrib", p.left_distrib),
        ("CReal.mul_assoc", p.mul_assoc),
        (
            "CReal.mul_le_mul_of_nonneg_left",
            p.mul_le_mul_of_nonneg_left,
        ),
        ("CReal.Apart", p.apart),
        ("CReal.apart_symm", p.apart_symm),
        ("CReal.apart_irrefl", p.apart_irrefl),
        ("CReal.apart_congr", p.apart_congr),
        ("CReal.not_equiv_of_apart", p.not_equiv_of_apart),
        ("CReal.apart_zero_one", p.apart_zero_one),
        ("CReal.no_total_inverse", p.no_total_inverse),
        ("CReal.ofRat_le", p.of_rat_le),
        ("CReal.PosBound", p.pos_bound),
        ("CReal.pos_of_pos_bound", p.pos_of_pos_bound),
        ("CReal.pos_bound_of_lt", p.pos_bound_of_lt),
    ];

    // (8): the headline count itself, read out of the kernel. Every one of the
    // 22 ordered-ring laws must be a checked Theorem with an empty footprint,
    // and the list must have 22 DISTINCT entries — a repeated name would
    // inflate the count without proving anything.
    let mut law_names: Vec<String> = p
        .ordered_ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    law_names.sort();
    law_names.dedup();
    let laws_distinct = law_names.len() == 22;
    let laws_proved = p.ordered_ring_laws().into_iter().all(|law| {
        matches!(
            kernel.environment().get(law),
            Some(Declaration::Theorem { .. })
        ) && kernel.axiom_footprint(law).is_empty()
    });

    let mut failed = false;
    println!("declaration\tkind\tfootprint");
    for (label, name) in admitted {
        let Some(declaration) = kernel.environment().get(name) else {
            println!("{label}\tMISSING\t-");
            failed = true;
            continue;
        };
        let kind = match declaration {
            Declaration::Theorem { .. } => "theorem",
            Declaration::Definition { .. } => "definition",
            Declaration::Inductive { .. } => "inductive",
            Declaration::Constructor { .. } => "constructor",
            Declaration::Recursor { .. } => "recursor",
            Declaration::Axiom { .. } => "AXIOM",
            Declaration::Opaque { .. } => "OPAQUE",
            Declaration::Quotient { .. } => "QUOTIENT",
        };
        if matches!(
            declaration,
            Declaration::Axiom { .. } | Declaration::Opaque { .. } | Declaration::Quotient { .. }
        ) {
            failed = true;
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        if !footprint.is_empty() {
            failed = true;
        }
        println!(
            "{label}\t{kind}\t{}",
            if footprint.is_empty() {
                "-".to_owned()
            } else {
                footprint.join(",")
            }
        );
    }

    // (3) and (4): the two claims that stop this being vacuous.
    let inhabited = matches!(
        kernel.environment().get(p.of_rat),
        Some(Declaration::Definition { .. })
    );
    let discriminating = matches!(
        kernel.environment().get(p.not_zero_one),
        Some(Declaration::Theorem { .. })
    );
    let ordered = matches!(
        kernel.environment().get(p.not_le_one_zero),
        Some(Declaration::Theorem { .. })
    );
    // (6): `lt` is neither empty nor total, and it takes both to say so.
    let strictly_inhabited = matches!(
        kernel.environment().get(p.zero_lt_one),
        Some(Declaration::Theorem { .. })
    );
    let strictly_irreflexive = matches!(
        kernel.environment().get(p.lt_irrefl),
        Some(Declaration::Theorem { .. })
    );
    // (7): `mul` is the product, not a degenerate binary operation that happens
    // to satisfy the five laws proved about it.
    let multiplicative = matches!(
        kernel.environment().get(p.of_rat_mul),
        Some(Declaration::Theorem { .. })
    );
    let mul_discriminates = matches!(
        kernel.environment().get(p.not_equiv_mul_one_one_zero),
        Some(Declaration::Theorem { .. })
    );
    // (9): `Apart` separates a pair, and no total inverse exists. `apart_symm`,
    // `apart_irrefl` and `apart_congr` all hold — footprint-free — of the
    // relation that separates NOTHING, which is also the relation over which
    // an inverse would be vacuously definable.
    let apart_inhabited = matches!(
        kernel.environment().get(p.apart_zero_one),
        Some(Declaration::Theorem { .. })
    );
    let inverse_refuted = matches!(
        kernel.environment().get(p.no_total_inverse),
        Some(Declaration::Theorem { .. })
    );
    if !inhabited {
        eprintln!(
            "FAIL: CReal.ofRat is not a checked definition, so CReal.Regular has no \
             exhibited solution. The carrier may be EMPTY and every setoid law above \
             vacuous — with empty footprints throughout."
        );
        failed = true;
    }
    if !discriminating {
        eprintln!(
            "FAIL: CReal.Equiv.not_zero_one is not a checked theorem, so nothing says \
             CReal.Equiv separates any two reals. The total relation is an equivalence \
             relation too."
        );
        failed = true;
    }
    if !ordered {
        eprintln!(
            "FAIL: CReal.not_le_one_zero is not a checked theorem, so nothing says \
             CReal.le separates any two reals. le_refl, le_trans and add_le_add all \
             hold of the order that relates every pair."
        );
        failed = true;
    }
    if !strictly_inhabited {
        eprintln!(
            "FAIL: CReal.zero_lt_one is not a checked theorem, so nothing exhibits a \
             single pair in CReal.lt. The other six strict-order laws all CONSUME a \
             lt, so all six hold — with empty footprints — of the EMPTY relation."
        );
        failed = true;
    }
    if !strictly_irreflexive {
        eprintln!(
            "FAIL: CReal.lt_irrefl is not a checked theorem, so nothing refuses a pair \
             in CReal.lt. With zero_lt_one alone the strict order could be the TOTAL \
             relation, which satisfies every other law proved about it."
        );
        failed = true;
    }
    if !multiplicative {
        eprintln!(
            "FAIL: CReal.ofRat_mul is not a checked theorem, so nothing pins CReal.mul \
             to Rat.mul ANYWHERE. mul_zero, mul_comm and sq_nonneg all hold — with \
             empty footprints — of the product that returns zero on every input."
        );
        failed = true;
    }
    if !apart_inhabited {
        eprintln!(
            "FAIL: CReal.apart_zero_one is not a checked theorem, so nothing exhibits \
             a pair CReal.Apart separates. apart_symm, apart_irrefl and apart_congr \
             all hold — with empty footprints — of the relation that separates \
             NOTHING, and that is exactly the relation an inverse would be \
             vacuously definable over."
        );
        failed = true;
    }
    if !inverse_refuted {
        eprintln!(
            "FAIL: CReal.no_total_inverse is not a checked theorem, so the claim that \
             the multiplicative inverse is PARTIAL is a scoping note rather than a \
             proved obstruction."
        );
        failed = true;
    }
    if !laws_distinct {
        eprintln!(
            "FAIL: CRealPrelude::ordered_ring_laws does not name 22 DISTINCT \
             declarations, so the count is inflated by a repeat."
        );
        failed = true;
    }
    if !laws_proved {
        eprintln!(
            "FAIL: not every entry of CRealPrelude::ordered_ring_laws is a \
             checked, footprint-empty Theorem. The '22 of 22' claim is read \
             from this list and nowhere else."
        );
        failed = true;
    }
    if !mul_discriminates {
        eprintln!(
            "FAIL: CReal.not_equiv_mul_one_one_zero is not a checked theorem, so \
             nothing exhibits a product the setoid separates from zero. The \
             constant-zero product satisfies three of the five laws proved here."
        );
        failed = true;
    }

    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    if !trusted.is_empty() {
        failed = true;
    }

    let all_laws = laws_distinct && laws_proved;
    eprintln!(
        "ℝ as a Bishop setoid over the constructed ℚ: {} declarations admitted, \
         trusted surface = {} ({}); carrier inhabited = {inhabited}, \
         Equiv discriminates = {discriminating}, le discriminates = {ordered}, \
         lt inhabited = {strictly_inhabited}, lt irreflexive = {strictly_irreflexive}, \
         mul agrees with Rat.mul on ℚ = {multiplicative}, mul discriminates = \
         {mul_discriminates}, Apart separates a pair = {apart_inhabited}, no total \
         inverse exists = {inverse_refuted}; all 22 ordered-ring laws proved = \
         {all_laws}",
        admitted.len(),
        trusted.len(),
        if trusted.is_empty() {
            "empty".to_owned()
        } else {
            trusted.join(",")
        }
    );
    if failed {
        eprintln!(
            "FAIL: the constructed reals are NOT free, or not inhabited, or not \
             discriminating — see above. ADR-0468's cost claim does not hold as stated."
        );
        std::process::exit(1);
    }
    eprintln!(
        "reflexivity, symmetry and transitivity of CReal.Equiv all hold at ZERO \
         trusted declarations; Equiv.trans, CReal.lt_irrefl and \
         CReal.Equiv.of_bounded are the three consumers of \
         Rat.le_of_le_add_natDivSucc (the Archimedean property of ℚ). ALL 22 \
         ordered-commutative-ring laws hold over the constructed ℝ. Thirteen \
         are the Real package's statements VERBATIM; the other nine mention Eq \
         there and are stated over CReal.Equiv here, because Eq CReal is not \
         the equality of real numbers. CReal.mul_congr — the fifth congruence \
         obligation, not one of the 22 — is proved too, so the ordered-ring \
         interface ADR-0468 phase R4 instantiates is complete. CReal.Apart — \
         Bishop's apartness, lt both ways — is defined with its four laws, and \
         CReal.no_total_inverse REFUTES every total multiplicative inverse, so \
         the field structure is missing as a proved obstruction and not as a \
         scoping note. CReal.pos_of_pos_bound and CReal.pos_bound_of_lt make \
         the inverse's domain precise in both directions: 0 < x and \
         (∃ k, 1/(k+1) ≤ x) are the SAME proposition, so the separating \
         modulus always exists — and Exists is a Prop, so it can never be \
         extracted into a CReal, which is why an inverse must take k as an \
         explicit Nat (ADR-0474)"
    );
}
