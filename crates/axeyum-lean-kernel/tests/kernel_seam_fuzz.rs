//! Deterministic seam-first kernel fuzzing for T6.0.3 / TL2.15.
//!
//! Kernel bugs cluster where individually reasonable features interact. This
//! harness therefore generates *combinations*, not isolated syntax nodes, and
//! records the four currently representable high-risk seams explicitly:
//!
//! 1. `Prop` × elimination;
//! 2. universes × inductives;
//! 3. proof irrelevance × iota reduction;
//! 4. literals × reduction/admission.
//!
//! Projection/eta generated seams remain outside this historical population.
//! TL2.10's quotient implementation has its own 576-descriptor, twice-repeated
//! package/reduction grammar in `quotient.rs`; it is not double-counted in this
//! 768-case summary. The historical complete large-elimination exploit remains
//! in `prop_large_elim_derives_false.rs`; this harness generalizes its feature
//! boundary and attempts a `False` admission in every generated case.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, Lit, NameId, NatLit, build_logic_prelude,
};

const PROP_CASES: usize = 192;
const UNIVERSE_CASES: usize = 320;
const LITERAL_CASES: usize = 256;
const TOTAL_CASES: usize = PROP_CASES + UNIVERSE_CASES + LITERAL_CASES;

const PROP_SEED: u64 = 0xA0E1_6003_0000_0001;
const UNIVERSE_SEED: u64 = 0xA0E1_6003_0000_0002;
const LITERAL_SEED: u64 = 0xA0E1_6003_0000_0003;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum ActiveSeam {
    PropElimination = 0,
    UniversesInductives = 1,
    ProofIrrelevanceIota = 2,
    LiteralsReduction = 3,
}

const ACTIVE_SEAMS: [ActiveSeam; 4] = [
    ActiveSeam::PropElimination,
    ActiveSeam::UniversesInductives,
    ActiveSeam::ProofIrrelevanceIota,
    ActiveSeam::LiteralsReduction,
];
const ALL_ACTIVE_SEAMS_MASK: u8 = (1 << ACTIVE_SEAMS.len()) - 1;

/// The repository's fixed-seed LCG pattern. It deliberately has no external
/// dependency and makes every failure reproducible from `(family seed, index)`.
#[derive(Debug, Clone, Copy)]
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn pick(&mut self, bound: usize) -> usize {
        assert!(bound > 0);
        usize::try_from(self.next_u64() % u64::try_from(bound).expect("bound fits u64"))
            .expect("bounded random value fits usize")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FuzzSummary {
    active_seams: u8,
    prop_cases: usize,
    universe_cases: usize,
    literal_cases: usize,
    false_admission_rejections: usize,
    prop_ctor_hits: [usize; 3],
    wrapper_depth_hits: [usize; 5],
    universe_shape_hits: [usize; UniverseShape::COUNT],
    universe_ctor_hits: [usize; 4],
    proof_field_hits: [usize; 3],
    data_field_hits: [usize; 3],
    literal_kind_hits: [usize; 2],
    literal_corner_hits: [usize; LiteralCorner::COUNT],
    typed_nat_literal_hits: usize,
    rejected_string_literal_hits: usize,
}

impl Default for FuzzSummary {
    fn default() -> Self {
        Self {
            active_seams: 0,
            prop_cases: 0,
            universe_cases: 0,
            literal_cases: 0,
            false_admission_rejections: 0,
            prop_ctor_hits: [0; 3],
            wrapper_depth_hits: [0; 5],
            universe_shape_hits: [0; UniverseShape::COUNT],
            universe_ctor_hits: [0; 4],
            proof_field_hits: [0; 3],
            data_field_hits: [0; 3],
            literal_kind_hits: [0; 2],
            literal_corner_hits: [0; LiteralCorner::COUNT],
            typed_nat_literal_hits: 0,
            rejected_string_literal_hits: 0,
        }
    }
}

impl FuzzSummary {
    fn hit(&mut self, seam: ActiveSeam) {
        self.active_seams |= 1 << (seam as u8);
    }

    fn assert_complete(&self) {
        assert_eq!(self.active_seams, ALL_ACTIVE_SEAMS_MASK, "{self:#?}");
        assert_eq!(self.prop_cases, PROP_CASES, "{self:#?}");
        assert_eq!(self.universe_cases, UNIVERSE_CASES, "{self:#?}");
        assert_eq!(self.literal_cases, LITERAL_CASES, "{self:#?}");
        assert_eq!(
            self.false_admission_rejections, TOTAL_CASES,
            "every generated case must reach and reject the False-admission gate: {self:#?}"
        );
        assert!(
            self.prop_ctor_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.wrapper_depth_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.universe_shape_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.universe_ctor_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.proof_field_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.data_field_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.literal_kind_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(
            self.literal_corner_hits.iter().all(|&hits| hits > 0),
            "{self:#?}"
        );
        assert!(self.typed_nat_literal_hits > 0, "{self:#?}");
        assert!(self.rejected_string_literal_hits > 0, "{self:#?}");
        assert_eq!(
            self.typed_nat_literal_hits + self.rejected_string_literal_hits,
            self.literal_cases,
            "every generated literal must reach exactly one typed boundary: {self:#?}"
        );
    }
}

fn binder_info(index: usize) -> BinderInfo {
    match index % 4 {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        _ => BinderInfo::InstImplicit,
    }
}

/// Wrap a well-typed term in alternating beta/zeta redexes without changing
/// its type or normal form. This makes the generated seam cross reduction and
/// binder metadata rather than testing only bare constructors.
fn wrap_typed_term(k: &mut Kernel, term: ExprId, ty: ExprId, depth: usize) -> ExprId {
    let anon = k.anon();
    let mut current = term;
    for step in 0..depth {
        let body = k.bvar(0);
        if step.is_multiple_of(2) {
            let identity = k.lam(anon, ty, body, binder_info(step));
            current = k.app(identity, current);
        } else {
            current = k.let_(anon, ty, current, body);
        }
    }
    current
}

fn assert_false_admission_rejected(
    k: &mut Kernel,
    false_type: ExprId,
    candidate: ExprId,
    case_name: &str,
) {
    let anon = k.anon();
    let theorem_name = k.name_str(anon, format!("bad_{case_name}"));
    let result = k.add_declaration(Declaration::Theorem {
        name: theorem_name,
        uparams: vec![],
        ty: false_type,
        value: candidate,
    });
    assert!(
        result.is_err(),
        "kernel accepted False for generated case {case_name}: {result:?}"
    );
    assert!(
        k.environment().get(theorem_name).is_none(),
        "failed False admission leaked into the environment for {case_name}"
    );
}

fn declare_nullary_enum(
    k: &mut Kernel,
    namespace: NameId,
    base: &str,
    ctor_count: usize,
    sort_level: usize,
) -> (NameId, Vec<NameId>) {
    let name = k.name_str(namespace, base);
    let mut level = k.level_zero();
    for _ in 0..sort_level {
        level = k.level_succ(level);
    }
    let ty = k.sort(level);
    let family = k.const_(name, vec![]);
    let ctor_names: Vec<_> = (0..ctor_count)
        .map(|index| k.name_str(name, format!("c{index}")))
        .collect();
    let constructors: Vec<_> = ctor_names.iter().map(|&ctor| (ctor, family)).collect();
    k.add_inductive(name, &[], 0, ty, &constructors)
        .unwrap_or_else(|error| panic!("{base} should admit: {error:?}"));
    (name, ctor_names)
}

fn fuzz_prop_elimination_and_proof_iota(summary: &mut FuzzSummary) {
    let mut rng = Lcg(PROP_SEED);
    for case_index in 0..PROP_CASES {
        let case_seed = rng.next_u64();
        let ctor_count = 2 + (case_index % 3);
        let selected_ctor = rng.pick(ctor_count);
        let wrapper_depth = if case_index < 5 {
            case_index
        } else {
            rng.pick(5)
        };
        let case_name = format!("prop_{case_index}_{case_seed:016x}");

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k);
        let anon = k.anon();
        let namespace = k.name_str(anon, format!("SeamProp{case_index}"));
        let (family_name, ctor_names) =
            declare_nullary_enum(&mut k, namespace, "Generated", ctor_count, 0);
        let (answer_name, answer_ctors) = declare_nullary_enum(&mut k, namespace, "Answer", 2, 1);

        let family = k.const_(family_name, vec![]);
        let answer = k.const_(answer_name, vec![]);
        let true_type = k.const_(logic.true_, vec![]);
        let false_type = k.const_(logic.false_, vec![]);
        let trivial = k.const_(logic.true_intro, vec![]);
        let ctor_values: Vec<_> = ctor_names
            .iter()
            .map(|&name| k.const_(name, vec![]))
            .collect();
        let answer_values: Vec<_> = answer_ctors
            .iter()
            .map(|&name| k.const_(name, vec![]))
            .collect();

        // Distinct constructors of a proposition are intentionally identified
        // by proof irrelevance. The eliminator must therefore be unable to
        // distinguish them into data.
        for &value in ctor_values.iter().skip(1) {
            assert!(
                k.def_eq(ctor_values[0], value),
                "proof irrelevance disappeared for {case_name}"
            );
        }

        let rec_name = k.name_str(family_name, "rec");
        let Declaration::Recursor { uparams, .. } =
            k.environment().get(rec_name).expect("generated recursor")
        else {
            panic!("expected recursor for {case_name}");
        };
        assert!(
            uparams.is_empty(),
            "multi-constructor Prop recursor gained a data-elimination universe for {case_name}"
        );

        // Prop-valued elimination remains legal and iota-reduces even when the
        // major and minor are hidden under generated beta/zeta redexes.
        let prop_motive = k.lam(anon, family, true_type, binder_info(case_index));
        let mut legal = k.const_(rec_name, vec![]);
        legal = k.app(legal, prop_motive);
        for minor_index in 0..ctor_count {
            let minor = wrap_typed_term(
                &mut k,
                trivial,
                true_type,
                (wrapper_depth + minor_index) % 5,
            );
            legal = k.app(legal, minor);
        }
        let major = wrap_typed_term(&mut k, ctor_values[selected_ctor], family, wrapper_depth);
        legal = k.app(legal, major);
        let legal_type = k.infer(legal).unwrap_or_else(|error| {
            panic!("legal Prop elimination failed for {case_name}: {error:?}")
        });
        assert!(k.def_eq(legal_type, true_type), "{case_name}");
        assert_eq!(k.whnf(legal), trivial, "iota failed for {case_name}");

        // The same recursor with a Type-valued motive is the forbidden side of
        // the seam. Branch and major terms are also reduction-wrapped so the
        // check cannot pass merely by avoiding beta/zeta interaction.
        let zero = k.level_zero();
        let one = k.level_succ(zero);
        let sort_one = k.sort(one);
        let answer_body = wrap_typed_term(&mut k, answer, sort_one, wrapper_depth);
        let data_motive = k.lam(anon, family, answer_body, binder_info(case_index + 1));
        let mut illegal = k.const_(rec_name, vec![]);
        illegal = k.app(illegal, data_motive);
        for minor_index in 0..ctor_count {
            let value = answer_values[minor_index % answer_values.len()];
            let minor =
                wrap_typed_term(&mut k, value, answer, (wrapper_depth + minor_index + 1) % 5);
            illegal = k.app(illegal, minor);
        }
        illegal = k.app(illegal, major);
        assert!(
            k.infer(illegal).is_err(),
            "data elimination from non-subsingleton Prop inferred for {case_name}"
        );
        assert_false_admission_rejected(&mut k, false_type, illegal, &case_name);

        summary.hit(ActiveSeam::PropElimination);
        summary.hit(ActiveSeam::ProofIrrelevanceIota);
        summary.prop_cases += 1;
        summary.false_admission_rejections += 1;
        summary.prop_ctor_hits[ctor_count - 2] += 1;
        summary.wrapper_depth_hits[wrapper_depth] += 1;
    }
}

#[derive(Debug, Clone, Copy)]
enum UniverseShape {
    Zero,
    One,
    Param,
    SuccParam,
    MaxParamOne,
    MaxParamZero,
    ImaxParamZero,
    ImaxOneParam,
}

impl UniverseShape {
    const COUNT: usize = 8;

    fn from_index(index: usize) -> Self {
        match index {
            0 => Self::Zero,
            1 => Self::One,
            2 => Self::Param,
            3 => Self::SuccParam,
            4 => Self::MaxParamOne,
            5 => Self::MaxParamZero,
            6 => Self::ImaxParamZero,
            7 => Self::ImaxOneParam,
            _ => panic!("universe shape index out of range: {index}"),
        }
    }

    fn index(self) -> usize {
        self as usize
    }

    fn uses_param(self) -> bool {
        !matches!(self, Self::Zero | Self::One)
    }

    /// Independent expectation, stated from Lean universe semantics rather
    /// than by calling the kernel predicate under test.
    fn provably_nonzero(self) -> bool {
        matches!(self, Self::One | Self::SuccParam | Self::MaxParamOne)
    }
}

#[derive(Debug, Clone, Copy)]
struct UniverseCase {
    seed: u64,
    shape: UniverseShape,
    ctor_count: usize,
    proof_fields: usize,
    data_fields: usize,
}

fn generate_universe_case(case_index: usize, rng: &mut Lcg) -> UniverseCase {
    let seed = rng.next_u64();
    // The first 288 cases exhaust the complete 8×4×3×3 corner product; the
    // tail uses the fixed-seed generator so this is not only a hand matrix.
    let (shape_index, ctor_count, proof_fields, data_fields) = if case_index < 288 {
        (
            case_index % UniverseShape::COUNT,
            (case_index / UniverseShape::COUNT) % 4,
            (case_index / (UniverseShape::COUNT * 4)) % 3,
            (case_index / (UniverseShape::COUNT * 4 * 3)) % 3,
        )
    } else {
        (
            rng.pick(UniverseShape::COUNT),
            rng.pick(4),
            rng.pick(3),
            rng.pick(3),
        )
    };
    UniverseCase {
        seed,
        shape: UniverseShape::from_index(shape_index),
        ctor_count,
        proof_fields,
        data_fields,
    }
}

fn instantiate_universe_shape(
    k: &mut Kernel,
    namespace: NameId,
    shape: UniverseShape,
) -> (
    axeyum_lean_kernel::LevelId,
    Vec<NameId>,
    Vec<axeyum_lean_kernel::LevelId>,
    axeyum_lean_kernel::LevelId,
) {
    let param_name = k.name_str(namespace, "u");
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let param = k.level_param(param_name);
    let result_level = match shape {
        UniverseShape::Zero => zero,
        UniverseShape::One => one,
        UniverseShape::Param => param,
        UniverseShape::SuccParam => k.level_succ(param),
        UniverseShape::MaxParamOne => k.level_max(param, one),
        UniverseShape::MaxParamZero => k.level_max(param, zero),
        UniverseShape::ImaxParamZero => k.level_imax(param, zero),
        UniverseShape::ImaxOneParam => k.level_imax(one, param),
    };
    if shape.uses_param() {
        (result_level, vec![param_name], vec![param], one)
    } else {
        (result_level, Vec::new(), Vec::new(), one)
    }
}

fn fuzz_universes_and_inductives(summary: &mut FuzzSummary) {
    let mut rng = Lcg(UNIVERSE_SEED);
    for case_index in 0..UNIVERSE_CASES {
        let UniverseCase {
            seed,
            shape,
            ctor_count,
            proof_fields,
            data_fields,
        } = generate_universe_case(case_index, &mut rng);
        let case_name = format!("universe_{case_index}_{seed:016x}");

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k);
        let anon = k.anon();
        let namespace = k.name_str(anon, format!("SeamUniverse{case_index}"));
        let family_name = k.name_str(namespace, "Generated");
        let (result_level, uparams, family_levels, one) =
            instantiate_universe_shape(&mut k, namespace, shape);
        let family_type = k.sort(result_level);
        let family = k.const_(family_name, family_levels);
        let true_type = k.const_(logic.true_, vec![]);
        // A field `p : Prop` carries data (the proposition itself), not a proof:
        // `Prop` has type `Sort 1`. This keeps the generated domain tiny while
        // exercising Lean's non-Prop-field branch independently of `True`
        // proof fields.
        let data_type = k.sort_zero();

        let mut constructors = Vec::new();
        for ctor_index in 0..ctor_count {
            let ctor_name = k.name_str(family_name, format!("c{ctor_index}"));
            let mut ctor_type = family;
            for field_index in 0..proof_fields {
                ctor_type = k.pi(
                    anon,
                    true_type,
                    ctor_type,
                    binder_info(field_index + case_index),
                );
            }
            for field_index in 0..data_fields {
                ctor_type = k.pi(
                    anon,
                    data_type,
                    ctor_type,
                    binder_info(field_index + proof_fields + case_index),
                );
            }
            constructors.push((ctor_name, ctor_type));
        }
        k.add_inductive(family_name, &uparams, 0, family_type, &constructors)
            .unwrap_or_else(|error| {
                panic!("generated inductive failed for {case_name}: {error:?}")
            });

        let syntactic_subsingleton = ctor_count == 0 || (ctor_count == 1 && data_fields == 0);
        let allows_large_elimination = shape.provably_nonzero() || syntactic_subsingleton;
        let rec_name = k.name_str(family_name, "rec");
        let Declaration::Recursor {
            uparams: rec_uparams,
            ..
        } = k.environment().get(rec_name).expect("generated recursor")
        else {
            panic!("expected recursor for {case_name}");
        };
        let expected_recursor_uparams = uparams.len() + usize::from(allows_large_elimination);
        assert_eq!(
            rec_uparams.len(),
            expected_recursor_uparams,
            "wrong elimination universe boundary for {case_name}: shape={shape:?}, \
             ctors={ctor_count}, proof_fields={proof_fields}, data_fields={data_fields}"
        );

        let rec_levels = vec![one; expected_recursor_uparams];
        let rec = k.const_(rec_name, rec_levels);
        k.infer(rec).unwrap_or_else(|error| {
            panic!("well-formed recursor failed for {case_name}: {error:?}")
        });

        if !allows_large_elimination {
            let mut extra_levels = vec![one; expected_recursor_uparams];
            extra_levels.push(one);
            let old_unrestricted_shape = k.const_(rec_name, extra_levels);
            assert!(
                matches!(
                    k.infer(old_unrestricted_shape),
                    Err(KernelError::UniverseArityMismatch { .. })
                ),
                "restricted recursor accepted an elimination universe for {case_name}"
            );
        }

        let false_type = k.const_(logic.false_, vec![]);
        assert_false_admission_rejected(&mut k, false_type, rec, &case_name);

        summary.hit(ActiveSeam::UniversesInductives);
        summary.universe_cases += 1;
        summary.false_admission_rejections += 1;
        summary.universe_shape_hits[shape.index()] += 1;
        summary.universe_ctor_hits[ctor_count] += 1;
        summary.proof_field_hits[proof_fields] += 1;
        summary.data_field_hits[data_fields] += 1;
    }
}

#[derive(Debug, Clone, Copy)]
enum LiteralCorner {
    NatZero,
    NatOne,
    NatMax,
    NatAboveU128,
    NatHuge,
    NatRandom,
    StringEmpty,
    StringAscii,
    StringUnicode,
    StringNul,
}

impl LiteralCorner {
    const COUNT: usize = 10;

    fn from_index(index: usize) -> Self {
        match index {
            0 => Self::NatZero,
            1 => Self::NatOne,
            2 => Self::NatMax,
            3 => Self::NatAboveU128,
            4 => Self::NatHuge,
            5 => Self::NatRandom,
            6 => Self::StringEmpty,
            7 => Self::StringAscii,
            8 => Self::StringUnicode,
            9 => Self::StringNul,
            _ => panic!("literal corner index out of range: {index}"),
        }
    }

    fn index(self) -> usize {
        self as usize
    }

    fn value(self, rng: &mut Lcg) -> Lit {
        match self {
            Self::NatZero => Lit::nat(0_u8),
            Self::NatOne => Lit::nat(1_u8),
            Self::NatMax => Lit::nat(u128::MAX),
            Self::NatAboveU128 => Lit::Nat(
                NatLit::from_decimal("340282366920938463463374607431768211456")
                    .expect("2^128 is a valid natural literal"),
            ),
            Self::NatHuge => Lit::Nat(
                NatLit::from_decimal(
                    "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031",
                )
                .expect("large decimal is a valid natural literal"),
            ),
            Self::NatRandom => {
                let high = u128::from(rng.next_u64());
                let low = u128::from(rng.next_u64());
                Lit::nat((high << 64) | low)
            }
            Self::StringEmpty => Lit::Str(String::new()),
            Self::StringAscii => Lit::Str(format!("seam-{:016x}", rng.next_u64())),
            Self::StringUnicode => Lit::Str(format!("λ→🪓-{:x}", rng.next_u64() & 0xffff)),
            Self::StringNul => Lit::Str(format!("a\0b-{:x}", rng.next_u64() & 0xff)),
        }
    }
}

/// Wrap a literal beneath beta/zeta redexes whose annotation is its expected
/// type for the current profile. String inference still fails at the literal;
/// Nat inference must traverse a well-typed wrapper and return `Nat`.
fn wrap_literal(k: &mut Kernel, literal: ExprId, annotation: ExprId, depth: usize) -> ExprId {
    let anon = k.anon();
    let mut current = literal;
    for step in 0..depth {
        let body = k.bvar(0);
        if step.is_multiple_of(2) {
            let identity = k.lam(anon, annotation, body, binder_info(step));
            current = k.app(identity, current);
        } else {
            current = k.let_(anon, annotation, current, body);
        }
    }
    current
}

fn fuzz_literals_and_reduction(summary: &mut FuzzSummary) {
    let mut rng = Lcg(LITERAL_SEED);
    for case_index in 0..LITERAL_CASES {
        let case_seed = rng.next_u64();
        let corner_index = case_index % LiteralCorner::COUNT;
        let corner = LiteralCorner::from_index(corner_index);
        let wrapper_depth = case_index % 5;
        let case_name = format!("literal_{case_index}_{case_seed:016x}");

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k);
        let literal_value = corner.value(&mut rng);
        let kind_index = usize::from(matches!(&literal_value, Lit::Str(_)));
        let literal = k.lit(literal_value.clone());
        assert_eq!(
            k.expr_node(literal),
            &axeyum_lean_kernel::ExprNode::Lit(literal_value)
        );

        // Closed structural operations must not truncate or rewrite a literal.
        assert_eq!(
            k.lift_loose_bvars(literal, 0, u32::MAX),
            literal,
            "{case_name}"
        );
        let arbitrary_substitution = k.sort_zero();
        assert_eq!(
            k.instantiate(literal, &[arbitrary_substitution]),
            literal,
            "{case_name}"
        );
        assert_eq!(
            k.substitute_expr_levels(literal, &[]),
            literal,
            "{case_name}"
        );

        let annotation = if kind_index == 0 {
            k.const_(logic.nat, vec![])
        } else {
            k.sort_zero()
        };
        let wrapped = wrap_literal(&mut k, literal, annotation, wrapper_depth);
        assert_eq!(
            k.whnf(wrapped),
            literal,
            "reduction lost literal for {case_name}"
        );
        if kind_index == 0 {
            let inferred = k.infer(wrapped).expect("Nat literal must infer");
            assert_eq!(inferred, annotation, "wrong Nat type for {case_name}");
            summary.typed_nat_literal_hits += 1;
        } else {
            assert!(
                matches!(k.infer(wrapped), Err(KernelError::UnsupportedLit)),
                "String literal escaped fail-closed inference for {case_name}"
            );
            summary.rejected_string_literal_hits += 1;
        }

        let false_type = k.const_(logic.false_, vec![]);
        assert_false_admission_rejected(&mut k, false_type, wrapped, &case_name);

        summary.hit(ActiveSeam::LiteralsReduction);
        summary.literal_cases += 1;
        summary.false_admission_rejections += 1;
        summary.literal_kind_hits[kind_index] += 1;
        summary.literal_corner_hits[corner.index()] += 1;
        summary.wrapper_depth_hits[wrapper_depth] += 1;
    }
}

fn run_seed() -> FuzzSummary {
    let mut summary = FuzzSummary::default();
    fuzz_prop_elimination_and_proof_iota(&mut summary);
    fuzz_universes_and_inductives(&mut summary);
    fuzz_literals_and_reduction(&mut summary);
    summary.assert_complete();
    summary
}

#[test]
fn seam_first_kernel_fuzz_is_complete_and_deterministic() {
    assert_eq!(ACTIVE_SEAMS.len(), 4, "update the explicit seam registry");
    let first = run_seed();
    let second = run_seed();
    assert_eq!(first, second, "fixed-seed seam summary drifted");
}
