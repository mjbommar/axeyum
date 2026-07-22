//! Public-path contract and deterministic generated grammar for TL2.11 strict
//! positivity (ADR-0352). Expectations are assigned by the grammar production,
//! then checked through `Kernel::add_inductive`; the test never calls a private
//! positivity helper.

use std::collections::BTreeSet;

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, KernelError, NameId};

const GENERATOR_SEED: u64 = 0x4158_5053_5452_4943;
const EXPECTED_GENERATED_SUMMARY: &str = "schema=axeyum-lean-strict-positivity-grammar-v2\n\
seed=4158505354524943\n\
cases=840\n\
admission=admit:360,recursive-indexed:0,reflexive:0,non-positive:270,invalid:210\n\
tl2.11-baseline-outcomes=admit:174,recursive-indexed:42,reflexive:144,non-positive:270,invalid:210\n\
profiles=0p0i:240,1p0i:270,1p1i:330\n\
sorts=prop:420,type:420\n\
depths=0:168,1:168,2:168,3:168,4:168\n\
tl2.11-descriptor-fnv1a64=02985687422aa0ff\n";

/// The repository's dependency-free fixed-seed generator. Grammar corners are
/// exhaustive; this stream selects orthogonal ordering variations and adds its
/// per-case state to the frozen descriptor.
#[derive(Clone, Copy, Debug)]
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Profile {
    Plain,
    Parametric,
    ParametricIndexed,
}

impl Profile {
    const ALL: [Self; 3] = [Self::Plain, Self::Parametric, Self::ParametricIndexed];

    const fn label(self) -> &'static str {
        match self {
            Self::Plain => "0p0i",
            Self::Parametric => "1p0i",
            Self::ParametricIndexed => "1p1i",
        }
    }

    const fn num_params(self) -> usize {
        match self {
            Self::Plain => 0,
            Self::Parametric | Self::ParametricIndexed => 1,
        }
    }

    const fn is_indexed(self) -> bool {
        matches!(self, Self::ParametricIndexed)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FamilySort {
    Prop,
    Type,
}

impl FamilySort {
    const ALL: [Self; 2] = [Self::Prop, Self::Type];

    const fn label(self) -> &'static str {
        match self {
            Self::Prop => "prop",
            Self::Type => "type",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Production {
    NoOccurrence,
    Canonical,
    PositivePi,
    NegativeDomain,
    MixedPolarity,
    DeepNegative,
    WrongParameter,
    NestedApplication,
    SelfIndex,
    WrongIndexArity,
    LetCanonical,
}

impl Production {
    const BASE: [Self; 8] = [
        Self::NoOccurrence,
        Self::Canonical,
        Self::PositivePi,
        Self::NegativeDomain,
        Self::MixedPolarity,
        Self::DeepNegative,
        Self::NestedApplication,
        Self::LetCanonical,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::NoOccurrence => "no-occurrence",
            Self::Canonical => "canonical",
            Self::PositivePi => "positive-pi",
            Self::NegativeDomain => "negative-domain",
            Self::MixedPolarity => "mixed-polarity",
            Self::DeepNegative => "deep-negative",
            Self::WrongParameter => "wrong-parameter",
            Self::NestedApplication => "nested-application",
            Self::SelfIndex => "self-index",
            Self::WrongIndexArity => "wrong-index-arity",
            Self::LetCanonical => "let-canonical",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expected {
    Admit,
    RecursiveIndexedDecline,
    ReflexiveDecline,
    NonPositive,
    Invalid,
}

impl Expected {
    const fn label(self) -> &'static str {
        match self {
            Self::Admit => "admit",
            Self::RecursiveIndexedDecline => "recursive-indexed-decline",
            Self::ReflexiveDecline => "reflexive-decline",
            Self::NonPositive => "non-positive",
            Self::Invalid => "invalid",
        }
    }

    const fn index(self) -> usize {
        match self {
            Self::Admit => 0,
            Self::RecursiveIndexedDecline => 1,
            Self::ReflexiveDecline => 2,
            Self::NonPositive => 3,
            Self::Invalid => 4,
        }
    }
}

#[derive(Clone, Debug)]
struct CaseSpec {
    id: String,
    profile: Profile,
    family_sort: FamilySort,
    production: Production,
    context_depth: usize,
    preceding_fields: usize,
    preceding_constructor: bool,
    expected: Expected,
}

fn expected_for(_profile: Profile, production: Production, _context_depth: usize) -> Expected {
    match production {
        Production::NoOccurrence
        | Production::Canonical
        | Production::PositivePi
        | Production::LetCanonical => Expected::Admit,
        Production::NegativeDomain | Production::MixedPolarity | Production::DeepNegative => {
            Expected::NonPositive
        }
        Production::WrongParameter
        | Production::NestedApplication
        | Production::SelfIndex
        | Production::WrongIndexArity => Expected::Invalid,
    }
}

/// The exact pre-TL2.12 public outcomes are retained only to prove that the
/// completed TL2.11 case population and descriptor did not move when M2
/// deliberately changes positive feature admission.
fn tl211_expected_for(profile: Profile, production: Production, context_depth: usize) -> Expected {
    match production {
        Production::NoOccurrence => Expected::Admit,
        Production::Canonical | Production::LetCanonical => {
            if matches!(production, Production::LetCanonical) && context_depth > 0 {
                Expected::ReflexiveDecline
            } else if profile.is_indexed() {
                Expected::RecursiveIndexedDecline
            } else {
                Expected::Admit
            }
        }
        Production::PositivePi => {
            if context_depth == 0 {
                if profile.is_indexed() {
                    Expected::RecursiveIndexedDecline
                } else {
                    Expected::Admit
                }
            } else {
                Expected::ReflexiveDecline
            }
        }
        Production::NegativeDomain | Production::MixedPolarity | Production::DeepNegative => {
            Expected::NonPositive
        }
        Production::WrongParameter
        | Production::NestedApplication
        | Production::SelfIndex
        | Production::WrongIndexArity => Expected::Invalid,
    }
}

fn environment_snapshot(kernel: &Kernel) -> Vec<(NameId, Declaration)> {
    kernel
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect()
}

fn family_type(
    kernel: &mut Kernel,
    profile: Profile,
    family_sort: FamilySort,
    binder: NameId,
) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let sort_zero = kernel.sort(zero);
    let sort_one = kernel.sort(one);
    let result = match family_sort {
        FamilySort::Prop => sort_zero,
        FamilySort::Type => sort_one,
    };
    match profile {
        Profile::Plain => result,
        Profile::Parametric => kernel.pi(binder, sort_one, result, BinderInfo::Default),
        Profile::ParametricIndexed => {
            let indexed = kernel.pi(binder, sort_one, result, BinderInfo::Default);
            kernel.pi(binder, sort_one, indexed, BinderInfo::Default)
        }
    }
}

fn family_application(
    kernel: &mut Kernel,
    profile: Profile,
    family: ExprId,
    parameter_depth: u32,
) -> ExprId {
    match profile {
        Profile::Plain => family,
        Profile::Parametric => {
            let parameter = kernel.bvar(parameter_depth);
            kernel.app(family, parameter)
        }
        Profile::ParametricIndexed => {
            let parameter = kernel.bvar(parameter_depth);
            let applied = kernel.app(family, parameter);
            let index = kernel.sort_zero();
            kernel.app(applied, index)
        }
    }
}

fn lift_into_binder(kernel: &mut Kernel, expression: ExprId) -> ExprId {
    kernel.lift_loose_bvars(expression, 0, 1)
}

fn wrap_positive_pi(
    kernel: &mut Kernel,
    binder: NameId,
    mut expression: ExprId,
    depth: usize,
) -> ExprId {
    for _ in 0..depth {
        let body = lift_into_binder(kernel, expression);
        let atom = kernel.sort_zero();
        expression = kernel.pi(binder, atom, body, BinderInfo::Default);
    }
    expression
}

fn wrap_reducible_let(
    kernel: &mut Kernel,
    binder: NameId,
    mut expression: ExprId,
    depth: usize,
) -> ExprId {
    for _ in 0..depth {
        let body = lift_into_binder(kernel, expression);
        let sort_one = {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            kernel.sort(one)
        };
        let value = kernel.sort_zero();
        expression = kernel.let_(binder, sort_one, value, body);
    }
    expression
}

fn offending_field(
    kernel: &mut Kernel,
    spec: &CaseSpec,
    family: ExprId,
    wrapper: Option<ExprId>,
    binder: NameId,
) -> ExprId {
    let parameter_depth = u32::try_from(spec.preceding_fields).expect("small field depth");
    let canonical = family_application(kernel, spec.profile, family, parameter_depth);
    let atom = kernel.sort_zero();

    match spec.production {
        Production::NoOccurrence => {
            let positive = wrap_positive_pi(kernel, binder, atom, spec.context_depth);
            wrap_reducible_let(kernel, binder, positive, spec.context_depth)
        }
        Production::Canonical => canonical,
        Production::PositivePi => wrap_positive_pi(kernel, binder, canonical, spec.context_depth),
        Production::NegativeDomain => {
            let negative = kernel.pi(binder, canonical, atom, BinderInfo::Default);
            wrap_reducible_let(kernel, binder, negative, spec.context_depth)
        }
        Production::MixedPolarity => {
            let body = lift_into_binder(kernel, canonical);
            let mixed = kernel.pi(binder, canonical, body, BinderInfo::Default);
            wrap_reducible_let(kernel, binder, mixed, spec.context_depth)
        }
        Production::DeepNegative => {
            let positive_body = lift_into_binder(kernel, canonical);
            let positive = kernel.pi(binder, atom, positive_body, BinderInfo::Default);
            let function_to_atom = kernel.pi(binder, positive, atom, BinderInfo::Default);
            let result = lift_into_binder(kernel, canonical);
            let deep = kernel.pi(binder, function_to_atom, result, BinderInfo::Default);
            wrap_reducible_let(kernel, binder, deep, spec.context_depth)
        }
        Production::WrongParameter => {
            let wrong = kernel.sort_zero();
            let applied = kernel.app(family, wrong);
            if spec.profile.is_indexed() {
                let index = kernel.sort_zero();
                kernel.app(applied, index)
            } else {
                applied
            }
        }
        Production::NestedApplication => {
            let wrapper = wrapper.expect("nested production declares its wrapper");
            let nested = kernel.app(wrapper, canonical);
            let positive = wrap_positive_pi(kernel, binder, nested, spec.context_depth);
            wrap_reducible_let(kernel, binder, positive, spec.context_depth)
        }
        Production::SelfIndex => {
            let parameter = kernel.bvar(parameter_depth);
            let applied = kernel.app(family, parameter);
            kernel.app(applied, canonical)
        }
        Production::WrongIndexArity => {
            let parameter = kernel.bvar(parameter_depth);
            kernel.app(family, parameter)
        }
        Production::LetCanonical => {
            wrap_reducible_let(kernel, binder, canonical, spec.context_depth)
        }
    }
}

fn constructor_type(
    kernel: &mut Kernel,
    profile: Profile,
    family: ExprId,
    binder: NameId,
    fields: &[ExprId],
) -> ExprId {
    let result_depth = u32::try_from(fields.len()).expect("small field count");
    let mut result = family_application(kernel, profile, family, result_depth);
    for &field in fields.iter().rev() {
        result = kernel.pi(binder, field, result, BinderInfo::Default);
    }
    if profile.num_params() == 1 {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let sort_one = kernel.sort(one);
        result = kernel.pi(binder, sort_one, result, BinderInfo::Default);
    }
    result
}

#[allow(clippy::too_many_lines)]
fn run_case(spec: &CaseSpec) {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let namespace = kernel.name_str(anon, &spec.id);
    let binder = kernel.name_str(namespace, "x");
    let family_name = kernel.name_str(namespace, "I");
    let family = kernel.const_(family_name, vec![]);
    let ty = family_type(&mut kernel, spec.profile, spec.family_sort, binder);

    let wrapper = if matches!(spec.production, Production::NestedApplication) {
        let wrapper_name = kernel.name_str(namespace, "Wrapper");
        let wrapper = kernel.const_(wrapper_name, vec![]);
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let sort_zero = kernel.sort(zero);
        let sort_one = kernel.sort(one);
        let family_sort = match spec.family_sort {
            FamilySort::Prop => sort_zero,
            FamilySort::Type => sort_one,
        };
        let wrapper_ty = kernel.pi(binder, family_sort, family_sort, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Axiom {
                name: wrapper_name,
                uparams: vec![],
                ty: wrapper_ty,
            })
            .expect("foreign wrapper should admit");
        Some(wrapper)
    } else {
        None
    };

    let target_ctor = kernel.name_str(family_name, "target");
    let mut fields = Vec::with_capacity(spec.preceding_fields + 1);
    for _ in 0..spec.preceding_fields {
        fields.push(kernel.sort_zero());
    }
    fields.push(offending_field(&mut kernel, spec, family, wrapper, binder));
    let target_ty = constructor_type(&mut kernel, spec.profile, family, binder, &fields);

    let mut constructors = Vec::with_capacity(2);
    if spec.preceding_constructor {
        let control_ctor = kernel.name_str(family_name, "control");
        let control_ty = constructor_type(&mut kernel, spec.profile, family, binder, &[]);
        constructors.push((control_ctor, control_ty));
    }
    constructors.push((target_ctor, target_ty));

    let before = environment_snapshot(&kernel);
    let result = kernel.add_inductive(
        family_name,
        &[],
        spec.profile.num_params(),
        ty,
        &constructors,
    );

    match spec.expected {
        Expected::Admit => {
            result.unwrap_or_else(|error| panic!("{}: expected admission, got {error:?}", spec.id));
            assert!(kernel.environment().contains(family_name), "{}", spec.id);
            for &(ctor, _) in &constructors {
                assert!(kernel.environment().contains(ctor), "{}", spec.id);
            }
        }
        Expected::RecursiveIndexedDecline => {
            assert_eq!(
                result.unwrap_err(),
                KernelError::RecursiveIndexedNotSupported {
                    inductive: family_name,
                    ctor: target_ctor,
                },
                "{}",
                spec.id
            );
            assert_eq!(environment_snapshot(&kernel), before, "{}", spec.id);
        }
        Expected::ReflexiveDecline => {
            assert_eq!(
                result.unwrap_err(),
                KernelError::ReflexiveOrNestedNotSupported {
                    inductive: family_name,
                    ctor: target_ctor,
                },
                "{}",
                spec.id
            );
            assert_eq!(environment_snapshot(&kernel), before, "{}", spec.id);
        }
        Expected::NonPositive => {
            assert_eq!(
                result.unwrap_err(),
                KernelError::NonPositiveInductiveOccurrence {
                    inductive: family_name,
                    ctor: target_ctor,
                    field_index: u32::try_from(spec.preceding_fields).expect("small field index"),
                },
                "{}",
                spec.id
            );
            assert_eq!(environment_snapshot(&kernel), before, "{}", spec.id);
        }
        Expected::Invalid => {
            assert_eq!(
                result.unwrap_err(),
                KernelError::InvalidInductiveOccurrence {
                    inductive: family_name,
                    ctor: target_ctor,
                    field_index: u32::try_from(spec.preceding_fields).expect("small field index"),
                },
                "{}",
                spec.id
            );
            assert_eq!(environment_snapshot(&kernel), before, "{}", spec.id);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn public_twelve_row_contract_matrix() {
    let rows = [
        (
            "no_occurrence",
            Profile::Plain,
            FamilySort::Prop,
            Production::NoOccurrence,
            2,
            0,
            true,
        ),
        (
            "direct",
            Profile::Plain,
            FamilySort::Type,
            Production::Canonical,
            0,
            0,
            false,
        ),
        (
            "positive_pi_1",
            Profile::Parametric,
            FamilySort::Type,
            Production::PositivePi,
            1,
            0,
            false,
        ),
        (
            "positive_pi_2",
            Profile::Plain,
            FamilySort::Prop,
            Production::PositivePi,
            2,
            0,
            false,
        ),
        (
            "recursive_indexed",
            Profile::ParametricIndexed,
            FamilySort::Type,
            Production::Canonical,
            0,
            0,
            false,
        ),
        (
            "negative_domain",
            Profile::Parametric,
            FamilySort::Prop,
            Production::NegativeDomain,
            0,
            0,
            false,
        ),
        (
            "mixed_polarity",
            Profile::Plain,
            FamilySort::Type,
            Production::MixedPolarity,
            1,
            1,
            true,
        ),
        (
            "deep_negative",
            Profile::Plain,
            FamilySort::Prop,
            Production::DeepNegative,
            2,
            2,
            false,
        ),
        (
            "wrong_parameter",
            Profile::Parametric,
            FamilySort::Type,
            Production::WrongParameter,
            0,
            0,
            false,
        ),
        (
            "nested_application",
            Profile::Plain,
            FamilySort::Type,
            Production::NestedApplication,
            1,
            0,
            false,
        ),
        (
            "self_index",
            Profile::ParametricIndexed,
            FamilySort::Type,
            Production::SelfIndex,
            0,
            0,
            false,
        ),
        (
            "wrong_index_arity",
            Profile::ParametricIndexed,
            FamilySort::Prop,
            Production::WrongIndexArity,
            0,
            0,
            false,
        ),
    ];

    for (
        id,
        profile,
        family_sort,
        production,
        context_depth,
        preceding_fields,
        preceding_constructor,
    ) in rows
    {
        let expected = expected_for(profile, production, context_depth);
        run_case(&CaseSpec {
            id: format!("matrix_{id}"),
            profile,
            family_sort,
            production,
            context_depth,
            preceding_fields,
            preceding_constructor,
            expected,
        });
    }
}

fn productions_for(profile: Profile) -> Vec<Production> {
    let mut productions = Production::BASE.to_vec();
    if !matches!(profile, Profile::Plain) {
        productions.push(Production::WrongParameter);
    }
    if profile.is_indexed() {
        productions.push(Production::SelfIndex);
        productions.push(Production::WrongIndexArity);
    }
    productions
}

fn fnv1a(mut digest: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        digest ^= u64::from(byte);
        digest = digest.wrapping_mul(0x0000_0100_0000_01b3);
    }
    digest
}

fn run_generated_grammar() -> String {
    let mut ids = BTreeSet::new();
    let mut outcome_counts = [0_usize; 5];
    let mut tl211_outcome_counts = [0_usize; 5];
    let mut profile_counts = [0_usize; 3];
    let mut sort_counts = [0_usize; 2];
    let mut depth_counts = [0_usize; 5];
    let mut digest = 0xcbf2_9ce4_8422_2325_u64;
    let mut rng = Lcg(GENERATOR_SEED);
    let mut cases = 0_usize;

    for (profile_index, profile) in Profile::ALL.into_iter().enumerate() {
        for (sort_index, family_sort) in FamilySort::ALL.into_iter().enumerate() {
            for production in productions_for(profile) {
                for (context_depth, depth_count) in depth_counts.iter_mut().enumerate() {
                    for preceding_fields in 0..=2 {
                        let case_seed = rng.next_u64();
                        let preceding_constructor = (case_seed & 1) == 1;
                        let id = format!(
                            "generated_{}_{}_{}_d{}_f{}_c{}",
                            profile.label(),
                            family_sort.label(),
                            production.label().replace('-', "_"),
                            context_depth,
                            preceding_fields,
                            usize::from(preceding_constructor)
                        );
                        assert!(ids.insert(id.clone()), "duplicate generated id: {id}");
                        let expected = expected_for(profile, production, context_depth);
                        let tl211_expected = tl211_expected_for(profile, production, context_depth);
                        let descriptor = format!(
                            "{id}|{}|{}|{}|{context_depth}|{preceding_fields}|{}|{}|{case_seed:016x}\n",
                            profile.label(),
                            family_sort.label(),
                            production.label(),
                            usize::from(preceding_constructor),
                            tl211_expected.label()
                        );
                        digest = fnv1a(digest, descriptor.as_bytes());
                        run_case(&CaseSpec {
                            id,
                            profile,
                            family_sort,
                            production,
                            context_depth,
                            preceding_fields,
                            preceding_constructor,
                            expected,
                        });
                        cases += 1;
                        outcome_counts[expected.index()] += 1;
                        tl211_outcome_counts[tl211_expected.index()] += 1;
                        profile_counts[profile_index] += 1;
                        sort_counts[sort_index] += 1;
                        *depth_count += 1;
                    }
                }
            }
        }
    }

    assert!(cases >= 256, "generated grammar shrank to {cases} cases");
    assert_eq!(ids.len(), cases, "generated cases are not identity-unique");
    assert!(outcome_counts[0] > 0 && outcome_counts[3] > 0 && outcome_counts[4] > 0);
    assert_eq!((outcome_counts[1], outcome_counts[2]), (0, 0));
    assert!(tl211_outcome_counts.iter().all(|&count| count > 0));
    assert!(profile_counts.iter().all(|&count| count > 0));
    assert!(sort_counts.iter().all(|&count| count > 0));
    assert!(depth_counts.iter().all(|&count| count > 0));

    format!(
        "schema=axeyum-lean-strict-positivity-grammar-v2\n\
         seed={GENERATOR_SEED:016x}\n\
         cases={cases}\n\
         admission=admit:{},recursive-indexed:{},reflexive:{},non-positive:{},invalid:{}\n\
         tl2.11-baseline-outcomes=admit:{},recursive-indexed:{},reflexive:{},non-positive:{},invalid:{}\n\
         profiles=0p0i:{},1p0i:{},1p1i:{}\n\
         sorts=prop:{},type:{}\n\
         depths=0:{},1:{},2:{},3:{},4:{}\n\
         tl2.11-descriptor-fnv1a64={digest:016x}\n",
        outcome_counts[0],
        outcome_counts[1],
        outcome_counts[2],
        outcome_counts[3],
        outcome_counts[4],
        tl211_outcome_counts[0],
        tl211_outcome_counts[1],
        tl211_outcome_counts[2],
        tl211_outcome_counts[3],
        tl211_outcome_counts[4],
        profile_counts[0],
        profile_counts[1],
        profile_counts[2],
        sort_counts[0],
        sort_counts[1],
        depth_counts[0],
        depth_counts[1],
        depth_counts[2],
        depth_counts[3],
        depth_counts[4],
    )
}

#[test]
fn generated_grammar_is_complete_and_byte_identical() {
    let first = run_generated_grammar();
    let second = run_generated_grammar();
    assert_eq!(first.as_bytes(), second.as_bytes());
    assert_eq!(first, EXPECTED_GENERATED_SUMMARY);
}
