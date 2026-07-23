//! End-to-end and mutation tests for the official format-3.1 fixture.

use std::io::{BufReader, Cursor, Read};

use axeyum_lean_import::{DeclarationKind, ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, KernelError, QuotKind};

const FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson");
const RECURSIVE_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson");
const PROJECTION_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-projection.ndjson");
const NAT_LITERAL_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nat-literal.ndjson");
const QUOTIENT_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

fn import(text: &str) -> Result<(Kernel, axeyum_lean_import::ImportReport), ImportError> {
    let completed = import_ndjson(Cursor::new(text.as_bytes()), ImportLimits::default())?;
    Ok(completed.into_parts())
}

fn metadata() -> &'static str {
    r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"test","version":"4.30.0"}}}"#
}

#[test]
fn official_flat_fixture_is_independently_admitted() {
    let (kernel, report) = import(FIXTURE).expect("the official flat fixture admits");
    assert_eq!(report.format_version, "3.1.0");
    assert_eq!(report.lean_version, "4.30.0");
    assert_eq!(
        report.lean_githash,
        "d024af099ca4bf2c86f649261ebf59565dc8c622"
    );
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (14, 2, 43, 5, 8)
    );
    assert_eq!(report.axioms, ["P"]);
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "Two",
            "Two.left",
            "Two.right",
            "Two.rec",
            "Two.recOn",
            "chooseLeft",
            "P",
            "identity",
        ]
    );
}

#[test]
fn official_direct_recursive_families_are_independently_admitted() {
    let (kernel, report) = import(RECURSIVE_FIXTURE).expect("direct-recursive fixture admits");
    let recursor_identity = |name: &str| {
        report
            .declaration_identities
            .iter()
            .find(|identity| identity.name == name)
            .unwrap_or_else(|| panic!("missing direct-recursive identity for {name}"))
            .content_sha256
            .as_str()
    };
    assert_eq!(
        recursor_identity("MiniNat.rec"),
        "dee04a36959066e63f15d5711a5a03de2ac91d71333c48135ef0fdc89cb0f5ef"
    );
    assert_eq!(
        recursor_identity("MiniList.rec"),
        "1087558f366706316eefaca0abc48a4b592da2a8496e5d6bbdaa7eea5b677660"
    );
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (30, 4, 130, 5, 11)
    );
    assert!(report.axioms.is_empty());
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "MiniList",
            "MiniList.nil",
            "MiniList.cons",
            "MiniList.rec",
            "MiniList.recOn",
            "MiniNat",
            "MiniNat.zero",
            "MiniNat.succ",
            "MiniNat.rec",
            "miniOne",
            "MiniNat.recOn",
        ]
    );
}

#[test]
fn official_projection_fixture_is_independently_admitted_and_computes() {
    let (mut kernel, report) = import(PROJECTION_FIXTURE).expect("projection fixture admits");
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (21, 2, 61, 4, 9)
    );
    assert!(report.axioms.is_empty());
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "Nat",
            "Nat.zero",
            "Nat.succ",
            "Nat.rec",
            "ImportPair",
            "ImportPair.mk",
            "ImportPair.rec",
            "ImportPair.left",
            "importPairLeft",
        ]
    );

    let anon = kernel.anon();
    let nat = kernel.name_str(anon, "Nat");
    let nat_zero = kernel.name_str(nat, "zero");
    let nat_succ = kernel.name_str(nat, "succ");
    let pair = kernel.name_str(anon, "ImportPair");
    let pair_mk = kernel.name_str(pair, "mk");
    let import_pair_left = kernel.name_str(anon, "importPairLeft");
    let zero = kernel.const_(nat_zero, vec![]);
    let one = {
        let succ = kernel.const_(nat_succ, vec![]);
        kernel.app(succ, zero)
    };
    let value = {
        let ctor = kernel.const_(pair_mk, vec![]);
        let with_left = kernel.app(ctor, zero);
        kernel.app(with_left, one)
    };
    let imported_call = {
        let function = kernel.const_(import_pair_left, vec![]);
        kernel.app(function, value)
    };
    assert_eq!(kernel.whnf(imported_call), zero);
    let right = kernel.proj(pair, 1, value);
    assert_eq!(kernel.whnf(right), one);
}

#[test]
fn official_nat_literal_fixture_is_independently_admitted_and_computes() {
    let (mut kernel, report) = import(NAT_LITERAL_FIXTURE).expect("Nat literal closure admits");
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (30, 4, 90, 5, 10)
    );
    assert!(report.axioms.is_empty());
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "Nat",
            "Nat.zero",
            "Nat.succ",
            "Nat.rec",
            "OfNat",
            "OfNat.mk",
            "OfNat.rec",
            "OfNat.ofNat",
            "instOfNatNat",
            "importNatLiteral",
        ]
    );

    let anon = kernel.anon();
    let imported_name = kernel.name_str(anon, "importNatLiteral");
    let imported = kernel.const_(imported_name, vec![]);
    let reduced = kernel.whnf(imported);
    assert_eq!(kernel.render_lean(reduced), "37");
}

#[test]
fn official_quotient_fixture_is_atomically_admitted_and_computes() {
    let (mut kernel, report) = import(QUOTIENT_FIXTURE).expect("quotient closure admits");
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (25, 3, 87, 5, 7)
    );
    assert!(report.axioms.is_empty());
    assert!(report.axiom_identities.is_empty());
    assert_eq!(report.declaration_identities.len(), 7);
    let quotient_identities = report
        .declaration_identities
        .iter()
        .filter(|identity| identity.kind == DeclarationKind::Quotient)
        .collect::<Vec<_>>();
    assert_eq!(quotient_identities.len(), 4);

    let root = kernel.anon();
    let quot = kernel.name_str(root, "Quot");
    let quot_mk = kernel.name_str(quot, "mk");
    let quot_lift = kernel.name_str(quot, "lift");
    let quot_ind = kernel.name_str(quot, "ind");
    for (name, kind) in [
        (quot, QuotKind::Type),
        (quot_mk, QuotKind::Ctor),
        (quot_lift, QuotKind::Lift),
        (quot_ind, QuotKind::Ind),
    ] {
        assert!(matches!(
            kernel.environment().get(name),
            Some(Declaration::Quotient {
                kind: actual_kind,
                ..
            }) if *actual_kind == kind
        ));
    }

    let zero = kernel.level_zero();
    let representative = kernel.sort_zero();
    let ty = kernel.sort_zero();
    let body = kernel.bvar(0);
    let function = kernel.lam(root, ty, body, axeyum_lean_kernel::BinderInfo::Default);
    let constructor = kernel.const_(quot_mk, vec![zero]);
    let constructor = kernel.app(constructor, ty);
    let constructor = kernel.app(constructor, ty);
    let constructor = kernel.app(constructor, representative);
    let lift = kernel.const_(quot_lift, vec![zero, zero]);
    let mut application = lift;
    for argument in [ty, ty, ty, function, ty, constructor] {
        application = kernel.app(application, argument);
    }
    assert_eq!(kernel.whnf(application), representative);
}

#[test]
fn quotient_wire_order_completeness_and_interleaving_are_fail_closed() {
    for end_line in [65, 73, 100] {
        let prefix = format!(
            "{}\n",
            QUOTIENT_FIXTURE
                .lines()
                .take(end_line)
                .collect::<Vec<_>>()
                .join("\n")
        );
        let error = import(&prefix).unwrap_err();
        assert!(
            matches!(error, ImportError::Malformed { line, ref message }
                if line == end_line && message.contains("incomplete quotient package")),
            "end_line={end_line}: {error:?}"
        );
    }

    let wrong_order = QUOTIENT_FIXTURE.replacen(r#""kind":"type""#, r#""kind":"ctor""#, 1);
    let error = import(&wrong_order).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 65, ref message }
            if message.contains("out of order")),
        "{error:?}"
    );

    let mut lines = QUOTIENT_FIXTURE.lines().collect::<Vec<_>>();
    lines.insert(
        65,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":15,"type":0}}"#,
    );
    let interleaved = format!("{}\n", lines.join("\n"));
    let error = import(&interleaved).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 66, ref message }
            if message.contains("interleaves")),
        "{error:?}"
    );

    let quotient_records = QUOTIENT_FIXTURE
        .lines()
        .filter(|line| line.starts_with(r#"{"quot":"#))
        .collect::<Vec<_>>();
    assert_eq!(quotient_records.len(), 4);
    let duplicated = format!("{QUOTIENT_FIXTURE}{}\n", quotient_records.join("\n"));
    let error = import(&duplicated).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 122, ref message }
            if message.contains("duplicate quotient package")),
        "{error:?}"
    );
}

#[test]
fn quotient_relation_and_proof_type_mutations_reach_the_kernel_gate() {
    for (needle, replacement) in [
        (
            r#"{"quot":{"kind":"lift","levelParams":[11,19],"name":18,"type":69}}"#,
            r#"{"quot":{"kind":"lift","levelParams":[11,19],"name":18,"type":68}}"#,
        ),
        (
            r#"{"quot":{"kind":"ind","levelParams":[11],"name":23,"type":86}}"#,
            r#"{"quot":{"kind":"ind","levelParams":[11],"name":23,"type":85}}"#,
        ),
    ] {
        let mutated = QUOTIENT_FIXTURE.replace(needle, replacement);
        assert_ne!(mutated, QUOTIENT_FIXTURE);
        let error = import(&mutated).unwrap_err();
        assert!(
            matches!(
                error,
                ImportError::Kernel {
                    line: 121,
                    source: KernelError::QuotientTypeMismatch { .. },
                    ..
                }
            ),
            "{error:?}"
        );
    }
}

#[test]
fn quotient_wire_shape_and_package_metadata_mutations_fail_closed() {
    for (needle, replacement, expected_line, expected_message) in [
        (
            r#""quot":{"kind":"type","levelParams":[11],"name":15,"type":43}"#,
            r#""quot":{"kind":"mystery","levelParams":[11],"name":15,"type":43}"#,
            65,
            "quot.kind is not",
        ),
        (
            r#""quot":{"kind":"type","levelParams":[11],"name":15,"type":43}"#,
            r#""quot":{"extra":0,"kind":"type","levelParams":[11],"name":15,"type":43}"#,
            65,
            "expected fields",
        ),
    ] {
        let mutated = QUOTIENT_FIXTURE.replace(needle, replacement);
        assert_ne!(mutated, QUOTIENT_FIXTURE);
        let error = import(&mutated).unwrap_err();
        assert!(
            matches!(error, ImportError::Malformed { line, ref message }
                if line == expected_line && message.contains(expected_message)),
            "{error:?}"
        );
    }

    for (needle, replacement, expected) in [
        (
            r#"{"quot":{"kind":"type","levelParams":[11],"name":15,"type":43}}"#,
            r#"{"quot":{"kind":"type","levelParams":[11],"name":1,"type":43}}"#,
            "name",
        ),
        (
            r#"{"quot":{"kind":"lift","levelParams":[11,19],"name":18,"type":69}}"#,
            r#"{"quot":{"kind":"lift","levelParams":[11],"name":18,"type":69}}"#,
            "universe",
        ),
    ] {
        let mutated = QUOTIENT_FIXTURE.replace(needle, replacement);
        assert_ne!(mutated, QUOTIENT_FIXTURE);
        let error = import(&mutated).unwrap_err();
        match expected {
            "name" => assert!(
                matches!(
                    error,
                    ImportError::Kernel {
                        line: 121,
                        source: KernelError::QuotientPackageNameMismatch { .. },
                        ..
                    }
                ),
                "expected name rejection, got {error:?}"
            ),
            "universe" => assert!(
                matches!(
                    error,
                    ImportError::Kernel {
                        line: 121,
                        source: KernelError::QuotientUniverseParametersMismatch { .. },
                        ..
                    }
                ),
                "expected universe rejection, got {error:?}"
            ),
            _ => unreachable!("unknown rejection expectation"),
        }
    }
}

#[test]
fn quotient_named_ordinary_axiom_remains_in_the_axiom_ledger() {
    let fixture = format!(
        "{QUOTIENT_FIXTURE}{{\"in\":26,\"str\":{{\"pre\":15,\"str\":\"sound\"}}}}\n\
         {{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":26,\"type\":3}}}}\n"
    );
    let (kernel, report) = import(&fixture).expect("ordinary post-package axiom admits");
    assert_eq!(report.axiom_identities.len(), 1);
    assert_eq!(report.axiom_identities[0].name, "Quot.sound");
    assert_eq!(
        report
            .declaration_identities
            .iter()
            .find(|identity| identity.name == "Quot.sound")
            .map(|identity| identity.kind),
        Some(DeclarationKind::Axiom)
    );
    assert!(matches!(
        kernel.environment().iter().find_map(|(_, declaration)| {
            (kernel.display_name(declaration.name()).to_string() == "Quot.sound")
                .then_some(declaration)
        }),
        Some(Declaration::Axiom { .. })
    ));
}

#[test]
fn nat_literal_wire_values_are_validated_without_fixed_width_narrowing() {
    let values = [
        "340282366920938463463374607431768211455", // 2^128 - 1
        "340282366920938463463374607431768211456", // 2^128
        "340282366920938463463374607431768211457", // 2^128 + 1
        "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031",
    ];
    for value in values {
        let fixture =
            NAT_LITERAL_FIXTURE.replace(r#""natVal":"37""#, &format!(r#""natVal":"{value}""#));
        assert_ne!(fixture, NAT_LITERAL_FIXTURE);
        let (mut kernel, report) =
            import(&fixture).expect("arbitrary-precision Nat closure admits");
        assert_eq!(report.admitted_declarations, 10);
        let anon = kernel.anon();
        let imported_name = kernel.name_str(anon, "importNatLiteral");
        let imported = kernel.const_(imported_name, vec![]);
        let reduced = kernel.whnf(imported);
        assert_eq!(kernel.render_lean(reduced), value);
    }
}

#[test]
fn malformed_nat_literal_wire_values_reject_before_the_typing_boundary() {
    for value in ["", "+1", "-1", " 1", "1 ", "1_0", "12a"] {
        let text = format!("{}\n{{\"ie\":0,\"natVal\":\"{value}\"}}\n", metadata());
        let error = import(&text).unwrap_err();
        assert!(
            matches!(error, ImportError::Malformed { line: 2, .. }),
            "{value:?}: {error:?}"
        );
    }

    let text = format!("{}\n{{\"ie\":0,\"natVal\":1}}\n", metadata());
    let error = import(&text).unwrap_err();
    assert!(matches!(error, ImportError::Malformed { line: 2, .. }));
}

#[test]
fn renamed_nat_bootstrap_rejects_literal_use_at_the_kernel_gate() {
    let mutated = NAT_LITERAL_FIXTURE.replace(
        r#"{"in":2,"str":{"pre":1,"str":"zero"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"zeroRenamed"}}"#,
    );
    assert_ne!(mutated, NAT_LITERAL_FIXTURE);
    let error = import(&mutated).unwrap_err();
    assert!(
        matches!(
            error,
            ImportError::Kernel {
                line: 130,
                ref declaration,
                source: KernelError::NatLiteralBootstrapMismatch { .. },
            } if declaration == "importNatLiteral"
        ),
        "{error:?}"
    );
}

#[test]
fn repeated_import_is_deterministic() {
    let (first_kernel, first_report) = import(FIXTURE).unwrap();
    let (second_kernel, second_report) = import(FIXTURE).unwrap();
    assert_eq!(first_report, second_report);
    let first: Vec<_> = first_kernel
        .environment()
        .iter()
        .map(|(_, declaration)| format!("{declaration:?}"))
        .collect();
    let second: Vec<_> = second_kernel
        .environment()
        .iter()
        .map(|(_, declaration)| format!("{declaration:?}"))
        .collect();
    assert_eq!(first, second);
}

#[test]
fn unknown_record_fails_closed() {
    let text = format!("{}\n{{\"mystery\":{{}}}}\n", metadata());
    let error = import(&text).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 2, .. }),
        "{error:?}"
    );
}

#[test]
fn forward_expression_reference_fails_closed() {
    let text = format!(
        "{}\n{{\"ie\":0,\"app\":{{\"fn\":1,\"arg\":1}}}}\n",
        metadata()
    );
    let error = import(&text).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 2, .. }),
        "{error:?}"
    );
}

#[test]
fn projection_records_translate_and_malformed_shapes_reject() {
    let projection = format!(
        concat!(
            "{}\n",
            "{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"T\"}}}}\n",
            "{{\"ie\":0,\"bvar\":0}}\n",
            "{{\"ie\":1,\"proj\":{{\"typeName\":1,\"idx\":0,\"struct\":0}}}}\n"
        ),
        metadata()
    );
    let (_, report) = import(&projection).expect("well-shaped projection record translates");
    assert_eq!(report.expressions, 2);

    let oversized_index = projection.replace(r#""idx":0"#, r#""idx":4294967296"#);
    let error = import(&oversized_index).unwrap_err();
    assert!(matches!(error, ImportError::Malformed { line: 4, .. }));

    let forward_structure = projection.replace(r#""struct":0"#, r#""struct":2"#);
    let error = import(&forward_structure).unwrap_err();
    assert!(matches!(error, ImportError::Malformed { line: 4, .. }));
}

#[test]
fn official_projection_name_and_index_mutations_reject_at_the_kernel_gate() {
    let wrong_name = PROJECTION_FIXTURE.replace(
        r#"{"ie":56,"proj":{"idx":0,"struct":5,"typeName":12}}"#,
        r#"{"ie":56,"proj":{"idx":0,"struct":5,"typeName":1}}"#,
    );
    let error = import(&wrong_name).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Kernel {
            line: 83,
            source: KernelError::ProjectionTypeMismatch { .. },
            ..
        }
    ));

    let wrong_index = PROJECTION_FIXTURE.replace(
        r#"{"ie":56,"proj":{"idx":0,"struct":5,"typeName":12}}"#,
        r#"{"ie":56,"proj":{"idx":2,"struct":5,"typeName":12}}"#,
    );
    let error = import(&wrong_index).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Kernel {
            line: 83,
            source: KernelError::ProjectionFieldOutOfBounds { .. },
            ..
        }
    ));
}

#[test]
fn unknown_format_has_a_stable_decline() {
    let wrong_format = metadata().replace("3.1.0", "4.0.0");
    let error = import(&wrong_format).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Unsupported {
            line: 1,
            code: "format-version"
        }
    ));
}

#[test]
fn tampered_theorem_value_is_rejected_by_kernel() {
    let tampered = FIXTURE.replace(
        r#"{"ie":42,"lam":{"binderInfo":"default","body":4,"name":14,"type":40}}"#,
        r#"{"ie":42,"lam":{"binderInfo":"default","body":39,"name":14,"type":40}}"#,
    );
    assert_ne!(tampered, FIXTURE);
    let error = import(&tampered).unwrap_err();
    assert!(
        matches!(
            error,
            ImportError::Kernel {
                ref declaration,
                ..
            } if declaration == "identity"
        ),
        "{error:?}"
    );
}

#[test]
fn tampered_recursor_rule_is_rejected_before_later_declarations() {
    let tampered = FIXTURE.replacen(r#""rhs":18"#, r#""rhs":17"#, 1);
    assert_ne!(tampered, FIXTURE);
    let error = import(&tampered).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 35, .. }),
        "{error:?}"
    );
}

#[test]
fn partial_definition_is_rejected() {
    let text = format!(
        concat!(
            "{}\n",
            "{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"loop\"}}}}\n",
            "{{\"ie\":0,\"sort\":0}}\n",
            "{{\"def\":{{\"name\":1,\"levelParams\":[],\"type\":0,",
            "\"value\":0,\"hints\":\"opaque\",\"safety\":\"partial\",\"all\":[1]}}}}\n"
        ),
        metadata()
    );
    let error = import(&text).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Unsupported {
            line: 4,
            code: "declaration-unsafe-or-partial"
        }
    ));
}

#[test]
fn resource_limits_reject_before_unbounded_import() {
    let error = import_ndjson(
        Cursor::new(FIXTURE.as_bytes()),
        ImportLimits {
            max_line_bytes: 32,
            max_records: 10,
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        ImportError::LineLimit { line: 1, limit: 32 }
    ));

    let error = import_ndjson(
        Cursor::new(FIXTURE.as_bytes()),
        ImportLimits {
            max_line_bytes: 16 * 1024 * 1024,
            max_records: 1,
        },
    )
    .unwrap_err();
    assert!(matches!(error, ImportError::RecordLimit { limit: 1 }));
}

#[derive(Debug)]
struct LateFailingRead {
    bytes: Vec<u8>,
    position: usize,
}

impl Read for LateFailingRead {
    fn read(&mut self, output: &mut [u8]) -> std::io::Result<usize> {
        if self.position == self.bytes.len() {
            return Err(std::io::Error::other(
                "injected failure after valid records",
            ));
        }
        let available = self.bytes.len() - self.position;
        let count = available.min(output.len());
        output[..count].copy_from_slice(&self.bytes[self.position..self.position + count]);
        self.position += count;
        Ok(count)
    }
}

#[test]
fn completed_import_publishes_kernel_and_matching_report_together() {
    let completed = import_ndjson(Cursor::new(FIXTURE.as_bytes()), ImportLimits::default())
        .expect("valid stream publishes one completed import");
    assert_eq!(completed.report().admitted_declarations, 8);
    assert_eq!(
        completed.kernel().environment().len(),
        completed.report().admitted_declarations
    );

    let (kernel, report) = completed.into_parts();
    assert_eq!(kernel.environment().len(), report.admitted_declarations);
}

#[test]
fn late_failures_never_return_a_partially_admitted_environment() {
    let malformed_after_complete = format!("{FIXTURE}{{\"truncated\":");
    let error = import_ndjson(
        Cursor::new(malformed_after_complete.as_bytes()),
        ImportLimits::default(),
    )
    .unwrap_err();
    assert!(matches!(error, ImportError::Json { .. }), "{error:?}");

    let tampered_final_declaration = FIXTURE.replace(
        r#"{"ie":42,"lam":{"binderInfo":"default","body":4,"name":14,"type":40}}"#,
        r#"{"ie":42,"lam":{"binderInfo":"default","body":39,"name":14,"type":40}}"#,
    );
    let error = import_ndjson(
        Cursor::new(tampered_final_declaration.as_bytes()),
        ImportLimits::default(),
    )
    .unwrap_err();
    assert!(matches!(error, ImportError::Kernel { .. }), "{error:?}");

    let malformed_after_quotient = format!("{QUOTIENT_FIXTURE}{{\"truncated\":");
    let error = import_ndjson(
        Cursor::new(malformed_after_quotient.as_bytes()),
        ImportLimits::default(),
    )
    .unwrap_err();
    assert!(matches!(error, ImportError::Json { .. }), "{error:?}");

    let record_limit = FIXTURE.lines().count() - 1;
    let error = import_ndjson(
        Cursor::new(FIXTURE.as_bytes()),
        ImportLimits {
            max_line_bytes: ImportLimits::default().max_line_bytes,
            max_records: record_limit,
        },
    )
    .unwrap_err();
    assert!(
        matches!(error, ImportError::RecordLimit { limit } if limit == record_limit),
        "{error:?}"
    );

    let failing = LateFailingRead {
        bytes: FIXTURE.as_bytes().to_vec(),
        position: 0,
    };
    let error = import_ndjson(BufReader::new(failing), ImportLimits::default()).unwrap_err();
    assert!(matches!(error, ImportError::Io(_)), "{error:?}");
}
