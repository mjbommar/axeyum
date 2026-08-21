//! A recursor record's `levelParams` must bind every universe parameter its
//! type and its ι-rules mention.
//!
//! Regression for the two violations the kernel-vs-kernel wire differential
//! found on 2026-08-18 (`ind.rec-uparams`, in
//! `real_lean_wire_differential.rs`). Renaming `True.rec`'s or `Acc.rec`'s
//! motive universe parameter **at the binding site** — leaving the type and the
//! rules mentioning the old name, which is now free — was admitted here and
//! contradicted by the recursor Lean's own kernel generated for the same
//! family: `Sort u` where Lean had `Sort uparam.0`.
//!
//! Why nothing caught it. A recursor is **generated** by this kernel and then
//! *compared* against the exported record; it is never admitted from the
//! stream, so `Kernel::check_declaration`'s universe-closure check — the one
//! round 2 added for exactly this failure — is never handed the exported
//! binding list. The comparison alpha-renames the exported parameters onto the
//! generated ones **positionally**, so a parameter the exported list does not
//! bind is simply not in the map and passes through untouched; if it happens to
//! spell the name the generated recursor uses, `def_eq` succeeds. `def_eq`
//! could not have seen it either way: it treats an unbound `Param` exactly like
//! a bound one, which is why universe closure has to be its own check
//! everywhere it is checked at all.
//!
//! Both guards are driven to failure here, separately: removing the type check
//! kills only [`renamed_recursor_universe_parameter_is_rejected`], removing the
//! ι-rule check kills only [`recursor_rule_universe_parameter_must_be_bound`],
//! and [`the_undamaged_export_still_imports`] is the control that fails if the
//! guards start rejecting well-formed streams instead.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Kernel, Lean4ExportMetadata, build_logic_prelude};
use serde_json::Value;

/// The logic prelude, rendered as an official-format NDJSON stream.
fn stream() -> Vec<String> {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");
    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export")
        .lines()
        .map(str::to_owned)
        .collect()
}

fn joined(lines: &[String]) -> String {
    let mut text = lines.join("\n");
    text.push('\n');
    text
}

fn import(lines: &[String]) -> Result<(), ImportError> {
    import_ndjson(
        Cursor::new(joined(lines).into_bytes()),
        ImportLimits::default(),
    )
    .map(|_| ())
}

fn malformed_message(error: &ImportError) -> String {
    match error {
        ImportError::Malformed { message, .. } => message.clone(),
        other => panic!("expected a malformed-record rejection, got {other:?}"),
    }
}

/// The first `inductive` record carrying a recursor with at least one universe
/// parameter, as `(line index, parsed record)`.
fn universe_polymorphic_group(lines: &[String]) -> (usize, Value) {
    for (index, line) in lines.iter().enumerate() {
        let Ok(record) = serde_json::from_str::<Value>(line) else {
            continue;
        };
        let Some(group) = record.get("inductive") else {
            continue;
        };
        let has_parameters = group["recs"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(|recursor| recursor["levelParams"].as_array())
            .is_some_and(|list| !list.is_empty());
        if has_parameters {
            return (index, record);
        }
    }
    panic!(
        "no inductive record carries a universe-polymorphic recursor; the \
         development this test damages no longer contains the construct it is \
         about, so a pass here would mean nothing"
    );
}

/// The number of name records the stream defines before `line`.
///
/// `Name.anonymous` occupies slot 0 before any record is read.
fn names_before(lines: &[String], line: usize) -> usize {
    1 + lines[..line]
        .iter()
        .filter_map(|text| serde_json::from_str::<Value>(text).ok())
        .filter(|record| record.get("in").is_some())
        .count()
}

#[test]
fn the_undamaged_export_still_imports() {
    let lines = stream();
    assert!(
        lines.len() > 100,
        "the export shrank to {} records; a control that checks nothing passes \
         just as loudly as one that checks everything",
        lines.len()
    );
    import(&lines).expect("our own export must re-import");
}

#[test]
fn renamed_recursor_universe_parameter_is_rejected() {
    let mut lines = stream();
    let (line, record) = universe_polymorphic_group(&lines);
    let mut damaged = record.clone();
    let declared = record["inductive"]["recs"][0]["levelParams"][0]
        .as_u64()
        .expect("a declared universe parameter");
    // Any other name already in the table: the record stays structurally valid
    // (every index still points at a real, earlier entry) and the recursor's
    // type and rules keep mentioning the parameter that is now unbound.
    let replacement = (declared + 1) % names_before(&lines, line) as u64;
    assert_ne!(
        replacement, declared,
        "the name table is too small to offer a different target"
    );
    damaged["inductive"]["recs"][0]["levelParams"][0] = Value::from(replacement);
    lines[line] = serde_json::to_string(&damaged).expect("re-serialize record");

    let error = import(&lines).expect_err(
        "a recursor whose type mentions a universe parameter its levelParams \
         does not bind must be refused; Lean's kernel refuses it",
    );
    let message = malformed_message(&error);
    assert!(
        message.contains("recursor type mentions unbound universe parameter"),
        "rejected for the wrong reason: {message}"
    );
}

#[test]
fn recursor_rule_universe_parameter_must_be_bound() {
    let mut lines = stream();
    let (line, record) = universe_polymorphic_group(&lines);

    // An ι-rule right-hand side is a separate expression from the recursor
    // type, so it can mention a parameter the type does not — and the exported
    // type stays byte-identical, which is what makes this reach the rule check
    // instead of stopping at the type check. Records are APPENDED immediately
    // before the group, so every existing name, level and expression index in
    // the stream keeps its meaning.
    let name_index = names_before(&lines, line);
    let level_index = 1 + lines[..line]
        .iter()
        .filter_map(|text| serde_json::from_str::<Value>(text).ok())
        .filter(|record| record.get("il").is_some())
        .count();
    let expr_index = lines[..line]
        .iter()
        .filter_map(|text| serde_json::from_str::<Value>(text).ok())
        .filter(|record| record.get("ie").is_some())
        .count();
    let additions = [
        format!(r#"{{"in":{name_index},"str":{{"pre":0,"str":"axeyum_unbound"}}}}"#),
        format!(r#"{{"il":{level_index},"param":{name_index}}}"#),
        format!(r#"{{"ie":{expr_index},"sort":{level_index}}}"#),
    ];

    let mut damaged = record.clone();
    damaged["inductive"]["recs"][0]["rules"][0]["rhs"] = Value::from(expr_index as u64);
    lines[line] = serde_json::to_string(&damaged).expect("re-serialize record");
    lines.splice(line..line, additions.iter().cloned());

    let error = import(&lines).expect_err(
        "an ι-rule right-hand side mentioning a universe parameter the \
         recursor does not bind must be refused",
    );
    let message = malformed_message(&error);
    // The assertion is on WHICH check fired, not merely that something did:
    // without the rule's closure check this stream is still refused, by the
    // def-eq comparison one line later, and a test that only asserted
    // `is_err()` would pass with the guard deleted.
    assert!(
        message.contains("recursor rule mentions unbound universe parameter"),
        "rejected for the wrong reason: {message}"
    );
}
