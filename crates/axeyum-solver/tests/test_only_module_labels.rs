//! The wiring ratchet for ADR-1812: **a module with no in-crate caller must say
//! so, and a module that says so must still have none.**
//!
//! `docs/solver-inventory-2026-09/11-wiring-and-integration.md` measured that
//! eleven `axeyum-solver` modules were reachable only from the crate's own test
//! suite. Roadmap item 2.7 resolved each one: two were wired, nine were
//! labelled with a recorded reason. Without a check, both halves rot silently —
//! a label outlives the condition that justified it, or a wiring is reverted and
//! nothing notices. Neither failure is visible to a compiler.
//!
//! # What this test measures, and how it can fail
//!
//! It reimplements the inventory's module-level reachability method over the
//! source text, with two corrections the original method needs (both of which
//! changed an answer here):
//!
//! * **Comments and string literals are not code.** `capabilities.rs` and
//!   `config_registry.rs` describe most of this crate in prose tables; a plain
//!   name search reads those as callers. `pdr_lia`/`imc_lia` looked referenced
//!   for exactly this reason. String literals are stripped over the WHOLE text,
//!   not line by line — a Rust literal continues across lines.
//! * **A bare identifier is not an import.** `quant_bool_model_sat.rs` defines
//!   its own `MAX_CANDIDATES`, which is also `abduct`'s re-exported name; a name
//!   search calls that a caller. A re-exported name counts only when the file
//!   actually imported it (`use …`) or wrote it as `crate::NAME`.
//!
//! Limits, stated because they bound what a pass means: this is source text with
//! no build and no run, so dispatch through a trait object, a macro, or a
//! registry table can hide a caller, and a dead *function* inside a live module
//! is invisible. It sees modules.
//!
//! Both parts below fail loudly by listing the offending modules. Deleting a
//! label, or reverting the `Int` branch of `horn.rs`'s dispatch, makes this test
//! red.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

/// The marker a module without an in-crate caller must carry in its module docs.
const MARKER: &str = "No in-crate caller";

/// The eleven modules `11-wiring-and-integration.md` measured as test-only on
/// 2026-09-09, with the disposition roadmap item 2.7 recorded for each.
///
/// This list is a literal, and deliberately so: it is the inventory's finding,
/// which is the authority for the item, not a fact re-derivable from today's
/// source. Part A below IS derived from the source and covers the whole crate.
const INVENTORY_2026_09_09: &[(&str, Disposition)] = &[
    ("abduct", Disposition::Labelled),
    ("enums", Disposition::Labelled),
    ("faithfulness", Disposition::Labelled),
    ("horn", Disposition::Labelled),
    ("hypothesis_min", Disposition::Labelled),
    ("imc_lia", Disposition::Wired),
    ("lex_reconstruct", Disposition::Labelled),
    ("pb", Disposition::Labelled),
    ("pdr_lia", Disposition::Wired),
    ("records", Disposition::Labelled),
    ("toy_bv_vm", Disposition::Labelled),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Disposition {
    /// Item 2.7 gave it a production caller; it must now have one.
    Wired,
    /// Item 2.7 recorded why it has none; it must carry the marker.
    Labelled,
}

fn src_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// Every `.rs` file under `src/`, sorted (determinism is a public promise here
/// too — a failure message must not depend on directory order).
fn src_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let entries = fs::read_dir(&d).unwrap_or_else(|e| panic!("read_dir {}: {e}", d.display()));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// Drop string literals and comment bodies. A mention in a doc comment or inside
/// a reporting table's string is documentation, not a caller.
fn code_only(text: &str) -> String {
    // Strings first, over the whole text: a Rust literal may span lines.
    let mut out = String::with_capacity(text.len());
    let bytes: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            if c == '\\' {
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            } else if c == '\n' {
                // Keep line structure so the line-comment pass stays aligned.
                out.push('\n');
            }
            i += 1;
            continue;
        }
        if c == '"' {
            in_string = true;
            i += 1;
            continue;
        }
        out.push(c);
        i += 1;
    }
    // Then line comments (doc comments included) and block comments.
    let mut result = String::with_capacity(out.len());
    for line in out.lines() {
        let cut = line.find("//").map_or(line, |idx| &line[..idx]);
        result.push_str(cut);
        result.push('\n');
    }
    strip_block_comments(&result)
}

fn strip_block_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("/*") {
        out.push_str(&rest[..start]);
        match rest[start..].find("*/") {
            Some(end) => rest = &rest[start + end + 2..],
            None => return out,
        }
    }
    out.push_str(rest);
    out
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether `needle` occurs in `haystack` with an identifier boundary on the
/// LEFT. For needles that end in `::` this is the whole check: `imc_lia::` must
/// not match inside `warm_imc_lia::`, but the character after `::` is of course
/// an identifier character.
fn contains_prefix(haystack: &str, needle: &str) -> bool {
    let mut from = 0;
    while let Some(idx) = haystack[from..].find(needle) {
        let start = from + idx;
        if start == 0
            || !haystack[..start]
                .chars()
                .next_back()
                .is_some_and(is_ident_char)
        {
            return true;
        }
        from = start + needle.len();
    }
    false
}

/// Whether `needle` occurs in `haystack` as a whole identifier path — boundaries
/// on both sides, so `crate::Foo` does not match `crate::FooBar`.
fn contains_exact(haystack: &str, needle: &str) -> bool {
    let mut from = 0;
    while let Some(idx) = haystack[from..].find(needle) {
        let start = from + idx;
        let end = start + needle.len();
        let before_ok = start == 0
            || !haystack[..start]
                .chars()
                .next_back()
                .is_some_and(is_ident_char);
        let after_ok = haystack[end..]
            .chars()
            .next()
            .is_none_or(|c| !is_ident_char(c));
        if before_ok && after_ok {
            return true;
        }
        from = end;
    }
    false
}

/// Whether `code` names the module `m` by path. `{m}::` covers `m::`,
/// `crate::m::`, `super::m::` and `self::m::` in one; the two exact forms cover
/// importing the module itself (`use crate::m;`).
fn names_module_path(code: &str, m: &str) -> bool {
    contains_prefix(code, &format!("{m}::"))
        || contains_exact(code, &format!("crate::{m}"))
        || contains_exact(code, &format!("super::{m}"))
}

/// Every identifier a file's `use` statements bring into scope.
fn imported_idents(code: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut rest = code;
    while let Some(idx) = rest.find("use ") {
        let after = &rest[idx + 4..];
        let end = after.find(';').unwrap_or(after.len());
        let chunk = &after[..end];
        let mut current = String::new();
        for c in chunk.chars() {
            if is_ident_char(c) {
                current.push(c);
            } else if !current.is_empty() {
                out.insert(std::mem::take(&mut current));
            }
        }
        if !current.is_empty() {
            out.insert(current);
        }
        rest = &after[end.min(after.len())..];
        if rest.is_empty() {
            break;
        }
        rest = &rest[1.min(rest.len())..];
    }
    out
}

/// The `mod X;` declarations of `lib.rs` (the default set plus everything inside
/// `full_modules!()`).
fn declared_modules(lib: &str) -> Vec<String> {
    let mut out = BTreeSet::new();
    for line in lib.lines() {
        let t = line.trim();
        let t = t.strip_prefix("pub ").unwrap_or(t);
        if let Some(rest) = t.strip_prefix("mod ")
            && let Some(name) = rest.strip_suffix(';')
            && !name.is_empty()
            && name
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
        {
            out.insert(name.to_owned());
        }
    }
    out.into_iter().collect()
}

/// The item names `lib.rs` re-exports from each module: `pub use [crate::]X::{a,
/// b};` and `pub use [crate::]X::a;`.
fn reexports_of(lib: &str, module: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let needles = [format!("use crate::{module}::"), format!("use {module}::")];
    for needle in &needles {
        let mut rest = lib;
        while let Some(idx) = rest.find(needle.as_str()) {
            // Reject a longer module name ending in this one (`int_reconstruct`
            // vs `reconstruct`): the char before `use` is whitespace anyway, so
            // check the char before the module name inside the matched needle.
            let after = &rest[idx + needle.len()..];
            let items: String = if after.starts_with('{') {
                let end = after.find('}').unwrap_or(after.len());
                after[1..end].to_owned()
            } else {
                let end = after.find(';').unwrap_or(after.len());
                after[..end].to_owned()
            };
            for item in items.split(',') {
                let name = item.split(" as ").next().unwrap_or("").trim();
                if !name.is_empty() && name != "self" && name.chars().all(is_ident_char) {
                    out.insert(name.to_owned());
                }
            }
            rest = &rest[idx + needle.len()..];
        }
    }
    out
}

/// The `src/` files (other than `lib.rs` and the module's own file/directory)
/// that reference `module`.
fn in_crate_callers(module: &str, reexports: &BTreeSet<String>, files: &[PathBuf]) -> Vec<String> {
    let src = src_dir();
    let own_file = src.join(format!("{module}.rs"));
    let own_dir = src.join(module);
    let lib = src.join("lib.rs");
    let mut out = Vec::new();
    for path in files {
        if *path == lib || *path == own_file || path.starts_with(&own_dir) {
            continue;
        }
        let text = fs::read_to_string(path).expect("read src file");
        let code = code_only(&text);
        let hit = names_module_path(&code, module) || {
            let idents = imported_idents(&code);
            reexports
                .iter()
                .any(|n| idents.contains(n) || contains_exact(&code, &format!("crate::{n}")))
        };
        if hit {
            out.push(
                path.strip_prefix(&src)
                    .unwrap_or(path)
                    .display()
                    .to_string(),
            );
        }
    }
    out
}

fn module_doc_has_marker(module: &str) -> bool {
    let path = src_dir().join(format!("{module}.rs"));
    fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .contains(MARKER)
}

/// **Part A (derived from the source, whole crate).** A module that claims to
/// have no in-crate caller must not have acquired one. A label that outlived its
/// condition is a false statement in the documentation, and it is exactly the
/// kind that survives forever because nothing reads it.
#[test]
fn every_labelled_module_really_has_no_in_crate_caller() {
    let src = src_dir();
    let files = src_files(&src);
    let lib = fs::read_to_string(src.join("lib.rs")).expect("read lib.rs");

    let mut labelled = Vec::new();
    for module in declared_modules(&lib) {
        if module_doc_has_marker(&module) {
            labelled.push(module);
        }
    }
    assert!(
        !labelled.is_empty(),
        "no module carries the `{MARKER}` marker — this test is measuring nothing. \
         Either the markers were removed or the marker text changed."
    );

    let mut stale = Vec::new();
    for module in &labelled {
        let callers = in_crate_callers(module, &reexports_of(&lib, module), &files);
        if !callers.is_empty() {
            stale.push(format!("{module} <- {}", callers.join(", ")));
        }
    }
    assert!(
        stale.is_empty(),
        "{} module(s) claim `{MARKER}` but now HAVE one. Wire-and-label is a \
         contradiction: delete the label section and record the caller instead.\n  {}",
        stale.len(),
        stale.join("\n  ")
    );
}

/// **Part B (the inventory's finding).** Each of the eleven modules
/// `11-wiring-and-integration.md` measured as test-only carries the disposition
/// roadmap item 2.7 gave it: wired ones have a caller, labelled ones say why they
/// do not.
///
/// This is the second, cheap guard on the `horn.rs` `Int` dispatch — reverting it
/// orphans `pdr_lia`/`imc_lia` again and fails here as well as in
/// `tests/horn_lia.rs`.
#[test]
fn the_2026_09_09_test_only_modules_are_wired_or_labelled() {
    let src = src_dir();
    let files = src_files(&src);
    let lib = fs::read_to_string(src.join("lib.rs")).expect("read lib.rs");
    let declared = declared_modules(&lib);

    let mut failures = Vec::new();
    for (module, disposition) in INVENTORY_2026_09_09 {
        assert!(
            declared.iter().any(|d| d == module),
            "`{module}` is no longer declared in lib.rs. If it was deleted, remove its \
             row from INVENTORY_2026_09_09 and say so in ADR-1812 — do not leave this \
             test asserting over a module that is gone."
        );
        let callers = in_crate_callers(module, &reexports_of(&lib, module), &files);
        match disposition {
            Disposition::Wired => {
                if callers.is_empty() {
                    failures.push(format!(
                        "{module}: recorded as WIRED by item 2.7, but no src module \
                         references it any more (the wiring was reverted)"
                    ));
                }
            }
            Disposition::Labelled => {
                if !module_doc_has_marker(module) {
                    failures.push(format!(
                        "{module}: recorded as LABELLED by item 2.7, but its module docs \
                         no longer contain `{MARKER}` (the recorded reason was lost)"
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} inventory modules lost their item-2.7 disposition:\n  {}",
        failures.len(),
        INVENTORY_2026_09_09.len(),
        failures.join("\n  ")
    );
}

/// A control on the measurement itself: the method must find real callers, or
/// Part A above cannot fail. `auto` is the dispatch core — if the reachability
/// check reports it uncalled, the check is broken, not the crate.
#[test]
fn the_reachability_check_finds_a_known_caller() {
    let src = src_dir();
    let files = src_files(&src);
    let lib = fs::read_to_string(src.join("lib.rs")).expect("read lib.rs");
    let callers = in_crate_callers("auto", &reexports_of(&lib, "auto"), &files);
    assert!(
        !callers.is_empty(),
        "`auto` (the dispatch core) reports zero in-crate callers — the reachability \
         check is broken and every 'no caller' result it produces is meaningless"
    );
}
