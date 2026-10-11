//! Datatype evidence exports retain reparsable declarations and operator names.
use axeyum_smtlib::{parse_script, write_script};

fn round_trip(source: &str) -> String {
    let parsed = parse_script(source).unwrap();
    let written = write_script(&parsed.arena, &parsed.assertions);
    let restored = parse_script(&written).unwrap_or_else(|e| panic!("{e}: {written}"));
    assert_eq!(restored.assertions.len(), parsed.assertions.len());
    assert_eq!(write_script(&restored.arena, &restored.assertions), written);
    assert!(!written.contains("(Datatype "), "{written}");
    assert!(!written.contains("construct/"), "{written}");
    assert!(!written.contains("select/"), "{written}");
    written
}

#[test]
fn nullary_constructor_exports_declaration_and_bare_symbol() {
    let written = round_trip("(declare-datatype Color ((red) (blue))) (assert (= red blue))");
    assert!(written.contains("(declare-datatypes ((Color 0)) (((red) (blue))))"));
    assert!(written.contains("(assert (= red blue))"));
}

#[test]
fn recursive_fields_selectors_and_testers_preserve_names() {
    let written = round_trip(
        "(declare-datatype List ((nil) (cons (head Int) (tail List))))
         (declare-const xs List)
         (assert ((_ is cons) xs))
         (assert (= (head xs) 3))
         (assert (= (tail xs) (cons 4 nil)))",
    );
    assert!(written.contains("(cons (head Int) (tail List))"));
    assert!(written.contains("((_ is cons) xs)"));
    assert!(written.contains("(head xs)"));
    assert!(written.contains("(tail xs)"));
    assert!(written.contains("(cons 4 nil)"));
}

#[test]
fn mutually_recursive_declarations_bind_sorts_before_fields() {
    let written = round_trip(
        "(declare-datatypes ((Tree 0) (Forest 0))
          (((leaf) (branch (children Forest)))
           ((empty) (more (first Tree) (rest Forest)))))
         (declare-const tree Tree)
         (assert (= tree (branch (more leaf empty))))",
    );
    assert!(written.contains("(declare-datatypes ((Tree 0) (Forest 0))"));
    assert!(written.contains("(children Forest)"));
    assert!(written.contains("(first Tree) (rest Forest)"));
}

#[test]
fn field_sort_dependency_is_exported_even_without_field_term() {
    let written = round_trip(
        "(declare-sort U 0)
         (declare-datatype Inner ((inner (value U))))
         (declare-datatype Outer ((none) (some (payload Inner))))
         (declare-datatype Unused ((unreachable)))
         (declare-const box Outer)
         (assert ((_ is none) box))",
    );
    let sort_pos = written.find("(declare-sort U 0)").unwrap();
    let dt_pos = written.find("(declare-datatypes").unwrap();
    assert!(sort_pos < dt_pos);
    assert!(written.contains("((Inner 0) (Outer 0))"));
    assert!(written.contains("(value U)"));
    assert!(!written.contains("Unused"));
}

#[test]
fn datatype_array_components_and_function_signature_round_trip() {
    let written = round_trip(
        "(declare-datatype Color ((red) (blue)))
         (declare-const a (Array Color Color))
         (declare-fun f (Color) Color)
         (assert (= (select a red) (f blue)))",
    );
    assert!(written.contains("(declare-const a (Array Color Color))"));
    assert!(written.contains("(declare-fun f (Color) Color)"));
}

#[test]
fn quoted_sort_constructor_and_selector_names_round_trip() {
    let written = round_trip(
        "(declare-datatype |a sort| ((|a constructor| (|a field| Int))))
         (declare-const x |a sort|)
         (assert ((_ is |a constructor|) x))
         (assert (= (|a field| x) 7))",
    );
    assert!(written.contains("(|a sort| 0)"));
    assert!(written.contains("(|a constructor| (|a field| Int))"));
    assert!(written.contains("((_ is |a constructor|) x)"));
}
