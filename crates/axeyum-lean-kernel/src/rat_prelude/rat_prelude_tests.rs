//! Tests for the rational prelude.

use super::{RatPrelude, build_rat_prelude};
use crate::{Declaration, Kernel};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

#[test]
fn rat_prelude_is_axiom_free() {
    let (kernel, _) = built();
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
    assert!(
        trusted.is_empty(),
        "the rational prelude must assume nothing, found: {trusted:?}"
    );
}

#[test]
fn every_named_declaration_exists() {
    let (kernel, p) = built();
    let expected = [
        ("zero", p.zero),
        ("one", p.one),
        ("le", p.le),
        ("lt", p.lt),
        ("inv", p.inv),
        ("sub", p.sub),
        ("div", p.div),
        ("mk_congr", p.mk_congr),
        ("eta", p.eta),
        ("ext", p.ext),
    ];
    for (label, name) in expected {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} was interned but never declared"
        );
    }
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// printed as opaque `ExprId`s. A `Debug` of `KernelError` says nothing about
/// what was refused; this says which two types failed to match.
#[test]
fn rat_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_rat_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a rational proof: {explained}");
        }
    }
}
