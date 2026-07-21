// Frozen total-scalar source fixture for ADR-0317.

#[axeyum_verify::verify]
#[axeyum_verify::requires(true)]
#[axeyum_verify::ensures(|result| result == x.wrapping_add(1))]
#[allow(dead_code)]
/// Adds one with `u8` wrapping semantics.
pub fn wrapping_inc(x: u8) -> u8 {
    x.wrapping_add(1)
}

/// Calls the annotated function through a real MIR call site.
pub fn call_wrapping_inc(x: u8) -> u8 {
    wrapping_inc(x)
}

/// Provides the independently reflected inlined control.
pub fn inlined_wrapping_inc(x: u8) -> u8 {
    x.wrapping_add(1)
}
