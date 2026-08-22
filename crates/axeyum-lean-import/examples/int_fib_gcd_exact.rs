//! Construct exact `Int.fib_gcd` from the sealed `Int.gcd_fib` closure.

#[allow(dead_code)]
#[path = "int_gcd_fib_exact.rs"]
mod int_gcd_fib_exact;

fn main() {
    if let Err(error) = int_gcd_fib_exact::run_int_fib_gcd_exact() {
        eprintln!("int-fib-gcd-exact: {error}");
        std::process::exit(1);
    }
}
