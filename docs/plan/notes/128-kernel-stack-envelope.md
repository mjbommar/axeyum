# Notes: 128-kernel-stack-envelope

Detail moved out of [`../status/128-kernel-stack-envelope.md`](../status/128-kernel-stack-envelope.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Method note worth more than the numbers.** The first measurement instrumented
`infer_core`, `whnf_core`, `def_eq_core_uncached` and `instantiate_aux` with a
stack-pointer probe and reported a `cpoint` peak of 1,681,616 B — **12× too
small**, and I nearly set the shared constant from it. A probe sees only the
frames it is installed in, and the deepest recursion of a run need not pass
through any of them (`Kernel::abstract_aux` recurses over the term and was not
instrumented). The subprocess bisection measures the process instead of a
chosen subset of it.

**Next.** (a) `creal/creal_tests.rs` still carries a private 1 GiB helper and a
doc comment blaming `axiom_footprint`, which is an explicit worklist and cannot
recurse — another lane owns that file. (b) `creal/integral.rs`'s
concrete-instantiation tests are the workload that set the 256 MiB constant and
the only one still unmeasured; they need their own probe mode. (c) The deferred
headroom probe, if a caller ever needs to survive exhaustion rather than gate
against it.
