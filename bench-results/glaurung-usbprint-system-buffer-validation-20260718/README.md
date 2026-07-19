# Glaurung usbprint SystemBuffer validation — 2026-07-18

This artifact independently classifies the five producer-high-confidence
`usbprint.sys` rows selected by ADR-0241 and explains the one Z3-only row. The
result is negative but important: all five rows came from an invalid Glaurung
WDM environment model. They are not validated driver findings and cannot be a
concretization-policy recall denominator.

## Result

The old seed treated `Irp->AssociatedIrp.SystemBuffer` as a free
attacker-selected 64-bit address. That is wrong for the observed
`METHOD_BUFFERED` IOCTL. Windows owns the kernel pointer; the caller controls
bytes copied into the I/O-manager allocation. After separating pointer
ownership from content taint in Glaurung `b79f269`, the unchanged Axeyum v5
authority harness accepts exact high-confidence parity at zero versus zero:

| Backend | Repetitions | Reachable/analyzed | Raw | High confidence | Diagnostic | Solves |
|---|---:|---:|---:|---:|---:|---:|
| Z3 | 2 | 21/18 complete | 214, 214 | 0, 0 | 214, 214 | 16,537 each |
| Axeyum | 2 | 21/18 complete | 214, 214 | 0, 0 | 214, 214 | 16,537 each |

The remaining raw difference is one generic-argument CRT `memcpy` diagnostic
per authority: Z3 reaches the aligned store at `0x140009793` with `Arg0`
ancestry, while Axeyum reaches the small-copy tail store at `0x14000969a` with
`Arg0`/`Arg2` ancestry. Both are producer diagnostics, not accepted driver
findings. Raw parity therefore remains false and visible; accepted parity is
true.

[`result.json`](result.json) is the compact machine-readable manifest for the
two order-balanced repetitions. The full v5 report was generated from clean
source identities and had SHA-256
`f9301cb39f4d4b67bfa4c871f6ed1d337c61206971a4501b4b903a0a118cdf9a`.

## Binary and IOCTL proof

The input is the complete x64 Windows 11 `usbprint.sys` image with SHA-256
`3eb6b8172849290bac6ff548b53fbf78c37c6f68a22bdc604b12418d1b22a968`.
The PE CodeView GUID is `{2CC0E16A-FABE-5F53-B727-4B87A0866448}`. The public
PDB has the same GUID and SHA-256
`fd28f90823256a7417de23d8f4bf5bc5c8cd5330fd4d0b8485182f26042325ff`,
but its stream age is 3 while the PE record requests age 1. Symbols are
therefore corroborating evidence rather than the sole identity proof; the raw
switch table and machine instructions establish the control flow directly.

The dispatch table maps IOCTL `0x0022003c` to the call at `0x1400052cf` into
`HPUsbIOCTLVendorGetCommand` at `0x1400026e0`. Its low method bits are zero
(`METHOD_BUFFERED`) and its access bits are zero (`FILE_ANY_ACCESS`). The
relevant instructions are:

```text
1400026fc  mov    rax, [rdx+0xb8]  ; CurrentStackLocation
140002705  mov    r15, [rdx+0x18]  ; AssociatedIrp.SystemBuffer
14000270f  mov    edi, [rax+0x8]   ; OutputBufferLength
140002712  test   r15, r15
140002715  je     0x14000297a
14000271b  cmp    edi, 3
14000271e  jb     0x14000297a
...
140002762  movzx  eax, byte ptr [r15+2]
140002770  movzx  r8d, byte ptr [r15+1]
140002775  movzx  edx, byte ptr [r15]
```

Thus every reported byte read is behind `SystemBuffer != NULL` and
`OutputBufferLength >= 3`. Microsoft documents that `METHOD_BUFFERED` uses an
I/O-manager-owned `SystemBuffer` and allocates the larger of the input and
output lengths:

- <https://learn.microsoft.com/en-us/windows-hardware/drivers/kernel/buffer-descriptions-for-i-o-control-codes>
- <https://learn.microsoft.com/en-us/windows-hardware/drivers/ddi/wdm/ns-wdm-_io_stack_location>
- <https://learn.microsoft.com/en-us/windows-hardware/drivers/kernel/failure-to-check-the-size-of-buffers>

This proves the five reads/null checks are neither attacker-selected-address
primitives nor length violations on the observed path.

## Why only Z3 emitted the second null row

Ordered traces were captured before the producer correction at clean Glaurung
`9692f3c`, using the same input and work limits. The Z3 trace contains 72,458
events, 3,079 paths, 7,009 distinct query artifacts, 2,175 assertions, and
16,553 warm checks. The Axeyum trace contains 73,972 events, 3,079 paths, 6,993
query artifacts, 2,177 assertions, and 16,553 warm checks.

At the first relevant address-concretization query
`386bb1083ffa1016be8b20bc34fd4a84af0adb33fb1bb183579921ef35455238`
for `SystemBuffer + 2`, Z3 returned effective address `0x1`; Axeyum returned
`0x3`. Under the invalid free-pointer model, Z3's representative binds the base
to `2^64 - 1`, making the next `SystemBuffer + 1` address wrap to zero. Axeyum's
equally valid AnyModel representative does not. The Z3-only row therefore
measures model steering inside a false environment, not superior bug recall.

The trace event streams were not committed because they total about 391 MiB.
Their content hashes are retained in `result.json`, along with the exact event
and query-index hashes needed to identify the evidence used here.

## Producer correction and regression gates

Glaurung `b79f269` stores a fixed synthetic kernel address in
`AssociatedIrp.SystemBuffer` and marks the corresponding concrete memory region
as attacker-controlled *contents*. Loads still acquire `*SystemBuffer`
provenance for dangerous handles, physical addresses, format strings, and
indirect-call targets; the address itself no longer creates controlled-access
or null-dereference sinks. Genuine pointer-control tests now use
`METHOD_NEITHER` `Type3InputBuffer` or `UserBuffer` sources.

The reduced regression emitted the same three controlled reads and two null
dereferences before the fix. After the fix, the guarded SystemBuffer regression
emits none, and all 22 focused IOCTL tests pass independently under both
backends:

```sh
cargo test --lib --features solver-z3 symbolic::ioctl::tests -- --nocapture
cargo test --lib --no-default-features --features solver-axeyum symbolic::ioctl::tests -- --nocapture
```

Both authority configurations also compile with their respective
`ioctlance` example. Glaurung's broader repository has inherited warnings and
repository-wide rustfmt debt; this increment introduces no whitespace errors
(`git diff --check` passes) and does not sweep unrelated files.

## Consequences and remaining boundary

Usbprint is retired as the nonzero policy-sweep candidate. A0 remains a small,
already-accepted policy knob, but there is no honest recall sweep until another
population has independently validated nonzero findings. Boundary/diverse
selection remains configuration work, not a new research program, and
symbolic memory remains conditional on residual validated coverage headroom.

This correction does not implement length-aware SystemBuffer bounds. The
producer conservatively content-taints the maximum 32-bit request span; a
future bounds primitive must compare accesses against the applicable request
length. The KMDF retrieve-buffer summary still uses the older symbolic-pointer
abstraction and must receive the same address/content separation before its
`SystemBuffer` rows are accepted.
