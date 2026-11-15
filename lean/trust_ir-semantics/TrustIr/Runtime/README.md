# Runtime implementation boundary

The canonical implementation library is `TrustIrRuntime`; the safe semantic Eval
root activates its native-only `TrustIrNativeLink` dependency. Executable roots
explicitly import `TrustIrRuntime`. Unsafe runtime declarations never enter the
mathematical import closure. The earlier `TrustIr.Runtime.Caches` implementation
and its measurements remain preserved in Git history and the runtime-isolation
report packet; its duplicate provider source has been retired.

`runtime-boundary.json` schema2 retains the historical41 runtime obligations,
15 interface correspondence obligations and3 additional initialization/linking/
evaluation support obligations as UNPROVED. Tests do not certify them.

The pure formal aggregate is `TrustIr.Formal`. Native evaluation fixtures remain
in `TrustIr`; `lake lean` supplies the initialized native-only attachment without
importing unsafe provider declarations into that logical environment. An explicit
`-KnativeLinker=/absolute/path/to/linker` selects the native linker; the proof gate
accepts the same executable through `TRUST_IR_NATIVE_LINKER` and forces Lake
configuration reload. This host qualifies LLVM 23.1.5 ld64.lld with pinned Lean 4.8.
