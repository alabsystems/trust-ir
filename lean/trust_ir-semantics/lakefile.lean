-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Lake build configuration for trust_ir-semantics Lean 4 formalization.
-- Depends ONLY on Lean core — no Mathlib (nothing under TrustIr/ imports it),
-- so `lake build` needs no `lake exe cache get` and no network.
--
-- Build: lake build
-- Check: lake env lean TrustIr.lean

import Lake
open Lake DSL

-- NOTE: Lean lake syntax uses backtick-quoted names.
-- These are Lean Name literals, not shell command injection.

def trustIrBuildDir : System.FilePath :=
  if Lean.versionString == "4.8.0" then ".lake/build"
  else s!".lake/build-{Lean.versionString}-{Lean.githash}"

package trust_irSemantics where
  -- The canonical oracle keeps its pinned 4.8 output path. SemR's 4.30
  -- proof package imports these same sources as a local dependency: its
  -- OLeans, generated C and lib/lean layout must never overwrite that cache.
  buildDir := trustIrBuildDir
  -- Use the host Apple linker for current SDK TAPI; applies to executables and runtime dynlibs.
  moreLinkArgs := match get_config? nativeLinker with
    | some linker => #["--ld-path=" ++ linker]
    | none => if System.Platform.isOSX then #["--ld-path=/usr/bin/ld", "-Wl,-no_data_const"] else #[]
  moreLeancArgs := if Lean.versionString == "4.30.0-rc2" then
    #["-include", (__dir__ / "native" / "runtime_ffi.h").toString] else #[]
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- The two pinned native Lake APIs differ at file jobs and facet descriptors.
-- Expand only the API of the compiler elaborating this configuration; both
-- versions retain the same source inputs, initializer, and provider facets.
macro "trustIrRuntimeInput " path:term : term => do
  if Lean.versionString == "4.8.0" then
    `(inputFile $path)
  else if Lean.versionString == "4.30.0-rc2" then
    `(inputBinFile $path)
  else
    Lean.Macro.throwError "unsupported native Lake version for TrustIR runtime facets"

macro "trustIrNativeFacet " facet:ident : term => do
  let name := Lake.Name.quoteFrom facet facet.getId
  if Lean.versionString == "4.8.0" then
    return name
  else if Lean.versionString == "4.30.0-rc2" then
    `(({ name := Lake.Module.facetKind ++ $name, data_eq := Lake.FamilyOut.fam_eq } : Lake.ModuleFacet System.FilePath))
  else
    Lean.Macro.throwError "unsupported native Lake version for TrustIR runtime facets"

-- Lake deliberately reduces its C facet trace to generated C contents. Mix the
-- consumed ABI header after that boundary, directly into each C object job.
macro "trustIrFfiOJob " mod:term:max shouldExport:term:max : term => do
  if Lean.versionString == "4.8.0" then
    `(if $shouldExport then ($mod).oExport.fetch else ($mod).o.fetch)
  else if Lean.versionString == "4.30.0-rc2" then
    `(do
      match ($mod).backend with
      | .llvm => ($mod).bco.fetch
      | .default | .c =>
        let source ← ($mod).c.fetch
        let header ← inputBinFile (($mod).pkg.dir / "native" / "runtime_ffi.h")
        let source := source.zipWith (fun path _ => path) header
        let file := ($mod).irPath (if $shouldExport then "ffi.o.export" else "ffi.o.noexport")
        let args := ($mod).leancArgs ++ (if $shouldExport then #["-DLEAN_EXPORTING"] else #[])
        buildLeanO file source ($mod).weakLeancArgs args ($mod).leanIncludeDir?)
  else Lean.Macro.throwError "unsupported native Lake version for TrustIR header-aware objects"

module_facet trustirFfiOExport (mod) : System.FilePath :=
  trustIrFfiOJob mod true

module_facet trustirFfiONoExport (mod) : System.FilePath :=
  trustIrFfiOJob mod false

macro "trustIrNativeObjects" : term => do
  if Lean.versionString == "4.8.0" then
    `(fun shouldExport => #[if shouldExport then Module.oExportFacet else Module.oFacet])
  else if Lean.versionString == "4.30.0-rc2" then
    let exported := Lean.mkIdent `trustirFfiOExport
    let internal := Lean.mkIdent `trustirFfiONoExport
    `(fun shouldExport =>
      if shouldExport || !System.Platform.isWindows then #[trustIrNativeFacet $exported:ident]
      else #[trustIrNativeFacet $internal:ident])
  else Lean.Macro.throwError "unsupported native Lake version for TrustIR native object selection"

-- A native-only dependency initializes the optimized provider without importing
-- its unsafe declarations into proof environments. The logical attachment is
-- deliberately declaration-free; its native facet supplies only the initializer.
macro "trustIrRuntimeInitFlags " mod:term : term => do
  if Lean.versionString == "4.8.0" then
    `(pure #["-DLEAN_EXPORTING", "-fPIC"])
  else if Lean.versionString == "4.30.0-rc2" then
    `(do
      let some provider ← findModule? `TrustIrRuntime | error "TrustIr runtime provider is absent"
      pure #["-DLEAN_EXPORTING", "-fPIC", "-DTRUST_IR_LEAN430",
        "-DTRUST_IR_ATTACHMENT_INITIALIZER=initialize_" ++ ($mod).dynlibName,
        "-DTRUST_IR_PROVIDER_INITIALIZER=initialize_" ++ provider.dynlibName])
  else Lean.Macro.throwError "unsupported native Lake version for TrustIR initializer ABI"

module_facet trustirRuntimeInit (mod) : System.FilePath := do
  let source ← trustIrRuntimeInput (mod.pkg.dir / "native" / "runtime_init.c")
  let flags ← trustIrRuntimeInitFlags mod
  buildLeanO (mod.pkg.buildDir / "native" / "runtime_init.o") source #[] flags

-- Modern Lake resolves native imports by library ownership. Co-locate exactly
-- the provider's logical foundations with its implementations in one DLL:
-- no whole-formal-library cycle, no duplicate native foundation globals.
-- Logical proof environments still import only the pure foundation modules.
macro "trustIrRuntimeProviderJob" : term => do
  if Lean.versionString == "4.8.0" then
    `(do
      let some provider ← findModule? `TrustIrRuntime | error "TrustIr runtime provider is absent"
      return (← provider.dynlib.fetch).map (·.path))
  else if Lean.versionString == "4.30.0-rc2" then
    `(do
      let some provider ← findModule? `TrustIrRuntime | error "TrustIr runtime provider is absent"
      return (← provider.lib.shared.fetch).map (·.path))
  else Lean.Macro.throwError "unsupported native Lake version for TrustIR runtime provider"

module_facet trustirRuntimeProvider (_mod) : System.FilePath :=
  trustIrRuntimeProviderJob

-- Executable roots explicitly import TrustIrRuntime, so Lake links its ordinary
-- module objects once. Interpreted code loads the complete provider DLL instead.
lean_lib TrustIrNativeLink where
  srcDir := "."
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then #[trustIrNativeFacet trustirRuntimeInit, trustIrNativeFacet trustirRuntimeProvider]
    else #[trustIrNativeFacet trustirRuntimeInit]

@[default_target]
lean_lib TrustIr where
  nativeFacets := trustIrNativeObjects
  srcDir := "."

-- The W5b Lean-execution oracle (roadmap WS2.19): a serde-JSON decoder and a
-- batch runner over `evalFunctionInContext`, linked into `trustir_eval`. NOT
-- a default target — it imports `Lean.Data.Json` (still Lean core, no
-- Mathlib, no network), which the axiom-audited `TrustIr` library never does,
-- and nothing under `TrustIr/` imports it. Build with `lake build trustir_eval`;
-- the Rust harness `crates/trust-ir-conformance/tests/lean_exec_differential.rs`
-- does so itself.
-- Lake 4.30 assigns imported modules to their owning library when collecting
-- shared objects; Lake 4.8 collects by root prefix instead. Keep the original
-- canonical module-dynlib path while giving modern Lake disjoint ownership.
def trustIrProviderFoundations : Array Lean.Name :=
  #[`TrustIr.Basic,
    `TrustIr.CompilerCompat,
    `TrustIr.Constant,
    `TrustIr.Semantics.Monad,
    `TrustIr.State.ArrayEncodingStats,
    `TrustIr.State.ByteImage,
    `TrustIr.State.ByteImageTraversal,
    `TrustIr.State.CompactArray,
    `TrustIr.State.MachineState,
    `TrustIr.State.Memory,
    `TrustIr.State.Permission,
    `TrustIr.State.ValueMap,
    `TrustIr.StringCompat]

def trustIrProviderRoots : Array Lean.Name :=
  if Lean.versionString == "4.8.0" then #[`TrustIrRuntime]
  else #[`TrustIrRuntime] ++ trustIrProviderFoundations

-- Pointer-memoized implementations are a separate, explicitly unproved runtime library.
lean_lib TrustIrRuntime where
  roots := trustIrProviderRoots
  nativeFacets := trustIrNativeObjects
  srcDir := "."
  -- The native attachment loads the complete provider. Preloading its imported
  -- model DLLs separately resolves their externs before the provider exists.
  precompileModules := false

lean_lib TrustIrEval where
  nativeFacets := trustIrNativeObjects
  srcDir := "."

-- Each independent executable owns its module and traced native objects.
lean_lib TrustIrLookupTools where
  roots := #[`Tools.FunctionLookupBenchmark]
  nativeFacets := trustIrNativeObjects

lean_lib TrustIrDecodedCFGTools where
  roots := #[`Tools.DecodedCFGBenchmark]
  nativeFacets := trustIrNativeObjects

lean_lib TrustIrCFGMappingTools where
  roots := #[`Tools.DecodedCFGMappingProbe]
  nativeFacets := trustIrNativeObjects

lean_exe trustir_eval where
  root := `TrustIrEval.Main
  -- Lean 4.8.0's bundled linker emits a `__DATA_CONST` segment without the
  -- `SG_READ_ONLY` flag that macOS 15+ dyld requires ("__DATA_CONST segment
  -- missing SG_READ_ONLY flag", abort at load). Not creating the segment
  -- sidesteps the check; Apple-linker-only, so it is not passed elsewhere.

-- Canonical internally transported ordinary function convention controls.
lean_exe trustir_indirect_convention where
  root := `TrustIrEval.IndirectConventionTests

lean_exe trustir_observation_sharing where
  root := `TrustIrEval.ObservationSharingTests

-- Optional measurement observer; no default target or semantic option changes.
lean_exe trustir_lookup_bench where
  root := `Tools.FunctionLookupBenchmark

-- Optional decoded-CFG phase observer; outside the default proof target.
lean_exe trustir_cfg_bench where
  root := `Tools.DecodedCFGBenchmark

lean_exe trustir_byte_images where
  root := `TrustIrEval.ByteImageTests

lean_exe trustir_typed_images where
  root := `TrustIrEval.TypedImageTests

lean_exe trustir_shared_consumers where
  root := `TrustIrEval.SharedConsumerTests

-- Correctness-only overlay; not part of the phase observer or default proof target.
lean_exe trustir_cfg_mapping_probe where
  root := `Tools.DecodedCFGMappingProbe

lean_exe trustir_periodic_values where
  root := `TrustIrEval.PeriodicValueTests

-- All fifteen foreign interfaces, through a separately compiled logical caller module.
lean_exe trustir_runtime_boundary where
  root := `TrustIrEval.RuntimeBoundaryTests

-- Decoder-boundary fixtures also run while the standing oracle root builds.
lean_exe trustir_wire_record_keys where
  root := `TrustIrEval.RecordKeysMain

-- Native form of the existing source-layout differential oracle.
lean_exe trustir_source_layout where
  root := `TrustIrEval.SourceLayoutOracle

-- Native/interpreted observations of actual enum memory-plan caches.
lean_exe trustir_enum_plans where
  root := `TrustIrEval.EnumPlanTests

-- Actual decoded-context enum checker/encoder/decoder observations.
lean_exe trustir_enum_codec where
  root := `TrustIrEval.EnumCodecTests

/-- Check the module owner actually selected by the pinned Lake resolver. -/
script trustir_native_ownership do
  let workspace ← getWorkspace
  let expected := if Lean.versionString == "4.8.0" then `TrustIr else `TrustIrRuntime
  for name in trustIrProviderFoundations do
    let some mod := workspace.findModule? name | throw (IO.userError s!"missing foundation {name}")
    unless mod.lib.name == expected do
      throw (IO.userError s!"foundation {name} belongs to {mod.lib.name}, expected {expected}")
    IO.println s!"{name}: {mod.lib.name}"
  let some formal := workspace.findModule? `TrustIr | throw (IO.userError "missing formal root")
  unless formal.lib.name == `TrustIr do throw (IO.userError "formal root moved into provider")
  IO.println s!"NATIVE_FOUNDATION_OWNERSHIP_PASS compiler={Lean.versionString} foundations={trustIrProviderFoundations.size} formal={formal.lib.name}"
  return 0

-- Independent raw-ingress runtime controls; no model/proof authority.
lean_exe raw_boundary_controls where
  root := `TrustIrEval.RawBoundaryControls
