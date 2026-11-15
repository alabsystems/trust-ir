-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.CompilerCompat
/-- Only the supported canonical pin elaborates actual Lean.HashMap internals.
    The modern pin proves actual Std.HashMap laws separately. No dummy proof
    declaration or assumed law is introduced on either compiler. -/
macro "trustIrLegacyMapCacheDecl " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure declaration
  else if Lean.versionString == "4.30.0-rc2" then `(command| run_cmd pure ())
  else Lean.Macro.throwError "unsupported compiler for actual cache laws"
macro "trustIrMapCacheEmptyWithCapacity " capacity:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Lean.mkHashMap $capacity)
  else if Lean.versionString == "4.30.0-rc2" then `(Std.HashMap.emptyWithCapacity $capacity)
  else Lean.Macro.throwError "unsupported compiler for actual empty cache"
