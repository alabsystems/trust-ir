-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIrEval.RawBoundary

namespace TrustIrEval.RawBoundaryControls
open Lean (Json)

private def require (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"raw-boundary control failed: {label}")
  count.modify (· + 1)
  IO.println s!"raw-boundary control PASS {label}"

private def decoded (text : String) : Json :=
  match Json.parse text with | .ok value => value | .error _ => .null

private def errorText (value : Json) : String :=
  match value.getObjValAs? String "error" with | .ok value => value | .error _ => ""

private def isRawError (value : Json) : Bool := (errorText value).startsWith "raw serde:"
private def answer (text : String) : Json := RawBoundary.runText text
private def agrees : Json := decoded "[{\"agree\":true}]"
private def row (ty : String) : String :=
  "{\"ty\":" ++ ty ++ ",\"params\":[],\"holes\":[],\"expected\":{\"Storage\":{\"size_bytes\":8,\"align_bytes\":8}}}"
private def good : String := "{\"Storage\":{\"size_bytes\":8,\"align_bytes\":8}}"
private def bad : String := "{\"Storage\":{\"size_bytes\":8e0,\"align_bytes\":8}}"
private def module (types : String := "[]") : String :=
  "{\"functions\":[],\"func_types\":[],\"globals\":[],\"enums\":[],\"structs\":[],\"types\":" ++ types ++ "}"
private def ordinary (wire : String) (fuel : String := "10") (runs : String := "[]") : String :=
  "{\"fuel\":" ++ fuel ++ ",\"call_depth\":10,\"batches\":[{\"module\":" ++ wire ++ ",\"runs\":" ++ runs ++ "}]}"

private def preserves (text : String) : Bool :=
  match Json.parse text with
  | .ok document => answer text == runRequest document
  | .error _ => false

/-- Runtime parser/ingress controls, never native proof evaluation or source authority. -/
def run : IO Unit := do
  let count ← IO.mkRef 0
  let require := require count
  let native := (decoded "{\"key\":0,\"key\":1}").getObjVal? "key"
  let nativeFirst := native.toOption == some (.num 0)
  require "native duplicate probe has an actual winner"
    (native.toOption == some (.num 0) || native.toOption == some (.num 1))
  require "actual native occurrence profile" (nativeFirst == RawJson.firstWins)
  let equalProjection := "{\"key\":8,\"key\":8e0}"
  let document ← match RawJson.parse equalProjection with
    | .ok document => pure document
    | .error _ => throw (IO.userError "lossless parse failed")
  let selected := match document.raw.field? "key" with
    | some (.scalar _ _ token) => token
    | _ => none
  require "same Json value retains selected raw spelling"
    (selected == some (if nativeFirst then "8" else "8e0"))
  let selectedReverse := match RawJson.parse "{\"key\":8e0,\"key\":8}" with
    | .ok document => match document.raw.field? "key" with
      | some (.scalar _ _ token) => token
      | _ => none
    | .error _ => none
  require "reverse occurrence retains selected raw spelling"
    (selectedReverse == some (if nativeFirst then "8e0" else "8"))
  require "UTF8 and escaped key projection"
    ((RawJson.parse "{\"é\":\"字\",\"size_\\u0062ytes\":8}").isOk)
  let selectedGoodFirst := "{\"template_subst\":[" ++ row good ++ "],\"template_subst\":[" ++ row bad ++ "]}"
  let selectedBadFirst := "{\"template_subst\":[" ++ row bad ++ "],\"template_subst\":[" ++ row good ++ "]}"
  let first := answer selectedGoodFirst
  let second := answer selectedBadFirst
  require "equal-projection selector source order1"
    (if nativeFirst then first == agrees else first.getArr?.toOption.any (fun rows => rows.size == 1 && isRawError rows[0]!))
  require "equal-projection selector source order2"
    (if nativeFirst then second.getArr?.toOption.any (fun rows => rows.size == 1 && isRawError rows[0]!) else second == agrees)
  let mixed := answer ("{\"template_subst\":[" ++ row good ++ "," ++ row bad ++ "," ++ row good ++ "]}")
  require "mixed substitution retains three verdict rows" (match mixed.getArr? with
    | .ok rows => rows.size == 3 && rows[0]! == decoded "{\"agree\":true}" && isRawError rows[1]! && rows[2]! == rows[0]!
    | _ => false)
  let mixedEnums := answer ("{\"enum_id_admission\":[" ++ module "[]" ++ "," ++ module ("[" ++ bad ++ "]") ++ "," ++ module "[]" ++ "]}")
  require "mixed enum documents retain three verdict rows" (match mixedEnums.getArr? with
    | .ok rows => rows.size == 3 && rows[0]! == decoded "{\"enum_ids_admitted\":true}" && isRawError rows[1]! && rows[2]! == rows[0]!
    | _ => false)
  require "template array wins over invalid enum selector"
    (answer "{\"template_subst\":[],\"enum_id_admission\":7}" == .arr #[])
  require "template nonarray falls through to enum"
    (answer ("{\"template_subst\":0,\"enum_id_admission\":[" ++ module "[]" ++ "]}") == decoded "[{\"enum_ids_admitted\":true}]")
  require "enum nonarray keeps old error"
    (answer "{\"template_subst\":null,\"enum_id_admission\":7}" == decoded "{\"error\":\"enum_id_admission: expected array\"}")
  let badModule := module ("[" ++ bad ++ "]")
  let fuelFailure := errorText (answer (ordinary badModule "false"))
  require "header fuel failure precedes raw module" (fuelFailure.startsWith "fuel:")
  let runFailure := errorText (answer (ordinary badModule "10" "[{}]"))
  require "run prefix failure precedes raw module" (runFailure.startsWith "function:")
  require "pool raw failure is a module error" (isRawError (answer (ordinary badModule)))
  require "ordinary template nonarray fallback"
    (preserves ("{\"template_subst\":0,\"fuel\":10,\"call_depth\":10,\"batches\":[{\"module\":" ++ module "[]" ++ ",\"runs\":[]}]}"))
  require "valid old unsupported type pool is retained"
    (preserves (ordinary (module "[{\"NotYet\":0}]")))
  let dropModule := "{\"functions\":[],\"func_types\":[],\"globals\":[],\"enums\":[],\"structs\":[],\"types\":[],\"drop_glue\":[{\"glue\":0,\"ty\":{\"NotYet\":0}}]}"
  require "valid old drop-glue missing type is retained" (preserves (ordinary dropModule))
  let recordModule := "{\"functions\":[],\"func_types\":[],\"globals\":[],\"enums\":[],\"structs\":[],\"types\":[],\"records\":[{\"id\":0,\"name\":\"r\",\"fields\":[{\"name\":\"f\",\"ty\":{\"NotYet\":0}}]}]}"
  require "old unsupported record remains absent" (preserves (ordinary recordModule))
  let bodyModule := "{\"functions\":[{\"id\":0,\"name\":\"f\",\"ty\":0,\"entry\":0,\"calling_conv\":\"C\",\"blocks\":[{\"id\":0,\"params\":[],\"body\":[{\"inst\":{\"NotYet\":{}},\"results\":[]}]}]}],\"func_types\":[{\"params\":[],\"returns\":[],\"is_vararg\":false}],\"globals\":[],\"enums\":[],\"structs\":[],\"types\":[]}"
  require "old body decode error stays lazy" (preserves (ordinary bodyModule))
  let unknown := "{\"Storage\":{\"size_bytes\":8,\"align_bytes\":8,\"unused\":{\"FnItem\":11e0},\"unused\":{\"Storage\":[-0,1]}}}"
  require "unknown duplicate pseudo-types remain ignored"
    (answer ("{\"template_subst\":[" ++ row unknown ++ "]}") == agrees)
  for text in ["", "{", "[1,]", "trueX"] do
    require "syntax error preserves native diagnostic" (match Json.parse text with
      | .error error => answer text == Json.mkObj [("error", .str s!"request is not JSON: {error}")]
      | .ok _ => false)
  IO.println s!"RAW_BOUNDARY_CONTROLS_PASS count={← count.get} native_first={nativeFirst}"
end TrustIrEval.RawBoundaryControls

def main : IO Unit := TrustIrEval.RawBoundaryControls.run
