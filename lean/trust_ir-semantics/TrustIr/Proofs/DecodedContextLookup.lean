-- Copyright 2026 Andrew Yates | Apache-2.0
-- Proof-only specification of the original decoded-context list lookups.
-- This does not install a compatibility executor or another runtime builder.
import TrustIr.DecodedContext
import TrustIr.Proofs.DecodedFunctionLookupProps
import TrustIr.Proofs.DecodedCFGProps

namespace TrustIrEval.FunctionLookup
open TrustIr

private def memoryRootsSpec (m : Module) : Inst → List Ty
  | .Alloca ty .. | .HeapAlloc ty .. | .GEP ty .. | .Load ty .. | .Store ty ..
  | .AtomicLoad ty .. | .AtomicStore ty .. | .AtomicRMW _ ty .. | .CmpXchg ty .. => [ty]
  | .SeqMap (.Sequence element) _ _ => ((trustIrListGet? m.types element.index).join).toList
  | _ => []

private noncomputable def memoryServiceSpec (m : Module) (model : ByteModel) :
    AggregateMemory.Service :=
  let source : SourceLayout.Environment :=
    { model, canonicalScalars := true, hasTargetInfo := m.hasTargetInfo,
      types := m.types, structs := m.structs, enums := m.enums,
      records := m.records.filterMap (·.2), closures := m.closureTys,
      tupleLayouts := m.tupleLayouts, closureLayouts := m.closureLayouts,
      functions := m.functions.map (fun function => (function.id, function.ty)),
      funcTypes := m.funcTys }
  let roots := [.I64] ++ m.globals.map (·.ty) ++ trustIrListBind m.functions (fun function =>
    match function.blocks with
    | .error _ => []
    | .ok blocks => trustIrListBind blocks (fun (_, block) =>
      trustIrListBind (block.body ++ [block.terminator]) (memoryRootsSpec m)))
  AggregateMemory.prepare source (roots.filter (fun ty => !ty.hasCanonicalMemoryLayout))

/-- The original complete context assembly, expressed only as a logical spec.
    It retains all raw duplicate/declaration/error and early-guard cases. -/
-- Restore only the original matcher declarations and their actual specification uses.
-- The recorded closed expressions retain full dependent domains and constructor dispatch.
macro "trustIrContextLookupOriginalMatchers " original:command : command => do
  if Lean.versionString == "4.8.0" then pure original
  else if Lean.versionString == "4.30.0-rc2" then
    let helpers ← `(command| run_cmd do
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_1
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 1 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 748)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 748)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 766)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.forallE
                  `function
                  (Lean.Expr.const `TrustIr.EvalFunction [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Option.some [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.FuncId []))
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction [])))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.bvar 0)))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 772)
                  (Lean.Expr.app
                    (Lean.Expr.const `Option [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                  (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 748)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 748)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 766)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.forallE
                  `function
                  (Lean.Expr.const `TrustIr.EvalFunction [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Option.some [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.FuncId []))
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction [])))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.bvar 0)))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 772)
                  (Lean.Expr.app
                    (Lean.Expr.const `Option [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                  (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                        (Lean.Expr.lam
                          `x
                          (Lean.Expr.app
                            (Lean.Expr.const `Option [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction []))))
                          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.app
                      (Lean.Expr.bvar 0)
                      (Lean.Expr.app
                        (Lean.Expr.const `Option.none [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.FuncId []))
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))))))
                  (Lean.Expr.lam
                    (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 775)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.FuncId []))
                      (Lean.Expr.app
                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction [])))
                          (Lean.Expr.lam
                            `x
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                            (Lean.Expr.app
                              (Lean.Expr.bvar 5)
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.FuncId []))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                                (Lean.Expr.bvar 0)))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 0))
                      (Lean.Expr.lam
                        (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 776)
                        (Lean.Expr.const `TrustIr.FuncId [])
                        (Lean.Expr.lam
                          (Lean.Name.num `snd.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 777)
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `Except.casesOn
                                        [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `TrustIrEval.DecodeError []))
                                    (Lean.Expr.const `TrustIr.EvalFunction []))
                                  (Lean.Expr.lam
                                    `x
                                    (Lean.Expr.app
                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                      (Lean.Expr.const `TrustIr.EvalFunction []))
                                    (Lean.Expr.app
                                      (Lean.Expr.bvar 7)
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `TrustIr.FuncId []))
                                            (Lean.Expr.app
                                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.FuncId []))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                                            (Lean.Expr.bvar 2))
                                          (Lean.Expr.bvar 0))))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.bvar 0))
                              (Lean.Expr.lam
                                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 778)
                                (Lean.Expr.const `TrustIrEval.DecodeError [])
                                (Lean.Expr.app
                                  (Lean.Expr.bvar 4)
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Option.some [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.FuncId []))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.FuncId []))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.EvalFunction [])))
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                                          (Lean.Expr.const `TrustIr.EvalFunction []))
                                        (Lean.Expr.bvar 0)))))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.lam
                              (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 779)
                              (Lean.Expr.const `TrustIr.EvalFunction [])
                              (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 0))
                              (Lean.BinderInfo.default)))
                          (Lean.BinderInfo.default))
                        (Lean.BinderInfo.default)))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_2
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 2 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 971)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 971)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 994)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.forallE
                  `message
                  (Lean.Expr.const `String [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Option.some [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.FuncId []))
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction [])))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1018)
                  (Lean.Expr.const `TrustIr.FuncId [])
                  (Lean.Expr.forallE
                    `feature
                    (Lean.Expr.const `String [])
                    (Lean.Expr.app
                      (Lean.Expr.bvar 4)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                            (Lean.Expr.bvar 1))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                              (Lean.Expr.const `TrustIr.EvalFunction []))
                            (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.Expr.forallE
                  `h_3
                  (Lean.Expr.forallE
                    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1028)
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                    (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 3))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 971)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 971)
            (Lean.Expr.app
              (Lean.Expr.const `Option [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncId []))
                (Lean.Expr.app (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero]) (Lean.Expr.const `TrustIr.EvalFunction []))))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 994)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.forallE
                  `message
                  (Lean.Expr.const `String [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Option.some [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.FuncId []))
                          (Lean.Expr.app
                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.EvalFunction []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction [])))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.const `TrustIr.EvalFunction []))
                          (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1018)
                  (Lean.Expr.const `TrustIr.FuncId [])
                  (Lean.Expr.forallE
                    `feature
                    (Lean.Expr.const `String [])
                    (Lean.Expr.app
                      (Lean.Expr.bvar 4)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.some [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                            (Lean.Expr.bvar 1))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                              (Lean.Expr.const `TrustIr.EvalFunction []))
                            (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.Expr.lam
                  `h_3
                  (Lean.Expr.forallE
                    (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1028)
                    (Lean.Expr.app
                      (Lean.Expr.const `Option [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                    (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction []))))
                          (Lean.Expr.lam
                            `x
                            (Lean.Expr.app
                              (Lean.Expr.const `Option [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.FuncId []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.EvalFunction []))))
                            (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.app
                        (Lean.Expr.bvar 0)
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.none [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.FuncId []))
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))))))
                    (Lean.Expr.lam
                      (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1031)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncId []))
                        (Lean.Expr.app
                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.EvalFunction [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.FuncId []))
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.EvalFunction [])))
                            (Lean.Expr.lam
                              `x
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.FuncId []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.EvalFunction [])))
                              (Lean.Expr.app
                                (Lean.Expr.bvar 6)
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Option.some [Lean.Level.zero])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.FuncId []))
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.EvalFunction []))))
                                  (Lean.Expr.bvar 0)))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.bvar 0))
                        (Lean.Expr.lam
                          (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1032)
                          (Lean.Expr.const `TrustIr.FuncId [])
                          (Lean.Expr.lam
                            (Lean.Name.num `snd.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1033)
                            (Lean.Expr.app
                              (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.EvalFunction []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `Except.casesOn
                                          [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                                      (Lean.Expr.const `TrustIr.EvalFunction []))
                                    (Lean.Expr.lam
                                      `x
                                      (Lean.Expr.app
                                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                        (Lean.Expr.const `TrustIr.EvalFunction []))
                                      (Lean.Expr.app
                                        (Lean.Expr.bvar 8)
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Option.some [Lean.Level.zero])
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.FuncId []))
                                              (Lean.Expr.app
                                                (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                (Lean.Expr.const `TrustIr.EvalFunction []))))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                                  (Lean.Expr.const `TrustIr.FuncId []))
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                  (Lean.Expr.const `TrustIr.EvalFunction [])))
                                              (Lean.Expr.bvar 2))
                                            (Lean.Expr.bvar 0))))
                                      (Lean.BinderInfo.default)))
                                  (Lean.Expr.bvar 0))
                                (Lean.Expr.lam
                                  (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1034)
                                  (Lean.Expr.const `TrustIrEval.DecodeError [])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TrustIrEval.DecodeError.casesOn [Lean.Level.param `u_1])
                                          (Lean.Expr.lam
                                            `x
                                            (Lean.Expr.const `TrustIrEval.DecodeError [])
                                            (Lean.Expr.app
                                              (Lean.Expr.bvar 9)
                                              (Lean.Expr.app
                                                (Lean.Expr.app
                                                  (Lean.Expr.const `Option.some [Lean.Level.zero])
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                                      (Lean.Expr.const `TrustIr.FuncId []))
                                                    (Lean.Expr.app
                                                      (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                      (Lean.Expr.const `TrustIr.EvalFunction []))))
                                                (Lean.Expr.app
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                                        (Lean.Expr.const `TrustIr.FuncId []))
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                                        (Lean.Expr.const `TrustIr.EvalFunction [])))
                                                    (Lean.Expr.bvar 3))
                                                  (Lean.Expr.app
                                                    (Lean.Expr.app
                                                      (Lean.Expr.app
                                                        (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                                                      (Lean.Expr.const `TrustIr.EvalFunction []))
                                                    (Lean.Expr.bvar 0)))))
                                            (Lean.BinderInfo.default)))
                                        (Lean.Expr.bvar 0))
                                      (Lean.Expr.lam
                                        (Lean.Name.num `feature.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1036)
                                        (Lean.Expr.const `String [])
                                        (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 6) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 0))
                                        (Lean.BinderInfo.default)))
                                    (Lean.Expr.lam
                                      (Lean.Name.num `msg.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1037)
                                      (Lean.Expr.const `String [])
                                      (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 7) (Lean.Expr.bvar 3)) (Lean.Expr.bvar 0))
                                      (Lean.BinderInfo.default)))
                                  (Lean.BinderInfo.default)))
                              (Lean.Expr.lam
                                (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1035)
                                (Lean.Expr.const `TrustIr.EvalFunction [])
                                (Lean.Expr.app
                                  (Lean.Expr.bvar 4)
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Option.some [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.FuncId []))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                          (Lean.Expr.const `TrustIr.EvalFunction []))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.FuncId []))
                                          (Lean.Expr.app
                                            (Lean.Expr.const `TrustIrEval.D [Lean.Level.zero])
                                            (Lean.Expr.const `TrustIr.EvalFunction [])))
                                        (Lean.Expr.bvar 2))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                                          (Lean.Expr.const `TrustIr.EvalFunction []))
                                        (Lean.Expr.bvar 0)))))
                                (Lean.BinderInfo.default)))
                            (Lean.BinderInfo.default))
                          (Lean.BinderInfo.default)))
                      (Lean.BinderInfo.default)))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_3
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 3 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 877)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 877)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                `feature
                (Lean.Expr.const `String [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  `msg
                  (Lean.Expr.const `String [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `List [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.BlockId []))
                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                      (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
                  (Lean.BinderInfo.default))
                (Lean.Expr.forallE
                  `h_3
                  (Lean.Expr.forallE
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 950)
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock [])))
                    (Lean.Expr.app
                      (Lean.Expr.bvar 4)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                          (Lean.Expr.app
                            (Lean.Expr.const `List [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.BlockId []))
                              (Lean.Expr.const `TrustIr.BasicBlock []))))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 3))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 877)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 877)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                `feature
                (Lean.Expr.const `String [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.unsupported []) (Lean.Expr.bvar 0))))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  `msg
                  (Lean.Expr.const `String [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `List [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.BlockId []))
                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                      (Lean.Expr.app (Lean.Expr.const `TrustIrEval.DecodeError.malformed []) (Lean.Expr.bvar 0))))
                  (Lean.BinderInfo.default))
                (Lean.Expr.lam
                  `h_3
                  (Lean.Expr.forallE
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 950)
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock [])))
                    (Lean.Expr.app
                      (Lean.Expr.bvar 4)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                          (Lean.Expr.app
                            (Lean.Expr.const `List [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.BlockId []))
                              (Lean.Expr.const `TrustIr.BasicBlock []))))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.app
                              (Lean.Expr.const `List [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.BlockId []))
                                (Lean.Expr.const `TrustIr.BasicBlock []))))
                          (Lean.Expr.lam
                            `x
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIrEval.DecodeError []))
                              (Lean.Expr.app
                                (Lean.Expr.const `List [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `TrustIr.BlockId []))
                                  (Lean.Expr.const `TrustIr.BasicBlock []))))
                            (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.lam
                        (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1038)
                        (Lean.Expr.const `TrustIrEval.DecodeError [])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `TrustIrEval.DecodeError.casesOn [Lean.Level.param `u_1])
                                (Lean.Expr.lam
                                  `x
                                  (Lean.Expr.const `TrustIrEval.DecodeError [])
                                  (Lean.Expr.app
                                    (Lean.Expr.bvar 6)
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                                        (Lean.Expr.app
                                          (Lean.Expr.const `List [Lean.Level.zero])
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `TrustIr.BlockId []))
                                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                                      (Lean.Expr.bvar 0)))
                                  (Lean.BinderInfo.default)))
                              (Lean.Expr.bvar 0))
                            (Lean.Expr.lam
                              (Lean.Name.num `feature.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1040)
                              (Lean.Expr.const `String [])
                              (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.lam
                            (Lean.Name.num `msg.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1041)
                            (Lean.Expr.const `String [])
                            (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                            (Lean.BinderInfo.default)))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.lam
                      (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1039)
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock [])))
                      (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                      (Lean.BinderInfo.default)))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_4
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 4 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 868)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 868)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                `f
                (Lean.Expr.const `TrustIrEval.Function [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  Lean.Name.anonymous
                  (Lean.Expr.const `Unit [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function [])))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 868)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 868)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                `f
                (Lean.Expr.const `TrustIrEval.Function [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  Lean.Name.anonymous
                  (Lean.Expr.const `Unit [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function [])))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.Function []))
                        (Lean.Expr.lam
                          `x
                          (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIrEval.Function []))
                          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Unit.unit [])))
                  (Lean.Expr.lam
                    (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1046)
                    (Lean.Expr.const `TrustIrEval.Function [])
                    (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_5
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 5 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1143)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1143)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                `signature
                (Lean.Expr.const `TrustIr.FuncTyDef [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  Lean.Name.anonymous
                  (Lean.Expr.const `Unit [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1143)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1143)
            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                `signature
                (Lean.Expr.const `TrustIr.FuncTyDef [])
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Option.some [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  Lean.Name.anonymous
                  (Lean.Expr.const `Unit [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app (Lean.Expr.const `Option.none [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Option.casesOn [Lean.Level.param `u_1, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.FuncTyDef []))
                        (Lean.Expr.lam
                          `x
                          (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Unit.unit [])))
                  (Lean.Expr.lam
                    (Lean.Name.num `val.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1179)
                    (Lean.Expr.const `TrustIr.FuncTyDef [])
                    (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_6
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 6 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1183)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1183)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                `blocks
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock [])))
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.forallE
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1211)
                  (Lean.Expr.const `TrustIrEval.DecodeError [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `List [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.BlockId []))
                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                      (Lean.Expr.bvar 0)))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 2))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1183)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1183)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `TrustIrEval.DecodeError []))
              (Lean.Expr.app
                (Lean.Expr.const `List [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `TrustIr.BlockId []))
                  (Lean.Expr.const `TrustIr.BasicBlock []))))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                `blocks
                (Lean.Expr.app
                  (Lean.Expr.const `List [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `TrustIr.BlockId []))
                    (Lean.Expr.const `TrustIr.BasicBlock [])))
                (Lean.Expr.app
                  (Lean.Expr.bvar 2)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Except.ok [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `TrustIrEval.DecodeError []))
                      (Lean.Expr.app
                        (Lean.Expr.const `List [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIr.BlockId []))
                          (Lean.Expr.const `TrustIr.BasicBlock []))))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.Expr.lam
                `h_2
                (Lean.Expr.forallE
                  (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1211)
                  (Lean.Expr.const `TrustIrEval.DecodeError [])
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Except.error [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIrEval.DecodeError []))
                        (Lean.Expr.app
                          (Lean.Expr.const `List [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIr.BlockId []))
                            (Lean.Expr.const `TrustIr.BasicBlock []))))
                      (Lean.Expr.bvar 0)))
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Except.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `TrustIrEval.DecodeError []))
                          (Lean.Expr.app
                            (Lean.Expr.const `List [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `TrustIr.BlockId []))
                              (Lean.Expr.const `TrustIr.BasicBlock []))))
                        (Lean.Expr.lam
                          `x
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Except [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `TrustIrEval.DecodeError []))
                            (Lean.Expr.app
                              (Lean.Expr.const `List [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `TrustIr.BlockId []))
                                (Lean.Expr.const `TrustIr.BasicBlock []))))
                          (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.lam
                      (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10095) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1213)
                      (Lean.Expr.const `TrustIrEval.DecodeError [])
                      (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.lam
                    (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num `a.«_@».Init.Prelude 10100) "TrustIr") "Proofs") "DecodedContextLookup") "_hyg") 1214)
                    (Lean.Expr.app
                      (Lean.Expr.const `List [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `TrustIr.BlockId []))
                        (Lean.Expr.const `TrustIr.BasicBlock [])))
                    (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe })
      let helperName := `TrustIrEval.FunctionLookup.listContextSpec.match_7
      if ((← Lean.getEnv).find? helperName).isSome then
        throwError "original context matcher 7 already exists; refusing replacement"
      let declaredType : Lean.Expr :=
        Lean.Expr.forallE
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 657)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
              (Lean.Expr.forallE
                (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.BinderInfo.default)))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 657)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
              (Lean.Expr.forallE
                (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.BinderInfo.default)))
            (Lean.Expr.forallE
              `h_1
              (Lean.Expr.forallE
                `signatures
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.Expr.forallE
                  `direct
                  (Lean.Expr.forallE
                    (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                    (Lean.Expr.const `TrustIr.FuncId [])
                    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                          (Lean.Expr.forallE
                            (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                            (Lean.Expr.const `TrustIr.FuncId [])
                            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.bvar 0)))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      let declaredValue : Lean.Expr :=
        Lean.Expr.lam
          `motive
          (Lean.Expr.forallE
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 657)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
              (Lean.Expr.forallE
                (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.BinderInfo.default)))
            (Lean.Expr.sort (Lean.Level.param `u_1))
            (Lean.BinderInfo.default))
          (Lean.Expr.lam
            (Lean.Name.num `x.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 657)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
              (Lean.Expr.forallE
                (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                (Lean.Expr.const `TrustIr.FuncId [])
                (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.BinderInfo.default)))
            (Lean.Expr.lam
              `h_1
              (Lean.Expr.forallE
                `signatures
                (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                (Lean.Expr.forallE
                  `direct
                  (Lean.Expr.forallE
                    (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                    (Lean.Expr.const `TrustIr.FuncId [])
                    (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app
                    (Lean.Expr.bvar 3)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Prod.mk [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                          (Lean.Expr.forallE
                            (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                            (Lean.Expr.const `TrustIr.FuncId [])
                            (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.bvar 0)))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Prod.casesOn [Lean.Level.param `u_1, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                      (Lean.Expr.forallE
                        (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                        (Lean.Expr.const `TrustIr.FuncId [])
                        (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.lam
                      `x
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Prod [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef [])))
                        (Lean.Expr.forallE
                          (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                          (Lean.Expr.const `TrustIr.FuncId [])
                          (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.lam
                  (Lean.Name.num `fst.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1215)
                  (Lean.Expr.app (Lean.Expr.const `Array [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                  (Lean.Expr.lam
                    (Lean.Name.num `snd.«_@».TrustIr.Proofs.DecodedContextLookup._hyg 1216)
                    (Lean.Expr.forallE
                      (Lean.Name.num `a.«_@».TrustIr.DecodedContext._hyg 855)
                      (Lean.Expr.const `TrustIr.FuncId [])
                      (Lean.Expr.app (Lean.Expr.const `Option [Lean.Level.zero]) (Lean.Expr.const `TrustIr.FuncTyDef []))
                      (Lean.BinderInfo.default))
                    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default)))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default)
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile (.defnDecl {
        name := helperName, levelParams := [Lean.Name.str Lean.Name.anonymous "u_1"],
        type := declaredType, value := declaredValue, hints := .abbrev, safety := .safe }))
    let helper (index : Nat) := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous
        "TrustIrEval") "FunctionLookup") "listContextSpec") s!"match_{index}")
    let h1 := helper 1
    let h2 := helper 2
    let h3 := helper 3
    let h4 := helper 4
    let h5 := helper 5
    let h6 := helper 6
    let h7 := helper 7
    -- Each pass consumes exactly one original match. Inner matches are rewritten first.
    let rewrite (index : Nat) (stx : Lean.Syntax) : StateT Nat Lean.MacroM (Option Lean.Syntax) := do
      if index == 1 then
        match stx with
        | `(term| match $selected:term with
            | some (_, Except.ok $function:ident) => $found:term
            | _ => $missing:term) =>
          modify (· + 1)
          let replacement ← `(term| $h1:ident (fun _ => Option EvalFunction) $selected:term
            (fun _ $function:ident => $found:term) (fun _ => $missing:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 2 then
        match stx with
        | `(term| match $selected:term with
            | some (_, Except.error (.malformed $message:ident)) => $malformed:term
            | some (_, Except.error (.unsupported $feature:ident)) => $unsupported:term
            | _ => $missing:term) =>
          modify (· + 1)
          let replacement ← `(term| $h2:ident (fun _ => Option SemError) $selected:term
            (fun _ $message:ident => $malformed:term)
            (fun _ $feature:ident => $unsupported:term) (fun _ => $missing:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 3 then
        match stx with
        | `(term| match $selected:term with
            | .error (.unsupported $feature:ident) => $unsupported:term
            | .error (.malformed $message:ident) => $malformed:term
            | .ok _ => $available:term) =>
          modify (· + 1)
          let replacement ← `(term| $h3:ident (fun _ => Option SemError) $selected:term
            (fun $feature:ident => $unsupported:term)
            (fun $message:ident => $malformed:term) (fun _ => $available:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 4 then
        match stx with
        | `(term| match $selected:term with
            | some $function:ident => $available:term
            | none => $missing:term) =>
          -- Only the outer function-error lookup has this syntax after pass 3.
          if function.getId != `f then return none
          modify (· + 1)
          let replacement ← `(term| $h4:ident (fun _ => Option SemError) $selected:term
            (fun $function:ident => $available:term) (fun _ => $missing:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 5 then
        match stx with
        | `(term| match $selected:term with
            | some $signature:ident => $available:term
            | none => $missing:term) =>
          if signature.getId != `signature then return none
          modify (· + 1)
          let replacement ← `(term| $h5:ident (fun _ => Except SemError FunctionHeader) $selected:term
            (fun $signature:ident => $available:term) (fun _ => $missing:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 6 then
        match stx with
        | `(term| match $selected:term with
            | .ok $blocks:ident => $available:term
            | .error _ => $missing:term) =>
          modify (· + 1)
          let replacement ← `(term| $h6:ident (fun _ => Option (FuncId × D EvalFunction)) $selected:term
            (fun $blocks:ident => $available:term) (fun _ => $missing:term))
          pure (some replacement.raw)
        | _ => pure none
      else if index == 7 then
        -- Keep the exact original prefix and continuation nodes of the do sequence.
        if stx.getKind != ``Lean.Parser.Term.doSeqIndent then return none
        let items := stx[0].getArgs
        let mut answer : Option Lean.Syntax := none
        for i in [:items.size] do
          match items[i]![0] with
          | `(doElem| let ($signatures:ident, $direct:ident) := $selected:term) =>
            if signatures.getId != `signatures || direct.getId != `direct then
              StateT.lift (Lean.Macro.throwError "unexpected original context pair binders")
            if i + 1 >= items.size then
              StateT.lift (Lean.Macro.throwError "original context pair has no continuation")
            modify (· + 1)
            let tail : Lean.TSyntax ``Lean.Parser.Term.doSeq :=
              ⟨stx.setArg 0 (stx[0].setArgs (items.extract (i + 1) items.size))⟩
            let replacement ← `(doElem| $h7:ident (fun _ => D EvalContext) $selected:term
              (fun $signatures:ident $direct:ident => do $tail:doSeq))
            let newItem := items[i]!.setArg 0 replacement.raw
            answer := some (stx.setArg 0 (stx[0].setArgs ((items.extract 0 i).push newItem)))
          | _ => pure ()
        pure answer
      else pure none
    let mut modernCommand := original.raw
    for index in [1:8] do
      let (updated, count) ← (modernCommand.replaceM (rewrite index)).run 0
      if count != 1 then
        Lean.Macro.throwError s!"original context matcher {index}: expected exactly one use, got {count}"
      modernCommand := updated
    pure ⟨Lean.mkNullNode #[helpers.raw, modernCommand]⟩
  else Lean.Macro.throwError "unsupported Lean version for original context matchers"

trustIrContextLookupOriginalMatchers
noncomputable def listContextSpec (m : Module) (maxCallDepth : Nat) : D EvalContext := do
  let selectedModel ← m.byteModel
  -- Deliberately conservative: the decoder retains the full claims, but this
  -- oracle currently refuses any module containing a typed ABI signature.
  -- Comparing logical argument values would not validate its carrier mapping.
  if m.funcTys.any (fun sig => sig.abi.isSome) then
    unsupported "signature_abi.transport_semantics"
  let (signatures, direct) := localTypeHeadersOf m
  let initialHeaders : Lean.RBMap Nat (Except SemError FunctionHeader) compare := Lean.mkRBMap ..
  let headers := m.functions.foldl (fun table function =>
    if table.contains function.id.index then table
    else table.insert function.id.index (match trustIrArrayGet? signatures function.ty.index with
      | some signature => .ok { signature, callingConv := function.callingConvention }
      | none => .error (.typeError s!"function {function.id.index}: original signature is absent"))) initialHeaders
  -- Keep each body's metadata failure lazy, exactly like its decode failure.
  -- Direct-call result declarations inspect original headers, never this table.
  let defs : List (FuncId × D EvalFunction) := m.functions.filterMap (fun f =>
    match f.blocks with
    | .ok blocks =>
      if f.isDeclaration then none
      else some (f.id, DecodedCFG.evalFunctionListSpec signatures direct f blocks)
    | .error _ => none)
  pure { byteModel := selectedModel
         valueSource := valueSourceOf m
         memoryService := some (memoryServiceSpec m selectedModel)
         originalClosureMemory := some (originalMemoryServiceOf m selectedModel)
         functions := fun fid =>
           match defs.find? (fun p => p.fst == fid) with
           | some (_, Except.ok function) => some function
           | _ => none
         functionHeaders := fun fid => headers.find? fid.index
         -- Memory code words use original source positions, including entries
         -- absent from executable `defs`. They decode to typed FnDef values;
         -- raw-pointer call admission and native reification remain separate.
         functionOrder := some (m.functions.map (·.id))
         funcPtrs := fun _ => none
         funcTys := fun id => trustIrArrayGet? signatures id.index
         maxCallDepth := maxCallDepth
         globalsTable := fun id => trustIrListGet? m.globals id.index
         -- A bodyless declaration is `unsupported.interprocedural_call` when
         -- called (the interpreter's `UnsupportedCall`), never "undefined".
         declared := fun fid => m.functions.any (fun f => f.id == fid && f.isDeclaration)
         functionErrors := fun fid =>
           match m.functions.find? (fun f => f.id == fid) with
           | some f => match f.blocks with
             | .error (.unsupported feature) => some (.unsupported .interproceduralCall
                 s!"function {fid.index} body is unsupported: {feature}")
             | .error (.malformed msg) => some (.typeError
                 s!"function {fid.index} body is malformed: {msg}")
             | .ok _ =>
               match defs.find? (fun row => row.fst == fid) with
               | some (_, Except.error (.malformed message)) => some (.typeError message)
               | some (_, Except.error (.unsupported feature)) => some (.unsupported .ssaTypeTable feature)
               | _ => none
           | none => none
         tupleLayouts := m.tupleLayouts
         -- Amendment D: a drop resolves to the glue of the row keyed on its
         -- type, and is then the ordinary `Call` / `Invoke`.
         dropGlue := dropGlueOf m }

/-- Exact equality to the complete original list-based assembly for every
    raw module and resource bound, including all refusal payloads and every
    context field. No module validity or unique-id premise is required. -/
theorem contextOf_eq_listContextSpec (source : Module) (maxDepth : Nat) :
    contextOf source maxDepth = listContextSpec source maxDepth := by
  trustIrCompilerProof {
  unfold contextOf listContextSpec
  simp only [findFunction_prepare, findError_prepare, isDeclared_prepare,
    DecodedCFG.evalFunctionOfWithTypes_eq_listSpec]
  rfl
  } {
    -- Both actual executable-query eliminators have the complete original
    -- behavior, for every selected row and unrestricted result callbacks.
    have originalExecutableDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onFunction : FuncId → EvalFunction → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        listContextSpec.match_1 (fun _ => α) selected onFunction onOther =
        (match selected with
         | some (key, Except.ok function) => onFunction key function
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result <;> rfl
    have originalExecutableRuntimeDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onFunction : FuncId → EvalFunction → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        findFunction_prepare.match_1 (fun _ => α) selected onFunction onOther =
        (match selected with
         | some (key, Except.ok function) => onFunction key function
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result <;> rfl
    have originalExecutableErrorDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onMalformed : FuncId → String → α)
        (onUnsupported : FuncId → String → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        listContextSpec.match_2 (fun _ => α) selected
          onMalformed onUnsupported onOther =
        (match selected with
         | some (key, Except.error (.malformed message)) => onMalformed key message
         | some (key, Except.error (.unsupported feature)) => onUnsupported key feature
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result with
        | ok function => rfl
        | error error => cases error <;> rfl
    have originalExecutableErrorRuntimeDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onMalformed : FuncId → String → α)
        (onUnsupported : FuncId → String → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        findError_prepare.match_1 (fun _ => α) selected
          onMalformed onUnsupported onOther =
        (match selected with
         | some (key, Except.error (.malformed message)) => onMalformed key message
         | some (key, Except.error (.unsupported feature)) => onUnsupported key feature
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result with
        | ok function => rfl
        | error error => cases error <;> rfl
    have originalSourceDispatch {α : Type} (selected : Option Function)
        (onSome : Function → α) (onNone : Unit → α) :
        listContextSpec.match_4 (fun _ => α) selected onSome onNone =
        (match selected with
         | some function => onSome function
         | none => onNone ()) := by
      cases selected <;> rfl
    have originalHeaderDispatch {α : Type} (selected : Option FuncTyDef)
        (onSome : FuncTyDef → α) (onNone : Unit → α) :
        listContextSpec.match_5 (fun _ => α) selected onSome onNone =
        (match selected with
         | some signature => onSome signature
         | none => onNone ()) := by
      cases selected <;> rfl
    have originalDefsDispatch {α : Type}
        (selected : Except DecodeError (List (BlockId × BasicBlock)))
        (onBlocks : List (BlockId × BasicBlock) → α) (onError : DecodeError → α) :
        listContextSpec.match_6 (fun _ => α) selected onBlocks onError =
        (match selected with
         | .ok blocks => onBlocks blocks
         | .error error => onError error) := by
      cases selected <;> rfl
    have originalDefsRuntimeDispatch {α : Type}
        (selected : Except DecodeError (List (BlockId × BasicBlock)))
        (onBlocks : List (BlockId × BasicBlock) → α) (onError : DecodeError → α) :
        contextOf.match_1 (fun _ => α) selected onBlocks onError =
        (match selected with
         | .ok blocks => onBlocks blocks
         | .error error => onError error) := by
      cases selected <;> rfl
    -- The preserved whole canonical Error type uses its original outer
    -- Option/Except eliminators; expose their complete callback behavior too.
    have originalCanonicalSourceDispatch {α : Type} (selected : Option Function)
        (onSome : Function → α) (onNone : Unit → α) :
        findError_prepare.match_6 (fun _ => α) selected onSome onNone =
        (match selected with
         | some function => onSome function
         | none => onNone ()) := by
      cases selected <;> rfl
    have originalCanonicalBlocksDispatch {α : Type}
        (selected : Except DecodeError (List (BlockId × BasicBlock)))
        (onUnsupported : String → α) (onMalformed : String → α)
        (onBlocks : List (BlockId × BasicBlock) → α) :
        findError_prepare.match_4 (fun _ => α) selected
          onUnsupported onMalformed onBlocks =
        (match selected with
         | .error (.unsupported feature) => onUnsupported feature
         | .error (.malformed message) => onMalformed message
         | .ok blocks => onBlocks blocks) := by
      cases selected with
      | error error => cases error <;> rfl
      | ok blocks => rfl
    -- The original three-way body dispatch is valid for every decode result
    -- and every callback; explicitly expose its complete constructor behavior.
    have originalBlocksDispatch {α : Type}
        (selected : Except DecodeError (List (BlockId × BasicBlock)))
        (onUnsupported : String → α) (onMalformed : String → α)
        (onBlocks : List (BlockId × BasicBlock) → α) :
        listContextSpec.match_3 (fun _ => α) selected
          onUnsupported onMalformed onBlocks =
        (match selected with
         | .error (.unsupported feature) => onUnsupported feature
         | .error (.malformed message) => onMalformed message
         | .ok blocks => onBlocks blocks) := by
      cases selected with
      | error error => cases error <;> rfl
      | ok blocks => rfl
    unfold contextOf listContextSpec
    simp only [findFunction_prepare, findError_prepare, isDeclared_prepare,
      DecodedCFG.evalFunctionOfWithTypes_eq_listSpec]
    -- The restored full dependent pair eliminator must see the actual pair,
    -- rather than be compared with projections of an unreduced product.
    generalize localTypeHeadersOf source = originalHeaders
    rcases originalHeaders with ⟨signatures, direct⟩
    delta listContextSpec.match_7
    simp only [originalExecutableDispatch, originalExecutableRuntimeDispatch,
      originalExecutableErrorDispatch, originalExecutableErrorRuntimeDispatch,
      originalSourceDispatch, originalHeaderDispatch, originalDefsDispatch,
      originalDefsRuntimeDispatch, originalBlocksDispatch,
      originalCanonicalSourceDispatch, originalCanonicalBlocksDispatch]
    rfl
  }

end TrustIrEval.FunctionLookup
