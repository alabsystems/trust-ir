/-
  `semr_eval`: SemR's executable, the oracle the SemR differential runs
  against the reference interpreter (`crates/trust-ir-conformance/tests/
  lean_exec_differential.rs`, the `semr_*` tests).

      semr_eval <module.tmbc> <runs.txt>
      semr_eval --executed <module.tmbc> <runs.txt>
      semr_eval --decode <dir> <n>

  `module.tmbc` is the module's binary image (`serialize_module`), decoded by
  SemR's own decoder (`SemR.decode`). Each line of `runs.txt` is one run:

      <fuel> <call depth> <function id> <arg>*    arg: i<IntTy code>:<raw> | b0 | b1
                                                    | t<IntTy code>:<dims>:<residues>

  (a tensor: its extents and its row-major residues, each list
  comma-separated and empty for none; `t2::7` is a rank-0 `i32` tensor)

  and the reply is one JSON verdict per line, in order, in the grammar of
  `lean/trust_ir-semantics/TrustIrEval/Run.lean`. `--executed` replies, per
  run, `{"executed":[…],"consts":[…]}`: the SemR `Inst` constructors of the
  nodes the run executed (the node at the program counter of each step `run`
  takes, the step that stops the run included), and the `CONSTANT_FRAGMENT.tsv`
  constructors of the constants those `const` nodes named, which the parity
  gate credits. `--decode` runs only the
  decoder, on `<dir>/0.tmbc` … `<dir>/<n-1>.tmbc`, one line per blob:
  `{"decoded":<summary>}` (`moduleSummary`: the decoded module, compared
  field for field with `deserialize_module`'s), `{"unsupported":…}` or
  `{"error":"decode: …"}` (the decoder differential). This driver is I/O only: it
  is not part of SemR and is not kernel-checked.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import SemR

open SemR

def intTyOfCode : Nat → Option IntTy
  | 0 => some .i8 | 1 => some .i16 | 2 => some .i32 | 3 => some .i64 | 4 => some .i128
  | 5 => some .isize | 6 => some .u8 | 7 => some .u16 | 8 => some .u32 | 9 => some .u64
  | 10 => some .u128 | 11 => some .usize | _ => none

inductive Argument where
  | bool (v : Bool)
  | int (t : IntTy) (sourceBits raw : Nat)
  | enum (id : Nat) (tag : IntTy) (raw : Nat)
  | tensor (elem : IntTy) (sourceBits : Nat) (dims elems : List Nat)

/-- A comma-separated list of naturals; the empty string is the empty list. -/
def parseNats (s : String) : Option (List Nat) :=
  if s == "" then some [] else (s.splitOn ",").mapM String.toNat?

def parseArg (s : String) : Option Argument :=
  if s == "b0" then some (.bool false)
  else if s == "b1" then some (.bool true)
  else if s.startsWith "e" then
    -- a fieldless enum value: `e<enum id>:<tag IntTy code>:<tag residue>`
    match (s.drop 1).toString.splitOn ":" with
    | [e, c, r] =>
      match e.toNat?, c.toNat?, r.toNat? with
      | some e, some c, some r =>
        match intTyOfCode c with
        | some t => if r < modulus (t.bits 64) then some (.enum e t r) else none
        | none => none
      | _, _, _ => none
    | _ => none
  else if s.startsWith "t" then
    -- a tensor value: `t<element IntTy code>:<element source bits>:<extents>:<residues>`
    -- (the residues at the source width, as an `i<code>:<bits>:<raw>` scalar's)
    match (s.drop 1).toString.splitOn ":" with
    | [c, w, ds, xs] =>
      match c.toNat?, w.toNat?, parseNats ds, parseNats xs with
      | some c, some w, some ds, some xs =>
        match intTyOfCode c with
        | some t => some (.tensor t w ds xs)
        | none => none
      | _, _, _, _ => none
    | _ => none
  else if s.startsWith "i" then
    match (s.drop 1).toString.splitOn ":" with
    | [c, r] =>
      match c.toNat?, r.toNat? with
      | some c, some r =>
        match intTyOfCode c with
        | some t => some (.int t (t.bits 64) r)
        | none => none
      | _, _ => none
    | [c, w, r] =>
      match c.toNat?, w.toNat?, r.toNat? with
      | some c, some w, some r =>
        match intTyOfCode c with
        | some t => some (.int t w r)
        | none => none
      | _, _, _ => none
    | _ => none
  else none

def argumentValue (m : Module) : Argument → R Val
  | .bool b => .ok (.bool b)
  | .int t w r => entryInt m t w r
  | .enum id t r => do
    let tag ← entryInt m t (t.bits 64) r
    pure (.enum id [tag])
  -- The interpreter's entry rule for a tensor (`narrow_pointer_width_ints`):
  -- an extent the target's `usize` cannot hold is refused, then each element
  -- is re-expressed at the target width exactly as a scalar entry integer.
  | .tensor t w ds xs => do
    if ds.any (fun d => decide (modulus m.pointerBits ≤ d)) then
      tyR "TypeError: entry argument: a tensor extent does not fit the target's usize"
    let elems ← xs.mapM (fun r => do
      match ← entryInt m t w r with
      | .int _ a => pure a
      | _ => tyR "TypeError: entry argument: a tensor element is not an integer")
    pure (.tensor t ds elems)

def jstr (s : String) : String :=
  let esc := s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 32 then acc ++ " " else acc.push c) ""
  "\"" ++ esc ++ "\""

def renderVal (pointerBits : Nat) : Nat → Val → String
  | 0, _ => "{\"other\":\"depth\"}"
  | _ + 1, .int t r => s!"\{\"int\":\{\"width\":{t.bits pointerBits},\"raw\":\"{r}\"}}"
  | _ + 1, .bool b => s!"\{\"bool\":{if b then "true" else "false"}}"
  | _ + 1, .nullPtr => "{\"ptr\":\"null\"}"
  | d + 1, .enum _ lanes =>
    "{\"aggregate\":[" ++ ",".intercalate (lanes.map (renderVal pointerBits d)) ++ "]}"
  | d + 1, .struct _ lanes =>
    "{\"aggregate\":[" ++ ",".intercalate (lanes.map (renderVal pointerBits d)) ++ "]}"
  | d + 1, .closure cid target captures =>
    s!"\{\"closure\":\{\"type\":{cid},\"func\":{target},\"captures\":[" ++
      ",".intercalate (captures.map (renderVal pointerBits d)) ++ "]}}"
  | _ + 1, .cellPtr id => s!"\{\"private_cell\":{id}}"
  | _ + 1, .unwritten _ => "{\"unwritten\":true}"
  | _ + 1, .frame _ slots => s!"\{\"frame\":{slots.length}}"
  | _ + 1, .poison _ => "{\"poison\":true}"
  | _ + 1, .ptr a o => s!"\{\"ptr\":\{\"alloc\":{a},\"offset\":{o}}}"
  | _ + 1, .partialBytes _ _ => "{\"poison\":true}"
  | _ + 1, .tensor t dims elems =>
    -- the element type by its IntTy code (exact: `i32` and `u32` differ),
    -- the extents, then the row-major residues
    s!"\{\"tensor\":\{\"elem\":{t.code},\"dims\":[" ++
      ",".intercalate (dims.map toString) ++ "],\"elems\":[" ++
      ",".intercalate (elems.map (fun r => s!"\"{r}\"")) ++ "]}}"

def renderOut (pointerBits : Nat) : Out → String
  | .ret vs => "{\"ok\":[" ++ ",".intercalate (vs.map (renderVal pointerBits 16)) ++ "]}"
  | .ub m => "{\"ub\":" ++ jstr m ++ "}"
  | .typeError m => "{\"type_error\":" ++ jstr m ++ "}"
  | .unsupported f => "{\"unsupported\":" ++ jstr f ++ "}"
  | .outOfFuel => "{\"out_of_fuel\":true}"
  | .panic m => "{\"panic\":" ++ jstr m ++ "}"
  | .globalDivPanic p =>
    let msg := match p.kind with
      | .divByZero => "attempt to divide by zero"
      | .remByZero => "attempt to calculate the remainder with a divisor of zero"
    "{\"panic\":" ++ jstr msg ++ ",\"site\":{\"entry\":" ++ toString p.entry ++
      ",\"location\":{\"global\":" ++ toString p.global ++ ",\"offset\":" ++
      toString p.offset ++ "}}}"
  | .outOfMemory => "{\"out_of_memory\":true}"

def runLine (m : Except DErr Module) (line : String) : String :=
  match (line.splitOn " ").filter (· ≠ "") with
  | fuel :: depth :: fid :: args =>
    match fuel.toNat?, depth.toNat?, fid.toNat?, (args.mapM parseArg) with
    | some fuel, some depth, some fid, some vals =>
      match m with
      | .error (.unsupported f) => "{\"unsupported\":" ++ jstr f ++ "}"
      | .error (.malformed msg) => "{\"error\":" ++ jstr s!"decode: {msg}" ++ "}"
      | .ok m =>
        if !m.executableTarget then renderOut m.pointerBits (.unsupported "target.byte_model")
        else
          match vals.mapM (argumentValue m) with
          | .stop o => renderOut m.pointerBits o
          | .ok args => renderOut m.pointerBits (runFunction m fid args fuel depth)
    | _, _, _, _ => "{\"error\":\"bad run line\"}"
  | _ => "{\"error\":\"bad run line\"}"

/-! ### What a run executed (`--executed`) -/

/-- The SemR `Inst` constructor's name, as the decoded or quoted ledger spells it.
    Only decoded constructors can earn `FRAGMENT.tsv` runtime parity credit. -/
def instName : Inst → String
  | .binop _ _ _ _ => "binop"
  | .unop _ _ _ => "unop"
  | .overflow _ _ _ _ => "overflow"
  | .icmp _ _ _ _ => "icmp"
  | .const _ _ => "const"
  | .copy _ _ => "copy"
  | .select _ _ _ _ => "select"
  | .extractField _ _ _ => "extractField"
  | .insertField _ _ _ _ => "insertField"
  | .undef _ => "undef"
  | .assume _ => "assume"
  | .allocaCell _ => "allocaCell"
  | .loadCell _ _ => "loadCell"
  | .storeCell _ _ _ => "storeCell"
  | .openFrame _ => "openFrame"
  | .bindSlot _ _ _ => "bindSlot"
  | .loadSlot _ _ _ => "loadSlot"
  | .closeFrame _ => "closeFrame"
  | .nullPtr => "nullPtr"
  | .unreachable => "unreachable"
  | .assert _ _ => "assert"
  | .assertSitedDiv _ _ _ => "assertSitedDiv"
  | .call _ _ => "call"
  | .makeClosure _ _ _ => "makeClosure"
  | .br _ _ => "br"
  | .condBr _ _ _ _ _ => "condBr"
  | .cast _ _ _ _ => "cast"
  | .switch _ _ _ _ => "switch"
  | .ret _ => "ret"
  | .alloca _ _ _ => "alloca"
  | .load _ _ _ _ => "load"
  | .store _ _ _ _ _ => "store"
  | .gep _ _ _ => "gep"
  | .dealloc _ => "dealloc"
  | .tensorContract _ _ _ _ _ => "tensorContract"
  | .tensorMap _ _ _ => "tensorMap"
  | .tensorReduce _ _ _ _ => "tensorReduce"
  | .tensorView _ _ _ _ _ _ _ => "tensorView"
  | .tensorGather _ _ _ => "tensorGather"
  | .tensorScatter _ _ _ _ => "tensorScatter"

/-- The SemR `Const` constructor a `const` node executes, as
    `CONSTANT_FRAGMENT.tsv` spells it, for the constants that ledger can
    credit (`none` for the rest, which the old Lean model mirrors). -/
def constName : Inst → Option String
  | .const _ (.tensorBlob _ _) => some "tensorBlob"
  | _ => none

/-- Add `x` to `acc` once. -/
def noteOnce (x : String) (acc : List String) : List String :=
  if acc.contains x then acc else x :: acc

/-- `run`'s steps from `k` under budget `b`, collecting the constructor of
    each node a step executes (each name once), and, as `const:<name>`, the
    ledgered constant constructor a `const` node executes. -/
def executedFrom (m : Module) : Nat → Core → List String → List String
  | 0, _, acc => acc
  | b + 1, k, acc =>
    let acc := match nth? k.block.body k.pc with
      | some n =>
        let acc := noteOnce (instName n.inst) acc
        match constName n.inst with
        | some c => noteOnce ("const:" ++ c) acc
        | none => acc
      | none => acc
    match stepCore m k with
    | .done _ => acc
    | .cont k' => executedFrom m b k' acc

def executedLine (m : Except DErr Module) (line : String) : String :=
  match (line.splitOn " ").filter (· ≠ "") with
  | fuel :: depth :: fid :: args =>
    match fuel.toNat?, depth.toNat?, fid.toNat?, (args.mapM parseArg) with
    | some fuel, some depth, some fid, some vals =>
      match m with
      | .error _ => "{\"executed\":[],\"consts\":[]}"
      | .ok m =>
        let names := match vals.mapM (argumentValue m) >>= fun args => start m fid args depth with
          | .stop _ => []
          | .ok k => executedFrom m fuel k []
        let insts := names.reverse.filter (fun n => !n.startsWith "const:")
        let consts := (names.reverse.filter (·.startsWith "const:")).map (·.drop 6)
        "{\"executed\":[" ++ ",".intercalate (insts.map jstr) ++ "],\"consts\":[" ++
          ",".intercalate (consts.map (fun c => jstr c.toString)) ++ "]}"
    | _, _, _, _ => "{\"error\":\"bad run line\"}"
  | _ => "{\"error\":\"bad run line\"}"

/-! ### The decoded module's summary (`--decode`)

What the decoder differential compares against `deserialize_module`'s module,
field for field: the signatures, the enums' variant field types, and every
function's blocks, block parameters and nodes (instruction, operands,
results). The spelling is the test's (`semr_summary_of` in
`lean_exec_differential.rs`). -/

def jlist (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def intTyStr : IntTy → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64" | .i128 => "i128"
  | .isize => "isize" | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .u128 => "u128" | .usize => "usize"

def tyStr : Ty → String
  | .int t => intTyStr t
  | .bool => "bool"
  | .ptr => "ptr"
  | .unit => "unit"
  | .never => "never"
  | .enum id => s!"enum{id}"
  | .struct id => s!"struct{id}"
  | .closure id => s!"closure{id}"
  -- Diagnostic parity with Rust's outside-the-fragment spelling. The wire
  -- decoder still refuses storage; formatting grants no initialized value.
  | .storage size align => s!"outside-the-fragment:storage<{size}, {align}>"
  | .tensor e rank => s!"tensor<{intTyStr e},{rank}>"

def binopStr : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .udiv => "udiv" | .sdiv => "sdiv"
  | .urem => "urem" | .srem => "srem" | .and => "and" | .or => "or" | .xor => "xor"
  | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr" | .bAnd => "band" | .bOr => "bor"
  | .bXor => "bxor" | .rotl => "rotl" | .rotr => "rotr"

def unopStr : UnOp → String
  | .neg => "neg" | .not => "not" | .ctpop => "ctpop" | .ctlz => "ctlz" | .cttz => "cttz"
  | .bswap => "bswap" | .bitreverse => "bitreverse"

def icmpStr : ICmpOp → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt"
  | .uge => "uge" | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def ovfStr : OvfOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"

def castStr : CastOp → String
  | .trunc => "trunc" | .zext => "zext" | .sext => "sext" | .bitcast => "bitcast"

def constStr : Nat → Const → String
  | 0, _ => "?"
  | _ + 1, .int p => s!"i{p}"
  | _ + 1, .bool b => if b then "b1" else "b0"
  | _ + 1, .uninit => "uninit"
  | d + 1, .aggregate es => "(" ++ ",".intercalate (es.map (constStr d)) ++ ")"
  | _ + 1, .tensorBlob dg dims =>
    "blob<" ++ String.join (dg.map toString |>.intersperse ".") ++ ">[" ++
      ",".intercalate (dims.map toString) ++ "]"

def kindStr : AssertKind → String
  | .unspecified => "unspecified"
  | .overflow op => s!"overflow{op}"
  | .divByZero => "div0"
  | .remByZero => "rem0"
  | .bounds i l => s!"bounds{i},{l}"
  | .misaligned r f => s!"misaligned{r},{f}"
  | .nullPtr => "null"

/-- Axis pairs: `[a:b,…]`. -/
def pairsStr (ps : List (Nat × Nat)) : String :=
  "[" ++ ",".intercalate (ps.map (fun (a, b) => s!"{a}:{b}")) ++ "]"

/-- A tensor map node (v68): its scalar instruction's spelling, then its lanes:
    `binop.<op>.<ty>.<l>.<r>`, `unop.<op>.<ty>.<x>`, `icmp.<op>.<ty>.<l>.<r>`,
    `select.<ty>.<c>.<t>.<e>`, `cast.<op>.<src>.<dst>.<x>`. -/
def mapNodeStr : MapNode → String
  | .binop op t l r => s!"binop.{binopStr op}.{tyStr t}.{l}.{r}"
  | .unop op t x => s!"unop.{unopStr op}.{tyStr t}.{x}"
  | .icmp op t l r => s!"icmp.{icmpStr op}.{tyStr t}.{l}.{r}"
  | .select t c a b => s!"select.{tyStr t}.{c}.{a}.{b}"
  | .cast op s d x => s!"cast.{castStr op}.{tyStr s}.{tyStr d}.{x}"

/-- A tensor reduction's operator (v68), its text spelling. -/
def reduceOpStr : ReduceOp → String
  | .add => "add" | .mul => "mul" | .and => "and" | .or => "or" | .xor => "xor"
  | .smin => "smin" | .smax => "smax" | .umin => "umin" | .umax => "umax"

/-- A tensor view node (v68): `lit<n>`, `param<k>`, `src_extent<j>`,
    `coord<i>`, or `<op><a>:<b>` (`add sub mul div rem min max`). -/
def ixExprStr : IxExpr → String
  | .lit n => s!"lit{n}"
  | .param k => s!"param{k}"
  | .srcExtent j => s!"src_extent{j}"
  | .coord i => s!"coord{i}"
  | .add a b => s!"add{a}:{b}"
  | .sub a b => s!"sub{a}:{b}"
  | .mul a b => s!"mul{a}:{b}"
  | .div a b => s!"div{a}:{b}"
  | .rem a b => s!"rem{a}:{b}"
  | .min a b => s!"min{a}:{b}"
  | .max a b => s!"max{a}:{b}"

/-- A list of numbers: `[a,b,…]`. -/
def natsStr (xs : List Nat) : String := "[" ++ ",".intercalate (xs.map toString) ++ "]"

/-- An optional immediate: `-`, or the number. -/
def optNatStr : Option Nat → String
  | none => "-"
  | some n => toString n

/-- An instruction's name (its op, type and immediates) and its operand ids. -/
def instSummary : Inst → String × List Nat
  | .binop op t a b => (s!"binop.{binopStr op}.{tyStr t}", [a, b])
  | .unop op t a => (s!"unop.{unopStr op}.{tyStr t}", [a])
  | .overflow op t a b => (s!"overflow.{ovfStr op}.{tyStr t}", [a, b])
  | .icmp op t a b => (s!"icmp.{icmpStr op}.{tyStr t}", [a, b])
  | .const t c => (s!"const.{tyStr t}.{constStr 64 c}", [])
  | .copy t a => (s!"copy.{tyStr t}", [a])
  | .select t c a b => (s!"select.{tyStr t}", [c, a, b])
  | .extractField t a f => (s!"extract.{tyStr t}.{f}", [a])
  | .insertField t a f x => (s!"insert.{tyStr t}.{f}", [a, x])
  | .undef t => (s!"undef.{tyStr t}", [])
  | .assume c => ("assume", [c])
  | .allocaCell t => (s!"private.alloca.{tyStr t}", [])
  | .loadCell t p => (s!"private.load.{tyStr t}", [p])
  | .storeCell t p v => (s!"private.store.{tyStr t}", [p, v])
  | .openFrame slots => ("open." ++ ",".intercalate (slots.map tyStr), [])
  | .bindSlot f s x => (s!"bind.{s}", [f, x])
  | .loadSlot f s t => (s!"load.{s}.{tyStr t}", [f])
  | .closeFrame f => ("close", [f])
  | .nullPtr => ("nullptr", [])
  | .unreachable => ("unreachable", [])
  | .assert c k => (s!"assert.{kindStr k}", [c])
  | .assertSitedDiv c k site =>
    let kind := match k with
      | .divByZero => "div_by_zero"
      | .remByZero => "rem_by_zero"
    (s!"quoted.assert_sited.{kind}.entry{site.entry}.global{site.global}", [c])
  | .call f xs => (s!"call.{f}", xs)
  | .makeClosure cid target captures => (s!"makeClosure.{cid}.{target}", captures)
  | .br t xs => (s!"br.{t}", xs)
  | .condBr c t ta e ea => (s!"condbr.{t}.{ta.length}.{e}", c :: ta ++ ea)
  | .ret xs => ("ret", xs)
  | .cast op s d x => (s!"cast.{castStr op}.{tyStr s}.{tyStr d}", [x])
  | .switch x dflt da cs =>
    (s!"switch.{dflt}.{da.length}." ++
      ",".intercalate (cs.map (fun (c, t, as) => s!"{constStr 64 c}:{t}:{as.length}")),
     x :: da ++ cs.flatMap (fun (_, _, as) => as))
  | .alloca t c al => (s!"alloca.{tyStr t}.{optNatStr al}", c.toList)
  | .load t p v al => (s!"mload.{tyStr t}.{if v then 1 else 0}.{optNatStr al}", [p])
  | .store t p x v al => (s!"mstore.{tyStr t}.{if v then 1 else 0}.{optNatStr al}", [p, x])
  | .gep t b xs => (s!"gep.{tyStr t}", b :: xs)
  | .dealloc p => ("dealloc", [p])
  | .tensorContract t a b batch contract =>
    (s!"tensor_contract.{tyStr t}.{pairsStr batch}.{pairsStr contract}", [a, b])
  | .tensorMap t args body =>
    (s!"tensor_map.{tyStr t}.[" ++ ";".intercalate (body.map mapNodeStr) ++ "]", args)
  | .tensorReduce t x op axes =>
    (s!"tensor_reduce.{reduceOpStr op}.{tyStr t}.{natsStr axes}", [x])
  | .tensorView t x params exprs shape index fill =>
    (s!"tensor_view.{tyStr t}.[" ++ ";".intercalate (exprs.map ixExprStr) ++
      s!"].{natsStr shape}.{natsStr index}.{if fill.isSome then "1" else "-"}",
     x :: params ++ fill.toList)
  | .tensorGather t d coords => (s!"tensor_gather.{tyStr t}", d :: coords)
  | .tensorScatter t a x coords => (s!"tensor_scatter.{tyStr t}", a :: x :: coords)

def nats (xs : List Nat) : String := jlist (xs.map toString)

def tys (ts : List Ty) : String := jlist (ts.map (fun t => jstr (tyStr t)))

def nodeSummary (n : Node) : String :=
  let (name, ops) := instSummary n.inst
  jlist [jstr name, nats ops, nats n.results]

def blockSummary (b : Block) : String :=
  jlist [toString b.id, jlist (b.params.map (fun p => jlist [toString p.1, jstr (tyStr p.2)])),
    jlist (b.body.map nodeSummary)]

def moduleSummary (m : Module) : String :=
  "{\"tys\":" ++ jlist (m.funcTys.map (fun ft =>
      jlist [tys ft.params, tys ft.returns, if ft.vararg then "true" else "false"]))
  ++ ",\"structs\":" ++ jlist (m.structs.map (fun s =>
      jlist [toString s.id, tys s.fields]))
  ++ ",\"enums\":" ++ jlist (m.enums.map (fun e =>
      jlist [toString e.id, jlist (e.variants.map (fun v => tys v.fields)),
        jlist (e.discs.map (fun d => jstr (toString d))), jstr (intTyStr e.tag)]))
  ++ ",\"fns\":" ++ jlist (m.functions.map (fun f =>
      jlist [toString f.id, toString f.ty, toString f.entry, jlist (f.blocks.map blockSummary),
        jlist (f.name.map toString)]))
  ++ ",\"target\":" ++ (match m.target with
      | none => "null"
      | some t => jlist [nats t.triple, toString t.pointerSize,
          if t.bigEndian then "true" else "false",
          match t.abi with | none => "null" | some a => nats a,
          toString t.structPassing])
  ++ ",\"blobs\":" ++ jlist (m.blobs.map (fun b => jlist [nats b.1, nats b.2]))
  ++ "}"

def decodeVerdict (bytes : ByteArray) : String :=
  match decode (bytes.toList.map (·.toNat)) with
  | .ok m => "{\"decoded\":" ++ moduleSummary m ++ "}"
  | .error (.unsupported f) => "{\"unsupported\":" ++ jstr f ++ "}"
  | .error (.malformed msg) => "{\"error\":" ++ jstr s!"decode: {msg}" ++ "}"

def semrEvalMain (argv : List String) : IO UInt32 := do
  match argv with
  | ["--decode", dir, count] =>
    match count.toNat? with
    | some n =>
      for i in List.range n do
        IO.println (decodeVerdict (← IO.FS.readBinFile s!"{dir}/{i}.tmbc"))
      pure 0
    | none => IO.eprintln "--decode: count is not a number"; pure 2
  | ["--executed", blob, runs] =>
    let bytes ← IO.FS.readBinFile blob
    let m := decode (bytes.toList.map (·.toNat))
    let text ← IO.FS.readFile runs
    for line in (text.splitOn "\n").filter (fun l => !(l.all Char.isWhitespace)) do
      IO.println (executedLine m line)
    pure 0
  | [blob, runs] =>
    let bytes ← IO.FS.readBinFile blob
    let m := decode (bytes.toList.map (·.toNat))
    let text ← IO.FS.readFile runs
    for line in (text.splitOn "\n").filter (fun l => !(l.all Char.isWhitespace)) do
      IO.println (runLine m line)
    pure 0
  | _ =>
    IO.eprintln "usage: semr_eval [--executed] <module.tmbc> <runs.txt> | semr_eval --decode <dir> <n>"
    pure 2
