# Bool cells and canonical byte memory

This proof component relates individual SemR Boolean cells to the existing
`TrustIr.Memory` allocation metadata and byte images. It imports the actual
SemR definitions and canonical memory functions through local Lake dependencies.
There is no second memory interpreter.

The 25 explicit theorems establish allocation, initialization and update facts:

- `Fresh` says bytes at and above the allocation bump remain unwritten. Empty
  memory satisfies it, and allocation and in-bounds one-byte writes preserve it.
- A one-byte, alignment-one, zero-slack stack allocation has its actual fresh
  identity and poison image. Another allocation's lookup/image is preserved
  when its identity differs from the fresh identity.
- Defined Bool stores write their exact 0/1 image; poison stores restore an
  unwritten byte. Reading back and preserving another address use the canonical
  byte functions. Updating SemR's shared cell is observed by its actual lookup.
- Counterexamples retain an existing byte through allocation and show that the
  canonical Bool decoder accepts a nonzero byte other than one. Thus allocation
  layout alone cannot replace `Fresh`, and decoder acceptance cannot replace
  the typed Bool image invariant.

`CellAt` records a live one-byte allocation and its exact image. It does not
establish a global layout or derive distinct addresses from distinct logical
identities. The different-address premises are explicit. The results concern
raw memory operations; lifting them to checked instruction execution, permissions,
frame lifetime, nonescape, source/body quotation and complete row proofs remains
required. The canonical legacy 64-bit model uses unbounded natural addresses;
these statements do not establish finite-u64 exhaustion behavior. All original
1116 obligation rows and the 317 uncertified aggregate refusals remain unchanged.

Run the standing check with the repository's genuine Targo:

```sh
build-slot -- targo --unverified test --locked --offline \
  -p trust-ir-conformance --test semr_bool_memory
```

The existing `lean-exec-differential` registry includes this target. Its declared
reads cover the complete package, SemR, the canonical byte-proof import
closure and the legacy oracle import closure used by the cache regression.
The standard `TRUST_IR_REQUIRE_LEAN=1` gate setting makes a missing
compiler a failure. Lake selects the package's pinned Lean 4.30.0-rc2.

Direct mathematical checks are ordinary Lake commands:

```sh
lake build
lake env lean BoolMemoryAudit.lean
```

The audit inventories all 75 declarations, including generated/private ones,
refuses new axioms, opaque/unsafe/partial declarations and native-evaluation
premises, then replays every declaration through the same Lean kernel from the
component's external imports. It checks the resulting kernel declaration's type
and value, rather than an elaborator cache entry. The reported 60 theorem
declarations include generated auxiliaries; they are not 60 independent claims.

Independent Clean ReferenceKernel replay is implemented in Trust commit
`ec8098456e64f9e4c51128e68a6657e73e24dd03`. Actual qualification checked every
new declaration and its dependency cone, with zero refusals or new axioms.
Both wrong-initialization and wrong-stored-value proof attempts failed with
genuine kernel `TypeMismatch`; six rehashed malformed bindings and a changed
artifact snapshot also refused. The original shared SemR replay still passed.
This is checked mathematical component evidence, with no shipping certificate,
proof-grade or pin change.

The full IR landing gates still require successful verification of all 396
laws and the normal readiness rows. Their fresh 8ebc run retained 32 passing
leg records and two failing proof legs; none of those requirements is waived
by these component checks.

## Checked Bool accesses

`SemRBoolAccess` lifts the byte image relation to the actual canonical
`TrustIr.semLoad` and `TrustIr.semStore` computations. `PointerAt` requires
the pointer SSA operand to contain the exact base and allocation identity
recorded by `CellAt`. That exact live one-byte allocation discharges the
wrappers' natural-alignment and provenance-specific bounds checks. A store
also requires its source SSA operand to contain the specified Bool or the
one-byte partial poison image. No access-result premise is assumed.

The theorems give the exact monadic state/result, including Load's SSA
binding. Defined Bool loads support both plain and strict modes. Plain poison
loads/stores transport `[none]`; strict poison access produces the actual UB
error. Stores preserve `CellAt`, pointer/local bindings and the permission
map. The composed Store-then-Load computations return the defined Bool or
transported poison through the same pointer. These results use canonical
memory and monad functions throughout.

The refusal controls use real wrapper computations: a live but wrong
allocation identity refuses even with initialized bytes at the numerical
address; missing provenance, unknown/dead allocations and a wrong declared
alignment also refuse. Strict/plain poison controls and two false result
definitions support independent kernel TypeMismatch controls. The standing
native target builds and audits both modules, serializing Lake access to
avoid concurrent writers to the shared package outputs.

These are pointwise instruction facts under explicit SSA lookups and cell
metadata/image assumptions. They do not construct a globally related heap,
derive distinct addresses from different cell IDs, establish SSA allocator
freshness over execution, or prove frame lifetime, nonescape, source/body
quotation, finite-u64 exhaustion or a whole-program simulation. The current
canonical access wrappers do not read borrow permissions: preserving the
permission map is not a permission-validity theorem. The original 176-fixture
and 1116-row denominators, all 317 uncertified panic aggregates, and the full
396-law/normal landing requirements remain unchanged.

The direct audit is `lake env lean BoolAccessAudit.lean`. It checks every
module-owned declaration, generated/private ones included, against the same
safe/nonpartial/no-axiom/no-opaque and Ax0-only policy, and replays from the
module's external imports before comparing kernel types and values.

Qualification under physical Lean 4.30 and genuine coherent C6 Targo passed
both maintained native tests, zero failed/ignored/filtered (8.83s runtime;
191.04s cold total, 5.60GB maxRSS). The checked-access audit replays 411
declarations including private/generated auxiliaries; its 364 theorem
declarations include generated equations and are not independent claims.
Independent Clean ReferenceKernel replay also passed every declaration in
the 2344-constant dependency cone, with zero refusals, Ax0 only and unchanged
default resource limits. Both false result claims produced actual kernel
TypeMismatch, and malformed input bindings/snapshot mutation refused. These
component checks do not close any of the scope obligations above.

## Executed Bool allocation

`SemRBoolAlloca` connects the existing raw allocation facts to the actual
canonical `semAlloca` computation. Its postcondition includes the new memory,
owned permission, returned SSA identifier and exact provenance-bearing pointer.
It composes allocation with plain/strict loads to distinguish transported
poison from the actual strict-load UB result. Other cells, permissions and SSA
bindings require distinct identities; unchanged machine fields remain explicit.

The reused-SSA control retains a malformed state's occupied result slot. The
canonical allocator overwrites that slot, so preservation of every preexisting
SSA binding requires a separate freshness invariant. Setting an owned permission
is an observed map update, not a proof that accesses enforce borrow permissions.
Fresh bytes remain a premise for poison initialization. No global heap,
frame/lifetime, source, finite-address or whole-execution result follows here.

The standing native case builds `SemRBoolAlloca` and runs
`BoolAllocaAudit.lean`, which requires all 17 explicit theorem names and
inventories/replays generated declarations too. Physical Lean4.30 checked all
26 declarations (22 theorem declarations include generated auxiliaries).
The newly built immutable D8 Trust SDK compiled and ran the complete maintained
target: 3 passed, zero failed/ignored/filtered; 206.28s cold total, 5.39GB maxRSS.

Independent Clean ReferenceKernel replay, also built by D8, checked all 26
declarations in the 2459-constant cone: 2455 admitted names plus kernel-owned
quotient primitives, 2004 replay units, zero refusals, Ax0 only and unchanged
default limits. Both false claims produced actual TypeMismatch; six rehashed
malformed bindings and a changed owned snapshot refused. The poison negative
uses a checked closed specialization, so its Fresh proof is inside the replayed
cone and the negative compares distinct result values, not forall versus Eq.
The focused native replay passed 2/2 in 19.94s after its first dependency build.
Receipts are in the common Git directory under
`qualification/semr-bool-alloca-20261028`. These are mathematical component and
unverified engineering builds, not all-verification self-build or original-row
proof authority. The full landing/proof requirements remain unchanged.

## Whole private-Bool heap

`SemRBoolHeap` is a separate proof layer for arbitrary-length heaps containing
only private one-byte Bool allocations, starting from canonical empty memory.
It relates the actual SemR cell list and next-cell counter to the actual
canonical Memory allocation table, counters and byte images. No allocation or
store evaluator is introduced. The structural relation records the complete
descending range of cell IDs and their one-byte placements; its preservation
under canonical allocation derives the placement from Memory.alloc. Both cell
and allocation identity uniqueness, address injection, bounds and disjointness
are consequences of those structural facts. Stores do not take disjointness
or in-bounds-write conclusions as separate assumptions.

Defined and poison stores use SemR.putCell and canonical byte writes, preserve
every mapped image and Fresh, and compose with the existing checked semStore
results. Actual findCell is related to exact cell membership, and the next
allocation's identity guard follows from the complete ID range. Duplicate IDs
cannot satisfy the relation. A two-allocation canonical-memory control writes
the first cell and requires both its defined readback and the second cell's
poison readback. Both addresses come from the actual allocation results, so
a missing write or reused placement cannot pass by leaving a fixed byte alone.

This is the private-Bool-only region grown without intervening foreign or
non-Bool allocations and without deallocation. The relation does not constrain
unallocated bytes below canonical empty memory's reserved frontier. It does not
prove arbitrary-layout heaps, frame/lifetime/nonescape, permission validity,
execution-wide SSA freshness, source/body quotation, finite-u64 exhaustion or
whole execution. Canonical semAlloca's pointwise wrapper is a separate component;
this layer proves raw allocation and mapping preservation. All original proof
refusals and 176/1116 denominators remain unchanged.

The maintained `semr_bool_memory` target includes a distinct heap component
check. `BoolHeapAudit.lean` inventories and kernel-replays every module-owned
declaration using the existing safe/nonpartial/no-axiom/no-opaque and Ax0-only
policy, with generated/private declarations included. Preparation waited until
the SDK publisher released exclusive admission and held its first normal
post-install slot. Physical Lean4.30 builds the component, and its complete
audit replays all58 declarations (46 theorem declarations include generated
auxiliaries). The maintained native target passes all3 checks, zero failed,
ignored or filtered:7.27s runtime,199.45s cold total,5.54GB maxRSS under normal
8GiB build-slot admission. Initial proof-bookkeeping failures are retained;
no theorem statement was weakened.

Independent Clean ReferenceKernel replay checks all58 declarations in the
2711-constant cone,2248units,zero refusals,Ax0 only and unchanged default
resource limits. Both false equality controls produce actual TypeMismatch;
malformed bindings and changed own snapshot also refuse. This is mathematical
component evidence. All original-row and whole-execution obligations above
remain required.

## Native toolchain cache isolation

The shared canonical semantics package retains `.lake/build` for its pinned
Lean 4.8 oracle. Other Lean versions build into a directory named by
`Lean.versionString` and `Lean.githash`. In particular, the 4.30 Bool proofs
must not replace the 4.8 generated C or introduce a `lib/lean` directory that
shadows Lean's namespace on a case-insensitive filesystem. The Lean sources,
compiler pins and theorem statements are unchanged.

The fifth standing native test builds and executes the 4.8 oracle, retains its
actual Memory OLean/C bytes, builds and loads the 4.30 Bool-memory component,
compares those retained bytes, then rebuilds and elaborates the actual 4.8
oracle root and executes signed scalar requests again. It performs no cleanup
between those operations. A warm executable alone cannot satisfy the import
load check. Use a version-aware native Lake frontend and both installed pins;
the test checks the actual selected versions.

An already mixed old `.lake/build` may need one normal pinned 4.8 `lake clean`
before rebuilding, or a fresh checkout/output tree. Isolation prevents future
mixing; it does not retroactively repair generated artifacts. The regression
uses the uninterrupted build order and does not hide mixing through cleanup.
This is native cache/build compatibility evidence, with no new proof authority
or change to the remaining full gate requirements.

## Frame build coverage and declaration replay

The pinned Lean4.30.0-rc2 package now builds all eight frame components through
`SemRFrameChecks`, which is a default target alongside the four Bool libraries.
`FrameAudit.lean` inventories and replays all 316 declarations (199 theorems) of
those eight components in fresh kernel environments containing only their
imports. Every component must be present and nonempty; named theorem witnesses,
standard-only axioms, exact replayed types/values and zero native evaluations are
checked. Unsafe, partial, opaque and axiom declarations are refused, including
private/generated declarations.

Run `lake build` and `lake env lean FrameAudit.lean` from this directory with
the compiler in `lean-toolchain`. A direct native Lake must match the pin;
the installed default on a host may be a different version. The standing
`semr_bool_memory` Rust test target now checks the full frame audit and invokes
`scripts/semr_frame_refusals.py`. Its ten actual Lean rejection cases cover
missing/duplicate components, omitted required owners, a missing theorem,
contaminated replay imports, and counterfeit axiom, opaque, unsafe, partial and
transitive-axiom declarations. Generated counterfeit inputs stay outside source
and supply no proof authority.

The earlier defect was real: at `7bf2831e2`, the four default Bool libraries
built but every optional frame library failed. The first stale references were
to `Memory.writeBytes.updateBytes`, removed by the compact-image memory change.
Frame preservation now uses the current public byte-store observation laws;
FP/LR raw-write correspondence relates byte observations, not equality of
compact storage trees. Raw and exact-effect store sequences use structural
folds with their original empty/head-tail equations proved by reflexivity,
removing the two generated unsafe recursion helpers caught by the new audit.

These are same-kernel mathematical component checks. Actual source-entry heap,
ABI/SP placement, machine instruction binding, callee/model agreement, lifetime,
full runtime refinement and independent Clean replay remain separate duties.
The historical frame descriptions are checkable again under the pinned compiler;
this does not supply their explicit compiler/caller premises or native authority.


## Unsigned division and remainder correspondence

`SemRUnsignedDivision` relates the actual `SemR.intBin .udiv` and
`TrustIr.semIntBinOp .UDiv` computations for every canonical unsigned operand
at every width and every integer postcondition. They return the same full
quotient and reject zero with the same UB reason. Even a continuation that
discards the result owes the nonzero divisor. This is an operator relation;
whole-body execution, memory, calls, source refinement and compiler-obligation
authority still require their own proofs.

`SemRUnsignedRemainder` relates the existing `.urem` and `.URem` operators on
the same full domains and arbitrary continuations. The canonical
`TrustIr.Proofs.UnsignedRemainderWp` theorem also states the actual U64 value
operation's success condition. Remainder shares the mandatory nonzero divisor;
an exact multiple returns zero, while a larger divisor retains the dividend.
These proofs introduce no new evaluator or production engine capability.

The core word-value lemmas have one definition in
`TrustIr.Proofs.BitVecUnsignedValues`; their existing public names and proof
bodies are retained. The canonical operator proof no longer imports an SMT
printer or solver bridge merely to use these mathematical facts.

```sh
lake build +SemRUnsignedDivisionChecks:olean
lake env lean UnsignedDivisionAudit.lean
lake build +SemRUnsignedRemainderChecks:olean
lake env lean UnsignedRemainderAudit.lean
```

These explicit targets check both full-range mathematics and the U8/U32/U64
value boundaries, zero divisor, false quotient and false postcondition controls.
The audit replays every declaration of the new relation and control modules
above only their external imports, refuses new axioms/unsafe/partial/native
proofs and checks that the replayed types and values are unchanged. This is
Lean-kernel replay; independent Clean reference replay is not claimed here.
The remainder audit covers the canonical operator theorems, SemR relation and
all nine remainder controls, with a base that excludes every target declaration.
The canonical remainder proof also builds with the separate Lean 4.8 package:
`lake build TrustIr.Proofs.UnsignedRemainderWp` from `lean/trust_ir-semantics`.

## U64 scalar register transition

`SemRScalarStep` relates the actual `SemR.stepCore` U64 division node to
`TrustIr.GenericCoro.Prefix.evalBodyStep`, the production body layer anchored
by the existing `stepNWithContext_succ_layer` definitional equality. The node
at the original program counter, both exact SSA operand lookups, canonical
U64 ranges and the original destination declaration check are explicit.
The theorem computes both full post-states, including the source program
counter and the target's private temporary publication/retirement. Its
success-and-arbitrary-continuation equivalence retains nonzero division even
when the continuation ignores the quotient.

`RegistersAgree` is the U64/Bool scalar register view, not a full value or heap
embedding. Register preservation additionally owes absence of the canonical
fresh temporary before the step. The controls exhibit initially agreeing
registers whose occupied temporary is lost, so this premise cannot be erased.
The actual reachable-state freshness invariant still needs discharge when
composing a complete body translation. Destination/input aliases and a
destination equal to the temporary remain supported. No caller, CFG, return,
memory, original-artifact or source/ABI refinement is established here.
No compiler evidence or proof grade is issued.

Run `lake build SemRScalarStepChecks` and `lake env lean ScalarStepAudit.lean`
with the package's pinned Lean. The audit replays only this component's new
source and controls above the existing imports, checks every declaration's
actual type/body and allows only the three foundational axioms. It does not
replay the unchanged canonical or SemR proof libraries.

`SemRScalarFreshStep` adds
`SemR.CanonicalScalarStep.division_step_fresh_registers_iff` discharges the one-slot premise using
the canonical `TrustIr.SSAFreshFrames.FreshState` high-water invariant.
`cleared_fresh`, `publish_fresh` and the existing `SSAFreshStep` / body-layer
preservation laws own that invariant. The scalar view intentionally erases
unmapped source values; relating complete source states and complete bodies
remains separate. `ScalarFreshStepAudit.lean` checks only this derived theorem
above the already checked scalar facts and canonical freshness owner.

## Complete U64 division/return function

`SemRScalarReturn.function_wp_iff` (in namespace
`SemR.CanonicalScalarReturn`) covers the actual `SemR.runFunction` and
`TrustIr.evalFunctionInContext` entry points. Both original functions have two
U64 parameters, a U64 return and the exact SSA interface 0/1 -> 2. The source
function, signature and entry block lookups, target layout, canonical function
and CFG lookups, destination declaration and absent typed ABI descriptor are
explicit. Real signature/arity, parameter, poison, nominal-lane and return
checks remain in both executions. The U64 nominal-lane fact belongs to the
existing `FunctionItemPresence.Prepared` owner; no replacement predicate is
introduced. Canonical SSA freshness follows from its existing checked block
parameter binding theorem, rather than an assumed successful entry.

For every canonical U64 argument pair, every source call-depth budget and every
canonical context/call-depth budget, source instruction fuel `extra + 2` and
canonical block fuel `fuel + 1` suffice for this complete call-free function.
Both return the same full quotient. Success and an arbitrary postcondition on
both returned value lists hold exactly when the divisor is nonzero and that
postcondition holds of those values. Zero remains UB before the return,
including a changed return that discards the quotient.

The 14 named controls execute both real entry points and cover maximum U64,
zero, a changed return operand, a wrong result destination, false postcondition,
missing signature, wrong arity, wrong function identity and insufficient fuel.
The canonical controls reuse admitted step and entry facts instead of expanding
the whole evaluator. The unchanged return/entry normalization definitions and
proofs have single shared owners in `ReturnBlockLayer` and `FunctionEntryLayer`;
existing AY replay users retain the same public names.

Run `lake build +SemRScalarReturnChecks:olean` and
`lake env lean ScalarReturnAudit.lean`. The audit replays this component and
both moved leaves above their original external imports, checks every type and
body and refuses new axioms/unsafe/partial/native proof evaluations. The two
legacy AY consumers also build under the separate pinned Lean 4.8 package.
This is a checked function-schema correspondence with the stated exact body
and SSA interface. Arbitrary CFGs, loops, calls, heap effects, renaming, binary
decoder correspondence, full original-artifact identity and source/ABI or
compiler certification remain separate; no proof grade is promoted here.

## Retained flat layouts and declared division

`SemRStructLayout` translates the original flat scalar declaration, including
its UTF-8 names, offsets, size and alignment, to the existing
`TrustIr.SourceLayout` service. Geometry and contextual errors come from that
service. Retention does not enable pointer, nominal, nonflat or aggregate
memory operations, and incomplete metadata is not repaired.

`SemRDeclaredDivisionReturn.function_wp_iff` covers the one-input U64 function
`Const 1; UDiv 1,d; Return` through actual `SemR.runFunction` and canonical
`evalFunctionInContext` entry and return. Both argument checks, canonical
`FreshState`, every instruction, the mandatory nonzero divisor and arbitrary
paired return postconditions remain part of the statement. The fuel offset
counts three SemR instructions and one canonical block. The complete source
module, including the retained layout declaration, is a parameter.

Run `lake build +SemRDeclaredDivisionChecks:olean` and
`lake env lean DeclaredDivisionAudit.lean` for the focused controls and
same-kernel declaration replay. This is an execution correspondence for the
stated scalar body. It does not check integer-text entry predicates through
the Boolean-only guarded consumer, establish a source/ABI translation, or
change any proof grade. General calls, loops and memory still need their
compositional correspondence and original contract duties.


`SemRDeclaredDivisionPacket` instantiates that theorem using the original
`division_question("d != 0")` capture. The complete packet fixture preserves
public/native identity, declarations, both original formulas, the actual
same-derivation VC/witness and result. Its binary module is decoded by SemR;
its unchanged module JSON is decoded and prepared by the existing canonical
owner. Both concrete entry/body shapes are checked before applying the
function theorem. The canonical constant decoder exposes one transparent
original layer on the pinned modern proof compiler, following its existing
type-layer interface; recursive runtime children retain the original callback
and refusal rules. The legacy 4.8 executable oracle uses that same grammar
through its original partial public parser boundary. It does not export the
modern public-constant theorem cohort and supplies no packet-proof authority.
Physical struct options use their fixed eight-byte wire format; instruction
alignments retain their separate varint reader.
