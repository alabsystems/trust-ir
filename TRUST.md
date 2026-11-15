# The Trust Toolchain Trusted Base

**Status:** Ratified (2026-06-13). This document is canonical. It states what
the correctness of a Trust-produced artifact rests on, and — equally important —
what it does **not**. Other repo documents link here instead of restating
folklore.

Boundary closures were driven by **Program CK1** (an internal confluent-kernel
design document, with an internal program ledger). That ledger
(`docs/PROGRAM-CK1.md`, internal) is **dormant — its last row is
dated 2026-07-11** — so CK1 should not be cited as the currently active program;
its gates remain wired in code and CI. The live, itemized tracker is
the internal roadmap ledger (`docs/roadmap/README.md`). The rule this document sets
is unchanged either way: closure claims land as reviewed edits to *this*
document, adversarially checked against the mechanization; boundaries are
restated or deleted here, never silently dropped elsewhere.

## Trusted base

The executable Lean oracle also has an explicitly unproved implementation
boundary. `TrustIrRuntime` supplies pointer-identity cache bodies through fifteen
safe structural interfaces. `TrustIrNativeLink` attaches and initializes that
native library without importing its unsafe declarations into mathematical
modules. The schema2 runtime ledger retains all41 historical runtime obligations,
15 interface correspondence obligations and3 additional initialization/linking/
evaluation support obligations as UNPROVED. Native differentials, ABI and lifecycle
controls are engineering evidence; kernel replay does not verify these implementations.

The Trust toolchain's correctness rests on exactly this trusted base:

1. **The Lean 4 kernel.**
2. **`ay_sound_unsat`** (`lean/trust_ir-semantics/TrustIr/Proofs/AYBridge.lean`):
   every `ay` UNSAT verdict is sound. This is the one first-party axiom; it is
   the documented SMT-solver soundness boundary.
3. **The trust-ir → Lean semantics correspondence**: the Lean operational
   semantics faithfully models the TrustIr that TrustCg consumes. This is a
   *known gap* wherever the Lean model lags the Rust reference interpreter — see
   the ratified UB/numerics policy §7 (numerics) and the B3 schema-parity gate. The
   gap is tracked, not hidden: the Rust reference interpreter is locked by tests
   (`crates/trust-ir-build/tests/numerics_policy.rs`), and the Lean side is
   specified pending reconciliation.
4. **The `trust-ir` validator** (`trust-ir-build::validate_module`): a module
   admitted by the validator is well-formed in the senses the validator checks
   (type-correctness of every instruction, SSA + dominance, CFG/terminator
   structure, ABI/entry-signature agreement, proof-obligation integrity,
   memory-effect attributes on defined bodies and borrow structure — see
   "Borrow discipline and memory-effect attributes" below).
5. **For self-hosted binaries only**: the bootstrap argument (diverse
   double-compilation and/or independent re-check) and the closure of the
   `ProofLineageNode` chain with zero `Trusted(...)` rungs.

Everything **outside** this list — including the `rustc`/LLVM that built the
first checker — is **not** trusted: its output is independently re-checkable
from the proof certificates. Items 6–14 below are the enumerated residual
assumptions behind specific certificate families, the v43 runtime-handle
boundary, the cross-crate link boundary, the contract-clause certificates,
borrow liveness, the pinned RC runtime and the island statement grounder; each
is stated once, here.

### Backend certificate boundaries (Clean producer, t-silicon route 1)

The Clean producer carries two kinds of `ck0`-kernel-rechecked certificate.
Both re-run `clean_kernel::check_type` with `axiom_deps ⊆ FOUNDATIONAL_AXIOMS`
(the `KERNEL_ANCHOR_CLEAN_BACKEND_TV` and `KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`
anchors in `crates/trust-ir-build/src/validate.rs`), so what the *kernel*
decides adds nothing to the trusted base above. Each carries **one** named
residual assumption, stated here so it is tracked, not hidden:

6. **Backend translation-validation denotation maps** (source → trust-ir): the
   `clean-reflect` maps that reflect an emitted trust-ir function and the source
   Clean `Expr` into one shared `Nat`-mod-`2^w` vocabulary are *checker spec*
   (the Fragment-1 discipline). The kernel decides the resulting equation
   `reflected ≐ original`; that the two maps compute the source/emitted meanings
   is the assumption. A miscompile of a body's own arithmetic, control flow,
   heap traffic or call arguments within the covered fragment IS caught (the
   kernel refuses the equation) — the maps' own in-kernel mechanization is the
   open deepening. The distinct readonly-call-family adapter uses the existing
   total ByteV1 load operation, including its memory and failure result, rather
   than adding a memory evaluator. Its source equation is over the entire
   context/memory/address function for the exact admitted load/forward-call
   shapes; correctness of that Rust shape-to-denotation adapter remains this
   same denotation-map boundary. It grants no initialized storage, caller
   execution, physical borrow or native permission. One Fragment-4 fact is NOT in the equation: the heap
   release. Each `HeapAlloc(CleanHeap)` result must be released by exactly one
   `Release` of its own result value, a `Dealloc` of such a cell is refused as
   a wrong emission (it is undefined behaviour: in the reference interpreter
   for every such cell, in the Lean model only for a scalar-typed one — every
   Fragment-4 cell measured, in trust-ir's and in the Clean minter's heap
   fixtures, is a struct or array, which Lean refuses as `unsupported.layout`,
   so for it the interpreter alone decides), and
   a `Release` of any other value is neither counted nor refused. That is a
   STRUCTURAL gate (`alloc_release_balance`) beside the kernel judgment —
   test-class evidence, not a kernel verdict.

   *The checker spec, as widened by WS1.15 (S1–S5).* Every fragment value has
   a sort: a `U8..U64` / `I8..I64` machine integer is its bit pattern in
   `[0, 2^w)` (a signed value is two's complement over `Nat` mod `2^w`; its
   sign is read only by the signed comparisons, through the bias
   `(x + 2^(w-1)) mod 2^w`), a `Bool` is the kernel `Bool` (the one Bool
   spelling, decision DG-34), and a fieldless-enum parameter is its
   discriminant tag. The maps are: `Add`/`Sub`/`Mul` → `Nat.add`/`Nat.sub`
   (wrapping)/`Nat.mul` under `Nat.mod 2^w`; `And`/`Or`/`Xor` →
   `Nat.land`/`Nat.lor`/`Nat.xor` (at `Bool`: `Bool.and`/`Bool.or`/`Bool.xor`);
   `UDiv`/`URem` → `Nat.div`/`Nat.mod`, admitted only with a divisor that is a
   nonzero constant or is nonzero by a dominating `CondBr` on `icmp eq/ne b 0`
   (an eager `select`-guarded division is refused: division by zero is UB);
   `Shl`/`LShr` → `Nat.mul a (Nat.pow 2 k)` under `Nat.mod 2^w` /
   `Nat.div a (Nat.pow 2 k)` (spelled through `Nat.pow` because the pinned
   prelude's `Nat.shiftRight` is an axiom the rooted audit refuses), admitted
   only with an amount that is a constant below `w` or `urem x, w`;
   `Ult`/`Ule`/`Eq` → `Nat.blt`/`Nat.ble`/`Nat.beq`, `Ne` → `Bool.not (Nat.beq)`,
   `Slt`/`Sle` → the biased `blt`/`ble` (`Ugt`/`Uge`/`Sgt`/`Sge` by argument
   swap); `Select` and a `CondBr` diamond → `Bool.rec` at the result sort; an
   entry `Switch` → the nested `if Nat.beq v k_i` in case order (distinct case
   values), whose dead `[Unreachable]` default is admitted only when the
   selector is a fieldless enum's tag lane and the cases are exactly its
   discriminants (the last case is then the `else`); `ZExt`/`Trunc` →
   `Nat.mod 2^w'` at the destination width. A Fragment-4 `GEP` index folds
   only from a closed NON-NEGATIVE literal (a negative signed index is UB in
   the reference semantics and is refused, never folded to a cell).
   `U128`/`Usize`, `SDiv`/`SRem`/`AShr`, `SExt`, and everything else stay
   outside and are refused by name.
   The theorem quantifies over all of `Nat`; the maps agree with the machine
   semantics on in-range inputs. The statement also binds the CARRIER: an
   `I<w>` parameter or result is stated at the signed carrier alias
   `CleanTV.Int<w> : Type := Nat` (a reducible definition installed beside
   the heap vocabulary — the kernel unfolds it, so the value vocabulary is
   still `Nat` mod `2^w`), and a comparand must spell that alias exactly
   where the emitted signature's PARAMETER is signed and `Nat` where it is
   unsigned. A retype that changes a width is refused by the kernel (the wrap
   moduli differ); one that changes only the signedness label of sign-agnostic
   operations (`u32` → `i32` around `Add`/`Mul`, which changes no bit) is
   refused by name, because the kernel alone could not tell the relabelled
   emission from its source; one that changes a comparison's signedness is
   refused by the kernel. **Honest scope of that carrier check:** it binds the
   PARAMETER positions only. The comparand carries one binder per parameter
   and nothing for the RESULT, and `CleanTV.Int<w>` is definitionally `Nat`,
   so a tamper that relabels only the result's signedness (`-> u32` becoming
   `-> i32`, no bit changed) still checks — a TRUE equation that does not
   re-earn the emitted RESULT signature against the source one. Closing it
   needs the producer to record the result carrier as well (a clean-side
   companion). By the same token a fieldless-enum parameter denotes at `Nat`,
   so it shares one comparand telescope with the bare unsigned tag of its
   width. Both boundaries are pinned by
   `crates/trust-ir-build/tests/tv_fragment_widening.rs`.

   *What binds a call.* The equation is parametric in its callees (each call is
   an anonymous `∀`-bound symbol), so it says nothing about which function a
   call reaches. The validator binds that separately: each call edge ↔ exactly
   one `InheritedFromCallee` row on the caller's obligation ↔ the callee's own
   kernel-rechecked TV obligation, over an acyclic composition graph. A call
   retargeted after certification (row left alone) is refused, and a callee
   with no TV of its own leaves its caller uncertifiable. Two residuals are
   stated, not closed: a *consistent* edit that retargets the call AND rewrites
   the row to another honestly-certified callee of the same arity is accepted
   (the certificate records no callee list yet), and that the comparand is the
   Clean source definition is established at mint time only — a validator
   without the Clean source cannot re-derive it. The anchor is
   producer-agnostic: `Function.producer` is claim-style provenance and
   neither earns nor forfeits a TV certificate.

   *What binds the comparand to the source (WS1.13).* A certificate that
   carries an ISLAND (`CertificateBinding.environment`) is source-bound: the
   island's Clean declarations are installed into the anchor environment with
   the kernel's checked `add_decl`, and the comparand must be definitionally
   equal to the value of the island declaration `source.decl`. For such a
   certificate the mint-time residual above is closed down to item 14's
   statement: what the island declares IS the source. An island-free
   certificate keeps the mint-time meaning (refused under
   `ValidationConfig::with_source_bound_certificates(true)`), and an
   island-bound CALLER is refused until slice 2 binds each callee to its own
   island declaration.
7. **Lowering-miter encoding fidelity** (trust-ir → machine): the kernel
   certifies UNSAT of the bit-blast clause list, and the untrusted producer's
   gate-level provenance (`trust_ir::proof::satprov`) is *checked* — the clause
   list is confirmed to be exactly the Tseitin miter of the recorded gate DAG,
   sides compared bit-for-bit. The single residual assumption is
   **gate-DAG ⇔ `SmtExpr`**: that `blast(ir_expr)` / `blast(machine_expr)`
   compute the rule's actual source/machine semantics. Closing it is t-silicon
   route (b) (route ay's own audited bit-blaster through the same cert), scoped
   on the internal t-silicon one-TCB design.
   *Composed-claim scope note:* `verify_source_to_silicon` requires a P3 miter
   cert for every ALU node in `f`'s body (unrecognized nodes fail closed), but
   the two trivially-lowered node kinds — `Const{i8}` → immediate
   materialization and single-value `Return` → calling-convention — carry no
   miter cert by construction. So the composed "source ≐ machine" claim
   additionally trusts those two lowerings (same trust class as the fidelity
   assumption above, for two non-ALU node kinds). A soundness review
   (2026-07-05) found no code hole in the composition beyond this.

   **Measured 2026-09-18 — this item reads stronger than the mechanization
   admits.** Since 2026-07-12 a lowering-resolution artifact is `Pending` and
   never `Certified`. The kernel does re-check UNSAT of the clause list, but
   the clause list is PRODUCER-SELECTED and the validator does not itself
   derive the lowering rule's miter from TrustIr semantics, so it refuses to
   let that UNSAT certify a lowering, and `verify_source_to_silicon` answers
   `LoweringSemanticBindingUnavailable` for every such artifact. The fidelity
   assumption above is therefore not currently TRUSTED to close a claim — it
   is REFUSED, which is the more conservative posture. The sentences here and
   under interpretation (B) saying the trust-ir → machine step "is
   kernel-checked by the lowering-resolution certificate" describe the
   2026-07-05 design, not what a module can claim today; the tests that pin
   the refusal are named in the evidence table below.

### Island-theorem boundary (user theorems, `clean_island`)

A `Custom { namespace: "lean.theorem", name }` row is `Certified` only through
the `KERNEL_ANCHOR_CLEAN_ISLAND` re-check: the island the certificate carries
is installed into the `clean_backend_tv` anchor environment (digest recomputed
first, bounded canonical decode, redeclared names, names under a
validator-owned theorem root and axioms refused, every declaration
kernel-checked on insertion), the cited theorem passes the rooted
audit, and its type must be definitionally equal to the proposition the
pinned statement grounder derives from the row's own first-order formula. Every
island constant that proposition cites must be the `source.decl` of a function
whose TV certificate carries the same island and passed item 6's source check.
What the kernel decides adds nothing to the trusted base; one residual is
stated:

14. **The island statement grounder** (`trust_ir::clean_expr_lowering::island`)
    is *checker spec*, like item 6's denotation maps. It reads the slice-1
    grammar — one equation, optionally under a `forall` whose binders are
    `Bool` or `(_ BitVec W)`, over island constants (cited, like a binder,
    only by a simple symbol no SMT-LIB theory spells as a function symbol or
    reserves as a symbol family) and `Nat` / `Bool`
    literals — as a kernel proposition, and a `(_ BitVec W)` binder as a `Nat`
    binder. The kernel then proves the `Nat` statement, which is STRONGER than
    the bit-vector one for a universal binder (every `W`-bit pattern is a
    `Nat`), and a TV certificate states the emitted function for every `Nat`
    argument; an `Int` binder, where the direction flips, is refused. That the
    grounder's reading is the formula's intended meaning is the assumption. The
    island itself is the source: a producer that elaborates the island from a
    different text than it claims changes what the theorem is about, not
    whether the theorem holds of the emitted code — the chain proves the
    theorem of what the module runs. `SourceDefinitionRef.closure_digest`
    names the source text and is not re-derivable here.

### Concurrency boundary (atomics and data-race freedom)

The Lean operational semantics is **single-threaded**. `MachineState`
(`lean/trust_ir-semantics/TrustIr/State/MachineState.lean`) is locals, memory,
permissions, refcounts, a fresh-id counter, and a global-address cache — it
carries no thread identity, so there is no second thread for a memory ordering
to order against. That yields one further named assumption, stated here so the
boundary stays enumerated rather than folded into item 3:

8. **Single-threaded sequential consistency; `DataRaceFree` is a claim, not a
   check.** `semAtomicLoad` / `semAtomicStore` (`Semantics/Atomic.lean`)
   *validate* the `Ordering` and then **ignore** it — a `Relaxed` load and a
   `SeqCst` load step identically to `semLoad` — and `semFence _ordering =
   pure ()`, mechanized as `fence_is_noop` (`Proofs/AtomicProps.lean`). The
   Rust reference interpreter does not even validate: it matches the ordering
   away (`interpret.rs`, `Inst::AtomicLoad { ty, ptr, .. }`). Correspondingly
   the concurrency annotations `DataRaceFree` / `AtomicOrdering` /
   `AtomicSetInsert` have **no discharge path**: `trust-ir-ay` fails them
   closed ("concurrency annotations need a happens-before model beyond the
   BV/FP encoding"), so carrying one is trusting the producer. Any proof whose
   validity depends on distinguishing two memory orderings, or on
   `DataRaceFree` having been established, rests on this assumption.

   **Scope — what this does *not* say.** It is not a restriction on what
   compiles or runs. Threaded programs build and execute normally: atomics
   lower to real hardware atomic instructions carrying the ordering the
   producer declared, and every atomic access reports
   `Inst::has_observable_effects` at *every* ordering, so no pass on the
   contract surface may elide one. Nor does it weaken safe Rust: a safe-Rust
   program's data-race freedom is established by rustc's own type and borrow
   discipline, upstream of TrustIr, exactly as for vanilla Rust. What is
   unsound is a *proof* that leans on a distinction the model does not make.
   Lifting this — a weak-memory model with a real happens-before relation — is
   the "Phase 5" concurrency workstream on the internal panic-and-UB decision
   record; until it lands, the honest reading of an atomics proof is "correct
   on the sequentially-consistent, single-threaded interleaving". The
   ratified UB/numerics policy §5 states the same boundary normatively.

### Runtime-handle boundary (v43 `Ty::Handle`)

A value of a trusted runtime's opaque type — Trust's arbitrary-precision `Nat`
first — is spelled `Ty::Handle(HandleTy { name, runtime })` (binary v43): one
pointer word at the machine level, never equal to `Ptr`, and origin-pinned.
The validator admits as its only producers and consumers the bodyless
`External` C declarations it pins by link-time symbol
(`trust_ir_build::validate::TRUSTED_HANDLE_RUNTIMES`, v1 row
`("Nat", "trust_bignum::Nat")` with
`trust_bignum_nat_{from_u64,add,sub,is_zero,drop}` — `drop` being the release
entry point, the one pinned entry that consumes a handle without producing
one), refuses every other origin and every non-transport use, and guards the
pinned symbol namespace on every module in all three spellings of a symbol
(`Function.name`, `Global.name`, `Constant::SymbolAddr`). What the validator
decides adds nothing to the trusted base; what it cannot decide is one row:

9. **The pinned handle runtimes.** Three things are trusted and are not
   re-checkable from any certificate: (a) the pin table itself — that the
   `(name, runtime)` pairs and the exact entry-point signatures in
   `TRUSTED_HANDLE_RUNTIMES` are the runtime's real ABI; (b) each shim
   the row names — `trust_bignum_nat_add` and its siblings, `#[no_mangle]
   extern "C"` functions in `trust-bignum` (in the Trust repo), compiled by
   the ordinary Rust toolchain outside the trust-ir lane and bound by the
   linker — is faithful to the Rust method it wraps; and (c) **handle
   LIFETIME: that every handle passed to a pinned entry point is live, and
   that the pinned release entry point (`trust_bignum_nat_drop`) is called at
   most once per allocation.** (c) is a validator NON-guarantee, stated here
   rather than implied: a handle is an opaque one-pointer word with no IR
   provenance, and §7's ratified transport set admits `Copy` and `Select`, so
   handle values are deliberately non-linear and two SSA values may denote one
   runtime allocation. Widening that set to register-level struct, tuple and
   enum LANES (the ratified aggregate amendment) does not narrow (c) either:
   an aggregate carrying a handle is copied, selected and passed like any
   other value, so a handle may now be duplicated by copying its CONTAINER as
   well as itself. The lane rules decide ORIGIN and lane TYPE — a lane is
   seeded only from an exactly-typed handle operand, read back only at that
   type, and an enum payload only under the tag switch that selects its
   variant — never liveness. Spilling a handle to a SEALED stack slot (the
   ratified memory amendment, WS3.7) does not narrow it either: a reload
   yields the stored handle again, so a slot is one more way to hold a second
   copy. The slot rule decides only that the word read back is exactly a
   handle some exact-typed store wrote — never whether it is still live — and
   it decides that over the slot pointer's own def-use graph: a wild write
   into the slot's bytes through a pointer NOT derived from it (an `IntToPtr`
   of a guessed address) is outside what it sees (internal spec ratifications
   §7, the amendment's boundary (3)), and the run-time half that would make
   such a forged reload fault is not built yet.
   A module that releases the same handle twice, or uses
   one after releasing it, VALIDATES — `validate_module` makes no liveness
   claim about a handle, and two tests pin that non-guarantee so it cannot be
   misread as a guarantee. Deciding it would need a linear discipline over
   handle values plus a per-parameter "consumes" contract the format does not
   have, and even then a release inside a callee is invisible to an
   intraprocedural rule; the runtime and the producer own it, exactly as a C
   caller owns `free`. What the validator DOES decide is that release happens
   through the pinned symbol or not at all: `Retain`/`Release`/`IsUnique`/
   `Dealloc`/`HeapAlloc` at a handle type are refused by name
   (`InvalidHandleUse`), an off-pin release declaration is
   `HandleEntryPointSignatureMismatch`, and a second release-shaped symbol is
   `HandleForeignDeclaration`. The pin table itself carries the singularity
   the sentence above needs: `HandleRegistry::from_pins` refuses a row with
   two consuming entry points (`HandlePinError::MultipleReleaseEntries`), so
   "the pinned release entry point" is one symbol by construction.

   **The release shim now EXISTS, and the release half of item 9 is an
   assumption about auditable code.** Measured 2026-09-18 in the Trust repo
   <!-- enforcement-links: external crates/trust-bignum/src/handle_abi.rs (the Trust repo) -->
   (`crates/trust-bignum/src/handle_abi.rs`, landed at `78f64c500e`): it exports
   five `#[unsafe(no_mangle)]` items — `from_u64`, `add`, `sub`, `is_zero` and
   `trust_bignum_nat_drop` — so every pinned symbol in the Nat row resolves at
   link time. This paragraph previously recorded the opposite, and the state it
   described was deliberate: the pin row landed FIRST (pinning it is what
   retires the correct-by-LEAK reading of §7), so for one day a module that
   called the release entry point VALIDATED here and then FAILED TO LINK — the
   loud state the other four symbols passed through, never a silent
   mis-execution. That gap is closed; what (b) and (c) trust is now the shim's
   one-line body (`Box::from_raw` + drop, behind a null check) rather than code
   that does not exist.

   **What no check establishes, and the runtime therefore owns.** Nothing in
   TrustIr or TrustCg detects a DOUBLE release or a USE AFTER release of a
   handle, and §7 says so rather than implying otherwise: a handle is an opaque
   one-pointer word with no IR provenance, and the ratified transport set
   admits `Copy` and `Select`, so two SSA values may denote one allocation by
   construction. A linear discipline would need both a non-`Copy` handle and a
   per-parameter consumes contract the format does not have, and even then a
   release inside a callee is invisible to any intraprocedural rule. The
   trusted base is one row larger; it is not one guarantee stronger.
   What DOES exist since WS3.22 (F-060) is the first EXECUTABLE witness of
   (c), and it is host-assisted, never a validator claim: the release entry
   points of the pinned runtimes are named in one place,
   `trust_ir_build::pinned_release_entry_points()` (`trust_bignum_nat_drop`
   for this row, `clean_dec` for item 13's, derived from the two tables), and
   the reference host model `PinnedHandleHost` decides that a call is a free
   by that table alone and marks the released handle dead
   (`HostState::release_handle`), so a double `drop` or a use after `drop`
   faults in the reference interpreter as `UndefinedBehavior`, while a no-op
   mutant of the model cannot see it. That run reports `host_calls > 0`: it
   is evidence about the model, not about the module, and `Inst::Dealloc` —
   which cannot state a free — is not widened.

   **The kernel-surface rows (WS3.2, 2026-09-18) — fourteen new instances
   of (b).** The Nat row also pins the Clean kernel's native `Nat` surface:
   `trust_bignum_nat_mul`, `_div`, `_mod` (wraps `Nat::rem`), `_beq`, `_ble`,
   `_fits_u64`, `_to_u64` (checked — ABORTS when the value does not fit,
   never wraps), `_clone`, `_land`, `_lor`, `_xor`, `_shift_left`,
   `_shift_right` and `_pow`. For these, (b) is stronger than "faithful to the
   Rust method": each shim must EQUAL the Clean kernel's native reducer for
   the Lean operation it names (`n / 0 = 0`, `n % 0 = n`, truncating `sub`,
   bitwise `xor`), because a kernel-`Certified` proof about `Nat.div` is a
   proof about the kernel's `div`. A shim that drifts yields a WRONG BINARY
   under a `Certified` verdict, and nothing in TrustIr or TrustCg can see it —
   the Lean-vs-kernel differential over `trust-bignum`
   <!-- enforcement-links: external crates/trust-bignum/tests/kernel_differential.rs (the Trust repo) -->
   (`crates/trust-bignum/tests/kernel_differential.rs`, in the Trust repo) is the only guard, so it is part of this row, not an
   optional extra. Measured 2026-09-18 (Trust `d9ea36f376`): none of the
   fourteen is exported yet, so a module calling one VALIDATES here and FAILS
   TO LINK — the same loud state `drop` passed through, never a silent
   mis-execution. `cmp`, a wrapping `to_u64_wrapping` and a Lean `Int` row are
   deliberately not pinned (internal spec ratifications §7).

   **One carrier (WS3.4, 2026-09-20) — and the spelling the validator cannot
   see.** A value of a pinned runtime's type crosses every producer boundary
   as `Ty::Handle` and nothing else, and `trust_bignum` is the one runtime
   whose `Nat` crosses a boundary. The validator enforces the half it can:
   a handle-bearing module that also DEFINES the runtime's type structurally
   (a `StructDef`/`EnumDef`/`RecordDef` named `trust_bignum::Nat`, the shape
   the Rust producer emitted) is refused
   (`HandleRuntimeSpelledStructurally`). The other half is a producer
   obligation with NO in-format witness: a `Nat` object spelled as a bare
   `Ptr` (the Clean general lane's boxed object, or Clean's own second
   bignum runtime `clean_nat_big`) names no type, so nothing here can tell it
   from any other pointer. Such a value cannot be passed where a handle is
   expected (`Ptr != Handle`), but it can be computed with, returned and
   stored beside the handle unrefused. That a producer converts or refuses
   it at the boundary is trusted, not checked.

   A handle-bearing module's correctness rests on (a)-(c); no
   proof obligation states any of them, the reference interpreter executes a
   handle only HOST-ASSISTED — through an installed host model of the runtime,
   which is itself a trusted model of it, never evidence for (a)-(c) (such a
   run reports `host_calls > 0`; without a host the call is refused as
   unsupported) — `bridge.rs` places handle modules outside the proven subset,
   and the Lean model gives `Ty.Handle` a width but no semantics.

   **The reference model of this runtime (WS2.13, 2026-09-19).**
   `trust_ir_build::host::PinnedHandleHost` is a REFERENCE MODEL OF A TRUSTED
   RUNTIME: a second, independent statement of what the nineteen pinned
   `trust_bignum_nat_*` shims do, written from the pin table's documented
   Lean semantics over a dependency-free `Vec<u64>` magnitude (truncating
   `sub`, `n / 0 = 0`, `n % 0 = n`, `to_u64` aborts above `u64::MAX`), keyed
   by the same table and served only under the exact pinned signature. A run
   that used it (`Interpreter::with_host`, `trust-ir run --host pinned`) is
   HOST-ASSISTED EVIDENCE — evidence about the model's reading of the runtime,
   reported as such by the interpreter's own `host_calls` count — and NOT
   in-format execution; it establishes nothing about (a) or (b), and a
   disagreement between the model and `trust-bignum` is a bug in one of them,
   found only by a differential, never averaged. The one thing the model
   observes that the runtime cannot is (c): its handles live in the
   interpreter's per-execution host state, so under the model a double
   release or a use after release is `UndefinedBehavior` by name. That is the
   residue surfacing at run time under a trusted model; it is not a validator
   guarantee and does not narrow (c). The
   module that DEFINES a pinned symbol is refused by the validator
   (`HandleEntryPointDefinedLocally`), deliberately: the runtime is linked
   trusted base, never a validated module. Each additional pin row, and each
   additional entry point, is a new instance of this item and lands as an edit
   here. Ratified in the internal spec ratifications §7.

### Cross-crate link boundary (import authentication)

A call into a dependency's handle-typed function (an import-backed handle
declaration, WS3.3) crosses the same boundary and no other: the linked walk
binds the importer's declaration to a dependency DEFINITION it validated, and
the import digest authenticates that dependency MODULE — not the object file
the linker binds the symbol to later. That the linked object was compiled from
the authenticated module is the same premise every cross-crate import rests on.

A cross-crate proof — a `proved` summary `backed_by` another module, or an
`InheritedFromCallee { external: Some }` certificate — is re-earned against
the authenticated dependency module, and it is about ONE far body. The import
verifier refuses a site on either end of the edge whose linkage lets the
linker bind a different definition (`Weak`, `LinkOnce`) or none at all
(`ExternalWeak`). What it cannot decide is one row:

10. **The one-definition-rule premise for ODR far sites.** A far function
    spelled `WeakOdr`, `LinkOnceOdr` or `AvailableExternally` backs a
    cross-crate proof on the premise that every copy the linker may select is
    the same definition — which is how Rust generic instances link. Nothing
    re-checks that the copy actually linked is the one proved. Dynamic symbol
    preemption (an `External` symbol interposed at load time, e.g. by
    `LD_PRELOAD` or a later shared object) is likewise outside the claim: a
    cross-crate proof speaks about the statically linked image.

### Contract-clause certificate boundary (the free-name nonneg clause)

A directive-less `CleanCic` contract certificate is re-checked in-process
against a goal the validator re-grounds from the obligation
(`trust_ir::clean_expr_lowering::contract`). For literal-only clauses the goal
is a closed Bool decision over `Nat` literals and nothing beyond the kernel is
assumed. The one clause over a free NAME — `(>= s 0)` / `(<= 0 s)` — grounds to
the closed proposition `∀ x : Nat, Nat.ble 0 x = true`, which quantifies over
`Nat` and discards `s`. That proposition is the clause's denotation only if `s`
IS a Nat-valued IR place, so it is produced only with the module in scope
(`contract_goal_in`, the `ModuleCleanCicRechecker` impl, the native-bundle
authority) and only after `bind_nat_nonneg` has checked: a contract kind; `s`
an SMT simple symbol and the clause's only free name; an owning function that
resolves uniquely with a resolvable `FuncTy`; exactly one binding, naming `s`;
a `Param` / `ResultSlot` / `MutParamExit` / `ParamPointeeEntry` place
(`&mut T` / `*mut T` exit; `&T` / `&mut T` value at entry, v62)
whose IR type is `u8`..`u128`, or `usize` under a `target_info`; and sort
`Int`. Before this check (finding F-001, closed by WS1.1) the clause TEXT alone
certified, so `fn f() -> i64 { -1 }` with `ensures (>= result 0)` reached
`Certified`. The contract analogue of item 6:

11. **Contract-clause denotation.** Two residuals, stated so they stay
    tracked:
    (a) *the nonneg denotation lemma* — "the `Int` value of an unsigned w-bit
    IR place is a `Nat`". The kernel decides `Nat.ble 0 x = true`; that the
    bound place's value, read at sort `Int`, lies in `Nat` is the assumption
    (it is the definition of an unsigned integer, but no certificate states
    it). The certificate LINEAGE binds the clause bindings
    (`clean_cic_lineage_digest`); `bind_nat_nonneg` binds the `FuncTy` side,
    which lineage cannot see. A bit-vector nonneg shape (`bvuge`) and a
    `Ty::Handle` Nat place are refused, not assumed.
    (b) *`ProofRef` backing is attribution, not entailment.* A `ProofRef`
    backs a safety-class claim (`DivNonZero`, `InBounds`, `NoPanic`, …) only
    with a row of that claim's own obligation kind (or a specific kind that
    covers its category — `MemorySafety`, `PanicFreedom`, `ArithmeticSafety`,
    `BoundsCheck`, and since WS1.9 `Termination` for `Terminates` and
    `Ownership` for `DataRaceFree` and the borrow / aliasing claims), and a
    node-level `ProofRef` only with a row sited
    on that very node. A category-ambiguous kind (`Precondition`,
    `Postcondition`, `LoopInvariant`, `TypeInvariant`, `RefinementType`,
    `TranslationValidation`, `TemporalSafety`, `Liveness`) still backs
    `Custom` claims and claims with no obligation kind (`Pure`,
    `Deterministic`, the memory-role / parallel / divergence hints,
    `ValueRange`, `KnownBits`) at function level — and nothing checks that
    its formula entails that claim, so such a backing is attribution only. No
    gate reads it: the GPU/ANE gates read the bare claim. Even a correctly
    kinded and sited row's formula is not compared with the claim's canonical
    formula. That residual is latent today — no kernel anchor certifies
    `ArithmeticSafety`, and a capability-replayed `Discharged` row is never
    `ProofRef` currency (only the kernel tier is) — and it opens the moment
    either changes; the formula-level link is the planned follow-up.

### Borrow discipline and memory-effect attributes

Two surfaces were claim-style until WS2.7; their cheap, sound part is now
decided by the validator, and the rest is one enumerated row.

*Decided.* `FuncAttrs.readnone` / `readonly` on a function WITH a body are
checked against it (`FuncAttrClaimViolated`): no write — and under `readnone`
no read — through an address that does not root at the function's own
`Alloca` (the root trace follows only a `GEP` base, `Copy` and `Cast PtrToPtr`;
a `Select`, block parameter, `IntToPtr`, `Load` result, call result or
`PtrFromParts` is a root, so none of them can launder a parameter pointer into
the exemption), no synchronizing atomic or fence, no heap, deallocation or
reference-count operation, no indirect call or opaque dialect op, and every
direct callee carries the same claim. On a bodyless declaration both remain a
claim. Borrow STRUCTURE is decided too: a `BorrowMut` may not be taken through
a shared reference — an operand typed `&T` / `*const T`, or one that may root
at a shared `Borrow` result through the same trace widened by both `Select`
arms and every block-parameter incoming argument, since for this ANY-root
question following more can only refuse more (`BorrowMutThroughSharedRef`) — and an
`EndBorrow` must end a `Borrow` / `BorrowMut` result (`EndBorrowOfNonBorrow`).

*Decided (v59, WS1.14).* A DEFINED function's typed effect summary
(`FunctionSummary.effects`) is checked against its body
(`EffectSummaryViolated`) by a sound, syntactic over-approximation: every
access address is traced through `GEP` / `PtrData` / `Copy` / both `Select`
arms / `Cast PtrToPtr` / a borrow to a formal parameter, a `GlobalAddr` or the
function's own `Alloca`, and anything else — a `Load` result, `IntToPtr`,
`PtrFromParts`, a block parameter, a call result — forces `Everything`; a call
contributes the callee's ADMISSIBLE summary mapped through its arguments, and
an unsummarized, interposable (`Weak` / `LinkOnce` / `ExternalWeak`) or
indirect call the top summary. On a bodyless declaration
the effect summary stays a claim, admissible at a call only once
`validate_linked_module` authenticated the declaration's `backed_by` (the far
effects restated exactly); unauthenticated, a caller havocs. The trace is
trusted code: its precision (a heap allocation's fresh memory, a store and
reload) is conservative, never permissive.

12. **Borrow LIVENESS is a producer obligation.** Exactly one `EndBorrow` per
    path, no two simultaneously live `BorrowMut` of one place, and no use of a
    borrow after its `EndBorrow` need a flow-sensitive borrow checker the
    validator does not have; a module that breaks any of them VALIDATES, and
    the reference interpreter runs it (it passes the address through). The
    obligation binds a producer whose discipline the permission machine is.
    A Rust producer is ruled out of the machine (ratification "A Rust
    reference carries no permission instruction"): it spells every reference
    as the place's address, and what rustc's borrow checker discharges is
    Rust's own reference discipline, which trust-ir does not state. The THIR
    producer already emits none. The Trust MIR bridge still emits `Borrow` /
    `BorrowMut` and no `EndBorrow` (measured 2026-09-29) until its
    respelling, which is in the Trust repository and not yet on its main,
    lands. For that output, for Clean and for hand-built producers that emit
    the instructions, the obligation is UNCHECKED. The
    structural trace does not follow memory (a store and reload), a call or an
    integer round trip, so an upgrade laundered through one of those is inside
    this row, not outside it. A
    ported ratchet (`validation_holes`,
    `ratchet_b6_ref_refmut_borrow_discipline_unchecked_liveness_half_ratified_producer_obligation`)
    pins this non-guarantee so it cannot be misread as a guarantee.

    One consequence is decided at run time since 2026-09-29: `Dealloc` of an
    allocation that a `Borrow` / `BorrowMut` not yet ended by `EndBorrow`
    names is undefined behaviour in both engines (ratification "Freeing an
    allocation under a live borrow is undefined behaviour"). That decides the
    free, not liveness: a missing `EndBorrow` still validates and still runs
    until a `Dealloc` of the same allocation. No producer emits `Dealloc`
    itself, but `trust-ir run` maps `__rust_dealloc` to one, so MIR-bridge
    output run there, until the bridge's respelling lands, meets the rule at
    every free of memory it borrowed: a hand-written module of that shape is
    refused, and runs once an `EndBorrow` is added (measured 2026-09-29; how
    much real output has that shape is not measured). Both engines name
    the allocation a borrow or `Dealloc` operand was derived from, so the
    shapes where an operand leaves it — a borrow one past the end, in heap
    slack or of a zero-size slot; such a borrow ended twice; a borrow taken
    through an integer round trip; a free of a zero-size slot — are decided,
    and both engines give the interpreter's verdict on every sampled cell
    (ratification "A pointer operand names the allocation it was derived
    from", 2026-09-30; which allocation an integer lands in is the reference
    placement's, which that ratification labels and does not ratify). What
    stays open is this row's own question: the liveness of a borrow itself.

### Reference-counting runtime boundary (Clean heap)

`Retain` / `Release` / `IsUnique` carry only a pointer, and a backend routes
them to the runtime that owns the cell. For Clean's Perceus heap
(`AllocOrigin::CleanHeap`) that runtime is now a pinned table,
`trust_ir_build::TRUSTED_RC_RUNTIMES`: `clean_inc(Ptr) -> ()`,
`clean_dec(Ptr) -> ()` and `clean_is_exclusive(Ptr) -> (U8)`, C calling
convention. The validator guards those symbols on every module in all three
spellings of a link-time symbol (`Function.name`, `Global.name`,
`Constant::SymbolAddr`): an off-pin declaration, a local definition, a global
wearing the name, a relocatable address of it and a declaration claiming the
runtime has no effects (`readnone` / `readonly`, a parameter attribute, `Pure`)
are each refused by name. What it cannot decide is one row:

13. **The pinned RC runtime.** Trusted and not re-checkable from any
    certificate: (a) the pin table is the Clean runtime's real ABI — that the
    three symbols and signatures are what the linked runtime exports; (b) the
    runtime maintains the count faithfully (`clean_inc` increments,
    `clean_dec` decrements and frees at zero, `clean_is_exclusive` reports a
    count of exactly one); and (c) **ownership transfer between heaps is
    NONE**: a `CleanHeap` object passed into Rust code stays `CleanHeap`-owned
    and is released only through the pinned `clean_dec`, never by a `RustHeap`
    free, and no Rust allocation is counted by this runtime. (c) is a ratified
    producer and backend convention, not a static check: the validator does
    not track which heap a pointer came from. The reference interpreter
    records each `HeapAlloc`'s origin and executes three parts of (c) as
    undefined behaviour: `Inst::Dealloc` of a Clean cell; since 2026-09-29,
    `Retain` / `Release` / `IsUnique` on a `RustHeap` / `CMalloc` cell or any
    other allocation that is not reference-counted (internal spec
    ratifications, "An ARC operation counts only a reference-counted cell";
    the Lean model agrees for a pointer whose address lies inside the
    allocation it was derived from); and, under the pinned host model, a
    pinned entry called on a cell of another heap. A call-spelled free of a
    Clean cell stays an opaque call. As with item 9, the module that DEFINES the
    runtime is refused (`RcEntryPointDefinedLocally`) — the runtime is linked
    trusted base built outside the trust-ir lane — and each additional row or
    entry point is a new instance of this item. The `release` entry
    (`clean_dec`) is also a row of the one-place release table
    `trust_ir_build::pinned_release_entry_points()` (WS3.22): a Clean cell
    is released by `Release` (which a backend routes to `clean_dec`) or by a
    direct call to `clean_dec`, never by `Inst::Dealloc`, which is undefined
    behaviour on a reference-counted cell (in the interpreter for every such
    cell, in the Lean model for a scalar-typed one), is
    refused for codegen and cannot state a runtime; a host model must treat that
    call as a release — the reference model does (the cell is
    dead at count zero, a second `clean_dec` or a load through it faults
    under the model; `a_double_clean_dec_and_a_load_after_it_fault_under_the_reference_model`);
    a `RustHeap` free is pinned by no table and stays an opaque call. The
    rest of Clean's runtime ABI
    (`clean_alloc_ctor`, `clean_ctor_get`, `clean_box`, ...) is NOT in the
    table and stays convention; Perceus reuse tokens are not part of the
    format. Ratified in the internal spec ratifications §10.

    **The reference model of this runtime (WS2.13, 2026-09-19).** The same
    `trust_ir_build::host::PinnedHandleHost` also models the triple: it
    CLASSIFIES an exact pinned declaration as the `retain` / `release` /
    `is_unique` entry of the `CleanHeap` runtime (`HostCalls::rc_op`), and the
    reference interpreter performs the count on its own
    `HeapAlloc { origin: CleanHeap }` cells — the table `Retain` / `Release` /
    `IsUnique` already maintain — refusing a cell of another heap, a stack
    slot, an interior pointer or null as undefined behaviour, which is (c)
    made observable under the model. It is a reference model of a trusted
    runtime, and a run that used it is host-assisted evidence, not in-format
    execution; (a) and (b) are untouched by it.

### Two interpretations of "proven"

- **(A) Per-module admissibility** — each emitted module carries proofs the
  validator + Lean semantics admit. The current artifacts satisfy A per-module.
- **(B) Whole-pipeline correctness** — the *transformation* from source to
  emitted code is proven correct end to end. The current artifacts satisfy B
  for the vector dialect and the proven dialect lowerings, and — for the Clean
  producer — over a growing *fragment*: the source → trust-ir step is
  kernel-checked by the backend TV certificate (boundary 6) and the
  trust-ir → machine step is kernel-checked by the lowering-resolution
  certificate for the i8 ALU lowering family (`iadd`/`isub`/`neg`/`band`/`bor`/
  `bxor`, boundary 7) — *measured 2026-09-18: not at HEAD; those artifacts stay
  `Pending`, see the dated note under item 7*. Composing the two on one artifact (the transitive
  source → machine claim under the single `ck0` kernel) is the t-silicon
  milestone-2 target. B remains **honestly known-not-closed** *in general*:
  `TransformCorrectness.lean` proves inlining correctness only in its
  *frame-discipline* form (`theorem inlining_preserving`: a `Call` is
  equivalent to executing the callee body on a fresh frame — mechanized and
  `sorry`-free); the stronger *splice* form, which rewrites the caller's CFG to
  run the callee's blocks in the caller's SSA id space, is still prose, because
  it needs a value-id/block-id renaming function plus a `TrustIr.stepInst`-equivariance
  lemma the model does not have. The file's transform-correctness notion is
  `behaviour_refines` (every target behaviour, including a trap, UB or
  divergence, is a behaviour of the UB-free source); the older
  `semantics_preserving` only relates returning runs and is proved not to
  exclude assertion deletion, panic-to-loop or divergence-to-return rewrites,
  so no claim rests on it. UB is top: a rewrite that only changes UB runs is
  admitted (`unreachableToReturn_refines`). Both notions are stated over the
  intraprocedural evaluator `stepN`, where a call is an `unsupported`
  behaviour. `TransformRefinementCtx.lean` states the same notion,
  `behaviour_refines_in`, over `stepNWithContext`, where calls are executed
  (fuel and call depth both quantified). It re-proves the UB-top rewrite and
  the trap-removal refusal there, states the frame-discipline inlining theorem
  at the behaviour level (`inlining_behaves_iff`: a call's behaviours are its
  inline body's, through the call boundary), and proves that a `stepN`
  refinement does not carry over to a body that calls
  (`behaviour_refines_not_imp_refines_in`). Its positive theorems are at
  panic=abort, and lifting a transform over every function of a module is
  not proved. The fragment also excludes memory, loops, recursion, and lowering
  rules past the i8 tier — each an open rung that would otherwise force a
  `Trusted(...)` gap.

### Lineage closure

A module's `ProofLineageNode` chain is **closed** iff every rung from the source
digest to the emitted-code digest is present, `depends_on`-connected, and **none
uses `ProofEvidence::Trusted(...)`**. Only a closed chain backs interpretation
B for that module. (Helper tracked on the internal roadmap,
proofchain-lineage-append.)

### What is checked around each item, and what is not

Every numbered item above is an ASSUMPTION, so none of them is proved — that is
what "trusted base" means. What can be mechanical is the BOUNDARY around an
item: that it is as small as stated. The table classifies that evidence, and
`scripts/check_enforcement_links.py` (gate 0 of `scripts/ci_gates.sh`) reads
it. Every backticked token in the Enforcement column is a citation that must
resolve in the tree — a cited test must be a real `#[test]` fn, a cited file
must exist — and a class must be WITNESSED by a citation of the matching kind,
so a class cannot be raised by rewording. `(corpus)` is a `(test)`-rung class
that cites a row of the must-refuse corpus as `refuse/<row>` (ratification
§16). Strongest first:
`(kernel-certificate)`, `(lean-theorem)`, `(proved-contract)` (a row of one
pure decision table that gate 13, `verified-contracts`, proves with the
Clean kernel re-checking it, under a same-shape mutant that must refute it;
the proof is about the table's OPTIMIZED MIR, and for a constant-valued law
rustc's optimizer does the case analysis and the kernel re-checks the folded
constant, which is why it ranks below the two classes whose case analysis
the kernel itself checks), `(type-level)` (unrepresentable,
rustc refuses it), `(test)` (something executes and would fail — EVIDENCE, not
proof), `(code)` (the implementing code is named and nothing executes to check
it), `(external)` (another repository, which this tree cannot check),
`(prose-only)` (nothing).

This gate is the first rung of moving in-text claims to mechanically verified
proof, and not the destination. It proves no item. It makes a rotted citation
a gate failure, and it keeps the count of items with NOTHING checked around
them (`scripts/gates/enforcement-ratchet.txt`) from rising. It does not check
that a cited test tests the claim, nor (in general) that a standing gate runs
it. The Lean rows are the exception since 2026-09-29: a `(lean-theorem)`
witness must be a theorem the `lean-proofs` gate (`scripts/lean_proofs.py`,
gate 14) builds, and that gate also censuses the axioms of every constant of
the library and re-sends every one of them to the kernel; it is required
wherever the elan `lake` is installed and SKIPS, saying so, where it is not.
A `(lean-theorem)` row also gives each theorem it cites the verdict its
conclusion states, where the gate's reader of the Lean source classifies
that conclusion, and names identifiers of its statement (rule E5); a theorem
whose conclusion the reader does not classify is held to its names only.
The `(proved-contract)` rows are the other exception: the witness must be a
law gate 13 (`scripts/verified_contracts.py`) HOLDS — a `pub fn` of
`crates/trust-ir-laws/src/laws.rs` in a file whose every law is one call of
its own table and is named in some mutant's `flips`, which the run must see
refute it, and in which every table over enum cells has a law at every cell
of its enums (so a glob over a family, `laws::rc_*`, names every cell) — and
each law must follow a citation of the table it calls: the table the row
cites most recently before the law, spelled so that it resolves to that
table's definition alone. That is a check of which table a law is cited
under and of the verdict the row gives it (rule E5), never of the rest of its
words. Gate 13 runs the verified lane over those laws and FAILS, never skips,
where the lane is missing; gate 0 checks what it holds before any run, never
that a run passed. A proved-contract row
proves the ROWS of a TABLE a rule reads; that the rule reads it is stated in
the row itself, as code or test and never as proved, and like every item
here the row's premise stays trusted. One premise is under every gate-13
verdict: `targo trust check` runs the build scripts of the lane's unit graph
outside the proof channel, uncontained (Trust blocker B5), so every law it
proves rests on them. Gate 13 checks WHICH scripts ran, equal to
`scripts/gates/verified-contracts-build-scripts.tsv` in every run (test); that
they did not interfere with the run stays trusted.

| Item | What the row is about | Enforcement |
|------|------------------------|-------------|
| 1 | the Lean 4 kernel is sound | (prose-only) trusted by declaration; nothing in this tree checks the kernel itself: the replay in the next row runs the SAME kernel a second time, and no independent checker runs (Lean 4.8.0 ships no leanchecker executable) |
| 1 | every safe constant of the `TrustIr` library was admitted by the kernel, none written into the environment by a meta-program, except the unsafe-recursion bodies of partial definitions, which no safe constant may name | (test) `lean/trust_ir-semantics/ProofCensus.lean`, run by the `lean-proofs` gate, replays each one through the kernel from its stored term on top of Init (Lean core's replay, the engine of lean4checker), a native_decide site with its evaluation re-run first, and the gate checks that the replayed and skipped counts cover every safe constant. Red demonstrated on a scratch copy with a False theorem written by a meta-program, which the build and the axiom census alone passed |
| 1 | the `native_decide` fixture theorems (462 on 2026-09-29) trust the Lean COMPILER and runtime as well as the kernel, and no other theorem does | (test) `lean/trust_ir-semantics/ProofCensus.lean`, run by the `lean-proofs` gate, admits the compiler axiom only in the modules `nativeDecideModules` names and refuses it by name everywhere else; such a fixture witnesses `(test)`, never `(lean-theorem)` |
| 2 | `ay_sound_unsat` is the ONLY first-party axiom | (test) `lean/trust_ir-semantics/ProofCensus.lean`, run by the `lean-proofs` gate: EVERY safe constant of the `TrustIr` library may rest on the Lean-core trio and `ay_sound_unsat` only, and no other safe axiom may be declared; a placeholder fails the same gate, from the census or, inside an example, from the build log. `lean/trust_ir-semantics/TrustIr/Proofs/AxiomAudit.lean` pins the exact printouts of a curated list. Skipped, by name, on a machine without the elan lake |
| 2 | every `ay` UNSAT verdict is sound | (prose-only) the axiom's content, assumed |
| 3 | the Rust and Lean schemas name the same constructs | (test) `crates/trust-ir/tests/lean_schema_parity.rs`, the `lean-schema-parity` gate. NAME parity only |
| 3 | the Rust reference interpreter is locked to the numerics policy | (test) `crates/trust-ir-build/tests/numerics_policy.rs` |
| 3 | the Lean semantics MEANS what the interpreter does | (prose-only) no theorem relates the two models' behaviour; this is the known gap. The sampled differential in the next row is evidence on its fixtures, not the correspondence |
| 3 | the Lean executable model and the reference interpreter agree on the subset fixtures and the seeded corpus | (test) `crates/trust-ir-conformance/tests/lean_exec_differential.rs`, the `lean-exec-differential` gate: `subset_fixtures_agree`, `generated_corpus_agrees_and_unsupported_is_ratcheted` and `negative_literal_constants_agree_across_engines` (negative integer literals in every operand position). A sample: agreement on the programs run, nothing beyond them. The remaining borrow divergences are pinned by `borrow_permission_divergences_stay_as_measured`; allocation/GEP signedness is now decided by `typed_memory_operand_signedness_agrees` and the wider `allocation_and_gep_operands_keep_declared_magnitudes_and_word_bounds` corpus, and the ARC-operand provenance ledger is decided by `arc_operand_provenance_agrees_across_engines`, and a divergence no row reaches is not excluded (unsigned-lane vector shapes and `AtomicRMW` signed `Max` / `Min` were two such, found by review on 2026-09-30 and closed with rows in `vector_icmp_cells_agree_across_engines_and_with_the_statement` and `negative_literal_constants_agree_across_engines`) |
| 3 | a transform is judged by `behaviour_refines`, not by `semantics_preserving`: the older notion relates returning runs only, so an assertion-deleting transform satisfies it while failing refinement | (lean-theorem) `assertElim` is `semantics_preserving` (`assertElim_semantics_preserving`) yet no `behaviour_refines` transform (`assertElim_not_refines`), so not every `semantics_preserving` transform refines (`semantics_preserving_not_imp_refines`); the identity is a `behaviour_refines` transform (`id_refines`) and such transforms compose under `behaviour_refines` (`compose_refines`), in `lean/trust_ir-semantics/TrustIr/Proofs/TransformCorrectness.lean`, built and censused by the `lean-proofs` gate; over the evaluator that executes calls, the assertion eliminator is no `behaviour_refines_in` transform (`assertElim_not_refines_in`), the identity is one under `behaviour_refines_in` (`id_refines_in`), such transforms compose under `behaviour_refines_in` (`compose_refines_in`), and not every `behaviour_refines` transform is one (`behaviour_refines_not_imp_refines_in`): a refinement over the intraprocedural evaluator does not carry over to a body that calls. These are in `lean/trust_ir-semantics/TrustIr/Proofs/TransformRefinementCtx.lean`. The positive call-executing theorems are at panic=abort. The concrete `unreachableToReturn` rewrite applied throughout the function table by `mapFunctionCFGs` is `program_refines` (`unreachableToReturn_program_refines`) in `lean/trust_ir-semantics/TrustIr/Proofs/ProgramRefinement.lean`, including recursive calls and all outcomes with the same resource budgets except source UB. General transformation lifting and splice-form inlining remain open |
| 4 | named malformed modules are refused | (test) the `validator-fail-closed` gate, `crates/trust-ir-build/tests/validation_holes.rs`. Evidence per refusal, not a soundness proof of the validator; the `ValidationError` variants no test names, and the ones nothing constructs, are counted in the ratchet ledger |
| 4 | the structural refusals a consumer meets on the wire are pinned as artifacts a consumer must refuse | (corpus) `refuse/tainted_value_reaches_sink`, `refuse/certified_with_empty_kernel_term`, `refuse/extern_weak_direct_call`, `refuse/duplicate_enum_id`, `refuse/func_type_out_of_range`, `refuse/ptr_data_of_non_pointer`; run by `crates/trust-ir-conformance/tests/refuse_corpus.rs` on the module decoded from the checked-in bytes, exhaustive over the variant list by the shrink-only allowlist `crates/trust-ir-conformance/tests/fixtures/refuse/UNCOVERED.tsv` (evidence about the refusal, not a proof of the validator) |
| 4 | a defined body honours its declared effect summary; a declaration's is admissible at a call only when authenticated | (test) `a_store_through_an_unlisted_param_is_refused`, `a_callee_write_maps_through_the_argument`, `an_unauthenticated_declaration_summary_is_havoc`, `an_authenticated_declaration_summary_is_admissible`, `removing_the_store_makes_the_tighter_summary_valid`, in `crates/trust-ir-build/tests/effect_summary_validation.rs` |
| 4 | `readnone` / `readonly` on a defined body are checked against it | (test) `c15_4a_readnone_with_store_through_param_is_refused`, `root_trace_does_not_follow_select`, `readonly_function_calling_an_unattributed_function_is_refused`, `ratchet_b2_gap_readnone_claim_on_a_storing_function_accepted`, in `crates/trust-ir-build/tests/validation_holes/claim_attrs_and_borrows.rs` |
| 4 | the validator's checks are sound and complete for the senses it lists | (prose-only) no proof and no model of the validator; the tests sample its refusals |
| 5 | a lineage chain is closed with zero trusted rungs | (test) `closed_lineage_passes`, `json_manifest_sidecar_accepted`, and the gates `lineage-closure-red` and `zero-trusted-census-red` |
| 5 | the bootstrap argument (diverse double-compilation) | (prose-only) no double-compilation run is recorded or checked in this tree |
| 6 | the kernel decides the reflected equation | (kernel-certificate) `KERNEL_ANCHOR_CLEAN_BACKEND_TV`, re-checked in-process by `validate_module` |
| 6 | the denotation maps compute the source and emitted meanings | (prose-only) the residual assumption itself |
| 6 | each call edge is bound to the callee it reaches | (test) `a2_retargeted_call_is_refused_on_every_layer`, `b0_caller_without_inheritance_row_is_refused`, `self_recursive_composition_is_refused_as_a_cycle`, in `crates/trust-ir-build/tests/tv_callee_binding.rs` (the `validator-fail-closed` gate) |
| 6 | a CONSISTENT retarget — the call and its row both rewritten — is accepted | (test) `b3_gap_composition_consistent_retarget_to_certified_callee`: the test pins the stated GAP, so it cannot be read as a guarantee |
| 6 | an island-bound certificate's comparand is the value of its island source declaration; a re-minted comparand under the honest island is refused (a re-minted island is another island, to which no theorem about the honest one bridges) | (test) `a_tv_comparand_that_is_not_the_named_declarations_value_is_refused`, `a_tv_certificate_naming_another_source_is_refused`, `an_island_bound_tv_source_must_name_an_island_definition`, `a_theorem_citing_a_constant_bound_in_another_island_is_refused`, in `crates/trust-ir-build/tests/island_theorem.rs` (the `validator-fail-closed` gate) |
| 6 | an island-free certificate keeps the mint-time source link; an island-bound caller is refused | (test) `an_island_free_tv_certificate_keeps_its_mint_time_meaning`, `an_island_bound_caller_is_the_disclosed_slice_two_residual`: the tests pin the stated residual |
| 6 | the Fragment-4 release gate is STRUCTURAL, beside the kernel equation: one `Release` per `HeapAlloc(CleanHeap)` result, a `Dealloc` of the cell refused by name, a `Release` of any other value neither counted nor refused | (test) `clean_backend_tv_rejects_heap_dropped_release`, `clean_backend_tv_rejects_heap_doubled_release`, `clean_backend_tv_refuses_a_dealloc_freed_heap_cell`, `clean_backend_tv_release_of_a_non_allocation_is_not_a_balance_verdict`; the certified body executes to the certified value, `clean_backend_tv_certified_heap_body_executes_to_the_certified_value` |
| 6 | a Fragment-5 (boxed `Nat`, `() -> Ptr`) body is outside the re-checker: its certificate is refused by name on the `Ptr` return, the module carrying it is refused, and Clean decides the fragment without minting it (the ratification "A reference-counted cell is released by `Release`, never by `Dealloc`", clause 4) | (test) `clean_backend_tv_refuses_a_boxed_nat_ptr_return`, `a_fragment5_certificate_refuses_the_module_with_its_certified_fragment2_root`, in `crates/trust-ir-build/tests/clean_backend_tv_fragment5.rs` (the `validator-fail-closed` gate). Clean's ownership balance and its not-minted gate are external; the ratification names them |
| 7 | UNSAT of the RECORDED clause list — not the lowering | (kernel-certificate) `KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`; a tampered chain is the kernel's refusal, `tampered_step_chain_is_rejected_by_kernel` |
| 7 | the clause list is the Tseitin miter of the recorded gate DAG | (test) `family_provenance_validates_against_clause_lists`, `tampered_provenance_is_rejected_at_cert_build` |
| 7 | that UNSAT cannot certify a lowering, and the composed claim is refused | (test) `alu_family_lowering_certs_remain_pending_cnf_assurance`, `producer_selected_unsat_cnf_cannot_mint_certified`, `source_to_silicon_rejects_unbound_lowering_assurance` |
| 7 | the clause list IS the lowering rule's semantic miter | (prose-only) not derived by the validator and, since 2026-07-12, not trusted either: the artifact stays pending |
| 8 | the model ignores the memory ordering of a fence | (lean-theorem) `semFence` at every `MemOrdering` is a no-op (`fence_is_noop`), in `lean/trust_ir-semantics/TrustIr/Proofs/AtomicProps.lean`. It mechanizes the LIMITATION, not data-race freedom |
| 8 | a data-race-freedom annotation has no discharge path | (test) `data_race_free_is_structured_unsupported`, `verify_proof_still_unsupported_annotations` |
| 8 | no `DataRaceFree` / `AtomicOrdering` annotation counts toward a `Discharged` obligation: a row sited on the claim-carrying atomic is refused without a certificate, stripping every such claim changes no verdict, and annotation synthesis mints `Pending` rows only | (test) `ws2_26_discharged_row_backed_only_by_concurrency_claims_is_refused`, `ws2_26_mutation_control_concurrency_claims_never_change_a_verdict`, `ws2_26_annotation_synthesis_mints_pending_rows_only`, in `crates/trust-ir-build/tests/validation_holes/ws2_26_concurrency_claims_discharge_nothing.rs` (the `validator-fail-closed` gate). Evidence that the validator does not count the claims, not a model of concurrency |
| 8 | correctness on any interleaving but the sequential one | (prose-only) nothing; the model is single-threaded |
| 9 | every forgery of a handle is refused, and release is the pinned symbol or nothing | (test) `crates/trust-ir-build/tests/handle_types.rs`, `validate::handle_registry_tests` |
| 9 | double release and use-after-release are NOT detected | (test) `a_double_release_validates_and_that_is_the_documented_non_guarantee`, `a_use_after_release_validates_and_that_is_the_documented_non_guarantee`: the tests pin the NON-guarantee |
| 9 | (c) the release entry points of the pinned runtimes are named in ONE place, derived from the tables, and the reference host model keys its dead-marking on it: a double `trust_bignum_nat_drop` is an interpreter FAULT, a single drop runs clean, a no-op-release mutant sees nothing (host-assisted: a trusted model, never in-format evidence) | (test) `crates/trust-ir-build/tests/release_entry_points.rs`, `the_pinned_release_entry_points_are_named_once`, `a_double_drop_faults_under_a_release_marking_host_and_a_single_drop_runs_clean`, `a_host_that_treats_drop_as_a_no_op_fails_the_double_drop_test`; `host::tests::every_pinned_release_entry_point_is_modelled_as_a_release`; (differential) `interpret_differential.rs`, `ws3_22_pinned_release_differential` |
| 9 | the pinned Nat row is exactly the ratified kernel surface, each role declarable and callable, every off-row spelling refused | (test) `crates/trust-ir-build/tests/nat_kernel_surface.rs`, `the_trusted_runtime_table_is_well_formed_and_ratified` |
| 9 | (b) each shim is faithful to the method it wraps | (external) `crates/trust-bignum/src/handle_abi.rs`, in the Trust repo |
| 9 | (b) each kernel-surface shim equals the Clean kernel's native reducer | (external) `crates/trust-bignum/tests/kernel_differential.rs`, in the Trust repo (pending for the fourteen WS3.2 roles) |
| 9 | the reference model serves every pinned Nat entry point under the exact pinned signature only, with the pinned Lean semantics; a run through it is host-assisted, and double release / use after release are UB under the model | (test) `every_pinned_entry_point_has_a_host_model` in `crates/trust-ir-build/src/host.rs`; `crates/trust-ir-conformance/tests/interpret_host_models.rs`; `nat_handle_program_executes_under_the_pinned_host_model`, `a_mis_declared_pinned_symbol_is_not_served_by_the_pinned_host_model` in `crates/trust-ir-cli/tests/cli_run.rs` |
| 9 | (a) the pin table is the runtime's real ABI; (c) handle lifetime | (prose-only) the trusted row itself |
| 10 | interposable sites are refused on both ends; the ODR spellings stay admitted | (test) `an_interposable_far_definition_cannot_back_a_cross_crate_claim`, `an_interposable_local_declaration_cannot_rely_on_a_cross_crate_claim`, `odr_and_available_externally_far_linkage_stay_admitted`, the `import-verification` gate |
| 10 | a linkage is INTERPOSABLE exactly at `Weak`, `LinkOnce` and `ExternalWeak`: `WeakOdr`, `LinkOnceOdr` and `AvailableExternally` (and `External`, `Internal`, `Private`) are not, which is what leaves the ODR spellings admitted under this item's premise. This is the table the interposable-site rule reads at both ends of a proof-bearing edge, not the set either end refuses: a claim-free call edge admits a local `ExternalWeak` declaration, and the far end also refuses an unexported `Internal` / `Private` definition | (proved-contract) `Linkage::is_interposable`, one law per linkage: true at `laws::interposable_weak`, `laws::interposable_link_once`, `laws::interposable_external_weak`; false at `laws::interposable_weak_odr`, `laws::interposable_link_once_odr`, `laws::interposable_available_externally`, `laws::interposable_external`, `laws::interposable_internal`, `laws::interposable_private`. That the verifier refuses by it is the tested row above, not proved |
| 10 | every copy the linker may select is the same definition | (prose-only) the premise itself; nothing re-checks the linked copy |
| 11 | (a) the binding rule in front of the nonneg certificate: sort, place and IR type are checked before the clause certifies | (test) `i64_result_returning_minus_one_is_refused`, `bitvec_sort_is_refused`, `value_place_is_refused`, `usize_place_needs_target_info`, in `crates/trust-ir-build/tests/contract_clause_binding.rs` (the `validator-fail-closed` gate). `b2_gap_kernel_certifies_nat_nonneg_ignoring_bindings_and_ir_type` is named for the gap it CLOSED and asserts the refusal |
| 11 | (a) that rule is load-bearing: without it the kernel alone accepts the forged twin | (test) `a_rechecker_without_the_binding_rule_accepts_the_i64_twin` |
| 11 | (a) the value of an unsigned IR place, read at the integer sort, is a natural | (prose-only) the denotation lemma itself; no certificate states it |
| 11 | (b) a proof backref backs only a row of its own kind, on its own node | (test) `certified_postcondition_cannot_back_div_non_zero_unsited_or_resited`, `ambiguous_kind_cannot_back_a_safety_claim`, `node_level_proof_ref_requires_the_exact_site` |
| 11 | (b) the category-AMBIGUOUS kinds are exactly `Precondition`, `Postcondition`, `LoopInvariant`, `TypeInvariant`, `RefinementType`, `TranslationValidation`, `TemporalSafety` and `Liveness`; every other kind, `Termination`, `Ownership` and `Custom` included, is not | (proved-contract) `trust_ir_laws::proof_ref_kind_is_ambiguous`, the table the backref category rule reads at the kind's shape, one law per kind, and gate 13 refuses to run while a kind has none: true at `laws::ambiguous_precondition`, `laws::ambiguous_postcondition`, `laws::ambiguous_loop_invariant`, `laws::ambiguous_type_invariant`, `laws::ambiguous_refinement_type`, `laws::ambiguous_translation_validation`, `laws::ambiguous_temporal_safety`, `laws::ambiguous_liveness`; false at the eight other laws of `laws::ambiguous_*`. That the rule reads it (`validate::proof_ref_kind_is_ambiguous` delegates) is code, tested by the row above |
| 11 | (b) the status tier that is backref currency is the kernel tier, `Certified` alone: a capability-replayed `Discharged` row is outside it, as are `Trusted`, `Pending` and `Failed` | (proved-contract) `ProofStatus::is_kernel_tier`, one law per status: true at `laws::kernel_tier_certified`; false at `laws::kernel_tier_discharged`, `laws::kernel_tier_trusted`, `laws::kernel_tier_pending`, `laws::kernel_tier_failed`. That the backref authority set (`validated_authority_refs`) filters by it is code, not proved |
| 11 | (b) a backing row's formula ENTAILS the claim it backs | (prose-only) attribution only, and pinned as accepted by `function_level_pure_backed_by_a_postcondition_is_still_accepted`; nothing compares the formula with the claim |
| 12 | borrow STRUCTURE is refused: a `BorrowMut` through a shared reference, an `EndBorrow` of a non-borrow | (test) `c15_3a_borrow_mut_through_shared_ref_param_is_refused`, `borrow_mut_of_a_shared_borrow_result_is_refused`, `review_borrow_mut_through_a_select_of_a_shared_borrow_is_refused`, `end_borrow_of_a_load_result_is_refused`, in `crates/trust-ir-build/tests/validation_holes/claim_attrs_and_borrows.rs` (the `validator-fail-closed` gate) |
| 12 | borrow LIVENESS is NOT checked: a function not stamped `Producer::TRust` with a missing `EndBorrow` validates and runs | (test) `ratchet_b6_ref_refmut_borrow_discipline_unchecked_liveness_half_ratified_producer_obligation`: the test pins the NON-guarantee, over the Clean-stamped `clean_read` |
| 12 | the permission predicate both Rust-reference checks read is exactly `Borrow`, `BorrowMut` and `EndBorrow` | (proved-contract) `InstShape::uses_borrow_permissions`, one law per instruction shape: true exactly at `laws::borrow_permission_borrow`, `laws::borrow_permission_borrow_mut` and `laws::borrow_permission_end_borrow`, and false at every other law of `laws::borrow_permission_*`. That the validator and the bundle check read it is code, tested by the rows below |
| 12 | the machine faults on a borrow of an allocation held by a live `BorrowMut`, and on a `BorrowMut` of one in any permission but `owned`, in every state; a `Copy` step touches neither memory nor permissions | (lean-theorem) `semBorrow` of an allocation held by a live `uniqueBorrow` is UB (`semBorrow_ub_of_uniqueBorrow`); `semBorrowMut` of an allocation in a permission other than `owned` is UB (`semBorrowMut_ub_of_not_owned`); a `Copy` step in the bare instruction model leaves memory and permissions as they were (`stepInst_copy_preserves_memory_and_permissions`), in `lean/trust_ir-semantics/TrustIr/Proofs/BorrowMemoryProps.lean`, built and censused by the `lean-proofs` gate |
| 12 | a permission instruction in a function stamped `Producer::TRust` is refused, by the validator and by the bundle check; a `RustMir` bundle is not keyed until the MIR bridge's respelling and trust-mc's alias change are on their mains | (test) `rust_producer_permission_borrow_is_refused`, `permission_machine_stays_valid_for_other_producers` (the `validator-fail-closed` gate); `rust_producer_bundle_refuses_a_permission_borrow`, `rust_producer_bundle_mint_refuses_a_permission_borrow`, `bundle_check_refuses_no_permission_borrow_outside_the_rust_stamp` (the `wire-format-goldens` gate) |
| 12 | a consumer refuses such a function | (corpus) `refuse/rust_reference_as_permission_borrow` |
| 12 | the Rust producers' spelling of the measured reference shapes runs to the same value in both engines, and two shapes no `EndBorrow` placement repairs fault in Lean | (test) `rust_reference_spelling_agrees_across_engines`, `borrow_permission_divergences_stay_as_measured` (the `lean-exec-differential` gate) |
| 12 | the THIR producer emits no permission instruction; the MIR bridge will lower no reference to one once its respelling lands | (external) Trust's producer ratchets once its trust-ir gitlink holds the validator rule; the bridge's census test `rust_references_spell_as_pointer_values` lands with the bridge's respelling in the Trust repository |
| 12 | trust-cg's rustc bridge and this repository's `frontend/` driver emit none; rustc's borrow checker discharges Rust's reference discipline for safe code | (prose-only) a source census; nothing in this tree re-checks either |
| 12 | `Dealloc` of an allocation with a live borrow is undefined behaviour in the Lean model | (lean-theorem) `semDealloc` is UB under a live `uniqueBorrow` or `sharedBorrow` permission (`semDealloc_borrowed_is_ub`) and after a `semBorrow` (`semDealloc_under_borrow_is_ub_example`), and runs after a `semEndBorrow` of every `semBorrow` (`semDealloc_after_every_endBorrow_ok_example`), in `lean/trust_ir-semantics/TrustIr/Proofs/MemorySafety.lean`, built and censused by the `lean-proofs` gate |
| 12 | the reference interpreter enforces the same rule, and both engines name the same allocation for a borrow and a `Dealloc` operand: the one it was derived from (decided; SPEC "A pointer operand names the allocation it was derived from"); the borrow shapes still undecided (clause 4, a borrow of a reference-counted cell) are a shrink-only ledger | (test) `dealloc_under_a_live_borrow_is_undefined_behavior` in `crates/trust-ir/src/interpret.rs`, `borrow_liveness_at_dealloc_agrees_across_engines`, `borrow_operand_provenance_agrees_across_engines` and the shrink-only ledger `borrow_permission_divergences_stay_as_measured` in `crates/trust-ir-conformance/tests/lean_exec_differential.rs` (the `lean-exec-differential` gate) |
| 13 | every forgery of the pinned RC-runtime symbols is refused: off-pin signature, a false effect claim (`readnone` / `readonly`, parameter attribute, `Pure`), local body, global, symbol address | (test) `clean_dec_returning_i32_is_refused_as_signature_mismatch`, `a_memory_effect_attribute_on_a_pinned_rc_declaration_is_refused`, `a_readnone_caller_cannot_launder_a_release_through_a_readnone_clean_dec`, `a_local_body_for_clean_inc_is_refused_as_defined_locally`, `a_global_named_clean_is_exclusive_is_refused`, `a_symbol_address_of_clean_dec_in_a_global_initializer_is_refused`, in `crates/trust-ir-build/tests/rc_runtime_pins.rs` (the `validator-fail-closed` gate), and `validate::rc_runtime_pin_tests` |
| 13 | the reference model classifies the exact pinned triple only, the interpreter counts `CleanHeap` cells with its own refcounts, and a cell of another heap, a stack slot, an interior pointer or null is UB under the model | (test) `ws2_13_clean_rc_triple_counts_clean_heap_cells`, `ws2_13_clean_rc_refuses_cells_of_another_heap_and_interior_pointers`, `ws2_13_a_mis_declared_rc_entry_point_is_not_served`, `ws2_13_review_the_last_clean_dec_frees_the_cell_for_in_format_operations`, `ws2_13_review_instruction_arc_and_host_rc_share_one_count_in_both_directions` in `crates/trust-ir-conformance/tests/interpret_host_models.rs`; `pinned_rc_entry_points_stay_bodyless_and_execute_under_the_pinned_host` in `crates/trust-ir-cli/tests/cli_run.rs` |
| 13 | `Inst::Dealloc` of a `CleanHeap` / `SwiftHeap` cell is undefined behaviour in the Lean model | (lean-theorem) `semDealloc` is UB on a cell holding `arcRef` (`semDealloc_arcRef_is_ub`), on a `CleanHeap` allocation (`semDealloc_cleanHeap_is_ub_example`) and on a `SwiftHeap` allocation (`semDealloc_swiftHeap_is_ub_example`), in `lean/trust_ir-semantics/TrustIr/Proofs/MemorySafety.lean`, built and axiom-censused by the `lean-proofs` gate |
| 13 | `Inst::Dealloc` of a `CleanHeap` / `SwiftHeap` cell is undefined behaviour in the reference interpreter too, and the two engines agree on the release matrix | (test) `dealloc_of_a_reference_counted_cell_is_undefined_behavior`; `release_discipline_agrees_across_engines` in `crates/trust-ir-conformance/tests/lean_exec_differential.rs` (the `lean-exec-differential` gate) |
| 13 | `Retain` / `Release` / `IsUnique` on an allocation that is not reference-counted (a stack slot, a `RustHeap` / `CMalloc` cell, a global's reservation) is undefined behaviour in the Lean model, for the live allocation the pointer was derived from, at any offset | (lean-theorem) on a live allocation whose permission is not `arcRef`, each ARC step is UB: `requireArcRef` (`requireArcRef_non_arcRef_is_ub`), `semRetain` (`semRetain_non_arcRef_is_ub`), `semRelease` (`semRelease_non_arcRef_is_ub`), `semIsUnique` (`semIsUnique_non_arcRef_is_ub`); the concrete instances are UB too, `semRetain` of a `semAlloca` slot (`semRetain_alloca_is_ub_example`), `semRelease` of a `RustHeap` cell (`semRelease_rustHeap_is_ub_example`), `semIsUnique` of a `CMalloc` cell (`semIsUnique_cMalloc_is_ub_example`) and `semRetain` of a `semGlobalAddr` reservation (`semRetain_globalAddr_is_ub_example`), in `lean/trust_ir-semantics/TrustIr/Proofs/MemorySafety.lean`, built and axiom-censused by the `lean-proofs` gate; that only an RC-origin `HeapAlloc` holds `arcRef` is read off the allocation sites, not proved |
| 13 | the same ARC operations are undefined behaviour in the reference interpreter, and so is an operand off its reference-counted cell's object base (SPEC clause 3, decided 2026-09-30); the two engines agree on the release matrix, on a global's reservation, on an operand whose provenance is not reference-counted wherever it points, and on a sample of operands that reach a reference-counted cell off its base | (test) `arc_operation_on_a_non_reference_counted_allocation_is_undefined_behavior` and `arc_operand_off_its_cell_base_is_undefined_behavior` in `crates/trust-ir/src/interpret.rs`; `release_discipline_agrees_across_engines`, `arc_on_a_global_reservation_agrees_across_engines` and `arc_operand_provenance_agrees_across_engines` in `crates/trust-ir-conformance/tests/lean_exec_differential.rs` (the `lean-exec-differential` gate) |
| 13 | an ARC operand off its reference-counted cell's object base is undefined behaviour in the Lean model | (lean-theorem) an operand derived from a live `arcRef` cell, at any address but the cell's object base, is UB for `semRetain` (`semRetain_interior_is_ub`), `semRelease` (`semRelease_interior_is_ub`) and `semIsUnique` (`semIsUnique_interior_is_ub`); the instances are UB too, `semRetain` inside a `CleanHeap` cell (`retain_interior_of_cleanHeap_is_ub`), `semRelease` one past one (`release_one_past_cleanHeap_is_ub`) and `semIsUnique` past its slack (`isUnique_past_slack_of_cleanHeap_is_ub`), in `lean/trust_ir-semantics/TrustIr/Proofs/MemorySafety.lean`, built and axiom-censused by the `lean-proofs` gate |
| 13 | a reference-counted cell is one whose origin is `SwiftHeap` or `CleanHeap`, and a `RustHeap` or `CMalloc` cell is not: the one table the interpreter decides `Retain`, `Release`, `IsUnique` and `Dealloc` by | (proved-contract) `AllocOrigin::is_reference_counted`, one law per origin: true at `laws::rc_swift_heap`, `laws::rc_clean_heap`; false at `laws::rc_rust_heap`, `laws::rc_c_malloc`. That the interpreter refuses by it (`arc_allocation_mut`, `is_unique`, `dealloc`) is code, tested by the rows above; the Lean rows rest on the allocation sites, not on this table |
| 13 | (a) the pin table is the runtime's real ABI; (b) the count is maintained faithfully; (c) no ownership transfer between heaps, beyond the parts the interpreter executes | (prose-only) the trusted row itself |
| 14 | the kernel decides the island theorem and its definitional equality with the grounded statement | (kernel-certificate) `KERNEL_ANCHOR_CLEAN_ISLAND`, re-checked in-process by `validate_module` |
| 14 | the island is untrusted: digest, decode, redeclaration, validator-owned-name, axiom and kernel-insertion refusals | (test) `an_island_digest_mismatch_is_refused`, `a_closure_that_redeclares_a_bound_name_is_refused`, `an_island_that_takes_the_tv_theorem_name_is_refused`, `an_island_theorem_may_not_take_a_validator_owned_theorem_name`, `an_island_that_is_empty_opaque_or_undecodable_is_refused_by_name`, `an_undeclared_axiom_in_the_island_is_refused`, `a_mutated_island_declaration_is_refused_by_the_kernel_on_insertion`, in `crates/trust-ir-build/tests/island_theorem.rs` |
| 14 | the statement is the row's formula, and it is about the code (the symbol bridge) | (test) `a_theorem_that_does_not_state_the_formula_is_refused_by_defeq`, `a_theorem_citing_a_constant_whose_tv_certificate_carries_no_island_is_refused`, `a_theorem_citing_a_constant_bound_in_another_island_is_refused`, `the_island_anchor_and_the_lean_theorem_kind_only_meet_each_other` |
| 14 | the grounder's slice-1 reading (a bit-vector binder over `Nat`, an `Int` binder refused) is the formula's meaning | (prose-only) the residual assumption itself; the refusals are sampled by `trust_ir::clean_expr_lowering::island::tests::slice_one_refusals_are_named` and, at the anchor, `an_island_constant_spelled_like_a_theory_operator_is_not_citable` |

## Build determinism

For an artifact to be *independently re-checkable* — and for diverse
double-compilation to mean anything — the same source must produce
**bit-identical** TrustIr and **identical** proof digests on any machine.

**What holds where (split 2026-10-07; the audit's G8 measurement).** The
sentence above is the GOAL; what holds today depends on which identity is
meant:

- **Import identity** (`Module::stable_digest`, the digest an import row
  records) is path-independent: it leaves every debug source path
  (`Module.files`) out, so the same crate built at two checkout paths is one
  module, and a dependency built on one machine authenticates on another.
- **Byte identity** (the binary encoding) and the codegen-cache identity
  (`Module::executable_content_digest_v1`) KEEP the debug source paths. They
  agree across machines only for a producer that writes PORTABLE source names
  (root-relative, or rewritten by its path-remapping option). Neither shipping
  producer guarantees that yet: the rustc-based producer was measured (2026-09-17)
  recording the absolute checkout path and ignoring `--remap-path-prefix`,
  and the Clean backend records its source file path exactly as given on its
  command line. Until those producer fixes land (tracked on the internal
  roadmap), bit-identical TrustIr — and so a byte-level diverse
  double-compilation comparison — holds only for builds at the same checkout
  path.

**Guarantee (ratified):** for a *fixed* producer version and a *fixed*
checkout path, Trust IR emission and proof-digest computation are
deterministic. This rests on:

- `ProofDigest::TrustIrStableV1` digests via explicit `write_*_stable` helpers,
  never `derive`d/`HashMap`-order output (verified by the SHA-256 known-answer
  tests and the stable-digest paths).
- A byte-golden conformance corpus pins every wire format
  (`crates/trust-ir-conformance`, backed by the internal binary-format and
  serialization-formats specs).
- `Module` stores all tables as order-stable `Vec`s; the semantic diff
  (`trust-ir-diff`) is the tool that makes ID-renumbering/reorder *observable*
  rather than silent.

**Audit obligation (discharged in-repo; one cross-repo hazard open):** every
`HashMap`/`HashSet` whose iteration feeds serialized output or a digest input,
and every interning/dedup step, is confirmed insertion-ordered / `BTreeMap` /
`Vec`-order — the per-item checklist (file:line verdicts),
`Module::stable_digest`, the cross-process determinism test, and the DDC
procedure live on the internal build-determinism roadmap. The one open hazard is
cross-repo and **live, not dormant**: canonical ay SMT proof transcripts.
`ProofEvidence::SmtProof` bytes are hashed as-is, and `trust-ir-ay`'s bv-blast
path mints non-empty `SmtProof` payloads *today* — `bvblast.rs` exports a
bounded bit-blast proof through `ay_proof::export_bv_blast_proof_expr_bounded`
and serializes it into the certificate's evidence bytes (the crate pins
`ay-proof`, see `crates/trust-ir-ay/Cargo.toml`). Because those bytes come out
of another repository, their byte-for-byte reproducibility is ay's property,
not this repo's. Until that closes, the determinism guarantee does **not**
cover `SmtProof` evidence digests on the bv-blast path.

### Build identity (`BUILD_IDENTITY`, every tool's `--version`)

`trust_ir::BUILD_IDENTITY` names the COMPILED crate: package version, source
sha, wire version and read range, and the module-identity digest domain. The
tools print it as `<name> <MAJOR.MINOR.0>+<source>`. `<source>` is `g<12-hex>`
only when packaging supplied `ALAB_BUILD_GIT_SHA` with
`ALAB_BUILD_GIT_DIRTY=0`, `g<12-hex>.dirty` when it said `1`,
`g<12-hex>.local` when the build script read `git` in the crate's OWN checkout
(the working tree is not attested), and `unknown` otherwise. A malformed
override fails the build, and so does the `TRUST_BUILD_GIT_*` spelling:
verified Targo scrubs `TRUST_*` from build scripts, so that name could not
carry the override on the verified lane. A crate vendored inside another repository reports
`unknown`, never the enclosing repository's sha.

What it is NOT: an authority. It is a provenance label that packaging
supplies and nothing verifies. No validator, digest, or admission decision
reads it, and a packager who sets the override is trusted to have told the
truth. It exists so a measurement can say WHICH build it measured, because
many commits share one package version.

Determinism: a binary's bytes now vary with the source sha. That is intended
and does not affect diverse double-compilation, because every diverse compiler
builds the same source with the same sha. Emitted TrustIr and every digest
are unaffected.

## Frontend emission handshake

Producers (tRust, Clean) emit TrustIr through the `trust-ir-build` builder
API and may carry source provenance via the debug-info source-file table
(`Module::intern_file` + `SourceSpan::file`, since binary VERSION 9). The pinned
conformance subset a producer must round-trip is the `trust-ir-conformance`
corpus. A typed in-process handoff for verification requests already exists
(`trust_ir::request::NativeVerificationBundle`). What remains roadmap is a
first-class span-threaded emission bridge from native MIR, tracked on the
internal frontend-emission integration roadmap.
