# TrustIr Vision: The Universal Proof-Carrying IR

> **Status: aspirational.** This document describes the long-term direction,
> not the current shape of the code. Where it describes TLA+ state-machine
> embedding, per-node obligations, information-flow labels, or a
> `struct TrustIr { systems, actions, temporal, … }`, treat that as the *goal*.
> For what TrustIr actually is today, read [`README.md`](README.md) (the
> current public surface) and [`TRUST.md`](TRUST.md) (the trusted-base
> statement). The real top-level type is `Module` (see "What TrustIr
> Contains Today" below), not an in-IR TLA+ state machine.

## The Core Problem

Every verified language frontend reinvents the wheel:
- Rust verification tools (Prusti, Creusot, Kani) each build their own IR
- Each has incompatible proof formats
- Proofs don't compose across languages
- Codegen is unverified (proofs stop at LLVM)

**The whole stack must be verified.** Source → IR → Binary. One gap breaks the chain.

---

## The Solution: TrustIr

TrustIr is the universal intermediate representation for the t* verified compilation stack.

```
┌─────────────────────────────────────────────────────────────┐
│                    Source Languages                          │
├─────────────────────────────────────────────────────────────┤
│  tRust                    Clean                              │
│  Rust+proofs              programs+proofs (fused)            │
│     │                        │                               │
│     └────────────────────────┘                               │
│                         │                                    │
│                         ▼                                    │
│  ┌───────────────────────────────────────────────────────┐  │
│  │                       TrustIr                             │  │
│  │                                                        │  │
│  │  - State machine semantics (TLA+ embedded)            │  │
│  │  - Proof obligations attached to every node           │  │
│  │  - Information flow labels                            │  │
│  │  - Trust boundary markers                             │  │
│  │  - Typed (maps to source types)                       │  │
│  └───────────────────────────────────────────────────────┘  │
│                         │                                    │
│            ┌────────────┴────────────┐                       │
│            ▼                         ▼                       │
│     ┌─────────────┐          ┌─────────────┐                 │
│     │  ty + ay  │          │    TrustCg    │                 │
│     │  (verify)   │          │  (codegen)  │                 │
│     └─────────────┘          └─────────────┘                 │
│                                     │                        │
│                                     ▼                        │
│                       Verified Machine Code                  │
└─────────────────────────────────────────────────────────────┘
```

---

## Why TrustIr Exists

### One IR, Many Languages

tRust and Clean compile to TrustIr. Verification tools operate on TrustIr. TrustCg consumes TrustIr. (tSwift/tC are deprecated; the format keeps their capabilities — ARC ops now serve Clean's reference-counted runtime.)

**Benefits:**
- Write verification once, apply to all languages
- Cross-language proofs compose
- Single codegen backend to verify

### Proofs Travel With Code

TrustIr is proof-carrying:

```
Traditional IR:
  instruction → instruction → instruction

TrustIr:
  (instruction, precondition, postcondition, proof) →
  (instruction, precondition, postcondition, proof) →
  ...
```

*(Aspirational framing.)* The goal is that every instruction carries the proof
context relevant to it and every control-flow edge is justified. **Today** the
realized mechanism is narrower: instructions carry `ProofAnnotation`s (with an
optional `ProofRef` backref), and the module carries proof obligations and
certificates — there is no per-edge postcondition→precondition proof object yet.

### TLA+ Semantics Embedded (aspirational)

> Not embedded in the IR today. Whole-program / temporal verification is
> currently carried out-of-band through the `request` model (e.g.
> `TrustMcInvariantSource::TrustIrProofObligations`, a CHC/PDR handshake with
> ty/ay), and `ObligationKind` already includes `TemporalSafety` / `Liveness`.
> The table below is the intended correspondence, not a current `Module` field.

The intended state-machine correspondence:

| TrustIr Construct | TLA+ Meaning |
|----------------|--------------|
| State block | VARIABLES |
| Action function | TLA+ action |
| Guard (where) | Enabling condition |
| Effect (ensures) | Next-state relation |
| Invariant | Safety property □P |
| Temporal property | Liveness ◇P, P ~> Q |

This enables whole-program verification: not just "this function is correct" but "this system satisfies these temporal properties."

---

## What TrustIr Contains Today

The real top-level type is `Module` (`crates/trust-ir/src/lib.rs`). It is a
function-and-type container with module-level proof state — **not** an in-IR
TLA+ state machine. There are no `systems` / `actions` / `invariants` /
`temporal` / `boundaries` / `flow` fields:

```rust
pub struct Module {
    pub name: String,
    pub functions: Vec<Function>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    pub records: Vec<RecordDef>,
    pub closure_types: Vec<ClosureTy>,
    pub globals: Vec<Global>,
    pub func_types: Vec<FuncTy>,
    pub types: Vec<Ty>,                              // the type arena
    pub proof_obligations: Vec<ProofObligation>,     // verification requirements
    pub proof_certificates: Vec<ProofCertificate>,   // discharged evidence
    pub target_info: Option<TargetInfo>,             // None = target-independent
}
```

Proof obligations carry an optional owning-function scope
(`function: Option<FuncId>`); proof annotations (and an optional `ProofRef`
backref) live on functions and instructions. The aspirational state-machine /
information-flow / per-edge-proof structure above is **not** represented here
yet — see the status banner at the top of this document.

## What TrustIr Aspires To Contain (future)

The state-machine vision — declared systems, actions, invariants, temporal
properties, trust boundaries, and an information-flow graph — remains a design
target, not a `Module` field. The most concrete current foothold is the
out-of-band whole-program-invariant handshake in the `request` model
(`TrustMcInvariantSource::TrustIrProofObligations`) plus the `TemporalSafety` /
`Liveness` obligation kinds.

---

## Design Reference

The complete TrustIr architecture is documented in:

**`ty/designs/2026-01-28-trust-ir-trusted-rust.md`**

This design covers:

1. **Trusted Rust syntax extensions** - state { }, invariant { }, #[action], temporal properties
2. **TrustIr data structures** - Systems, Actions, Predicates, Obligations
3. **Verification pipeline** - MIR → TrustIr → verify → codegen
4. **Trust boundary analysis** - Identifying external dependencies
5. **Information flow types** - Tainted<T>, Secret<T>, tracking provenance
6. **TLA+ interop** - Extraction, import, refinement checking
7. **Critique and improvements** - Scalability, concurrency models, error handling

---

## The Guarantee

If TrustIr verifies and TrustCg compiles it:

**The binary provably does what the source specification says.**

No gaps. No "trust the compiler" hand-waving. Mathematical proof from source to machine code.
