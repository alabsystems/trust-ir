// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact instruction data for the versioned Core byte/world profile.
//!
//! This is not an evaluator. Module validation and the parent reflection pass
//! supply the mandatory layout, alignment, signature, and result context;
//! the shared Clean profile supplies the operational meaning. In particular,
//! the older cell-memory evaluator is not an authority for these memory
//! instructions merely because it accepts the same `IRInst` syntax.

use super::{CoreReflectionError, Reflection, app, boolean, c, cc, ids, nat, reject};
use clean_kernel::Expr;
use trust_ir::{AtomicRMWOp, BinOp, CastOp, ICmpOp, Inst, Ordering, OverflowOp, Ty};

// This is typed reflection, not an arithmetic prover. The byte profile's
// carrier checks and evaluator retain unsupported/fault outcomes; a consumer
// must prove its actual run. Validated scalar Bool BAnd/BOr/BXor map to the
// typed and_/or_/xor_ operators. This preserves Boolean values and faults, not
// nominal opcode identity or the separate Lean integer model's opcodes. Source
// validation rejects integer B* operands; reflection excludes Boolean vectors.
// The original module identity remains independent of canonical context equality.
fn binary(op: BinOp) -> Result<Expr, CoreReflectionError> {
    Ok(c(match op {
        BinOp::Add => "IRBinOp.add",
        BinOp::Sub => "IRBinOp.sub",
        BinOp::Mul => "IRBinOp.mul",
        BinOp::UDiv => "IRBinOp.udiv",
        BinOp::SDiv => "IRBinOp.sdiv",
        BinOp::URem => "IRBinOp.urem",
        BinOp::SRem => "IRBinOp.srem",
        BinOp::FAdd => "IRBinOp.fadd",
        BinOp::FSub => "IRBinOp.fsub",
        BinOp::FMul => "IRBinOp.fmul",
        BinOp::FDiv => "IRBinOp.fdiv",
        BinOp::FRem => "IRBinOp.frem",
        BinOp::FMin => "IRBinOp.fmin",
        BinOp::FMax => "IRBinOp.fmax",
        BinOp::And | BinOp::BAnd => "IRBinOp.and_",
        BinOp::Or | BinOp::BOr => "IRBinOp.or_",
        BinOp::Xor | BinOp::BXor => "IRBinOp.xor_",
        BinOp::Shl => "IRBinOp.shl",
        BinOp::LShr => "IRBinOp.lshr",
        BinOp::AShr => "IRBinOp.ashr",
        // WS3.20 (F-057): the pinned kernel's `IRBinOp` alphabet has no
        // rotate / copySign constructor. Inventing a name would reflect an
        // operator the kernel cannot evaluate, so these FAIL CLOSED until the
        // Clean side grows the constructors (a pin move, not a rename here).
        BinOp::RotL | BinOp::RotR | BinOp::FCopySign => {
            return Err(reject(
                "rotl / rotr / fcopysign have no IRBinOp constructor in the pinned Core byte \
                 profile v1 reflection",
            ));
        }
    }))
}

fn comparison(op: ICmpOp) -> Expr {
    c(match op {
        ICmpOp::Eq => "IRICmpOp.eq_",
        ICmpOp::Ne => "IRICmpOp.ne_",
        ICmpOp::Ult => "IRICmpOp.ult",
        ICmpOp::Ule => "IRICmpOp.ule",
        ICmpOp::Ugt => "IRICmpOp.ugt",
        ICmpOp::Uge => "IRICmpOp.uge",
        ICmpOp::Slt => "IRICmpOp.slt",
        ICmpOp::Sle => "IRICmpOp.sle",
        ICmpOp::Sgt => "IRICmpOp.sgt",
        ICmpOp::Sge => "IRICmpOp.sge",
    })
}

fn checked_arithmetic_type(ty: &Ty) -> Result<(), CoreReflectionError> {
    if matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
    ) {
        Ok(())
    } else {
        Err(reject(
            "checked arithmetic requires a nominal fixed-width integer in the Core byte profile",
        ))
    }
}

// Preserve syntax even for casts outside the byte evaluator's execution
// frontier. Reflection supplies no conversion, provenance or access proof:
// ir_byte_cast_eval_v1 checks the exact opcode, types and canonical carrier.
fn cast(op: CastOp) -> Expr {
    c(match op {
        CastOp::Trunc => "IRCastOp.trunc",
        CastOp::ZExt => "IRCastOp.zext",
        CastOp::SExt => "IRCastOp.sext",
        CastOp::FPTrunc => "IRCastOp.fptrunc",
        CastOp::FPExt => "IRCastOp.fpext",
        CastOp::FPToUI => "IRCastOp.fptoui",
        CastOp::FPToSI => "IRCastOp.fptosi",
        CastOp::FPToUISat => "IRCastOp.fptouisat",
        CastOp::FPToSISat => "IRCastOp.fptosisat",
        CastOp::UIToFP => "IRCastOp.uitofp",
        CastOp::SIToFP => "IRCastOp.sitofp",
        CastOp::PtrToInt => "IRCastOp.ptrtoint",
        CastOp::IntToPtr => "IRCastOp.inttoptr",
        CastOp::PtrToPtr => "IRCastOp.ptrtoptr",
        CastOp::Bitcast => "IRCastOp.bitcast",
        CastOp::Transmute => "IRCastOp.transmute",
        CastOp::ReifyFnPointer => "IRCastOp.reifyfnpointer",
    })
}

fn memory_options(volatile: bool, align: Option<u64>) -> Result<(), CoreReflectionError> {
    if volatile {
        return Err(reject(
            "volatile memory operations have no Core byte profile semantics",
        ));
    }
    if align == Some(0) {
        // The accompanying context uses zero to encode absent alignment, so
        // accepting Some(0) here would identify distinct source annotations.
        return Err(reject("explicit zero alignment cannot be reflected"));
    }
    Ok(())
}

fn scalar_memory_type(ty: &Ty) -> Result<(), CoreReflectionError> {
    if matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Usize
            | Ty::Ptr
            | Ty::Func(_)
    ) {
        Ok(())
    } else {
        Err(reject(
            "byte profile supports scalar loads/stores only, not aggregate memory",
        ))
    }
}

fn fat_pointer_type(ty: &Ty) -> Result<(), CoreReflectionError> {
    if matches!(ty, Ty::FatPtr(_)) {
        Ok(())
    } else {
        Err(reject(
            "only nominal fat-pointer part operations are admitted by this reflection profile",
        ))
    }
}

impl Reflection<'_> {
    pub(super) fn instruction(&mut self, inst: &Inst) -> Result<Expr, CoreReflectionError> {
        Ok(match inst {
            Inst::CallCannotUnwind { .. } | Inst::CallIndirectCannotUnwind { .. } => {
                return Err(reject(
                    "call unwind boundary requires a host-unwind semantic rule",
                ));
            }
            Inst::Const { ty, value } => {
                let reflected_ty = self.ty(ty)?;
                let reflected_value = self.constant(ty, value)?;
                app("IRInst.const_", [reflected_ty, reflected_value])
            }
            // There is no legacy IRInst.nullptr constructor. This explicit
            // mapping has exactly the same pointer type and null value;
            // it does not invent a numeric address or alias null to undef.
            Inst::NullPtr => app("IRInst.const_", [c("IRTy.ptr_"), c("IRConst.null_")]),
            Inst::BinOp { op, ty, lhs, rhs } => app(
                "IRInst.binop",
                [
                    binary(*op)?,
                    self.ty(ty)?,
                    nat(u64::from(lhs.0)),
                    nat(u64::from(rhs.0)),
                ],
            ),
            Inst::ICmp { op, ty, lhs, rhs } => app(
                "IRInst.icmp",
                [
                    comparison(*op),
                    self.ty(ty)?,
                    nat(u64::from(lhs.0)),
                    nat(u64::from(rhs.0)),
                ],
            ),
            Inst::Overflow { op, ty, lhs, rhs } => {
                checked_arithmetic_type(ty)?;
                // Preserve the actual opcode, signedness, width and SSA reads.
                // The shared Byte model computes both result lanes; reflection
                // proves neither their values nor the absence of overflow.
                // Assert kind/site and panic behavior remain unsupported.
                app(
                    "IRInst.overflow",
                    [
                        c(match op {
                            OverflowOp::AddOverflow => "IROverflowOp.addoverflow",
                            OverflowOp::SubOverflow => "IROverflowOp.suboverflow",
                            OverflowOp::MulOverflow => "IROverflowOp.muloverflow",
                        }),
                        self.ty(ty)?,
                        nat(u64::from(lhs.0)),
                        nat(u64::from(rhs.0)),
                    ],
                )
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => app(
                "IRInst.cast",
                [
                    cast(*op),
                    self.ty(src_ty)?,
                    self.ty(dst_ty)?,
                    nat(u64::from(operand.0)),
                ],
            ),
            Inst::Br { target, args } => app("IRInst.br", [nat(u64::from(target.0)), ids(args)]),
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => app(
                "IRInst.condbr",
                [
                    nat(u64::from(cond.0)),
                    nat(u64::from(then_target.0)),
                    ids(then_args),
                    nat(u64::from(else_target.0)),
                    ids(else_args),
                ],
            ),
            Inst::Call { callee, args } => {
                app("IRInst.call", [nat(u64::from(callee.0)), ids(args)])
            }
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => app(
                "IRInst.callindirect",
                [
                    nat(u64::from(callee.0)),
                    nat(u64::from(sig.0)),
                    ids(args),
                    nat(cc(*calling_conv)),
                ],
            ),
            Inst::Return { values } => app("IRInst.ret", [ids(values)]),
            // Only the fixed checked-source full-context path retains this
            // canonical syntax. Its actual Release33 dispatcher is explicitly
            // UNMODELLED, not an ARC transition, host call or rewritten body.
            Inst::Release { ptr } if self.retains_release => {
                app("IRInst.release", [nat(u64::from(ptr.index()))])
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => app(
                "IRInst.extractfield",
                [
                    self.ty(ty)?,
                    nat(u64::from(aggregate.0)),
                    nat(u64::from(*field)),
                ],
            ),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => app(
                "IRInst.insertfield",
                [
                    self.ty(ty)?,
                    nat(u64::from(aggregate.0)),
                    nat(u64::from(*field)),
                    nat(u64::from(value.0)),
                ],
            ),
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => {
                memory_options(*volatile, *align)?;
                scalar_memory_type(ty)?;
                app(
                    "IRInst.load",
                    [self.ty(ty)?, nat(u64::from(ptr.0)), boolean(*volatile)],
                )
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => {
                memory_options(*volatile, *align)?;
                scalar_memory_type(ty)?;
                app(
                    "IRInst.store",
                    [
                        self.ty(ty)?,
                        nat(u64::from(ptr.0)),
                        nat(u64::from(value.0)),
                        boolean(*volatile),
                    ],
                )
            }
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::U64,
                ptr,
                value,
                ordering: Ordering::Relaxed,
            } => {
                // This is the explicitly SEQUENTIAL byte model, not a
                // concurrent atomic/ownership certificate. The constructor
                // fixes width and ordering; preserve both actual SSA operands.
                // It returns the old value and checks eight-byte alignment in
                // the shared primitive, independently of site metadata.
                app(
                    "IRInst.atomic_fetch_add_relaxed_u64_seq",
                    [nat(u64::from(ptr.0)), nat(u64::from(value.0))],
                )
            }
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::Usize,
                ptr,
                value,
                ordering: Ordering::Relaxed,
            } => app(
                "IRInst.atomic_fetch_add_relaxed_usize_seq",
                [
                    nat(u64::from(self.usize_bits()?)),
                    nat(u64::from(ptr.0)),
                    nat(u64::from(value.0)),
                ],
            ),
            Inst::AtomicRMW { .. } => {
                return Err(reject(
                    "only Add/Relaxed/U64 or target-indexed Usize64 has sequential atomic byte-profile reflection",
                ));
            }
            Inst::Alloca { ty, count, align } => {
                memory_options(false, *align)?;
                // A count is an SSA operand, not a compile-time element count.
                // None and Some(value 0) must remain distinct constructors.
                let count = match count {
                    None => app("IROption.none", [c("Nat")]),
                    Some(id) => app("IROption.some", [c("Nat"), nat(u64::from(id.0))]),
                };
                app("IRInst.alloca", [self.ty(ty)?, count])
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => app(
                "IRInst.gep",
                [
                    self.ty(pointee_ty)?,
                    nat(u64::from(base.0)),
                    ids(indices),
                    boolean(*inbounds),
                ],
            ),
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => app(
                "IRInst.select",
                [
                    self.ty(ty)?,
                    nat(u64::from(cond.0)),
                    nat(u64::from(then_val.0)),
                    nat(u64::from(else_val.0)),
                ],
            ),
            Inst::Assume { .. } => {
                return Err(reject("Assume cannot be erased by Core reflection"));
            }
            Inst::Copy { ty, operand } => {
                app("IRInst.copy", [self.ty(ty)?, nat(u64::from(operand.0))])
            }
            Inst::PtrData { ptr_ty, ptr } => {
                fat_pointer_type(ptr_ty)?;
                app("IRInst.ptrdata", [self.ty(ptr_ty)?, nat(u64::from(ptr.0))])
            }
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => {
                fat_pointer_type(ptr_ty)?;
                app(
                    "IRInst.ptrmetadata",
                    [
                        self.ty(ptr_ty)?,
                        self.ty(metadata_ty)?,
                        nat(u64::from(ptr.0)),
                    ],
                )
            }
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => {
                fat_pointer_type(ptr_ty)?;
                app(
                    "IRInst.ptrfromparts",
                    [
                        self.ty(ptr_ty)?,
                        self.ty(metadata_ty)?,
                        nat(u64::from(data.0)),
                        nat(u64::from(metadata.0)),
                    ],
                )
            }
            _ => {
                return Err(reject(
                    "instruction is outside the Core byte profile v1 reflection",
                ));
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cast_alphabet_preserves_all_seventeen_exact_constructors() {
        for (op, name) in [
            (CastOp::Trunc, "trunc"),
            (CastOp::ZExt, "zext"),
            (CastOp::SExt, "sext"),
            (CastOp::FPTrunc, "fptrunc"),
            (CastOp::FPExt, "fpext"),
            (CastOp::FPToUI, "fptoui"),
            (CastOp::FPToSI, "fptosi"),
            (CastOp::FPToUISat, "fptouisat"),
            (CastOp::FPToSISat, "fptosisat"),
            (CastOp::UIToFP, "uitofp"),
            (CastOp::SIToFP, "sitofp"),
            (CastOp::PtrToInt, "ptrtoint"),
            (CastOp::IntToPtr, "inttoptr"),
            (CastOp::PtrToPtr, "ptrtoptr"),
            (CastOp::Bitcast, "bitcast"),
            (CastOp::Transmute, "transmute"),
            (CastOp::ReifyFnPointer, "reifyfnpointer"),
        ] {
            assert_eq!(cast(op), c(&format!("IRCastOp.{name}")));
        }
    }

    #[test]
    fn binary_alphabet_preserves_exact_canonical_operator() {
        for (op, name) in [
            (BinOp::Add, "add"),
            (BinOp::Sub, "sub"),
            (BinOp::Mul, "mul"),
            (BinOp::UDiv, "udiv"),
            (BinOp::SDiv, "sdiv"),
            (BinOp::URem, "urem"),
            (BinOp::SRem, "srem"),
            (BinOp::FAdd, "fadd"),
            (BinOp::FSub, "fsub"),
            (BinOp::FMul, "fmul"),
            (BinOp::FDiv, "fdiv"),
            (BinOp::FRem, "frem"),
            (BinOp::FMin, "fmin"),
            (BinOp::FMax, "fmax"),
            (BinOp::And, "and_"),
            (BinOp::Or, "or_"),
            (BinOp::Xor, "xor_"),
            (BinOp::Shl, "shl"),
            (BinOp::LShr, "lshr"),
            (BinOp::AShr, "ashr"),
        ] {
            assert_eq!(binary(op).unwrap(), c(&format!("IRBinOp.{name}")));
        }
        // WS3.20: no kernel constructor exists for these yet; reflection
        // refuses rather than inventing one.
        for op in [BinOp::RotL, BinOp::RotR, BinOp::FCopySign] {
            assert!(
                binary(op).is_err(),
                "{op} must be refused by Core reflection"
            );
        }
    }

    #[test]
    fn comparison_alphabet_preserves_signedness_and_strictness() {
        for (op, name) in [
            (ICmpOp::Eq, "IRICmpOp.eq_"),
            (ICmpOp::Ne, "IRICmpOp.ne_"),
            (ICmpOp::Ult, "IRICmpOp.ult"),
            (ICmpOp::Ule, "IRICmpOp.ule"),
            (ICmpOp::Ugt, "IRICmpOp.ugt"),
            (ICmpOp::Uge, "IRICmpOp.uge"),
            (ICmpOp::Slt, "IRICmpOp.slt"),
            (ICmpOp::Sle, "IRICmpOp.sle"),
            (ICmpOp::Sgt, "IRICmpOp.sgt"),
            (ICmpOp::Sge, "IRICmpOp.sge"),
        ] {
            assert_eq!(comparison(op), c(name));
        }
    }

    #[test]
    fn checked_arithmetic_reflection_preserves_opcode_type_width_and_operands() {
        let module = crate::ModuleBuilder::new("instruction_data_only")
            .build()
            .expect("empty module");
        let mut reflection = Reflection {
            module: &module,
            fields: crate::core_reflection::runtime_fields::OperationalModuleFields::partition(
                &module,
            )
            .0,
            retains_release: false,
            memory_index_profile: crate::core_reflection::CoreMemoryIndexProfileV1::StrictI64,
            layout_table: module.layout_table(),
            functions: Default::default(),
            types: Default::default(),
            visiting: Default::default(),
            layouts: Vec::new(),
            layout_terms: Default::default(),
        };
        for (op, name) in [
            (OverflowOp::AddOverflow, "IROverflowOp.addoverflow"),
            (OverflowOp::SubOverflow, "IROverflowOp.suboverflow"),
            (OverflowOp::MulOverflow, "IROverflowOp.muloverflow"),
        ] {
            for (ty, carrier, width) in [
                (Ty::I8, "IRTy.int_", 8),
                (Ty::I16, "IRTy.int_", 16),
                (Ty::I32, "IRTy.int_", 32),
                (Ty::I64, "IRTy.int_", 64),
                (Ty::I128, "IRTy.int_", 128),
                (Ty::U8, "IRTy.uint_", 8),
                (Ty::U16, "IRTy.uint_", 16),
                (Ty::U32, "IRTy.uint_", 32),
                (Ty::U64, "IRTy.uint_", 64),
                (Ty::U128, "IRTy.uint_", 128),
            ] {
                let instruction = Inst::Overflow {
                    op,
                    ty,
                    lhs: trust_ir::ValueId::new(17),
                    rhs: trust_ir::ValueId::new(29),
                };
                assert_eq!(
                    reflection
                        .instruction(&instruction)
                        .expect("nominal integer"),
                    app(
                        "IRInst.overflow",
                        [c(name), app(carrier, [nat(width)]), nat(17), nat(29)]
                    )
                );
            }
            for ty in [Ty::Bool, Ty::Ptr, Ty::F32, Ty::F64, Ty::Usize, Ty::Isize] {
                assert!(
                    reflection
                        .instruction(&Inst::Overflow {
                            op,
                            ty,
                            lhs: trust_ir::ValueId::new(17),
                            rhs: trust_ir::ValueId::new(29),
                        })
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn unsupported_memory_annotations_do_not_silently_disappear() {
        assert!(memory_options(false, None).is_ok());
        assert!(memory_options(false, Some(1)).is_ok());
        assert!(memory_options(false, Some(8)).is_ok());
        assert!(memory_options(false, Some(0)).is_err());
        assert!(memory_options(true, None).is_err());
        assert!(memory_options(true, Some(8)).is_err());
    }

    #[test]
    fn atomic_instruction_reflection_is_exactly_add_relaxed_u64() {
        // Instruction-level data mapping only. Whole-module validation and
        // kernel execution are exercised separately; no target is invented.
        let module = crate::ModuleBuilder::new("instruction_data_only")
            .build()
            .expect("ModuleBuilder::build: test fixture");
        let mut reflection = Reflection {
            module: &module,
            fields: crate::core_reflection::runtime_fields::OperationalModuleFields::partition(
                &module,
            )
            .0,
            retains_release: false,
            memory_index_profile: crate::core_reflection::CoreMemoryIndexProfileV1::StrictI64,
            layout_table: module.layout_table(),
            functions: Default::default(),
            types: Default::default(),
            visiting: Default::default(),
            layouts: Vec::new(),
            layout_terms: Default::default(),
        };
        for op in [
            AtomicRMWOp::Xchg,
            AtomicRMWOp::Add,
            AtomicRMWOp::Sub,
            AtomicRMWOp::And,
            AtomicRMWOp::Or,
            AtomicRMWOp::Xor,
            AtomicRMWOp::Max,
            AtomicRMWOp::Min,
            AtomicRMWOp::UMax,
            AtomicRMWOp::UMin,
        ] {
            for ordering in [
                Ordering::Relaxed,
                Ordering::Acquire,
                Ordering::Release,
                Ordering::AcqRel,
                Ordering::SeqCst,
            ] {
                for ty in [
                    Ty::U8,
                    Ty::U16,
                    Ty::U32,
                    Ty::U64,
                    Ty::U128,
                    Ty::Usize,
                    Ty::I8,
                    Ty::I16,
                    Ty::I32,
                    Ty::I64,
                    Ty::I128,
                    Ty::Isize,
                    Ty::Bool,
                    Ty::Ptr,
                    Ty::F64,
                ] {
                    let result = reflection.instruction(&Inst::AtomicRMW {
                        op,
                        ty: ty.clone(),
                        ptr: trust_ir::ValueId::new(19),
                        value: trust_ir::ValueId::new(11),
                        ordering,
                    });
                    if op == AtomicRMWOp::Add && ordering == Ordering::Relaxed && ty == Ty::U64 {
                        assert_eq!(
                            result.unwrap(),
                            app(
                                "IRInst.atomic_fetch_add_relaxed_u64_seq",
                                [nat(19), nat(11)]
                            )
                        );
                    } else {
                        assert!(
                            result.is_err(),
                            "unsupported atomic shape: {op:?}/{ordering:?}/{ty:?}"
                        );
                    }
                }
            }
        }
        for instruction in [
            Inst::AtomicLoad {
                ty: Ty::U64,
                ptr: trust_ir::ValueId::new(19),
                ordering: Ordering::Relaxed,
            },
            Inst::AtomicStore {
                ty: Ty::U64,
                ptr: trust_ir::ValueId::new(19),
                value: trust_ir::ValueId::new(11),
                ordering: Ordering::Relaxed,
            },
            Inst::Fence {
                ordering: Ordering::SeqCst,
            },
        ] {
            assert!(reflection.instruction(&instruction).is_err());
        }
    }
}
