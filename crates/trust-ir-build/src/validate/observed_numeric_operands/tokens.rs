// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn binary<O: ExecutionObserver>(
    op: BinOp,
    work: &mut Work<'_, '_, O>,
) -> R<&'static str> {
    work.admit(26, size_of::<&str>())?;
    Ok(match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::UDiv => "udiv",
        BinOp::SDiv => "sdiv",
        BinOp::URem => "urem",
        BinOp::SRem => "srem",
        BinOp::FAdd => "fadd",
        BinOp::FSub => "fsub",
        BinOp::FMul => "fmul",
        BinOp::FDiv => "fdiv",
        BinOp::FRem => "frem",
        BinOp::FMin => "fmin",
        BinOp::FMax => "fmax",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::LShr => "lshr",
        BinOp::AShr => "ashr",
        BinOp::BAnd => "band",
        BinOp::BOr => "bor",
        BinOp::BXor => "bxor",
        BinOp::RotL => "rotl",
        BinOp::RotR => "rotr",
        BinOp::FCopySign => "fcopysign",
    })
}
pub(super) fn unary<O: ExecutionObserver>(op: UnOp, work: &mut Work<'_, '_, O>) -> R<&'static str> {
    work.admit(13, size_of::<&str>())?;
    Ok(match op {
        UnOp::Neg => "neg",
        UnOp::FNeg => "fneg",
        UnOp::FAbs => "fabs",
        UnOp::FSqrt => "fsqrt",
        UnOp::FFloor => "ffloor",
        UnOp::FCeil => "fceil",
        UnOp::FTrunc => "ftrunc",
        UnOp::Not => "not",
        UnOp::CtPop => "ctpop",
        UnOp::CtLz => "ctlz",
        UnOp::CtTz => "cttz",
        UnOp::BSwap => "bswap",
        UnOp::BitReverse => "bitreverse",
    })
}
pub(super) fn overflow<O: ExecutionObserver>(
    op: OverflowOp,
    work: &mut Work<'_, '_, O>,
) -> R<&'static str> {
    work.admit(3, size_of::<&str>())?;
    Ok(match op {
        OverflowOp::AddOverflow => "add.overflow",
        OverflowOp::SubOverflow => "sub.overflow",
        OverflowOp::MulOverflow => "mul.overflow",
    })
}
