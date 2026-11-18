// Copyright 2026 Andrew Yates | Apache-2.0
//! Composition of the canonical ByteV1 operations. This module implements no
//! memory access, encoding, fault or permission semantics of its own.

use super::*;
use clean_kernel::{BinderInfo, Expr, Level};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), arguments)
}
fn ty(ty: &Ty) -> Expr {
    match ty {
        Ty::Ptr => c("IRTy.ptr_"),
        Ty::I8 => app("IRTy.int_", [Expr::nat_lit(8)]),
        Ty::U8 => app("IRTy.uint_", [Expr::nat_lit(8)]),
        Ty::I64 => app("IRTy.int_", [Expr::nat_lit(64)]),
        Ty::U64 => app("IRTy.uint_", [Expr::nat_lit(64)]),
        _ => unreachable!("the complete original plan checked every type"),
    }
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, domain, body)
}

/// Exact whole effect function: context -> incoming memory -> context address
/// -> output address -> (normal void unit OR original fault, final memory).
/// No source declaration or footprint is synthesized here. The independent
/// island definition must have this complete type and pass the original kernel.
pub(crate) fn denote(module: &Module, function: &Function) -> Result<(Expr, Expr), String> {
    denote_profile(module, function, Profile::ContextOutput)
}
pub(crate) fn denote_profile(
    module: &Module,
    function: &Function,
    profile: Profile,
) -> Result<(Expr, Expr), String> {
    let original = plan_profile(module, function, profile)?;
    let count = original.function.blocks[0].params.len();
    let values = original.function.blocks[0]
        .params
        .iter()
        .enumerate()
        .map(|(i, (id, _))| {
            (
                *id,
                app("IRScalar.ptr_", [Expr::bvar((count - i - 1) as u32)]),
            )
        })
        .collect();
    let body = tail(
        &original.function.blocks[0].body,
        values,
        Expr::bvar((count + 1) as u32),
        Expr::bvar(count as u32),
    )?;
    let mut domains = vec![c("IRByteContextV1"), c("IRByteMemoryV1")];
    domains.extend((0..count).map(|_| c("Nat")));
    let function_type = domains
        .iter()
        .rev()
        .fold(c("IRByteMemoryResultV1"), |body, domain| {
            Expr::pi(BinderInfo::Default, domain.clone(), body)
        });
    let value = domains
        .into_iter()
        .rev()
        .fold(body, |body, domain| lam(domain, body));
    Ok((function_type, value))
}

fn tail(
    nodes: &[trust_ir::InstrNode],
    mut values: BTreeMap<ValueId, Expr>,
    context: Expr,
    memory: Expr,
) -> Result<Expr, String> {
    let (node, rest) = nodes
        .split_first()
        .ok_or("byte entry denotation is missing Return")?;
    let get = |id: &ValueId| {
        values
            .get(id)
            .cloned()
            .ok_or("byte entry denotation lost an original SSA value")
    };
    let operation = match &node.inst {
        Inst::Return { values: returned } => {
            return Ok(app(
                "IRByteMemoryResultV1.value",
                [
                    if let [value] = returned.as_slice() {
                        get(value)?
                    } else {
                        c("IRScalar.unit_")
                    },
                    memory,
                ],
            ));
        }
        Inst::Const {
            value: Constant::Int(n),
            ..
        } => {
            values.insert(
                node.results[0],
                app("IRScalar.int_", [Expr::nat_lit(*n as u64)]),
            );
            return tail(rest, values, context, memory);
        }
        Inst::Copy { operand, .. } => {
            let source = get(operand)?;
            values.insert(node.results[0], source);
            return tail(rest, values, context, memory);
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            // The original plan establishes one nonnegative literal I64 index.
            // Use the SAME typed-index canonical operation as ByteV1's step.
            let index = get(&indices[0])?;
            let selected = app("ir_byte_gep_typed_index_v1", [ty(&Ty::I64), index]);
            app(
                "ir_byte_gep_typed_v1",
                [
                    context.clone(),
                    ty(pointee_ty),
                    get(base)?,
                    selected,
                    c(if *inbounds { "Bool.true" } else { "Bool.false" }),
                    memory.clone(),
                ],
            )
        }
        Inst::Load {
            ty: lane,
            ptr,
            align,
            ..
        } => app(
            "ir_byte_load_v1",
            [
                context.clone(),
                ty(lane),
                get(ptr)?,
                Expr::nat_lit(align.unwrap_or(0)),
                c("Bool.false"),
                memory.clone(),
            ],
        ),
        Inst::Store {
            ty: lane,
            ptr,
            value,
            align,
            ..
        } => app(
            "ir_byte_store_v1",
            [
                context.clone(),
                ty(lane),
                get(ptr)?,
                get(value)?,
                Expr::nat_lit(align.unwrap_or(0)),
                c("Bool.false"),
                memory.clone(),
            ],
        ),
        _ => unreachable!("the complete original plan checked every instruction"),
    };
    // A real fault returns immediately with precisely its actual memory. Only
    // a successful value branch executes the next original source instruction.
    let mut lifted = values
        .into_iter()
        .map(|(id, value)| (id, value.lift(2)))
        .collect::<BTreeMap<_, _>>();
    if let [id] = node.results.as_slice() {
        lifted.insert(*id, Expr::bvar(1));
    }
    let continuation = tail(rest, lifted, context.lift(2), Expr::bvar(0))?;
    let success = lam(c("IRScalar"), lam(c("IRByteMemoryV1"), continuation));
    let fault = lam(
        c("IROutcome"),
        lam(
            c("IRByteMemoryV1"),
            app("IRByteMemoryResultV1.fault", [Expr::bvar(1), Expr::bvar(0)]),
        ),
    );
    Ok(Expr::apps(
        Expr::const_(
            clean_kernel::Name::from_string("IRByteMemoryResultV1.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            lam(c("IRByteMemoryResultV1"), c("IRByteMemoryResultV1")),
            success,
            fault,
            operation,
        ],
    ))
}
