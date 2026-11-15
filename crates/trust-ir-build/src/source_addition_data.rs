// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Private custody of the complete ORIGINAL typed logical arithmetic body.
//! No Rust frontend/TCX, physical ABI, native, admission or grade authority.
use crate::core_reflection::{ReflectedCoreModuleV1, reflect_core_rust_u64_add_literal_v1};
use trust_ir::{BinOp, BlockId, Constant, FuncId, FuncTyId, Inst, Module, Ty, ValueId};

pub struct RustU64AdditionModule<'m> {
    reflected: ReflectedCoreModuleV1<'m>,
    original_bytes: Vec<u8>,
    name: &'m str,
    function: FuncId,
    signature: FuncTyId,
    entry: BlockId,
    parameter: ValueId,
    constant: ValueId,
    literal: u64,
    addition: ValueId,
    returned: ValueId,
}
impl<'m> RustU64AdditionModule<'m> {
    pub fn from_module(module: &'m Module, fid: FuncId, address: u64) -> Result<Self, String> {
        let [function] = module.functions.as_slice() else {
            return Err("one complete original function required".into());
        };
        if function.id != fid {
            return Err("original function id mismatch".into());
        }
        let [block] = function.blocks.as_slice() else {
            return Err("one complete actual block required".into());
        };
        if block.id != function.entry {
            return Err("actual entry mismatch".into());
        }
        let [(parameter, Ty::U64)] = block.params.as_slice() else {
            return Err("exact U64 entry parameter required".into());
        };
        let [constant_node, add_node, return_node] = block.body.as_slice() else {
            return Err("complete Const/Add/Return population required".into());
        };
        let Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(literal),
        } = &constant_node.inst
        else {
            return Err("actual U64 integer constant required".into());
        };
        let literal = u64::try_from(*literal).map_err(|_| "literal outside full U64 domain")?;
        let [constant] = constant_node.results.as_slice() else {
            return Err("constant result arity".into());
        };
        let Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs,
            rhs,
        } = &add_node.inst
        else {
            return Err("actual U64 Add required".into());
        };
        if lhs != parameter || rhs != constant {
            return Err("actual Add parameter/literal operands mismatch".into());
        }
        let [addition] = add_node.results.as_slice() else {
            return Err("Add result arity".into());
        };
        let Inst::Return { values } = &return_node.inst else {
            return Err("actual Return required".into());
        };
        let [returned] = values.as_slice() else {
            return Err("Return operand arity".into());
        };
        if returned != addition || !return_node.results.is_empty() {
            return Err("Return must carry actual Add result".into());
        }
        let reflected = reflect_core_rust_u64_add_literal_v1(module, &[(fid, address)])
            .map_err(|e| e.to_string())?;
        let original_bytes =
            trust_ir::binary::serialize_module(module).map_err(|e| e.to_string())?;
        Ok(Self {
            reflected,
            original_bytes,
            name: &function.name,
            function: fid,
            signature: function.ty,
            entry: block.id,
            parameter: *parameter,
            constant: *constant,
            literal,
            addition: *addition,
            returned: *returned,
        })
    }
    pub fn reflected(&self) -> &ReflectedCoreModuleV1<'m> {
        &self.reflected
    }
    pub fn original_bytes(&self) -> &[u8] {
        &self.original_bytes
    }
    pub fn function_name(&self) -> &str {
        self.name
    }
    pub fn function_id(&self) -> FuncId {
        self.function
    }
    pub fn signature_id(&self) -> FuncTyId {
        self.signature
    }
    pub fn entry_block(&self) -> BlockId {
        self.entry
    }
    pub fn parameter(&self) -> ValueId {
        self.parameter
    }
    pub fn constant(&self) -> ValueId {
        self.constant
    }
    pub fn literal(&self) -> u64 {
        self.literal
    }
    pub fn addition(&self) -> ValueId {
        self.addition
    }
    pub fn returned(&self) -> ValueId {
        self.returned
    }
}
