// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Original typed-module witness, not an authenticated Rust frontend/source
//! binding or a proof-grade constructor. All semantic images come from the
//! existing common reflector and the exact original module's binary encoder.
use crate::core_reflection::{ReflectedCoreModuleV1, reflect_core_rust_u64_leaf_v1};
use trust_ir::{BlockId, FuncId, FuncTyId, Inst, Module, Ty, ValueId};

pub struct RustU64IdentityModule<'m> {
    name: &'m str,
    reflected: ReflectedCoreModuleV1<'m>,
    original_bytes: Vec<u8>,
    function: FuncId,
    signature: FuncTyId,
    entry: BlockId,
    parameter: ValueId,
    returned: ValueId,
}
impl<'m> RustU64IdentityModule<'m> {
    /// Select a complete original singleton module. This does not manufacture
    /// an identity body: every actual node, signature, entry and operand is
    /// retained/checked, including the independently selected return operand.
    /// The original Rust/THIR body correspondence remains a separate premise.
    pub fn from_module(module: &'m Module, fid: FuncId, address: u64) -> Result<Self, String> {
        let [function] = module.functions.as_slice() else {
            return Err("source identity needs one complete original module function".into());
        };
        if function.id != fid {
            return Err("selected original function id mismatch".into());
        }
        let [block] = function.blocks.as_slice() else {
            return Err("source identity requires one complete entry block".into());
        };
        if block.id != function.entry {
            return Err("actual entry block mismatch".into());
        }
        let [(parameter, Ty::U64)] = block.params.as_slice() else {
            return Err("source identity requires its exact U64 entry parameter".into());
        };
        let [node] = block.body.as_slice() else {
            return Err("source identity requires its one complete Return node".into());
        };
        let Inst::Return { values } = &node.inst else {
            return Err("actual source-identity terminator is not Return".into());
        };
        let [returned] = values.as_slice() else {
            return Err("actual source-identity Return arity".into());
        };
        if !node.results.is_empty() {
            return Err("Return cannot manufacture SSA results".into());
        }
        let reflected =
            reflect_core_rust_u64_leaf_v1(module, &[(fid, address)]).map_err(|e| e.to_string())?;
        let original_bytes =
            trust_ir::binary::serialize_module(module).map_err(|e| e.to_string())?;
        Ok(Self {
            name: &function.name,
            reflected,
            original_bytes,
            function: fid,
            signature: function.ty,
            entry: function.entry,
            parameter: *parameter,
            returned: *returned,
        })
    }
    pub fn reflected(&self) -> &ReflectedCoreModuleV1<'m> {
        &self.reflected
    }
    pub fn original_bytes(&self) -> &[u8] {
        &self.original_bytes
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
    pub fn returned(&self) -> ValueId {
        self.returned
    }
    pub fn function_name(&self) -> &str {
        self.name
    }
}
