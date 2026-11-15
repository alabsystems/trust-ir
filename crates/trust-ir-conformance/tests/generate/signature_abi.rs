// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo};

#[path = "signature_abi_descriptor.rs"]
mod descriptor_fixture;
pub use descriptor_fixture::descriptor;

pub fn signature() -> FuncTy {
    FuncTy {
        params: vec![
            Ty::Ptr,
            Ty::I8,
            Ty::U64,
            Ty::F64,
            Ty::Tuple(vec![Ty::F32, Ty::F32, Ty::F32]),
            Ty::Ptr,
        ],
        returns: vec![],
        is_vararg: false,
        abi: Some(descriptor()),
    }
}
pub fn module() -> Result<Module, trust_ir::IdSpaceExhausted> {
    let mut module = Module::new("typed_signature_abi");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("darwinpcs".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.add_func_type(signature())?;
    Ok(module)
}

#[cfg(test)]
mod tests {
    use trust_ir::signature_abi::{AbiPassMode, AbiScalar};

    /// Regression (fix4 C5, `descriptor_fixture::scalar`): every scalar the
    /// descriptor builds carries `value_bits == 8 * source_bytes` and a register
    /// of its own width, computed without the old `(bytes * 8) as u16`.
    #[test]
    fn descriptor_scalars_have_exact_bit_widths() {
        let abi = super::descriptor();
        let mut scalars: Vec<&AbiScalar> = Vec::new();
        for argument in &abi.arguments {
            match &argument.mode {
                AbiPassMode::Direct(scalar) => scalars.push(scalar),
                AbiPassMode::Pair(first, second) => scalars.extend([first, second]),
                AbiPassMode::Ignore | AbiPassMode::Cast { .. } | AbiPassMode::Indirect { .. } => {}
            }
        }
        let widths: Vec<(u64, u16)> = scalars
            .iter()
            .map(|scalar| (scalar.source_bytes, scalar.value_bits))
            .collect();
        assert_eq!(widths, vec![(1, 8), (8, 64), (8, 64)]);
        for scalar in scalars {
            assert_eq!(scalar.register.bytes, scalar.source_bytes);
        }
    }
}
