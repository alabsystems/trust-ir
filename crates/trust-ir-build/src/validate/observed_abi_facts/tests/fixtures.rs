// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn module() -> Module {
    let mut m = Module::new("abi_group");
    m.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    m
}
pub(super) fn function() -> Function {
    Function::new(FuncId::new(6602), "f", FuncTyId::new(0), BlockId::new(0))
}
pub(super) fn untyped(
    params: Vec<Ty>,
    returns: Vec<Ty>,
    attrs: Vec<ParamAttrs>,
    ret: ParamAttrs,
) -> Module {
    let mut m = module();
    m.func_types
        .push(FuncTy::unrecorded(params, returns, false));
    let mut f = function();
    f.attrs.params = attrs;
    f.attrs.ret = ret;
    m.functions.push(f);
    m
}
pub(super) fn fact(pass: PassMode) -> ParamAttrs {
    ParamAttrs {
        pass: Some(pass),
        ..Default::default()
    }
}
pub(super) fn one(ty: Ty, attrs: ParamAttrs) -> Module {
    untyped(vec![ty], vec![], vec![attrs], Default::default())
}
pub(super) fn many_errors() -> Module {
    untyped(
        vec![Ty::U64, Ty::Bool],
        vec![Ty::U64],
        vec![
            ParamAttrs {
                ext: ArgExt::SignExt,
                pass: Some(PassMode::Cast { pieces: vec![] }),
                byval: true,
                ..Default::default()
            },
            fact(PassMode::Pair),
            ParamAttrs {
                nonnull: true,
                ..Default::default()
            },
        ],
        ParamAttrs {
            byval: true,
            sret: true,
            readonly: true,
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..Default::default()
        },
    )
}
pub(super) fn typed() -> Module {
    let abi = descriptor::descriptor();
    let mut m = module();
    m.target_info = Some(TargetInfo {
        triple: abi.target.triple.clone(),
        pointer_size: u32::from(abi.target.pointer_bytes),
        endianness: Endianness::Little,
        abi: Some(abi.target.abi.clone()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    m.func_types.push(FuncTy {
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
        abi: Some(abi),
    });
    let mut f = function();
    f.attrs.params = vec![ParamAttrs::default(); 6];
    f.attrs.params[0].sret = true;
    f.attrs.params[1].ext = ArgExt::SignExt;
    m.functions.push(f);
    m
}
