// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Edge {
    Call,
    Invoke,
    Panic,
}
pub(super) fn convention(value: CallingConv) -> &'static str {
    match value {
        CallingConv::C => "ccc",
        CallingConv::Fast => "fastcc",
        CallingConv::Cold => "coldcc",
        CallingConv::Rust => "rustcc",
        CallingConv::Swift => "swiftcc",
        CallingConv::CUnwind => "c_unwindcc",
        CallingConv::SysV64 => "sysv64cc",
        CallingConv::Win64 => "win64cc",
        CallingConv::Aapcs => "aapcscc",
        CallingConv::EfiApi => "efiapicc",
        CallingConv::VectorCall => "vectorcallcc",
        CallingConv::RustCold => "rust_coldcc",
    }
}
fn unique<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'m Function>> {
    let mut found = None;
    let mut index = 0;
    while let Some(function) = work.at(&module.functions, index)? {
        work.admit(1, size_of::<FuncId>())?;
        if function.id == id {
            work.admit(1, size_of::<Option<&Function>>())?;
            if found.is_some() {
                return Ok(None);
            }
            found = Some(function);
        }
        work.next(&mut index)?;
    }
    Ok(found)
}
fn direct<O: ExecutionObserver>(
    module: &Module,
    caller: &Function,
    id: FuncId,
    kind: Edge,
    work: &mut Work<'_, '_, O>,
    out: &mut String,
) -> R<bool> {
    let Some(callee) = unique(module, id, work)? else {
        return Ok(false);
    };
    work.admit(1, 2 * size_of::<CallingConv>())?;
    if callee.calling_conv == caller.calling_conv {
        return Ok(false);
    }
    work.text(
        match kind {
            Edge::Call => "cross-convention call edge `",
            Edge::Invoke => "cross-convention invoke edge `",
            Edge::Panic => "cross-convention panic-site edge `",
        },
        out,
    )?;
    work.text(&caller.name, out)?;
    work.text("` (", out)?;
    work.text(convention(caller.calling_conv), out)?;
    work.text(") -> `", out)?;
    work.text(&callee.name, out)?;
    work.text("` (", out)?;
    work.text(convention(callee.calling_conv), out)?;
    work.text(")", out)?;
    Ok(true)
}
pub(super) fn first<O: ExecutionObserver>(
    module: &Module,
    work: &mut Work<'_, '_, O>,
    out: &mut String,
) -> R<bool> {
    work.admit(1, 0)?;
    if out.capacity() != 0 {
        return Err(ObservedValueError::InvalidRange);
    }
    // Exact original precedence: all bodyless declarations before any edge.
    let mut f = 0;
    while let Some(function) = work.at(&module.functions, f)? {
        work.admit(3, size_of::<CallingConv>() + size_of::<Linkage>())?;
        if function.blocks.is_empty()
            && matches!(function.linkage, Linkage::External | Linkage::ExternalWeak)
            && function.calling_conv != CallingConv::Rust
        {
            work.text("bodyless ", out)?;
            work.text(
                match function.linkage {
                    Linkage::External => "external",
                    Linkage::ExternalWeak => "external_weak",
                    _ => return Err(ObservedValueError::InvalidRange),
                },
                out,
            )?;
            work.text(" declaration `", out)?;
            work.text(&function.name, out)?;
            work.text("`", out)?;
            return Ok(true);
        }
        work.next(&mut f)?;
    }
    let mut f = 0;
    while let Some(function) = work.at(&module.functions, f)? {
        let mut b = 0;
        while let Some(block) = work.at(&function.blocks, b)? {
            let mut n = 0;
            while let Some(node) = work.at(&block.body, n)? {
                work.admit(1, 0)?;
                match &node.inst {
                    Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } => {
                        if direct(module, function, *callee, Edge::Call, work, out)? {
                            return Ok(true);
                        }
                    }
                    Inst::Invoke { callee, .. } => {
                        if direct(module, function, *callee, Edge::Invoke, work, out)? {
                            return Ok(true);
                        }
                    }
                    Inst::Assert {
                        site: Some(site), ..
                    }
                    | Inst::AssertInvoke { site, .. } => {
                        if direct(module, function, site.entry, Edge::Panic, work, out)? {
                            return Ok(true);
                        }
                    }
                    Inst::CallIndirect { calling_conv, .. }
                    | Inst::CallIndirectCannotUnwind { calling_conv, .. }
                    | Inst::InvokeIndirect { calling_conv, .. } => {
                        work.admit(1, 2 * size_of::<CallingConv>())?;
                        if *calling_conv != function.calling_conv {
                            work.text("cross-convention indirect call edge in `", out)?;
                            work.text(&function.name, out)?;
                            work.text("` (", out)?;
                            work.text(convention(function.calling_conv), out)?;
                            work.text(") declaring ", out)?;
                            work.text(convention(*calling_conv), out)?;
                            return Ok(true);
                        }
                    }
                    _ => {}
                }
                work.next(&mut n)?;
            }
            work.next(&mut b)?;
        }
        work.next(&mut f)?;
    }
    Ok(false)
}
