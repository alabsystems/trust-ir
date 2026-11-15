// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Collect several roots in the EXISTING instance worklist. Root ordinals are
//! retained independently of discovery order; neither a repeated root nor a
//! shared callee produces another body. This is compilation, not proof credit.

use super::*;

pub(super) fn function_id(base: u32, ordinal: u32) -> LResult<FuncId> {
    base.checked_add(ordinal).map(FuncId::new).ok_or_else(|| {
        LowerError(format!(
            "worklist function id exceeds its space: base {base}, ordinal {ordinal}"
        ))
    })
}

pub(super) fn next_function_id(mb: &ModuleBuilder) -> LResult<FuncId> {
    mb.peek_next_func_id()
        .map_err(|error| LowerError(format!("worklist has no next builder function id: {error}")))
}

pub(super) fn collect_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    roots: impl IntoIterator<Item = MonoInstance<'tcx>>,
) -> LResult<(Worklist<'tcx>, Vec<u32>)> {
    let typing_env = TypingEnv::fully_monomorphized();
    let mut wl = Worklist::new();
    let root_ids = roots
        .into_iter()
        .map(|root| {
            // Reachability resolves callees with normalized, erased-region args;
            // roots must use the SAME canonical identity before interning.
            let args = tcx.normalize_erasing_regions(typing_env, ty::Unnormalized::new(root.args));
            wl.intern(MonoInstance {
                def: root.def,
                args,
            })
        })
        .collect::<LResult<Vec<_>>>()?;
    if root_ids.is_empty() {
        return bail("multi-root worklist requires an actual source root");
    }

    // Process each typed instance once, exactly as the single-root collector
    // did. Seeding all roots first keeps original use-order root ids explicit.
    let mut cursor = 0;
    while cursor < wl.instances.len() {
        let inst = &wl.instances[cursor];
        let (thir_steal, body_expr) = tcx
            .thir_body(inst.def)
            .map_err(|_| LowerError("M4: thir_body errored (tainted)".into()))?;
        let thir = thir_steal.borrow();
        let mut found = Vec::new();
        collect_calls_in_body(tcx, typing_env, &thir, inst.args, body_expr, &mut found)?;
        for callee in found {
            wl.intern(callee)?;
        }
        cursor += 1;
    }
    Ok((wl, root_ids))
}

/// Single-root export adapters keep their published names. A batch has no
/// ambiguous bare-method symbol: each body is named from its actual compiler
/// instance at creation, and all calls still target the typed worklist's ids.
pub(super) enum WorklistSymbols<'tcx, 'name> {
    Legacy(&'name str),
    SourceOwned,
    RootExport {
        root: InstanceKey<'tcx>,
        suffix: &'name str,
    },
}

impl<'tcx> WorklistSymbols<'tcx, '_> {
    pub(super) fn name(&self, tcx: TyCtxt<'tcx>, inst: &MonoInstance<'tcx>) -> String {
        let legacy = match self {
            Self::Legacy(suffix) => Some(*suffix),
            Self::RootExport { root, suffix } if *root == inst.key() => Some(*suffix),
            Self::SourceOwned | Self::RootExport { .. } => None,
        };
        match legacy {
            Some(suffix) => format!("{}__{suffix}", tcx.item_name(inst.def.to_def_id())),
            None => tcx
                .symbol_name(Instance::new_raw(inst.def.to_def_id(), inst.args))
                .name
                .to_string(),
        }
    }
}

/// Roots arrive in the caller's original order. The index is an explicit
/// retained worklist ordinal, not an assumption that a root is FuncId 0.
pub(super) fn selected_roots(
    lowered: &[LoweredInstance],
    ordinals: &[u32],
) -> LResult<Vec<LoweredInstance>> {
    ordinals
        .iter()
        .map(|ordinal| {
            lowered.get(*ordinal as usize).cloned().ok_or_else(|| {
                LowerError(format!(
                    "multi-root emission has no retained root ordinal {ordinal}"
                ))
            })
        })
        .collect()
}
