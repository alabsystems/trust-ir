// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Original entry-prefix image assembly using the iteration assembler's exact
//! SSA, primitive, branching and image-composition path. No header operation
//! or synthetic analysis Return is executed by this prefix.
use super::*;

/// Which original successor occurrence reaches the selected header.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryHeaderEdge {
    Unconditional,
    Then,
    Else,
}

/// A function whose entry IS the header has no incoming source instruction.
pub enum EntryHeaderArrival<'m> {
    FunctionEntry,
    Edge {
        site: CutSite<'m>,
        arm: EntryHeaderEdge,
    },
}

/// Keep both the real edge argument identity and its header parameter binding.
pub struct EntryHeaderArgument {
    pub parameter: ValueId,
    pub ty: Ty,
    pub actual: CutValue,
}

/// Untrusted model inputs, freshly derived from the original prefix context.
/// Captures are computed original definitions, never fresh prefix parameters.
pub struct EntryHeaderBoundary<'m> {
    pub module: &'m Module,
    pub function: &'m Function,
    pub header: BlockId,
    pub arrival: EntryHeaderArrival<'m>,
    pub arguments: Vec<EntryHeaderArgument>,
    pub captures: Vec<CutValue>,
}
impl EntryHeaderBoundary<'_> {
    /// Current header SSA context for a separately reconstructed step image.
    /// This map is not an independent source-correspondence theorem.
    pub fn bindings(&self) -> Vec<CutValue> {
        self.arguments
            .iter()
            .map(|a| CutValue {
                id: a.parameter,
                ty: a.ty.clone(),
                term: a.actual.term.clone(),
            })
            .chain(self.captures.iter().cloned())
            .collect()
    }
}

/// Validated ORIGINAL entry-to-header prefix, including real early Returns.
/// The model must retain the complete header payload in its result. In
/// particular `Option::None` is insufficient unless the genuine post-state
/// already contains every computed header lane/capture. No state is invented.
pub struct EntryCutImageEndpoint<'m> {
    original: OriginalEndpoint<'m>,
    cut: EntryPrefixCut<'m>,
}
impl<'m> EntryCutImageEndpoint<'m> {
    pub fn new(
        report: &ModuleValidationReport<'m>,
        function: FuncId,
        header: BlockId,
    ) -> Result<Self> {
        let mut original = OriginalEndpoint::new(report, function)?;
        let cut = EntryPrefixCut::new(original.function, header)?;
        original.index_values()?;
        Ok(Self { original, cut })
    }

    /// Only actual entry parameters form this telescope, in signature order.
    /// All captures/edge arguments at the header are computed in the prefix.
    pub fn reconstruct<M: CutImageModel, L: ScopedLocalAllocator>(
        &self,
        model: &M,
        locals: &mut L,
        types: ImageTypes,
        limits: CutImageLimits,
    ) -> Result<ParameterizedCutImage<'m>> {
        if limits.operations == 0 || limits.depth == 0 || limits.lanes == 0 {
            return Err("invalid cut image construction limits".into());
        }
        model.original(self.original.module, self.original.function)?;
        let entry = self
            .original
            .function
            .blocks
            .iter()
            .find(|b| b.id == self.original.function.entry)
            .ok_or("missing original entry block")?;
        if entry.params.len() > limits.lanes {
            return Err("entry image parameter lane limit".into());
        }
        let ids = entry.params.iter().map(|(id, _)| *id).collect::<Vec<_>>();
        let mut parameters = Vec::new();
        let mut bindings = BTreeMap::new();
        for (id, ty) in &entry.params {
            let local = locals.allocate_local(model.value_type(self.original.module, ty)?)?;
            bindings.insert(*id, local.term().clone());
            parameters.push(local);
        }
        let mut assembly = Assembly {
            original: &self.original,
            region: Region::Entry(&self.cut),
            model,
            locals,
            types,
            limits,
            operations: 0,
        };
        let candidate = if entry.id == self.cut.header() {
            assembly.spend(0)?;
            let args = ids
                .iter()
                .map(|id| assembly.read(&bindings, *id))
                .collect::<Result<Vec<_>>>()?;
            assembly.enter_header(EntryHeaderArrival::FunctionEntry, args, &bindings)?
        } else {
            assembly.block(entry.id, bindings, 0)?
        };
        Ok(ParameterizedCutImage {
            module: self.original.module,
            function: self.original.function,
            header: self.cut.header(),
            role: ImageRole::Entry,
            nominal_types: entry.params.iter().map(|(_, ty)| ty.clone()).collect(),
            ids,
            parameters,
            candidate,
            operations: assembly.operations,
        })
    }

    /// Nominal custody and substitution only, with the SAME owner/freshness/
    /// expression-meaning obligations as `CutImageEndpoint::at_boundary`.
    /// An iteration image cannot be rebound here, even for an entry-header loop.
    pub fn at_entry(
        &self,
        image: &ParameterizedCutImage<'m>,
        bindings: &[CutValue],
    ) -> Result<CutImageCandidate> {
        let entry = self
            .original
            .function
            .blocks
            .iter()
            .find(|b| b.id == self.original.function.entry)
            .ok_or("missing original entry block")?;
        let ids = entry.params.iter().map(|(id, _)| *id).collect::<Vec<_>>();
        self.original
            .instantiate(image, self.cut.header(), ImageRole::Entry, &ids, bindings)
    }
}

impl<'a, 'm, M: CutImageModel, L: ScopedLocalAllocator> Assembly<'a, 'm, M, L> {
    pub(super) fn enter_header(
        &mut self,
        arrival: EntryHeaderArrival<'m>,
        arguments: Vec<CutValue>,
        bindings: &BTreeMap<ValueId, Expr>,
    ) -> Result<CutImageCandidate> {
        let Region::Entry(cut) = &self.region else {
            return Err("entry arrival outside prefix mode".into());
        };
        let header = self
            .original
            .function
            .blocks
            .iter()
            .find(|b| b.id == cut.header())
            .ok_or("missing original entry header")?;
        if arguments.len() != header.params.len() {
            return Err("entry header argument arity".into());
        }
        if arguments
            .len()
            .checked_add(cut.boundary_captures().len())
            .is_none_or(|n| n > self.limits.lanes)
        {
            return Err("entry header boundary lane limit".into());
        }
        let arguments = header
            .params
            .iter()
            .zip(arguments)
            .map(|((id, ty), actual)| {
                if *ty != actual.ty {
                    return Err("entry header nominal argument type".into());
                }
                Ok(EntryHeaderArgument {
                    parameter: *id,
                    ty: ty.clone(),
                    actual,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let captures = cut
            .boundary_captures()
            .iter()
            .map(|id| self.read(bindings, *id))
            .collect::<Result<Vec<_>>>()?;
        let boundary = EntryHeaderBoundary {
            module: self.original.module,
            function: self.original.function,
            header: cut.header(),
            arrival,
            arguments,
            captures,
        };
        self.model.entering(self.locals, &boundary, &self.types)
    }
}
