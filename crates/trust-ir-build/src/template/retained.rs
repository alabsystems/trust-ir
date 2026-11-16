// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual template coalescing followed by retained canonical merge placement.
//! These records are data correspondence only, never source/proof authority.

use std::collections::BTreeMap;
use std::sync::Arc;

use trust_ir::template::{HoleKind, Template};
use trust_ir::{FuncId, HoleId, Module, ProofDigest};

use super::{AnswerLog, InstantiateError, Instantiated, InstantiationHost, instantiate_mapped};
use crate::merge::{MergeError, RetainedImage};

/// One actual validated instantiation and the original template function/hole
/// IDs retained through its canonical symbol coalescing. Private fields prevent
/// attaching a copied map to unrelated data. Cloning preserves the same image.
/// Neither construction nor placement supplies any Rust/body/proof license.
#[derive(Clone, Debug)]
pub struct RetainedInstantiation {
    template: Arc<Template>,
    image: RetainedImage,
    template_digest: ProofDigest,
    instance_digest: ProofDigest,
    answers: AnswerLog,
    functions: BTreeMap<FuncId, FuncId>,
    callees: BTreeMap<HoleId, FuncId>,
}

impl RetainedInstantiation {
    /// Complete original input, including every original declaration and key.
    /// This is retained data, not authentication of a source-language owner.
    pub fn template(&self) -> &Template {
        &self.template
    }

    pub fn image(&self) -> &RetainedImage {
        &self.image
    }

    pub fn module(&self) -> &Module {
        self.image.module()
    }

    pub fn template_digest(&self) -> ProofDigest {
        self.template_digest
    }

    pub fn instance_digest(&self) -> ProofDigest {
        self.instance_digest
    }

    pub fn answers(&self) -> &AnswerLog {
        &self.answers
    }

    /// Actual final location of an original template function, including a
    /// declaration coalesced into the root. Unknown original IDs refuse.
    pub fn function_in(
        &self,
        image: &RetainedImage,
        original: FuncId,
    ) -> Result<FuncId, MergeError> {
        let function = self
            .functions
            .get(&original)
            .copied()
            .ok_or(MergeError::Dangling {
                table: "original template function",
                id: original.index(),
            })?;
        image.function_from(&self.image, function)
    }

    /// Locate an original callee hole through actual coalescing and placement.
    /// A type/global hole or an unknown hole is not a callee declaration.
    pub fn callee_in(&self, image: &RetainedImage, hole: HoleId) -> Result<FuncId, MergeError> {
        let original = self
            .callees
            .get(&hole)
            .copied()
            .ok_or(MergeError::Dangling {
                table: "original template callee hole",
                id: hole.index(),
            })?;
        self.function_in(image, original)
    }

    /// Extract the legacy data. Wrapping its module again cannot recover this
    /// instantiation's original allocation or its canonical placement history.
    pub fn into_instantiated(self) -> Instantiated {
        let Self {
            template: _,
            image,
            template_digest,
            instance_digest,
            answers,
            functions: _,
            callees: _,
        } = self;
        Instantiated {
            module: image.into_module(),
            template_digest,
            instance_digest,
            answers,
        }
    }
}

/// The same algorithm, validation, answers, module and digests as `instantiate`,
/// retaining the actual canonical declaration mapping in a separate API.
/// No wire format or serialized proof/capability is added.
pub fn instantiate_retained(
    template: &Template,
    host: &mut dyn InstantiationHost,
) -> Result<RetainedInstantiation, InstantiateError> {
    let (instance, coalesced) = instantiate_mapped(template, host)?;
    let Instantiated {
        module,
        template_digest,
        instance_digest,
        answers,
    } = instance;
    let invalid = |why: String| InstantiateError::AnswerConflict { why };
    let mut functions = BTreeMap::new();
    for original in &template.module.functions {
        let final_id = coalesced.get(&original.id).copied().ok_or_else(|| {
            invalid("canonical template coalescing lost an original function".into())
        })?;
        if module.function_by_id(final_id).is_none() {
            return Err(invalid(
                "canonical template function is absent from the final image".into(),
            ));
        }
        functions.insert(original.id, final_id);
    }
    let mut callees = BTreeMap::new();
    for (index, hole) in template.header.holes.iter().enumerate() {
        if let HoleKind::Callee { decl } = &hole.kind {
            let index =
                u32::try_from(index).map_err(|_| invalid("callee hole exceeds u32".into()))?;
            if !functions.contains_key(decl) {
                return Err(invalid(
                    "original callee hole lacks its canonical declaration".into(),
                ));
            }
            callees.insert(HoleId::new(index), *decl);
        }
    }
    let image = RetainedImage::new(module)
        .map_err(|error| invalid(format!("canonical template image: {error}")))?;
    Ok(RetainedInstantiation {
        template: Arc::new(template.clone()),
        image,
        template_digest,
        instance_digest,
        answers,
        functions,
        callees,
    })
}
