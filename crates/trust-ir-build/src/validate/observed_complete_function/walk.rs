// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
// Fixed private pass selection expresses the original ordering; it is not an
// external flag, acceptance shortcut, callback or source authority.
enum Pass {
    Structure,
    Source,
    BodyGate,
    Symbols,
    Refinements,
    Havoc,
    Ssa,
    Types,
    Cfg,
    Switch,
    Parameters,
    Unwind,
    Frames,
    Memory,
    Flow,
    Effects,
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        module: Option<&Module>,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for pass in [Pass::Structure, Pass::Source, Pass::BodyGate, Pass::Symbols] {
            self.pass(pass, function, module, pointer_bits, work)?;
        }
        work.admit(1, 0)?;
        if module.is_none() {
            for pass in [Pass::Refinements, Pass::Havoc] {
                self.pass(pass, function, module, pointer_bits, work)?;
            }
        }
        work.admit(1, 0)?;
        if function.blocks.is_empty() {
            return Ok(());
        }
        self.ready(work)?;
        let checks =
            validate_function_instruction_checks_observed(function, work.session, work.site)?;
        // Immediate ownership before any reserve, new check or publication.
        self.pending = checks.errors;
        self.indirect = checks.has_indirect_call;
        self.merge(work)?;
        for pass in [
            Pass::Ssa,
            Pass::Types,
            Pass::Cfg,
            Pass::Switch,
            Pass::Parameters,
            Pass::Unwind,
            Pass::Frames,
            Pass::Memory,
            Pass::Flow,
        ] {
            self.pass(pass, function, module, pointer_bits, work)?;
        }
        work.admit(1, 0)?;
        if module.is_none() {
            self.pass(Pass::Effects, function, module, pointer_bits, work)?;
        }
        Ok(())
    }
    fn pass<O: ExecutionObserver>(
        &mut self,
        pass: Pass,
        function: &Function,
        module: Option<&Module>,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.admit(16, size_of::<Vec<ValidationError>>())?;
        self.pending = match pass {
            Pass::Structure => {
                validate_function_structure_observed(function, work.session, work.site)?
            }
            Pass::Source => {
                observed_source_provenance::validate_function_source_provenance_observed(
                    function,
                    module,
                    work.session,
                    work.site,
                )?
            }
            Pass::BodyGate => {
                validate_function_body_gate_observed(function, work.session, work.site)?
            }
            Pass::Symbols => {
                validate_function_symbol_attributes_observed(function, work.session, work.site)?
            }
            Pass::Refinements => validate_function_standalone_refinements_observed(
                function,
                work.session,
                work.site,
            )?,
            Pass::Havoc => {
                validate_function_havoc_placement_observed(function, work.session, work.site)?
            }
            Pass::Ssa => validate_function_ssa_observed(function, work.session, work.site)?,
            Pass::Types => {
                validate_function_types_observed(function, module, work.session, work.site)?
            }
            Pass::Cfg => {
                validate_function_control_flow_observed(function, work.session, work.site)?
            }
            Pass::Switch => validate_function_exhaustive_switch_shape_observed(
                function,
                pointer_bits,
                work.session,
                work.site,
            )?,
            Pass::Parameters => {
                validate_function_block_params_observed(function, module, work.session, work.site)?
            }
            Pass::Unwind => {
                validate_function_unwind_structure_observed(function, work.session, work.site)?
            }
            Pass::Frames => {
                validate_function_binding_frames_observed(function, work.session, work.site)?
            }
            Pass::Memory => {
                validate_function_memory_roles_observed(function, work.session, work.site)?
            }
            Pass::Flow => {
                validate_function_information_flow_observed(function, work.session, work.site)?
            }
            Pass::Effects => observed_effect_claims::validate_function_effect_claims_observed(
                function,
                module,
                work.session,
                work.site,
            )?,
        };
        self.merge(work)
    }
}
