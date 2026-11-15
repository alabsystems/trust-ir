// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls for carrier consistency, no authority claim.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode, ModuleCompleteness, UnloweredRow};
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original completeness stop");
        }
        if self.cleanup && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(125))
}
fn row(symbol: &str) -> UnloweredRow {
    UnloweredRow {
        symbol: symbol.into(),
        display_path: None,
        reason: "opaque reason".into(),
    }
}
fn function(id: u32, name: &str, body: bool) -> Function {
    let mut f = Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
    if body {
        f.blocks.push(Block::new(BlockId::new(0)));
    }
    f
}
fn fixture() -> Module {
    let mut m = Module::new("partial");
    m.completeness = Some(ModuleCompleteness::Partial(vec![
        row("x"),
        row("x"),
        row("missing"),
    ]));
    m.functions = vec![
        function(7, "x", true),
        function(1, "x", true),
        function(7, "x", true),
        function(9, "x", false),
    ];
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_completeness_claim_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, validate_completeness_claim(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    (out, o)
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    work.retire_text(&mut state.symbol);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
#[test]
fn none_and_complete_remain_diagnostic_only_exemptions_not_completeness_evidence() {
    let mut m = fixture();
    for completeness in [None, Some(ModuleCompleteness::Complete)] {
        m.completeness = completeness;
        let (out, o) = run(&m);
        assert!(out.is_empty());
        assert_eq!(
            o.events
                .iter()
                .filter(|e| e.phase == ExecutionPhase::Validation)
                .count(),
            2
        );
    }
}
#[test]
fn empty_partial_claim_is_exactly_one_original_error() {
    let mut m = fixture();
    m.completeness = Some(ModuleCompleteness::Partial(vec![]));
    assert_eq!(run(&m).0, vec![ValidationError::EmptyPartialClaim]);
}
#[test]
fn every_physical_definition_is_reported_once_and_duplicate_claim_continues_before_definitions() {
    assert_eq!(
        run(&fixture()).0,
        vec![
            ValidationError::UnloweredRowNamesDefinition {
                symbol: "x".into(),
                function: 7
            },
            ValidationError::UnloweredRowNamesDefinition {
                symbol: "x".into(),
                function: 1
            },
            ValidationError::UnloweredRowNamesDefinition {
                symbol: "x".into(),
                function: 7
            },
            ValidationError::DuplicateUnloweredRow { symbol: "x".into() }
        ]
    );
}
#[test]
fn full_unicode_and_empty_symbol_identity_is_never_normalized() {
    let mut m = Module::new("unicode");
    m.completeness = Some(ModuleCompleteness::Partial(vec![
        row(""),
        row(" λ\0"),
        row("λ"),
        row(""),
    ]));
    m.functions = vec![
        function(0, "", true),
        function(1, " λ\0", false),
        function(2, "λ", true),
        function(3, "λ ", true),
    ];
    assert_eq!(
        run(&m).0,
        vec![
            ValidationError::UnloweredRowNamesDefinition {
                symbol: "".into(),
                function: 0
            },
            ValidationError::UnloweredRowNamesDefinition {
                symbol: "λ".into(),
                function: 2
            },
            ValidationError::DuplicateUnloweredRow { symbol: "".into() }
        ]
    );
}
#[test]
fn unrelated_reason_displaypath_and_body_contents_are_not_read_by_this_old_rule() {
    let mut m = Module::new("opaque");
    let mut item = row("x");
    item.reason = "λ".repeat(100_000);
    item.display_path = Some("p".repeat(100_000));
    m.completeness = Some(ModuleCompleteness::Partial(vec![item]));
    let mut f = function(3, "other", true);
    f.blocks[0].body = vec![InstrNode::new(Inst::Const {
        ty: Ty::Tuple(vec![Ty::Error; 10_000]),
        value: Constant::Aggregate(vec![Constant::Int(0); 10_000]),
    })];
    m.functions.push(f);
    let (out, o) = run(&m);
    assert!(out.is_empty());
    assert!(o.work < 100);
}
