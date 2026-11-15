// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored controls only; all Rust controls are UNRUN.
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncId;
mod nested_cases;
mod payloads;
mod stops;
mod witnesses;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    work_cap: Option<usize>,
    refuse_later: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        if self.stop == Some(self.events.len()) {
            return Err("original cleanup refusal");
        }
        if self.refuse_later && self.stop.is_some_and(|stop| self.events.len() > stop) {
            return Err("later cleanup refusal");
        }
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("original cumulative work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(209))
}
fn headers(observer: &Observer) -> usize {
    // Current owned flat headers are String and Vec. Their retirement weights
    // agree; fixed fields in this exact enum inventory have different weights.
    assert_eq!(size_of::<String>(), size_of::<Vec<ValidationError>>());
    observer
        .events
        .iter()
        .filter(|event| {
            event.phase == ExecutionPhase::ScratchRetirement
                && event.work == size_of::<String>() + 1
        })
        .count()
}
fn one(error: ValidationError, expected_headers: usize) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_validation_error_observed(error, &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert_eq!(headers(&observer), expected_headers);
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.site == site() && event.copy_bytes == 0)
    );
    observer
}
fn corpus() -> Vec<ValidationError> {
    vec![
        ValidationError::BindingFrameAnalysisFailed {
            reason: "incomplete frame analysis".into(),
        },
        ValidationError::DuplicateFunctionSymbol {
            name: "name".into(),
            first: 1,
            second: 2,
            first_producer: Some(trust_ir::Producer::Other("foreign".into())),
            second_producer: None,
            first_display_path: Some(String::with_capacity(8)),
            second_display_path: Some("path".into()),
        },
        ValidationError::ImportCycle {
            import: 0,
            path: vec!["first".into(), "second".into(), String::with_capacity(32)],
        },
        ValidationError::FormulaTextsDisagree {
            site: trust_ir::proof::FormulaSite::SpecInvariant {
                machine: "machine".into(),
                invariant: "invariant".into(),
            },
        },
        ValidationError::InvalidSpecStructure {
            violation: trust_ir::SpecLinkViolation::CleanTheoremUnresolved {
                machine: "machine".into(),
                action: "action".into(),
                theorem: "theorem".into(),
                detail: "detail".into(),
            },
        },
        ValidationError::PointerConstantRefused {
            location: "location".into(),
            symbol: "symbol".into(),
            ty: "ty".into(),
            reason: PointerConstantRefusal::InvalidLength {
                length: "bad length".into(),
            },
        },
        ValidationError::AmbiguousImportedSymbol {
            symbol: "symbol".into(),
            imports: vec![1, 2, 3],
        },
    ]
}
fn run_corpus() -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire_validation_errors_observed(corpus(), &mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
    observer
}
