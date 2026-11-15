// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_symbol_scalar_stop_retains_the_exact_prefix_before_later_fields() {
    let error = CompletenessError::ModuleIncomplete {
        rows: vec![row("beforeλafter", Some("must-not-start"), "unread")],
    };
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut output = String::new();
    display::write(
        &error,
        &mut Work {
            session: &mut session,
            site: site(),
        },
        &mut output,
    )
    .unwrap();
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.work == 8 * u32::BITS as usize && e.copy_bytes == size_of::<core::char::EscapeDebug>()
        })
        .nth(3)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut output = String::new();
    assert_eq!(
        display::write(&error, &mut work, &mut output),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        output,
        "the module claims to be partial: 1 unlowered item(s); \"bef"
    );
    let bytes = output.len();
    work.retire_text(output);
    assert_eq!(observer.events[stop].work, bytes + size_of::<String>() + 1);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_raw_reason_second_chunk_stop_retains_owned_prefix_and_no_smaller_diagnostic() {
    let error = CompletenessError::ModuleIncomplete {
        rows: vec![row("x", None, &"λ".repeat(3000))],
    };
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut output = String::new();
    display::write(
        &error,
        &mut Work {
            session: &mut session,
            site: site(),
        },
        &mut output,
    )
    .unwrap();
    let stop = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == 1024 && e.copy_bytes == 1024)
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut output = String::new();
    assert_eq!(
        display::write(&error, &mut work, &mut output),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        output,
        "the module claims to be partial: 1 unlowered item(s); \"x\": ".to_owned()
            + &"λ".repeat(512)
    );
    let bytes = output.len();
    work.retire_text(output);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "original completeness stop"
    );
    assert_eq!(observer.events[stop].work, bytes + size_of::<String>() + 1);
}
