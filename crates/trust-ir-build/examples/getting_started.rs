// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build, validate, and print a minimal executable TrustIr module.
//!
//! Pass `--trusted` to attach a structurally valid, faith-stamped proof
//! obligation for the README's `--forbid-trusted` tutorial.
//!
//! Run from the workspace root:
//!
//! ```text
//! cargo run --quiet --locked -p trust-ir-build --example getting_started
//! ```

use trust_ir::{ObligationKind, ProofId, ProofObligation, ProofStatus, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

fn main() {
    let mut module = ModuleBuilder::new("answer");
    let signature = module.add_func_type(vec![], vec![Ty::I64]);

    let mut program = module.function("program", signature);
    let entry = program.create_block();
    program.switch_to_block(entry);
    let twenty = program.iconst(Ty::I64, 20);
    let twenty_two = program.iconst(Ty::I64, 22);
    let answer = program.add(Ty::I64, twenty, twenty_two);
    program.ret(vec![answer]);
    program.build();

    let mut module = module.build();
    if std::env::args().any(|arg| arg == "--trusted") {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Trusted,
            "tutorial obligation accepted on faith",
        ));
    }

    let errors = validate_module(&module);
    assert!(errors.is_empty(), "{errors:#?}");
    print!("{module}");
}
