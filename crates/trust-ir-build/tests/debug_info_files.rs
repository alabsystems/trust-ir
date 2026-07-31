// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Validator coverage for the debug-info source-file table: a `SourceSpan::file`
// index must point into `Module::files` when a table is present. (The binary/
// text round trip and the intern API are covered in the trust-ir crate's own
// tests/debug_info_files.rs.)

use trust_ir::Ty;
use trust_ir::value::SourceSpan;
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

#[test]
fn validator_rejects_out_of_range_span_file_index() {
    let mut mb = ModuleBuilder::new("dbg");
    let ft = mb.add_func_type(vec![], vec![]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let _z = fb.iconst(Ty::I32, 0);
        fb.ret(vec![]);
        fb.build();
    }
    let mut m = mb.build();
    m.intern_file("only.rs"); // 1 entry; index 0 valid, anything >= 1 dangles.

    // Plant an out-of-range span on the first node of the entry block.
    m.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file: 5,
        line: 1,
        col: 1,
    });

    let errs = validate_module(&m);
    assert!(
        errs.iter()
            .any(|e| matches!(e, ValidationError::SpanFileIndexOutOfRange { file: 5, .. })),
        "expected SpanFileIndexOutOfRange, got {errs:?}"
    );
}

#[test]
fn empty_file_table_skips_span_index_check() {
    // With no file table, spans are file-less (back-compat): any file value is
    // accepted because there is nothing to index into.
    let mut mb = ModuleBuilder::new("dbg");
    let ft = mb.add_func_type(vec![], vec![]);
    {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let _z = fb.iconst(Ty::I32, 0);
        fb.ret(vec![]);
        fb.build();
    }
    let mut m = mb.build();
    m.functions[0].blocks[0].body[0].span = Some(SourceSpan {
        file: 9,
        line: 1,
        col: 1,
    });
    assert!(
        !validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::SpanFileIndexOutOfRange { .. })),
        "empty file table must not trigger the span-index check"
    );
}
