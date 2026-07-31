// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Supremacy Fixture Generator
//! Generates a large-scale CHC transition module for throughput testing.

use clap::Parser;
use std::fs;
use std::path::PathBuf;
use trust_ir::ty::Ty;
use trust_ir_build::AYBatchBuilder;

#[derive(Parser)]
struct Args {
    /// Number of states (basic blocks) to generate.
    #[arg(short, long, default_value_t = 10000)]
    states: usize,

    /// Output path for the generated .trust_ir module.
    #[arg(short, long, default_value = "supremacy.trust_ir")]
    output: PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    println!(
        "Generating supremacy fixture with {} states...",
        args.states
    );

    let mut ay = AYBatchBuilder::new("supremacy_fixture");
    let mut fb = ay.transition_function();

    let entry = fb.create_block();
    // Signature: (ptr, u64, ptr, u64, ptr, u64, ptr) -> u32
    let _model_values = fb.add_block_param(entry, Ty::Ptr);
    let _model_len = fb.add_block_param(entry, Ty::U64);
    let _batch_meta = fb.add_block_param(entry, Ty::Ptr);
    let _batch_meta_len = fb.add_block_param(entry, Ty::U64);
    let _output = fb.add_block_param(entry, Ty::Ptr);
    let _output_len = fb.add_block_param(entry, Ty::U64);
    let _status = fb.add_block_param(entry, Ty::Ptr);

    fb.switch_to_block(entry);

    // Create a chain of blocks
    for i in 1..args.states {
        let next_block = fb.create_block();
        // Add same params to each block for simplicity if needed,
        // but for a pure chain we just jump.
        fb.br(next_block, vec![]);
        fb.switch_to_block(next_block);

        if i % 1000 == 0 {
            println!("  Created {} blocks...", i);
        }
    }

    // Final block returns 0
    let ret_val = fb.iconst(Ty::U32, 0);
    fb.ret(vec![ret_val]);
    fb.build();

    let module = ay.build();
    let bytes = trust_ir::binary::serialize_module(&module);

    fs::write(&args.output, bytes)?;
    println!(
        "Successfully wrote supremacy fixture to {}",
        args.output.display()
    );

    Ok(())
}
