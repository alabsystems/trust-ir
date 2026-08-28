// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Raft Fixture Generator
//! Generates a TLA+ Raft grid-parallel synthesis module.

use clap::Parser;
use std::fs;
use std::path::PathBuf;
use trust_ir::ty::Ty;
use trust_ir_build::AYBatchBuilder;

#[derive(Parser)]
struct Args {
    /// Output path for the generated binary (`.tmbc`) module.
    // The fixture writes BINARY bytes (`serialize_module`), and the CLI maps the
    // `.trust_ir` extension to the TEXT format — so the default must be `.tmbc`
    // or a default-named output is a binary blob wearing a text extension.
    #[arg(short, long, default_value = "raft.tmbc")]
    output: PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    println!("Generating Raft fixture...");

    let mut ay = AYBatchBuilder::new("raft_fixture");
    let mut fb = ay.transition_function();

    let entry = fb.create_block();
    let _model_values = fb.add_block_param(entry, Ty::Ptr);
    let _model_len = fb.add_block_param(entry, Ty::U64);
    let _batch_meta = fb.add_block_param(entry, Ty::Ptr);
    let _batch_meta_len = fb.add_block_param(entry, Ty::U64);
    let _output = fb.add_block_param(entry, Ty::Ptr);
    let _output_len = fb.add_block_param(entry, Ty::U64);
    let _status = fb.add_block_param(entry, Ty::Ptr);

    fb.switch_to_block(entry);

    // Get thread/block ids for grid-parallel synthesis
    let tx = fb.gpu_thread_id_x().expect("tx");
    let bx = fb.gpu_block_id_x().expect("bx");
    let bdim = fb.gpu_block_dim_x().expect("bdim");

    // Simulate some TLA+ Raft state transition computation
    let prod = fb.mul(Ty::U32, bx, bdim);
    let _gid = fb.add(Ty::U32, prod, tx);

    fb.gpu_barrier().expect("barrier");

    let ret_val = fb.iconst(Ty::U32, 0);
    fb.ret(vec![ret_val]);
    fb.build();

    let module = ay.build();
    let bytes = trust_ir::binary::serialize_module(&module);

    fs::write(&args.output, bytes)?;
    println!(
        "Successfully wrote Raft fixture to {}",
        args.output.display()
    );

    Ok(())
}
