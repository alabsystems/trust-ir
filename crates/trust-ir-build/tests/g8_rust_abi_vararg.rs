// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GAP G8 regression tests — the VACUOUS CALL CHECK.
//
// `FuncTy::is_vararg` documents no meaning, and the vacancy gets used: a
// producer that cannot recover a callee's real signature encodes it as
// `params: [], is_vararg: true`, because that is the one shape the validator
// accepts unconditionally. It is an OFF-SWITCH, not an under-specification —
// the arity test becomes `actual < 0` (never true) and the arg/param zip
// iterates an empty list — and it lands on exactly the cross-producer edges
// the format's only structural guarantee is supposed to cover.
//
// The FORMAT half of the fix, tested here: `CallingConv::Rust` + `is_vararg`
// is refused. `extern "Rust"` has no variadic form, so the combination
// describes nothing a Rust function can be. A genuine `printf`-shaped C
// variadic is untouched — tested in both directions.
//
// (The PRODUCER half — giving an unknown signature an honest spelling — lives
// in the emitting repo and is out of scope here.)

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{CallingConv, Endianness, Function, Linkage, Module, TargetInfo};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{ModuleBuilder, validate_module};

/// Cross-object ABI agreement is only defined against a pinned target, so any
/// module carrying a foreign-ABI boundary needs one (`TargetInfoRequired`).
fn pin_target(module: &mut Module) {
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
}

fn vararg_errors(module: &Module) -> Vec<String> {
    validate_module(module)
        .into_iter()
        .filter_map(|error| match error {
            ValidationError::RustAbiVararg { detail, .. } => Some(detail),
            _ => None,
        })
        .collect()
}

/// One import declaration: `name`, `conv`, signature `params` (+ vararg tail).
fn import_module(name: &str, conv: CallingConv, params: Vec<Ty>, is_vararg: bool) -> Module {
    let mut module = Module::new("g8");
    pin_target(&mut module);
    let ft = module
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), name, ft, BlockId::new(0));
    func.linkage = Linkage::External;
    func.calling_conv = conv;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

// ---------------------------------------------------------------------------
// declarations
// ---------------------------------------------------------------------------

#[test]
fn the_unknown_signature_pattern_is_refused_on_a_rust_declaration() {
    // The exact shape measured on ~88% of call edges: no params, vararg true,
    // Rust ABI. Nothing about a call to it can be checked.
    let module = import_module("unknown_callee", CallingConv::Rust, vec![], true);
    assert!(
        vararg_errors(&module)
            .iter()
            .any(|d| d.contains("declares the Rust calling convention with variadic")),
        "the Rust+vararg smuggling pattern must be refused: {:?}",
        validate_module(&module)
    );
}

#[test]
fn a_rust_declaration_with_a_fixed_prefix_is_still_refused() {
    // The rule is about the ABI, not about the arity: `extern "Rust"` has no
    // variadic form at all, so a fixed prefix does not rehabilitate it. (And a
    // prefix is what makes the pattern hardest to spot: the zip checks the
    // first two args and waves the rest through.)
    let module = import_module(
        "half_known",
        CallingConv::Rust,
        vec![Ty::I32, Ty::Ptr],
        true,
    );
    assert_eq!(
        vararg_errors(&module).len(),
        1,
        "{:?}",
        validate_module(&module)
    );
}

#[test]
fn a_printf_shaped_c_variadic_declaration_still_validates() {
    // The rule must not cost the format its real variadic ABI: C IS variadic,
    // and `printf(const char *fmt, ...)` is the canonical shape.
    let module = import_module("printf", CallingConv::C, vec![Ty::Ptr], true);
    assert!(
        validate_module(&module).is_empty(),
        "a genuine C variadic import must validate: {:?}",
        validate_module(&module)
    );
}

#[test]
fn other_variadic_conventions_are_untouched() {
    for conv in [
        CallingConv::C,
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Swift,
    ] {
        let module = import_module("variadic", conv, vec![Ty::Ptr], true);
        assert!(
            vararg_errors(&module).is_empty(),
            "{conv} + vararg must not be refused: {:?}",
            validate_module(&module)
        );
    }
}

#[test]
fn a_non_variadic_rust_declaration_validates() {
    let module = import_module("ordinary", CallingConv::Rust, vec![Ty::I32], false);
    assert!(
        validate_module(&module).is_empty(),
        "the control case must stay clean: {:?}",
        validate_module(&module)
    );
}

// ---------------------------------------------------------------------------
// definitions
// ---------------------------------------------------------------------------

#[test]
fn a_rust_variadic_definition_is_refused_too() {
    // Restricting the rule to body-less declarations would leave a legal
    // spelling of an illegal signature: a DEFINED Rust function cannot be
    // variadic either, and a caller reading its signature is misled the same
    // way.
    let mut mb = ModuleBuilder::new("g8_def");
    let ft = mb.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("defined", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].calling_conv = CallingConv::Rust;

    assert!(
        vararg_errors(&module).len() == 1,
        "a defined Rust function must not be variadic either: {:?}",
        validate_module(&module)
    );

    // Same body under the C convention: legitimate, and untouched.
    module.functions[0].calling_conv = CallingConv::C;
    assert!(
        vararg_errors(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
}

// ---------------------------------------------------------------------------
// indirect edges
// ---------------------------------------------------------------------------

/// `fn caller(fptr: ptr, x: i32) -> i32 { call_indirect[conv] fptr(x) }` over a
/// variadic `sig`.
fn indirect_edge_module(conv: CallingConv) -> Module {
    let mut mb = ModuleBuilder::new("g8_indirect");
    let sig = mb.add_vararg_func_type(vec![Ty::I32], vec![Ty::I32]);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("caller", ft);
    let entry = fb.create_block();
    let fptr = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let r = fb.call_indirect_cc(fptr, sig, vec![x], conv);
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // A call edge whose conv differs from the enclosing function's is itself an
    // ABI boundary, so pin the target.
    pin_target(&mut module);
    module
}

#[test]
fn an_indirect_edge_declaring_rust_over_a_variadic_signature_is_refused() {
    let module = indirect_edge_module(CallingConv::Rust);
    assert!(
        vararg_errors(&module)
            .iter()
            .any(|d| d.contains("indirect call edge in bb0 declares the Rust calling convention")),
        "the same smuggling pattern on an indirect edge must be refused: {:?}",
        validate_module(&module)
    );

    // The edge really does have a callee-shaped instruction; this is not a
    // vacuous match on an empty body.
    assert!(matches!(
        module.functions[0].blocks[0].body[0].inst,
        Inst::CallIndirect { .. }
    ));
}

#[test]
fn an_indirect_edge_declaring_c_over_a_variadic_signature_validates() {
    let module = indirect_edge_module(CallingConv::C);
    assert!(
        validate_module(&module).is_empty(),
        "an indirect C variadic edge is legitimate: {:?}",
        validate_module(&module)
    );
    let _ = InstrNode::new(Inst::Unreachable);
}
