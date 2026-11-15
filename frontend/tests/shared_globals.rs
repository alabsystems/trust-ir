//! Actual MIR-closure regression: body-local ids must not alias earlier data.
use std::path::Path;
use std::process::Command;
use trust_ir::interpret::Interpreter;

fn emit(root: &str) -> trust_ir::Module {
    // The Trust compiler this frontend links: RUSTC, else `trustc` — never a
    // bare `rustc` (targo exports RUSTC to build scripts, not to tests).
    let compiler = std::env::var_os("RUSTC")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "trustc".into());
    let output = Command::new(&compiler)
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{compiler:?} --print sysroot failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let sysroot = String::from_utf8(output.stdout).unwrap();
    let temp = std::env::temp_dir().join(format!(
        "trust-ir-shared-globals-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&temp).unwrap();
    let artifact = temp.join("shared.tir");
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/shared_globals_corpus.rs");
    let output = Command::new(env!("CARGO_BIN_EXE_trust_ir_mir"))
        .arg(source)
        .args([
            "--crate-type=lib",
            "--edition=2021",
            "--sysroot",
            sysroot.trim(),
        ])
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Cdebug-assertions=off",
        ])
        .args(["-Ztrust-verify=off", "--mir-emit-closure", root])
        .arg(&artifact)
        .current_dir(&temp)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let log = String::from_utf8(output.stderr).unwrap();
    assert!(log.contains("validate_module = 0 error(s)"), "{log}");
    assert!(log.contains("re-parse: OK"), "{log}");
    let text = std::fs::read_to_string(artifact).unwrap();
    let module = trust_ir::parser::parse_module(&text).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    std::fs::remove_dir_all(temp).unwrap();
    module
}

/// The globals a panic site's static location reaches (trust-ir amendment
/// P): the `Location` records sited checks name, and everything their
/// initializers point to (the file-name bytes). Every check now carries its
/// `Location`, so these sit beside the literals this file counts; they are
/// shared like any other constant allocation.
fn panic_location_globals(module: &trust_ir::Module) -> std::collections::BTreeSet<usize> {
    let mut found = std::collections::BTreeSet::new();
    let mut work: Vec<usize> = module
        .functions
        .iter()
        .flat_map(|f| f.instructions())
        .filter_map(|node| node.inst.panic_site())
        .filter_map(|site| site.location_global())
        .map(|global| global.as_usize())
        .collect();
    while let Some(index) = work.pop() {
        if !found.insert(index) {
            continue;
        }
        if let Some(init) = &module.globals[index].initializer {
            init.visit_constants(|constant| {
                if let trust_ir::Constant::SymbolAddr { symbol, .. } = constant {
                    if let Some(target) = module.globals.iter().position(|g| &g.name == symbol) {
                        work.push(target);
                    }
                }
            });
        }
    }
    found
}

/// The module's globals other than the panic-location ones.
fn data_globals(module: &trust_ir::Module) -> Vec<&trust_ir::Global> {
    let locations = panic_location_globals(module);
    assert!(
        !locations.is_empty(),
        "`byte_at`'s bounds check is a sited assert naming a static `Location`"
    );
    module
        .globals
        .iter()
        .enumerate()
        .filter(|(index, _)| !locations.contains(index))
        .map(|(_, global)| global)
        .collect()
}

#[test]
fn closure_members_share_absolute_global_ids_and_literal_identity() {
    let module = emit("shared_globals_root");
    let data = data_globals(&module);
    assert_eq!(data.len(), 3, "A, u and v; repeated u shares one global");
    let names: std::collections::BTreeSet<_> = module.globals.iter().map(|g| &g.name).collect();
    assert_eq!(
        names.len(),
        module.globals.len(),
        "no duplicate linker symbols"
    );
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "shared_globals_root")
        .unwrap();
    let result = Interpreter::with_module(&module)
        .execute_func(function.id, [])
        .unwrap();
    assert_eq!(result.returns.len(), 1);
    assert_eq!(
        result.returns[0].as_int().map(|value| value.as_unsigned()),
        Some(0x4175_7675)
    );
}

#[test]
fn later_vtables_count_prior_literals_and_reuse_the_same_table() {
    use trust_ir::{Constant, Inst};
    let module = emit("shared_vtables_root");
    let data = data_globals(&module);
    assert_eq!(data.len(), 3, "one literal and two distinct vtables");
    let global_for = |name: &str, size: i128| {
        let function = module.functions.iter().find(|f| f.name == name).unwrap();
        let ids: Vec<_> = function
            .instructions()
            .filter_map(|node| match node.inst {
                Inst::GlobalAddr { global } => Some(global),
                _ => None,
            })
            .collect();
        assert_eq!(ids.len(), 1, "{name} materializes one vtable address");
        let global = &module.globals[ids[0].as_usize()];
        assert!(global.name.starts_with("vtable."));
        let Some(Constant::Aggregate(fields)) = &global.initializer else {
            panic!("vtable initializer")
        };
        assert_eq!(
            fields[1],
            Constant::Int(size),
            "vtable must describe the actual referent"
        );
        ids[0]
    };
    let u64_table = global_for("vtable_u64", 8);
    assert_eq!(global_for("vtable_u64_repeat", 8), u64_table);
    assert_ne!(global_for("vtable_u32", 4), u64_table);
    assert!(data
        .iter()
        .any(|g| matches!(&g.initializer, Some(Constant::Bytes { data, .. }) if data == b"A")));
}
