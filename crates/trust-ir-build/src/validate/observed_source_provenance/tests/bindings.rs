// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn blank_sort_duplicate_hir_duplicate_place_and_global_inconsistency_keep_per_binding_order() {
    let mut module = module();
    let mut source = rows().remove(0);
    source.bindings = vec![
        binding("z", 100, SourcePlace::FunctionParameter { index: 0 }),
        binding(" \t", 100, SourcePlace::FunctionParameter { index: 0 }),
    ];
    seal(&mut module, vec![source]);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec![
            "source loop 0 contains a blank binding name",
            "source loop 0 bindings are not strictly name-sorted at \" \\t\"",
            "source loop 0 duplicates binding HIR local id 100",
            "source loop 0 maps more than one identifier to FunctionParameter { index: 0 }",
            "HIR local id 100 is inconsistently mapped as \" \\t\"/(0, 0, 0)",
        ]
    );
}
#[test]
fn both_parameter_place_variants_preserve_missing_u32_maximum_index_spelling() {
    let mut module = module();
    let mut source = rows().remove(0);
    source.bindings = vec![
        binding(
            "entry",
            100,
            SourcePlace::FunctionParameter { index: u32::MAX },
        ),
        binding("loop", 101, SourcePlace::LoopParameter { index: u32::MAX }),
    ];
    seal(&mut module, vec![source]);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec![
            "binding \"entry\" names missing function parameter 4294967295",
            "binding \"loop\" names missing bb1 loop parameter 4294967295",
        ]
    );
    let mut module = super::module();
    extra_loop(&mut module, 4);
    let mut sources = rows();
    let mut second = sources[0].clone();
    second.source_loop_id = u32::MAX;
    second.hir_local_id = u32::MAX;
    second.header = BlockId::new(4);
    sources.push(second);
    seal(&mut module, sources);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec![
            "source-loop row 1 has id 4294967295, expected dense ordered id 1",
            "HIR local id 101 is inconsistently mapped as \"iter\"/(1, 4294967295, 0)",
        ]
    );
}
#[test]
fn loop_places_are_row_scoped_function_places_are_global_and_first_hir_mapping_is_retained() {
    let mut module = module();
    extra_loop(&mut module, 4);
    let mut sources = rows();
    let mut second = sources[0].clone();
    second.source_loop_id = 1;
    second.hir_local_id = 11;
    second.header = BlockId::new(4);
    second.bindings[1].hir_local_id = 201;
    sources.push(second);
    seal(&mut module, sources);
    assert!(parity(&module.functions[0], Some(&module)).is_empty());
    extra_loop(&mut module, 5);
    let mut sources = vec![];
    for (id, header, name, index) in [(0, 1, "arg", 0), (1, 4, "bad", 1), (2, 5, "arg", 0)] {
        sources.push(SourceLoopProvenance {
            source_loop_id: id,
            hir_local_id: 10 + id,
            header: BlockId::new(header),
            bindings: vec![binding(name, 100, SourcePlace::FunctionParameter { index })],
        });
    }
    seal(&mut module, sources);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec!["HIR local id 100 is inconsistently mapped as \"bad\"/(0, 0, 1)"]
    );
}
#[test]
fn global_hir_then_place_conflicts_preserve_original_first_values_and_tuple_spelling() {
    let mut module = module();
    extra_loop(&mut module, 4);
    extra_loop(&mut module, 5);
    let sources = vec![
        SourceLoopProvenance {
            source_loop_id: 0,
            hir_local_id: 10,
            header: BlockId::new(1),
            bindings: vec![binding(
                "arg",
                100,
                SourcePlace::FunctionParameter { index: 0 },
            )],
        },
        SourceLoopProvenance {
            source_loop_id: 1,
            hir_local_id: 11,
            header: BlockId::new(4),
            bindings: vec![binding(
                "changed",
                100,
                SourcePlace::LoopParameter { index: 0 },
            )],
        },
        SourceLoopProvenance {
            source_loop_id: 2,
            hir_local_id: 12,
            header: BlockId::new(5),
            bindings: vec![binding(
                "other",
                101,
                SourcePlace::FunctionParameter { index: 0 },
            )],
        },
    ];
    seal(&mut module, sources);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec![
            "HIR local id 100 is inconsistently mapped as \"changed\"/(1, 1, 0)",
            "place (0, 0, 0) is ambiguously mapped to HIR locals 100 and 101",
        ]
    );
}
#[test]
fn unicode_blank_scans_and_full_debug_string_quoting_match_ordinary_diagnostics_exactly() {
    let names = vec![
        "'\0λ\"\\\n\t\u{7f}\u{200d}\u{301}".to_string(),
        "a\u{301}".to_string(),
        "🙂\u{fe0f}".to_string(),
        "'\u{85}".to_string(),
        "λ".repeat(2000),
    ];
    for name in names {
        let mut module = module();
        let mut source = rows().remove(0);
        source.bindings = vec![
            binding(
                "\u{10ffff}",
                100,
                SourcePlace::FunctionParameter { index: 0 },
            ),
            binding(&name, 101, SourcePlace::LoopParameter { index: 0 }),
        ];
        seal(&mut module, vec![source]);
        assert_eq!(
            details(&parity(&module.functions[0], Some(&module))),
            vec![format!(
                "source loop 0 bindings are not strictly name-sorted at {name:?}"
            )]
        );
    }
    let mut module = module();
    let mut source = rows().remove(0);
    source.bindings = vec![binding(
        "\u{2003}\u{85}\t",
        100,
        SourcePlace::FunctionParameter { index: 0 },
    )];
    seal(&mut module, vec![source]);
    assert_eq!(
        details(&parity(&module.functions[0], Some(&module))),
        vec!["source loop 0 contains a blank binding name"]
    );
}
