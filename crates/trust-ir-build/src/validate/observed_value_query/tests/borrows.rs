// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn reverse_stored_borrow_chains_keep_all_five_exact_fat_root_spellings() {
    for kind in [
        FatPtrKind::Slice(TyId::new(4)),
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: 81 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ] {
        let mut f = function(vec![
            node(Inst::Borrow { ptr: id(8) }, &[7]),
            node(Inst::BorrowMut { ptr: id(9) }, &[8]),
            node(Inst::Borrow { ptr: id(1) }, &[9]),
        ]);
        f.blocks[0].params.push((id(1), Ty::FatPtr(kind)));
        for value in [7, 8, 9] {
            assert_eq!(parity(&f, value), Some(Ty::FatPtr(kind)));
        }
    }
}

#[test]
fn every_borrow_result_id_resolves_even_when_bridge_only_corrects_its_first_result() {
    let mut f = function(vec![node(Inst::Borrow { ptr: id(1) }, &[7, 8, 9])]);
    f.blocks[0]
        .params
        .push((id(1), Ty::FatPtr(FatPtrKind::Str)));
    for value in [7, 8, 9] {
        assert_eq!(parity(&f, value), Some(Ty::FatPtr(FatPtrKind::Str)));
    }
    assert_eq!(
        super::super::super::build_function_value_types(&f)[&8],
        Ty::Ptr
    );
}

#[test]
fn first_duplicate_borrow_operand_wins_even_when_the_bridge_map_keeps_the_last() {
    let mut f = function(vec![
        node(Inst::Borrow { ptr: id(1) }, &[7]),
        node(Inst::BorrowMut { ptr: id(2) }, &[7]),
    ]);
    f.blocks[0]
        .params
        .extend([(id(1), Ty::FatPtr(FatPtrKind::Str)), (id(2), Ty::Ptr)]);
    assert_eq!(parity(&f, 7), Some(Ty::FatPtr(FatPtrKind::Str)));
    assert_eq!(
        super::super::super::build_function_value_types(&f)[&7],
        Ty::Ptr
    );
}

#[test]
fn cycles_terminate_and_absent_thin_and_refined_fat_roots_still_return_some_ptr() {
    let cycle = function(vec![
        node(Inst::Borrow { ptr: id(8) }, &[7]),
        node(Inst::BorrowMut { ptr: id(7) }, &[8]),
    ]);
    for value in [7, 8] {
        assert_eq!(parity(&cycle, value), Some(Ty::Ptr));
    }
    let mut f = function(vec![node(Inst::Borrow { ptr: id(1) }, &[7])]);
    assert_eq!(parity(&f, 7), Some(Ty::Ptr));
    for ty in [
        Ty::Ptr,
        Ty::Tuple(vec![Ty::Error; 100]),
        Ty::Refine(TyId::new(99), PredId::new(1)),
    ] {
        f.blocks[0].params = vec![(id(1), ty)];
        assert_eq!(parity(&f, 7), Some(Ty::Ptr));
    }
}

#[test]
fn borrow_count_counts_instructions_including_empty_and_duplicate_result_lists() {
    let f = function(vec![
        node(Inst::Borrow { ptr: id(8) }, &[7]),
        node(Inst::BorrowMut { ptr: id(7) }, &[8]),
        node(Inst::Borrow { ptr: id(1) }, &[]),
        node(Inst::Borrow { ptr: id(2) }, &[7, 8]),
    ]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        scan::borrow_count(
            &f,
            &mut Work {
                session: &mut session,
                site: site()
            }
        )
        .unwrap(),
        4
    );
    assert_eq!(super::super::super::borrow_instruction_count(&f), 4);
    assert_eq!(parity(&f, 7), Some(Ty::Ptr));
}

#[test]
fn root_lookup_preserves_first_typeable_definition_and_skips_discarded_nonfat_clones() {
    let mut f = function(vec![
        node(Inst::Borrow { ptr: id(1) }, &[7]),
        node(Inst::Undef { ty: Ty::U8 }, &[1]),
        node(
            Inst::Undef {
                ty: Ty::FatPtr(FatPtrKind::Str),
            },
            &[1],
        ),
    ]);
    assert_eq!(parity(&f, 7), Some(Ty::Ptr));
    let shallow = run(&f, 7).1.events;
    f.blocks[0].body[1].inst = Inst::Undef {
        ty: Ty::Tuple(vec![Ty::Error; 100_000]),
    };
    assert_eq!(run(&f, 7).1.events, shallow);
    assert_eq!(parity(&f, 7), Some(Ty::Ptr));
    f.blocks[0].body.swap(1, 2);
    assert_eq!(parity(&f, 7), Some(Ty::FatPtr(FatPtrKind::Str)));
}
