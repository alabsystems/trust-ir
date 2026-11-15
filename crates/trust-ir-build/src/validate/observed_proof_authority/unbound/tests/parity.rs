use super::*;
#[test]
fn all_five_statuses_only_inspect_the_actual_kernel_tier() {
    for status in [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Certified,
    ] {
        let mut m = fixture();
        m.proof_obligations[0].status = status;
        for mode in [Mode::Unbound, Mode::Source] {
            run(&m, mode);
        }
        assert_eq!(
            oracle(&m, Mode::Unbound).len(),
            usize::from(status == ProofStatus::Certified)
        );
    }
}
#[test]
fn none_directive_binding_and_island_are_distinct_from_present_malformed_data() {
    for recheck in [
        None,
        Some(directive(None)),
        Some(directive(Some(binding(false)))),
        Some(directive(Some(binding(true)))),
    ] {
        let mut m = fixture();
        m.proof_certificates[0] = cert(&m.proof_obligations[0], recheck);
        for mode in [Mode::Unbound, Mode::Source] {
            run(&m, mode);
        }
    }
    let mut m = fixture();
    let mut r = directive(None);
    r.anchor = "clean_backend_tv_extra".into();
    m.proof_certificates[0] = cert(&m.proof_obligations[0], Some(r));
    assert_eq!(oracle(&m, Mode::Source), vec![]);
    run(&m, Mode::Source);
}
#[test]
fn empty_terms_missing_nonclean_and_wrong_id_candidates_do_not_double_name_replay_errors() {
    let mut m = fixture();
    m.proof_certificates.clear();
    for mode in [Mode::Unbound, Mode::Source] {
        run(&m, mode);
        assert!(oracle(&m, mode).is_empty());
    }
    for evidence in [
        ProofEvidence::Trusted("fake".into()),
        ProofEvidence::CleanCic {
            term: vec![],
            context: vec![1],
            lineage: clean_cic_lineage_digest(&m.proof_obligations[0]),
            kernel_recheck: Some(directive(None)),
        },
    ] {
        m.proof_certificates = vec![ProofCertificate {
            obligation: ProofId::new(7),
            prover: "x".into(),
            evidence,
            assurance: None,
        }];
        for mode in [Mode::Unbound, Mode::Source] {
            run(&m, mode);
            assert!(oracle(&m, mode).is_empty());
        }
    }
    let mut c = cert(&m.proof_obligations[0], Some(directive(None)));
    c.obligation = ProofId::new(99);
    m.proof_certificates = vec![c];
    run(&m, Mode::Unbound);
    assert!(oracle(&m, Mode::Unbound).is_empty());
}
#[test]
fn all_indexed_v5_v6_v7_and_symbolic_v8_lineages_preserve_actual_binding() {
    for version in [5, 6, 7, 8] {
        let mut m = fixture();
        if version >= 6 {
            let mut f = ProofFormula::new("schema", "payload");
            f.bindings = vec![(
                "x".into(),
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place: ClausePlace::Param { index: 0 },
                },
            )];
            m.proof_obligations[0].formula = Some(f);
        }
        if version >= 7 {
            m.proof_obligations[0].spec = Some(SpecObligationRef::new("machine", "temporal"));
        }
        m.proof_certificates[0] = if version == 8 {
            v8(&m, &m.proof_obligations[0], Some(directive(None)))
        } else {
            cert(&m.proof_obligations[0], Some(directive(None)))
        };
        for mode in [Mode::Unbound, Mode::Source] {
            run(&m, mode);
            assert_eq!(oracle(&m, mode).len(), 1);
        }
    }
}
#[test]
fn physical_row_duplicates_and_multiple_matching_certificates_preserve_row_order_once_each() {
    let mut m = fixture();
    m.proof_obligations = vec![row(19), row(7), row(19)];
    m.proof_certificates = m
        .proof_obligations
        .iter()
        .rev()
        .map(|r| cert(r, Some(directive(None))))
        .collect();
    m.proof_certificates.push(m.proof_certificates[0].clone());
    for mode in [Mode::Unbound, Mode::Source] {
        run(&m, mode);
        assert_eq!(oracle(&m, mode).len(), 3);
    }
    assert_eq!(
        oracle(&m, Mode::Unbound),
        vec![
            ValidationError::UnboundCertificate { obligation: 19 },
            ValidationError::UnboundCertificate { obligation: 7 },
            ValidationError::UnboundCertificate { obligation: 19 }
        ]
    );
}
#[test]
fn symbolic_owner_uses_unique_sparse_ids_and_never_a_duplicate_index_fallback() {
    let mut m = fixture();
    m.functions.push(Function::new(
        FuncId::new(77),
        "actual λ🙂 owner",
        FuncTyId::new(0),
        BlockId::new(1),
    ));
    m.proof_obligations[0].function = Some(FuncId::new(77));
    m.proof_certificates[0] = v8(&m, &m.proof_obligations[0], Some(directive(None)));
    run(&m, Mode::Unbound);
    assert_eq!(oracle(&m, Mode::Unbound).len(), 1);
    m.functions.push(Function::new(
        FuncId::new(77),
        "later duplicate",
        FuncTyId::new(0),
        BlockId::new(2),
    ));
    for mode in [Mode::Unbound, Mode::Source] {
        run(&m, mode);
        assert!(oracle(&m, mode).is_empty());
    }
    m.proof_certificates[0] = cert(&m.proof_obligations[0], Some(directive(None)));
    run(&m, Mode::Unbound);
    assert_eq!(
        oracle(&m, Mode::Unbound).len(),
        1,
        "indexed lineage has no symbol dependency"
    );
}
#[test]
fn any_candidate_search_continues_after_stale_rows_and_stops_after_first_actual_match() {
    let mut m = fixture();
    let good = m.proof_certificates[0].clone();
    let mut stale = good.clone();
    if let ProofEvidence::CleanCic { lineage, .. } = &mut stale.evidence {
        lineage.bytes[0] ^= 1;
    }
    m.proof_certificates = vec![stale, good.clone(), good];
    for mode in [Mode::Unbound, Mode::Source] {
        run(&m, mode);
        assert_eq!(oracle(&m, mode).len(), 1);
    }
}
#[test]
fn an_empty_table_has_no_errors_and_a_foreign_catalog_is_an_outer_binding_error() {
    let m = Module::new("");
    for mode in [Mode::Unbound, Mode::Source] {
        run(&m, mode);
    }
    let other = Module::new("");
    let c = ModuleFunctionCatalog::new(&other);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        call(&m, &c, Mode::Unbound, &mut s),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(s.first_refusal().is_none());
}
