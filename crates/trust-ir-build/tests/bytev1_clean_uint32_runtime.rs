#![cfg(feature = "source-value-operational")]
use clean_kernel::{BinderInfo, Expr, Level, Name, TypeChecker};
use std::sync::OnceLock;
use trust_ir::clean_boxed_u32::{self as source, Allocation, RuntimeSources, UInt32Heap};
use trust_ir::{
    CallingConv, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
};
use trust_ir_build::{
    ModuleBuilder,
    bytev1_clean_uint32::{
        self as runtime, CheckedRuntimeProfile, RuntimeOperation, RuntimeSpecification,
    },
};
fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}
fn a(s: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(s), x)
}
fn n(v: u64) -> Expr {
    Expr::nat_lit(v)
}
fn list(ty: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    let x: Vec<_> = x.into_iter().collect();
    x.into_iter()
        .rev()
        .fold(a("IRList.nil", [c(ty)]), |tail, v| {
            a("IRList.cons", [c(ty), v, tail])
        })
}
fn spec() -> &'static RuntimeSpecification {
    static SPEC: OnceLock<RuntimeSpecification> = OnceLock::new();
    SPEC.get_or_init(|| runtime::specification().unwrap())
}
fn stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}
fn binding() -> source::RuntimeSourceBinding {
    RuntimeSources {
        object_model: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/object_model.rs.txt"
        ),
        ctor_scalar: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/ctor_scalar.rs.txt"
        ),
        rc_core: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/rc_core.rs.txt"
        ),
        refcount: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/refcount.rs.txt"
        ),
        public_api: include_bytes!(
            "../../trust-ir/tests/fixtures/clean_uint32_runtime/public_api.rs.txt"
        ),
    }
    .bind()
    .unwrap()
}
fn image(address: u64, value: u32, rc: u32) -> Allocation {
    let mut b = rc.to_le_bytes().to_vec();
    b.extend([0, 0, 0, 4]);
    b.extend(value.to_le_bytes());
    Allocation {
        address,
        alignment: 8,
        bytes: b.into_iter().map(Some).collect(),
        live: true,
    }
}
fn heap(images: Vec<Allocation>, credits: &[(u64, u64)]) -> UInt32Heap {
    UInt32Heap::new(binding(), images, credits.iter().copied().collect()).unwrap()
}
#[derive(Clone, Copy)]
enum Kind {
    Decode,
    Encode,
    Release,
    Alias,
    Unknown,
}
fn fixture(kind: Kind) -> (Module, FuncId) {
    let mut b = ModuleBuilder::new_with_target_info(
        "fresh_runtime_transition_fixture",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let ds = b.add_func_type(vec![Ty::Ptr], vec![Ty::U32]);
    let es = b.add_func_type(vec![Ty::U32], vec![Ty::Ptr]);
    let rs = b.add_func_type(vec![Ty::Ptr], vec![]);
    let decode = b.declare_function("clean_unbox_uint32", ds);
    let encode = b.declare_function("clean_box_uint32", es);
    let release = b.declare_function("clean_dec", rs);
    let unknown = b.declare_function("unbound_runtime", ds);
    let (params, returns) = match kind {
        Kind::Decode | Kind::Unknown => (vec![Ty::Ptr], vec![Ty::U32]),
        Kind::Encode => (vec![Ty::U32], vec![Ty::Ptr]),
        Kind::Release => (vec![Ty::Ptr], vec![]),
        Kind::Alias => (vec![Ty::Ptr, Ty::Ptr], vec![Ty::U32]),
    };
    let sig = b.add_func_type(params.clone(), returns);
    let root = b.declare_function("fresh_calling_function", sig);
    let mut f = b.define_function(root).unwrap();
    let entry = f.create_block();
    let args: Vec<_> = params
        .into_iter()
        .map(|ty| f.add_block_param(entry, ty))
        .collect();
    f.switch_to_block(entry);
    match kind {
        Kind::Decode => {
            let v = f.call(decode, vec![args[0]]);
            f.ret(vec![v]);
        }
        Kind::Encode => {
            let v = f.call(encode, vec![args[0]]);
            f.ret(vec![v]);
        }
        Kind::Release => {
            f.call_void(release, vec![args[0]]);
            f.ret(vec![]);
        }
        Kind::Alias => {
            let first = f.call(decode, vec![args[0]]);
            let _second = f.call(decode, vec![args[1]]);
            f.call_void(release, vec![args[0]]);
            f.call_void(release, vec![args[1]]);
            f.ret(vec![first]);
        }
        Kind::Unknown => {
            let v = f.call(unknown, vec![args[0]]);
            f.ret(vec![v]);
        }
    }
    f.build();
    (b.build().unwrap(), root)
}
fn tc() -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(spec().env());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(5_000_000);
    tc.set_max_cache_entries(100_000);
    tc
}
fn prove(label: &str, ty: Expr, left: Expr, right: Expr, accepted: bool) {
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), left, right.clone()],
    );
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, right],
    );
    let tc = tc();
    tc.check_type(&prop, &Expr::sort(Level::zero())).unwrap();
    let verdict = tc.check_type(&term, &prop);
    if accepted {
        assert!(verdict.is_ok(), "{label}: {verdict:?}");
        assert!(
            spec()
                .env()
                .audit_certification(&prop, &term)
                .is_certified()
        );
        let raw = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
        let restored = trust_ir::proof::decode_clean_expr_dag_v2(&raw).unwrap();
        tc.check_type(&restored, &prop).unwrap();
    } else {
        assert!(verdict.is_err(), "false refinement accepted: {label}");
    }
    assert!(
        !tc.heartbeat_spent(),
        "resource stop is not a verdict: {label}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}
fn run(
    module: &Module,
    root: FuncId,
    profile: &CheckedRuntimeProfile,
    state: &runtime::ProjectedRuntimeState,
    args: Vec<Expr>,
    fuel: u64,
) -> Expr {
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect();
    let reflected =
        trust_ir_build::core_reflection::reflect_core_module_v1(module, &addresses).unwrap();
    let ctx = reflected.context_term().clone();
    let initial = a(
        "ir_byte_init_v1",
        [
            c("IRCU32HostV1"),
            ctx.clone(),
            n(root.index().into()),
            list("IRScalar", args),
            state.memory.clone(),
            state.host.clone(),
        ],
    );
    a(
        "ir_byte_run_v1",
        [
            c("IRCU32HostV1"),
            ctx,
            profile.providers(),
            n(fuel),
            initial,
        ],
    )
}
fn outcome(run: Expr) -> Expr {
    a("ir_byte_outcome_v1", [c("IRCU32HostV1"), run])
}
fn final_world(run: Expr) -> Expr {
    a("ir_byte_final_world_v1", [c("IRCU32HostV1"), run])
}
fn final_memory(run: Expr) -> Expr {
    a(
        "ir_byte_world_memory_v1",
        [c("IRCU32HostV1"), final_world(run)],
    )
}
fn ret(v: Vec<Expr>) -> Expr {
    a("IROutcome.ret", [list("IRScalar", v)])
}
#[test]
fn checked_roots_have_general_heap_release_decoder_and_frame_laws() {
    stack(|| {
        for name in [
            "ir_cu32_decode_heap_law_v1",
            "ir_cu32_release_heap_law_v1",
            "ir_cu32_decode_tagged_law_v1",
            "ir_cu32_encode_law_v1",
            "ir_cu32_other_frame_credit_v1",
            "ir_cu32_rc_write_frame_v1",
            "ir_cu32_tagged_roundtrip_v1",
            "ir_cu32_drop_preserves_owners_v1",
        ] {
            let d = spec().get_definition(name).unwrap();
            let ty = d.elaborated_type.as_ref().unwrap();
            let term = d.elaborated_value.as_ref().unwrap();
            tc().check_type(term, ty).unwrap();
            assert!(spec().env().audit_certification(ty, term).is_certified());
        }
    })
}
#[test]
fn complete_original_catalog_is_bound_without_erasing_any_metadata() {
    stack(|| {
        let raw = include_bytes!("fixtures/source_value_equations/boundActualEquation/module.bin");
        let module = trust_ir::binary::deserialize_module(raw).unwrap();
        let before = module.clone();
        let p = CheckedRuntimeProfile::new(&module, binding()).unwrap();
        assert_eq!(module.functions.len(), 72);
        assert_eq!(module.func_types.len(), 73);
        assert_eq!(module.proof_obligations.len(), 1);
        assert_eq!(module.proof_certificates.len(), 1);
        let helper = module
            .functions
            .iter()
            .find(|f| f.name == "l_boundActualEquation___boxed")
            .unwrap();
        let releases: Vec<_> = helper
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|i| matches!(i.inst, Inst::Release { .. }))
            .collect();
        assert_eq!(releases.len(), 2);
        for release in releases {
            assert!(
                matches!(p.release_call(&module,&release.inst).unwrap(),Inst::Call{callee,..} if callee.index()==1)
            );
        }
        let addresses: Vec<_> = module
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
            .collect();
        assert!(
            trust_ir_build::core_reflection::reflect_core_module_v1(&module, &addresses).is_err()
        );
        let normalized = p.execution_module(&module).unwrap();
        assert_eq!(normalized.module().functions.len(), 72);
        assert_eq!(normalized.module().func_types.len(), 73);
        assert_eq!(
            normalized.module().proof_certificates,
            module.proof_certificates
        );
        assert_eq!(
            normalized.module().proof_obligations,
            module.proof_obligations
        );
        assert!(normalized.reflect(&addresses).is_err());
        assert_eq!(module, before);
        assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), raw);
    })
}
#[test]
fn typed_profile_rejects_duplicate_ids_signature_body_and_module_retargeting() {
    stack(|| {
        let (m, _) = fixture(Kind::Decode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut bad = m.clone();
        bad.functions[1].id = bad.functions[0].id;
        assert!(CheckedRuntimeProfile::new(&bad, binding()).is_err());
        let mut bad = m.clone();
        bad.functions[0].calling_conv = CallingConv::Fast;
        assert!(CheckedRuntimeProfile::new(&bad, binding()).is_err());
        let mut bad = m.clone();
        let ty = bad.functions[0].ty;
        bad.func_types[ty.as_usize()].returns = vec![Ty::U64];
        assert!(CheckedRuntimeProfile::new(&bad, binding()).is_err());
        assert!(
            p.release_call(
                &bad,
                &Inst::Release {
                    ptr: trust_ir::ValueId::new(0)
                }
            )
            .is_err()
        );
    })
}
#[test]
fn source_bridge_replays_real_heap_alias_effects_and_other_frame_credits() {
    stack(|| {
        let (m, _) = fixture(Kind::Alias);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(
            vec![image(8192, u32::MAX, 2), image(16384, 99, 0)],
            &[(8192, 2), (16384, 1)],
        );
        let f = h.begin(&[8192, 8192]).unwrap();
        let other = h.begin(&[16384]).unwrap();
        let owners = [(f, 1), (other, 7)];
        let a = p
            .check_transition(
                spec(),
                &h,
                f,
                &owners,
                RuntimeOperation::Release { slot: 0 },
            )
            .unwrap();
        a.replay(spec()).unwrap();
        let b = p
            .check_transition(
                spec(),
                a.source_after(),
                f,
                &owners,
                RuntimeOperation::Release { slot: 1 },
            )
            .unwrap();
        assert!(b.source_after().allocations()[&8192].live);
        assert_eq!(b.source_after().decode(8192), Ok(u32::MAX));
        assert_eq!(b.source_after().decode_input(other, 0), Ok(99));
        assert!(
            p.check_transition(
                spec(),
                b.source_after(),
                f,
                &owners,
                RuntimeOperation::Release { slot: 0 }
            )
            .is_err()
        );
    })
}
#[test]
fn actual_byte_machine_decodes_heap_and_every_u32_tagged_edge() {
    stack(|| {
        let (m, root) = fixture(Kind::Decode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        for v in [0, 1, 0x7fffffff, 0x80000000, u32::MAX] {
            let mut h = heap(vec![image(8192, v, 0)], &[(8192, 1)]);
            let f = h.begin(&[8192]).unwrap();
            let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
            for word in [8192, source::encode(v).word()] {
                let r = run(&m, root, &p, &state, vec![a("IRScalar.ptr_", [n(word)])], 2);
                prove(
                    "actual imported decode + root return",
                    c("IROutcome"),
                    outcome(r),
                    ret(vec![a("IRScalar.int_", [n(v.into())])]),
                    true,
                );
            }
        }
    })
}
#[test]
fn actual_byte_machine_encoder_has_no_31_bit_cutoff() {
    stack(|| {
        let (m, root) = fixture(Kind::Encode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        for v in [0, 0x80000000, u32::MAX] {
            let mut h = heap(vec![], &[]);
            let f = h.begin(&[]).unwrap();
            let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
            let r = run(
                &m,
                root,
                &p,
                &state,
                vec![a("IRScalar.int_", [n(v.into())])],
                2,
            );
            prove(
                "actual encoder",
                c("IROutcome"),
                outcome(r),
                ret(vec![a("IRScalar.ptr_", [n(source::encode(v).word())])]),
                true,
            );
        }
    })
}
#[test]
fn actual_alias_run_observes_every_fuel_prefix_rc_free_and_root_retirement() {
    stack(|| {
        let (m, root) = fixture(Kind::Alias);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(
            vec![image(8192, 0x80000000, 1), image(16384, 23, 3)],
            &[(8192, 2)],
        );
        let f = h.begin(&[8192, 8192]).unwrap();
        let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
        for fuel in 0..=5 {
            let r = run(
                &m,
                root,
                &p,
                &state,
                vec![a("IRScalar.ptr_", [n(8192)]); 2],
                fuel,
            );
            let expected = if fuel == 5 {
                ret(vec![a("IRScalar.int_", [n(0x80000000)])])
            } else {
                c("IROutcome.fuel_out")
            };
            prove(
                "exact fuel outcome",
                c("IROutcome"),
                outcome(r.clone()),
                expected,
                true,
            );
            let mem = final_memory(r.clone());
            let rc = if fuel < 3 {
                1
            } else if fuel == 3 {
                0
            } else {
                u32::MAX
            };
            prove(
                "actual RC bytes",
                a("IROption", [c("Nat")]),
                a(
                    "ir_byte_read_word_v1",
                    [a("ir_byte_mem_bytes_v1", [mem.clone()]), n(4), n(8192)],
                ),
                a("IROption.some", [c("Nat"), n(rc.into())]),
                true,
            );
            let row = a(
                "ir_cu32_allocation_at_v1",
                [a("ir_byte_mem_allocs_v1", [mem]), n(8192)],
            );
            let expected = a(
                "IROption.some",
                [
                    c("IRByteAllocationV1"),
                    a(
                        "IRByteAllocationV1.mk",
                        [
                            n(8192),
                            n(12),
                            n(0),
                            c(if fuel < 4 { "Bool.true" } else { "Bool.false" }),
                        ],
                    ),
                ],
            );
            prove(
                "last alias retires only heap leaf",
                a("IROption", [c("IRByteAllocationV1")]),
                row,
                expected,
                true,
            );
            let owners = a(
                "ir_byte_world_owners_v1",
                [c("IRCU32HostV1"), final_world(r)],
            );
            prove(
                "actual root owner retirement",
                a("IRList", [c("Nat")]),
                owners,
                if fuel < 5 {
                    list("Nat", [n(1)])
                } else {
                    list("Nat", [])
                },
                true,
            );
        }
    })
}
#[test]
fn actual_sticky_release_preserves_header_and_live_cell() {
    stack(|| {
        let (m, root) = fixture(Kind::Release);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        for rc in [0xe0000000, 0xf0000000, u32::MAX - 1] {
            let mut h = heap(vec![image(8192, 19, rc)], &[(8192, 1)]);
            let f = h.begin(&[8192]).unwrap();
            let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
            p.check_transition(
                spec(),
                &h,
                f,
                &[(f, 1)],
                RuntimeOperation::Release { slot: 0 },
            )
            .unwrap();
            let r = run(&m, root, &p, &state, vec![a("IRScalar.ptr_", [n(8192)])], 2);
            prove(
                "sticky actual return",
                c("IROutcome"),
                outcome(r.clone()),
                ret(vec![]),
                true,
            );
            prove(
                "sticky actual count",
                a("IROption", [c("Nat")]),
                a(
                    "ir_byte_read_word_v1",
                    [a("ir_byte_mem_bytes_v1", [final_memory(r)]), n(4), n(8192)],
                ),
                a("IROption.some", [c("Nat"), n(rc.into())]),
                true,
            );
        }
    })
}
#[test]
fn actual_invalid_inputs_and_unknown_imports_have_explicit_faults() {
    stack(|| {
        let (m, root) = fixture(Kind::Decode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        for case in 0..5 {
            let mut cell = image(8192, 17, 0);
            match case {
                0 => cell.live = false,
                1 => cell.bytes[5] = Some(3),
                2 => cell.bytes[8] = None,
                3 => cell.alignment = 16,
                _ => cell.bytes[..4].fill(Some(255)),
            };
            let mut h = heap(vec![cell], &[]);
            let f = h.begin(&[]).unwrap();
            let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
            let r = run(&m, root, &p, &state, vec![a("IRScalar.ptr_", [n(8192)])], 1);
            prove(
                "invalid heap ABI",
                c("IROutcome"),
                outcome(r),
                a("IROutcome.ub", [c("IRFault.bad_addr")]),
                true,
            );
        }
        let (m, root) = fixture(Kind::Unknown);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(vec![], &[]);
        let f = h.begin(&[]).unwrap();
        let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
        prove(
            "unknown runtime never executes",
            c("IROutcome"),
            outcome(run(
                &m,
                root,
                &p,
                &state,
                vec![a("IRScalar.ptr_", [n(1)])],
                1,
            )),
            a("IROutcome.unmodelled", [c("IRFault.width_bounded")]),
            true,
        );
    })
}
#[test]
fn changed_semantic_result_is_rejected_by_actual_core_replay() {
    stack(|| {
        let (m, root) = fixture(Kind::Decode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(vec![], &[]);
        let f = h.begin(&[]).unwrap();
        let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
        let r = run(
            &m,
            root,
            &p,
            &state,
            vec![a("IRScalar.ptr_", [n(source::encode(17).word())])],
            2,
        );
        prove(
            "wrong decoded value",
            c("IROutcome"),
            outcome(r),
            ret(vec![a("IRScalar.int_", [n(18)])]),
            false,
        );
    })
}

#[test]
fn actual_import_release_preserves_unrelated_frame_and_next_owner() {
    stack(|| {
        let (m, root) = fixture(Kind::Release);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(
            vec![image(8192, 29, 0), image(16384, 39, 0)],
            &[(8192, 1), (16384, 1)],
        );
        let f = h.begin(&[8192]).unwrap();
        let other = h.begin(&[16384]).unwrap();
        let owners = [(f, 1), (other, 7)];
        let state = runtime::project(&h, f, &owners).unwrap();
        let proof = p
            .check_transition(
                spec(),
                &h,
                f,
                &owners,
                RuntimeOperation::Release { slot: 0 },
            )
            .unwrap();
        let args = proof.provider_result().get_app_args();
        let returned_memory = (*args[2]).clone();
        let returned_host = (*args[3]).clone();
        let block = &m.functions.iter().find(|f| f.id == root).unwrap().blocks[0];
        let param = block.params[0].0;
        let destinations = list("Nat", []);
        let binding = |word| {
            a(
                "IRBinding.mk",
                [n(param.index().into()), a("IRScalar.ptr_", [n(word)])],
            )
        };
        let head = a(
            "IRFrame.mk",
            [
                n(root.index().into()),
                n(block.id.index().into()),
                n(0),
                list("IRBinding", [binding(8192)]),
                list("Nat", []),
            ],
        );
        let tail = list(
            "IRFrame",
            [a(
                "IRFrame.mk",
                [
                    n(root.index().into()),
                    n(block.id.index().into()),
                    n(1),
                    list("IRBinding", [binding(16384)]),
                    list("Nat", []),
                ],
            )],
        );
        let legacy = list("IRMemSlot", []);
        let machine = a(
            "IRMachine.mk",
            [
                a("IRList.cons", [c("IRFrame"), head.clone(), tail.clone()]),
                legacy.clone(),
                n(0),
            ],
        );
        let world = a(
            "IRByteWorldV1.mk",
            [
                c("IRCU32HostV1"),
                state.memory,
                state.host,
                list("Nat", [n(1), n(7)]),
                n(8),
            ],
        );
        let addresses: Vec<_> = m
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
            .collect();
        let reflected =
            trust_ir_build::core_reflection::reflect_core_module_v1(&m, &addresses).unwrap();
        let actual = a(
            "ir_byte_run_v1",
            [
                c("IRCU32HostV1"),
                reflected.context_term().clone(),
                p.providers(),
                n(1),
                a(
                    "IRByteConfigV1.running",
                    [c("IRCU32HostV1"), machine, world],
                ),
            ],
        );
        let expected = a(
            "IRByteConfigV1.running",
            [
                c("IRCU32HostV1"),
                a(
                    "IRMachine.mk",
                    [
                        a(
                            "IRList.cons",
                            [
                                c("IRFrame"),
                                a(
                                    "ir_frame_advance",
                                    [a(
                                        "ir_frame_set_many",
                                        [head, destinations, list("IRScalar", [])],
                                    )],
                                ),
                                tail,
                            ],
                        ),
                        legacy,
                        n(0),
                    ],
                ),
                a(
                    "IRByteWorldV1.mk",
                    [
                        c("IRCU32HostV1"),
                        returned_memory,
                        returned_host,
                        list("Nat", [n(1), n(7)]),
                        n(8),
                    ],
                ),
            ],
        );
        prove(
            "actual full import-release world/tail frame",
            a("IRByteConfigV1", [c("IRCU32HostV1")]),
            actual,
            expected,
            true,
        );
    })
}

#[test]
fn source_bridge_closes_last_alias_and_checks_allocation_liveness() {
    stack(|| {
        let (m, _) = fixture(Kind::Alias);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(vec![image(8192, 42, 1)], &[(8192, 2)]);
        let f = h.begin(&[8192, 8192]).unwrap();
        let owners = [(f, 1)];
        let first = p
            .check_transition(
                spec(),
                &h,
                f,
                &owners,
                RuntimeOperation::Release { slot: 0 },
            )
            .unwrap();
        let last = p
            .check_transition(
                spec(),
                first.source_after(),
                f,
                &owners,
                RuntimeOperation::Release { slot: 1 },
            )
            .unwrap();
        assert!(!last.source_after().allocations()[&8192].live);
        let mut retired = last.source_after().clone();
        let output = retired.finish(f, 42).unwrap();
        assert_eq!(output.word(), 85);
        assert!(retired.is_retired(f));
        assert!(
            p.check_transition(
                spec(),
                &retired,
                f,
                &owners,
                RuntimeOperation::Release { slot: 1 }
            )
            .is_err()
        );
    })
}

#[test]
fn initialization_errors_precede_arity_and_typed_runtime_carrier_errors() {
    stack(|| {
        let (m, root) = fixture(Kind::Decode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        let mut h = heap(vec![], &[]);
        let f = h.begin(&[]).unwrap();
        let state = runtime::project(&h, f, &[(f, 1)]).unwrap();
        let malformed = runtime::ProjectedRuntimeState {
            memory: a(
                "IRByteMemoryV1.mk",
                [
                    list(
                        "IRByteAllocationV1",
                        [a(
                            "IRByteAllocationV1.mk",
                            [n(0), n(12), n(0), c("Bool.true")],
                        )],
                    ),
                    Expr::lam(
                        BinderInfo::Default,
                        c("Nat"),
                        a("IROption.none", [c("Nat")]),
                    ),
                    n(16),
                ],
            ),
            host: state.host.clone(),
            active_owner: 1,
        };
        prove(
            "initial memory before wrong arity",
            c("IROutcome"),
            outcome(run(&m, root, &p, &malformed, vec![], 0)),
            a("IROutcome.type_error", [c("IRFault.bad_addr")]),
            true,
        );
        prove(
            "valid memory then wrong arity",
            c("IROutcome"),
            outcome(run(&m, root, &p, &state, vec![], 0)),
            a("IROutcome.type_error", [c("IRFault.bad_field")]),
            true,
        );
        let (m, root) = fixture(Kind::Encode);
        let p = CheckedRuntimeProfile::new(&m, binding()).unwrap();
        prove(
            "noncanonical U32 rejected before provider",
            c("IROutcome"),
            outcome(run(
                &m,
                root,
                &p,
                &state,
                vec![a("IRScalar.int_", [n(1u64 << 32)])],
                0,
            )),
            a("IROutcome.type_error", [c("IRFault.bad_field")]),
            true,
        );
    })
}
