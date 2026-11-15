//! Target-bound cases shared by classifier and Rust/Lean execution controls.
//! No array-layout or unsupported-operation waiver is used to admit a case.
#![allow(dead_code)] // Classifier controls also use this module without oracle expectations.
use trust_ir::inst::{AllocOrigin, AtomicRMWOp, Ordering};
use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::{CastOp, Constant, Endianness, FuncId, Global, Linkage, Module, TargetInfo};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
pub enum Cell {
    WrapAdd,
    WrapSub,
    SignedOverflow,
    UsizeStride,
    FatStride,
    ThinRoundTrip,
    ThinParts,
    Fat(FatPtrKind),
    IntToPtr(u128),
    Gep(u128),
    AtomicRmw,
    AtomicCmp,
    Global,
    Heap,
    Exhaustion,
    Tuple,
    MemSet,
    MemCopy,
    UnsignedInput,
    SignedInput,
}

pub const CELLS: &[Cell] = &[
    Cell::WrapAdd,
    Cell::WrapSub,
    Cell::SignedOverflow,
    Cell::UsizeStride,
    Cell::FatStride,
    Cell::ThinRoundTrip,
    Cell::ThinParts,
    Cell::Fat(FatPtrKind::Slice(trust_ir::TyId::new(0))),
    Cell::Fat(FatPtrKind::Str),
    Cell::Fat(FatPtrKind::ContainerLen),
    Cell::Fat(FatPtrKind::TraitObject { trait_id: 7 }),
    Cell::Fat(FatPtrKind::ContainerVtable),
    Cell::IntToPtr(0xFFFF_FFFF),
    Cell::IntToPtr(0x1_0000_0000),
    Cell::Gep(15),
    Cell::Gep(16),
    Cell::AtomicRmw,
    Cell::AtomicCmp,
    Cell::Global,
    Cell::Heap,
    Cell::Exhaustion,
    Cell::Tuple,
    Cell::MemSet,
    Cell::MemCopy,
    Cell::UnsignedInput,
    Cell::SignedInput,
];

impl Cell {
    pub fn in_subset(self) -> bool {
        !matches!(self, Self::MemSet | Self::MemCopy)
    }
    pub fn expected(self, bits: u32) -> Option<u128> {
        Some(match self {
            Self::WrapAdd | Self::AtomicRmw => {
                if bits == 32 {
                    0
                } else {
                    0x1_0000_0000
                }
            }
            Self::WrapSub => {
                if bits == 32 {
                    0xFFFF_FFFF
                } else {
                    u64::MAX as u128
                }
            }
            Self::SignedOverflow if bits == 32 => return None,
            Self::SignedOverflow => 0x8000_0000,
            Self::UsizeStride => u128::from(bits / 8),
            Self::FatStride => u128::from(bits / 4),
            Self::ThinRoundTrip
            | Self::ThinParts
            | Self::Fat(FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable) => 42,
            Self::Fat(_) => 3,
            Self::IntToPtr(a) if bits == 32 && a > 0xFFFF_FFFF => return None,
            Self::IntToPtr(a) => a,
            Self::Gep(n) if bits == 32 && n == 16 => return None,
            Self::Gep(n) => 0xFFFF_FFF0 + n,
            Self::AtomicCmp => 2,
            Self::Global | Self::Heap => 43,
            Self::Exhaustion if bits == 32 => return None,
            Self::Exhaustion => 1,
            Self::Tuple | Self::MemCopy => 0xC000_0001,
            Self::MemSet => {
                if bits == 32 {
                    0x0101_0101
                } else {
                    0x0101_0101_0101_0101
                }
            }
            Self::UnsignedInput => 3,
            Self::SignedInput => u64::MAX as u128,
        })
    }
    pub fn refusal(self, bits: u32) -> Option<&'static str> {
        if self.expected(bits).is_some() {
            None
        } else if matches!(self, Self::Exhaustion) {
            Some("out_of_memory")
        } else {
            Some("ub")
        }
    }
}

pub fn target(bits: u32) -> TargetInfo {
    TargetInfo {
        triple: if bits == 32 {
            "wasm32-unknown-unknown"
        } else {
            "x86_64-unknown-linux-gnu"
        }
        .into(),
        pointer_size: bits / 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

pub fn module(cell: Cell, bits: u32) -> (Module, FuncId) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("target_{bits}_{cell:?}"), target(bits));
    mb.add_type(Ty::U8);
    if matches!(cell, Cell::Global) {
        mb.add_global(Global {
            name: "target_word".into(),
            ty: Ty::Usize,
            mutable: true,
            initializer: Some(Constant::Int(41)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }
    let input = match cell {
        Cell::UnsignedInput => vec![Ty::Usize],
        Cell::SignedInput => vec![Ty::Isize],
        _ => vec![],
    };
    let sig = mb.add_func_type(input.clone(), vec![Ty::U64]);
    let mut fb = mb.function("program", sig);
    let e = fb.create_block();
    let arg = input.first().map(|ty| fb.add_block_param(e, ty.clone()));
    fb.switch_to_block(e);
    let word = if bits == 32 { Ty::U32 } else { Ty::U64 };
    let out = match cell {
        Cell::WrapAdd | Cell::WrapSub => {
            let a = fb.uconst(
                Ty::Usize,
                if matches!(cell, Cell::WrapAdd) {
                    0xFFFF_FFFF
                } else {
                    0
                },
            );
            let one = fb.uconst(Ty::Usize, 1);
            let result = if matches!(cell, Cell::WrapAdd) {
                fb.add(Ty::Usize, a, one)
            } else {
                fb.sub(Ty::Usize, a, one)
            };
            fb.zext(Ty::Usize, Ty::U64, result)
        }
        Cell::SignedOverflow => {
            let a = fb.iconst(Ty::Isize, -0x8000_0000);
            let minus_one = fb.iconst(Ty::Isize, -1);
            let q = fb.sdiv(Ty::Isize, a, minus_one);
            fb.zext(Ty::Isize, Ty::U64, q)
        }
        Cell::UsizeStride | Cell::FatStride => {
            let ty = if matches!(cell, Cell::UsizeStride) {
                Ty::Usize
            } else {
                Ty::FatPtr(FatPtrKind::Str)
            };
            let base = fb.alloca(ty.clone());
            let one = fb.uconst(Ty::Usize, 1);
            let next = fb.gep(ty, base, vec![one]);
            let start = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, base);
            let end = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, next);
            fb.sub(Ty::U64, end, start)
        }
        Cell::ThinRoundTrip | Cell::MemCopy => {
            let data = fb.alloca(Ty::U32);
            let value = fb.uconst(
                Ty::U32,
                if matches!(cell, Cell::ThinRoundTrip) {
                    42
                } else {
                    0xC000_0001
                },
            );
            fb.store(Ty::U32, data, value);
            let first = fb.alloca(Ty::Ptr);
            fb.store(Ty::Ptr, first, data);
            let loaded = if matches!(cell, Cell::MemCopy) {
                let second = fb.alloca(Ty::Ptr);
                let bytes = fb.uconst(Ty::Usize, u128::from(bits / 8));
                fb.memcopy(second, first, bytes, false);
                fb.load(Ty::Ptr, second)
            } else {
                fb.load(Ty::Ptr, first)
            };
            let result = fb.load(Ty::U32, loaded);
            fb.zext(Ty::U32, Ty::U64, result)
        }
        Cell::ThinParts => {
            let data = fb.alloca(Ty::U32);
            let value = fb.uconst(Ty::U32, 42);
            fb.store(Ty::U32, data, value);
            let unit = fb.const_value(Ty::Unit, Constant::PhantomData);
            let thin = fb.ptr_from_parts(Ty::Ptr, Ty::Unit, data, unit);
            fb.ptr_metadata(Ty::Ptr, Ty::Unit, thin);
            let actual = fb.ptr_data(Ty::Ptr, thin);
            let loaded = fb.load(Ty::U32, actual);
            fb.zext(Ty::U32, Ty::U64, loaded)
        }
        Cell::Fat(kind) => {
            let fat = Ty::FatPtr(kind);
            let data = fb.alloca(Ty::U32);
            let meta_ty = if matches!(
                kind,
                FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable
            ) {
                Ty::Ptr
            } else {
                word.clone()
            };
            let metadata = if meta_ty == Ty::Ptr {
                let p = fb.alloca(Ty::U32);
                let value = fb.uconst(Ty::U32, 42);
                fb.store(Ty::U32, p, value);
                p
            } else {
                fb.uconst(meta_ty.clone(), 3)
            };
            let value = fb.ptr_from_parts(fat.clone(), meta_ty.clone(), data, metadata);
            let slot = fb.alloca(fat.clone());
            fb.store(fat.clone(), slot, value);
            let loaded = fb.load(fat.clone(), slot);
            let meta = fb.ptr_metadata(fat, meta_ty.clone(), loaded);
            if meta_ty == Ty::Ptr {
                let result = fb.load(Ty::U32, meta);
                fb.zext(Ty::U32, Ty::U64, result)
            } else if meta_ty == Ty::U64 {
                meta
            } else {
                fb.zext(meta_ty, Ty::U64, meta)
            }
        }
        Cell::IntToPtr(address) | Cell::Gep(address) => {
            let raw = fb.uconst(
                Ty::U64,
                if matches!(cell, Cell::Gep(_)) {
                    0xFFFF_FFF0
                } else {
                    address
                },
            );
            let mut pointer = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, raw);
            if matches!(cell, Cell::Gep(_)) {
                let offset = fb.uconst(Ty::Usize, address);
                pointer = fb.gep(Ty::U8, pointer, vec![offset]);
            }
            fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, pointer)
        }
        Cell::AtomicRmw | Cell::AtomicCmp => {
            let p = fb.alloca(Ty::Usize);
            let first = fb.uconst(
                Ty::Usize,
                if matches!(cell, Cell::AtomicRmw) {
                    0xFFFF_FFFF
                } else {
                    1
                },
            );
            fb.atomic_store(Ty::Usize, p, first, Ordering::SeqCst);
            let one = fb.uconst(Ty::Usize, 1);
            if matches!(cell, Cell::AtomicRmw) {
                fb.atomic_rmw(AtomicRMWOp::Add, Ty::Usize, p, one, Ordering::SeqCst);
            } else {
                let two = fb.uconst(Ty::Usize, 2);
                fb.cmpxchg(Ty::Usize, p, one, two, Ordering::SeqCst, Ordering::Relaxed);
            }
            let result = fb.atomic_load(Ty::Usize, p, Ordering::SeqCst);
            fb.zext(Ty::Usize, Ty::U64, result)
        }
        Cell::Global | Cell::Heap => {
            let p = if matches!(cell, Cell::Global) {
                fb.global_addr(trust_ir::value::GlobalId::new(0))
            } else {
                fb.heap_alloc(Ty::Usize, None, None, AllocOrigin::RustHeap)
            };
            let value = fb.uconst(Ty::Usize, 43);
            fb.store(Ty::Usize, p, value);
            let alias = if matches!(cell, Cell::Global) {
                fb.global_addr(trust_ir::value::GlobalId::new(0))
            } else {
                p
            };
            let result = fb.load(Ty::Usize, alias);
            fb.zext(Ty::Usize, Ty::U64, result)
        }
        Cell::Exhaustion => {
            // Below the signed-count ambiguity boundary;8GiB still exhausts32-bit storage.
            let count = fb.uconst(Ty::Usize, 0x4000_0000);
            fb.heap_alloc(Ty::U64, Some(count), None, AllocOrigin::RustHeap);
            fb.uconst(Ty::U64, 1)
        }
        Cell::Tuple => {
            let ty = Ty::Tuple(vec![Ty::Usize, Ty::U8]);
            let aggregate = fb.const_value(
                ty,
                Constant::Aggregate(vec![Constant::Int(0xC000_0001), Constant::Int(7)]),
            );
            let first = fb.extract_field(Ty::Usize, aggregate, 0);
            fb.zext(Ty::Usize, Ty::U64, first)
        }
        Cell::MemSet => {
            let p = fb.alloca(Ty::Usize);
            let byte = fb.uconst(Ty::U8, 1);
            let count = fb.uconst(Ty::Usize, u128::from(bits / 8));
            fb.memset(p, byte, count);
            let result = fb.load(Ty::Usize, p);
            fb.zext(Ty::Usize, Ty::U64, result)
        }
        Cell::UnsignedInput => {
            let one = fb.uconst(Ty::Usize, 1);
            let result = fb.add(Ty::Usize, arg.unwrap(), one);
            fb.zext(Ty::Usize, Ty::U64, result)
        }
        Cell::SignedInput => {
            let wide = fb.sext(Ty::Isize, Ty::I64, arg.unwrap());
            fb.cast(CastOp::Bitcast, Ty::I64, Ty::U64, wide)
        }
    };
    fb.ret(vec![out]);
    let fid = fb.build();
    (mb.build().expect("target-bound model fixture"), fid)
}
