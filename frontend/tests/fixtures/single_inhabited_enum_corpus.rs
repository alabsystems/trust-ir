// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]

use std::convert::Infallible;
use std::intrinsics::mir::*;

pub enum LiveSecond {
    Dead(Infallible),
    Live(u32),
}

pub enum NestedDead {
    Dead((Infallible, [u128; 4096])),
    Live(u32),
}

#[repr(C)]
pub enum ReprCDead {
    Dead(Infallible),
    Live(u32),
}

pub enum TwoLive {
    First(u32),
    Second(u32),
}

pub fn make_result(value: u32) -> Result<u32, Infallible> {
    Ok(value)
}
pub fn make_second(value: u32) -> LiveSecond {
    LiveSecond::Live(value)
}
pub fn make_nested(value: u32) -> NestedDead {
    NestedDead::Live(value)
}
pub fn make_repr_c(value: u32) -> ReprCDead {
    ReprCDead::Live(value)
}
pub fn make_two_live(value: u32) -> TwoLive {
    TwoLive::Second(value)
}

// Preserve this MIR statement explicitly: a tagless discriminant write must
// leave the live payload intact, including its low byte.
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn set_single_discriminant(value: u32) -> u32 {
    mir! {
        let result: LiveSecond;
        {
            place!(Field::<u32>(Variant(result, 1), 0)) = value;
            SetDiscriminant(result, 1);
            RET = Field::<u32>(Variant(result, 1), 0);
            Return()
        }
    }
}
