// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
mod part_0;
mod part_1;
mod part_10;
mod part_2;
mod part_3;
mod part_4;
mod part_5;
mod part_6;
mod part_7;
mod part_8;
mod part_9;
pub(super) fn all() -> Vec<(ValidationError, usize)> {
    let mut values = Vec::new();
    values.extend(part_0::cases());
    values.extend(part_1::cases());
    values.extend(part_2::cases());
    values.extend(part_3::cases());
    values.extend(part_4::cases());
    values.extend(part_5::cases());
    values.extend(part_6::cases());
    values.extend(part_7::cases());
    values.extend(part_8::cases());
    values.extend(part_9::cases());
    values.extend(part_10::cases());
    values
}
