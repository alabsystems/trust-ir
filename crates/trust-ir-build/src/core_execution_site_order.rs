// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted linear certificates for the original complete site-uniqueness
//! guard. Only increasing concrete catalogs take this path. Reordered,
//! duplicate, symbolic and overflowing catalogs retain the existing fallback.

use super::*;

fn literal(expression: &Expr) -> Option<u64> {
    match expression.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(value)) => value.to_u64(),
        _ => None,
    }
}

impl Assembler<'_> {
    /// Build a candidate for the unchanged site uniqueness predicate, using
    /// adjacent positive ranks and the shared constructive chain theorem.
    /// `None` means this acceleration does not cover the supplied catalog;
    /// it is never evidence of uniqueness. Every returned proof must replay.
    pub fn site_catalog_uniqueness(
        &mut self,
        model: &MachineModel,
    ) -> Result<Option<PendingEquality>> {
        self.charge()?;
        if let Some((context, candidate)) = &self.site_catalog_unique
            && context == model.context()
        {
            return Ok(Some(candidate.clone()));
        }
        self.build_site_catalog_uniqueness(model)
    }

    // The complete constructor has sizable proof/list temporaries even when
    // the caller only needs its cached result. Keep that frame off repeated
    // cache hits; this changes neither the candidate nor any construction charge.
    #[inline(never)]
    fn build_site_catalog_uniqueness(
        &mut self,
        model: &MachineModel,
    ) -> Result<Option<PendingEquality>> {
        let fields = model.context().get_app_args();
        let name = match model.context().get_app_fn().kind() {
            ExprKind::Const(name, _) => name.to_string(),
            _ => return Ok(None),
        };
        if !matches!(
            (name.as_str(), fields.len()),
            ("IRByteContextV1.mk", 5) | ("IRByteContextV1.mke", 6)
        ) {
            return Ok(None);
        }
        let sites = fields[4].clone();
        let mut cursor = sites.clone();
        let mut rows = Vec::new();
        let mut max_block = 0;
        let mut max_pc = 0;
        loop {
            self.charge()?;
            let fields = cursor.get_app_args();
            if cursor.get_app_fn() == &constant("IRList.nil") {
                if fields.len() != 1 || fields[0] != &constant("IRByteSiteV1") {
                    return Ok(None);
                }
                break;
            }
            if cursor.get_app_fn() != &constant("IRList.cons")
                || fields.len() != 3
                || fields[0] != &constant("IRByteSiteV1")
            {
                return Ok(None);
            }
            let row = fields[1];
            let row_fields = row.get_app_args();
            let constructor = match row.get_app_fn().kind() {
                ExprKind::Const(name, _) => name.to_string(),
                _ => return Ok(None),
            };
            if !matches!(
                (constructor.as_str(), row_fields.len()),
                ("IRByteSiteV1.mk", 6) | ("IRByteSiteV1.mkt", 7) | ("IRByteSiteV1.mki", 7)
            ) {
                return Ok(None);
            }
            let (Some(function), Some(block), Some(pc)) = (
                literal(row_fields[0]),
                literal(row_fields[1]),
                literal(row_fields[2]),
            ) else {
                return Ok(None);
            };
            max_block = max_block.max(block);
            max_pc = max_pc.max(pc);
            // This walks the immutable reflected model; it does not build a
            // replacement IRList or accept a host list argument. The existing
            // per-operation budget bounds each retained catalog row, and the
            // later rank/proof passes charge again. Keep max_list_items for
            // the host lists built by bindings/resolve/list_congruence.
            rows.try_reserve(1)
                .map_err(|_| "site catalog allocation refused")?;
            rows.push((row.clone(), fields[2].clone(), function, block, pc));
            let next = fields[2].clone();
            drop(row_fields);
            drop(fields);
            cursor = next;
        }
        let Some(block_stride) = max_pc.checked_add(1) else {
            return Ok(None);
        };
        let Some(function_stride) = max_block
            .checked_add(1)
            .and_then(|n| n.checked_mul(block_stride))
        else {
            return Ok(None);
        };
        let rank = app(
            "ir_byte_site_rank_v1",
            [nat(function_stride), nat(block_stride)],
        );
        let compatible = app(
            "ir_byte_site_key_rank_v1",
            [nat(function_stride), nat(block_stride)],
        );
        let mut ranks = Vec::new();
        ranks
            .try_reserve_exact(rows.len())
            .map_err(|_| "site rank allocation refused")?;
        let mut previous = 0;
        for (_, _, function, block, pc) in &rows {
            self.charge()?;
            let Some(value) = function
                .checked_mul(function_stride)
                .and_then(|n| {
                    block
                        .checked_mul(block_stride)
                        .and_then(|b| n.checked_add(b))
                })
                .and_then(|n| n.checked_add(*pc))
                .and_then(|n| n.checked_add(1))
            else {
                return Ok(None);
            };
            if value <= previous {
                return Ok(None);
            }
            ranks.push((previous, value));
            previous = value;
        }
        let mut chain = constant("True.intro");
        for ((row, tail, _, _, _), (lower, upper)) in rows.iter().zip(&ranks).rev() {
            self.charge()?;
            let rank_row = Expr::app(rank.clone(), row.clone());
            let left = app("Nat.lt", [nat(*lower), rank_row.clone()]);
            let right = app(
                "ir_byte_site_rank_chain_v1",
                [rank.clone(), tail.clone(), rank_row],
            );
            // One compact ordinary Nat theorem, not an evaluated site-pair
            // matrix: successor(lower) <= successor(lower) + positive_gap.
            let less = app("Nat.le_add_right", [nat(lower + 1), nat(upper - lower - 1)]);
            chain = app("And.intro", [left, right, less, chain]);
        }
        let candidate = PendingEquality::candidate(
            constant("Bool"),
            app(
                "ir_byte_sites_unique_v1",
                [app("ir_byte_context_sites_v1", [model.context().clone()])],
            ),
            constant("Bool.true"),
            app(
                "ir_byte_sites_unique_rank_chain_v1",
                [rank, compatible, sites, nat(0), chain],
            ),
        );
        self.site_catalog_unique = Some((model.context().clone(), candidate.clone()));
        Ok(Some(candidate))
    }
}
