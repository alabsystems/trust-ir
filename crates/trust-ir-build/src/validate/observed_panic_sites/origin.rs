// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn is_global<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut b = 0;
    loop {
        let Some(block) = work.at(&function.blocks, b)? else {
            return Ok(false);
        };
        let mut n = 0;
        loop {
            let Some(node) = work.at(&block.body, n)? else {
                break;
            };
            let mut r = 0;
            let mut found = false;
            loop {
                let Some(result) = work.at(&node.results, r)? else {
                    break;
                };
                work.admit(1, size_of::<bool>())?;
                if *result == value {
                    found = true;
                    break;
                }
                work.next(&mut r)?;
            }
            if found {
                // Exact original find: first physical node with this result
                // decides even on malformed duplicates. No Copy provenance.
                work.admit(16, size_of::<Option<&str>>())?;
                return match &node.inst {
                    Inst::GlobalAddr { .. } => Ok(true),
                    Inst::Const {
                        value: Constant::SymbolAddr { symbol, addend: 0 },
                        ..
                    } => {
                        let mut g = 0;
                        loop {
                            let Some(global) = work.at(&module.globals, g)? else {
                                return Ok(false);
                            };
                            if work.same_text(&global.name, symbol)? {
                                return Ok(true);
                            }
                            work.next(&mut g)?;
                        }
                    }
                    _ => Ok(false),
                };
            }
            work.next(&mut n)?;
        }
        work.next(&mut b)?;
    }
}
