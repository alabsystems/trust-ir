# `semr_compiled` — the stage-2 compiler's own trust-ir artifacts

Each `.bin` is the crate module `rustc -Ztrust-ir-lower=on -Ztrust-dump=ir:<dir>` wrote
(`<crate>.trust-ir.bin`, wire v52, byte for byte), from the stage-2 Trust toolchain
`rustc 1.101.0-dev (f7b7a4771 2026-10-24)` (Trust's lattice-3 sysroot). They carry what a
compiled artifact carries and the hand-built corpus does not: a target record
(`arm64-apple-macosx`, 8-byte pointers, little-endian), per-node proof annotations
(`#proof: div_nonzero`, `no_overflow`) and formula-free proof obligations; `fieldless.bin`
adds explicit discriminants, `repr` hints, direct layout records, casts and `switch`.

| Blob | Source |
|---|---|
| `collision.bin` | Trust `tests/ui/trust/r1/caller_closure_key_space_collision.rs`, `--crate-name=t --crate-type=lib -Ztrust-verify=on` |
| `no_collision.bin` | Trust `tests/ui/trust/r1/caller_closure_key_space_no_collision.rs`, same flags |
| `r1_budget_control.bin` | Trust `tests/ui/trust/r1_budget_trip_mints_no_flip.rs`, revision `control` (`-Ztrust-policy=strict --crate-name=t`) |
| `mut_wrap.bin` | `fn add_u8(a: u8, b: u8) -> u8 { a + b }` (`--crate-type=lib -Ztrust-policy=advisory`) |
| `mut_sign.bin` | `fn below(x: i8) -> i8 { if x < 0 { x - 100 } else { x } }` (same) |
| `mut_sign_le.bin` | `fn below_le(x: i8) -> i8 { if x <= 0 { x - 100 } else { x } }` (an `sle`; same flags) |
| `mut_sign_gt.bin` | `fn below_gt(x: i8) -> i8 { if x > 0 { x } else { x - 100 } }` (an `sgt`; same flags) |
| `mut_sign_ge.bin` | `fn below_ge(x: i8) -> i8 { if x >= 1 { x } else { x - 100 } }` (an `sge`; same flags) |
| `twins.bin` | `add_twin` (`a <= 100 && b <= 100` guards `a + b`) and `below_twin` (`x + 100` under `x < 0`) (same) |
| `fieldless.bin` | D-2(b): fieldless enums by value — `#[repr(u8)] ContainmentMode` (0, 1, 2; aterm's, without derives) with `level` (`self as u8`: an extract and a bitcast) and `headroom` (`100 / (m as u8 + 1)`), `#[repr(i8)] Ordering3` (-1, 0, 1) with `sign` (an `sext`) and `flip_index` (a `switch`), an implicit `Implicit` with `pick`, `mk`/`mk_level` (an enum constant), `Sparse { A = 5, B = 9 }` with `sparse_tag`, and mirrors of `FpCategory` and `atomic::Ordering` with `is_finite_class` and `strength` (`-Ztrust-ir-lower=strict`, same flags) |

VF5 (Trust's proven-core plan) proves these artifacts' rows over SemR in Clean
(`crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/vf5_f1/`); this differential holds
SemR's decode and runs of the same bytes to `deserialize_module` and the interpreter.

`semr_compiled_fieldless_variants_agree_with_the_interpreter` derives further modules from
`fieldless.bin` (each enum's layout record dropped, its discriminants permuted or redrawn), so the
decoder's two fieldless-enum arms (with and without a layout record) are each compared with
`deserialize_module` and run against the interpreter; `semr_decoder_agrees_on_mutated_compiled_artifacts`
runs the one-byte decoder differential over every artifact here.
