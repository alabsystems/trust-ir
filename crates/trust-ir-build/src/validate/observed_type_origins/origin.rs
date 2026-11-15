// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn algorithm(value: ProofDigestAlgorithm) -> u8 {
    match value {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    }
}
fn digest_equal<O: ExecutionObserver>(
    a: &ProofDigest,
    b: &ProofDigest,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    // No rest; an added field/algorithm or changed byte width forces review.
    let ProofDigest {
        algorithm: aa,
        bytes: ab,
    } = a;
    let ProofDigest {
        algorithm: ba,
        bytes: bb,
    } = b;
    let ab: &[u8; 32] = ab;
    let bb: &[u8; 32] = bb;
    work.admit(2, size_of::<ProofDigest>())?;
    if algorithm(*aa) != algorithm(*ba) {
        return Ok(false);
    }
    work.admit(32, 0)?;
    Ok(ab == bb)
}
pub(super) fn equal<O: ExecutionObserver>(
    a: &TypeOrigin,
    b: &TypeOrigin,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(2, 2 * size_of::<&TypeOrigin>())?;
    match (a, b) {
        (
            TypeOrigin::Rust {
                stable_crate_id: ac,
                def_path_hash: ap,
                args_digest: ad,
            },
            TypeOrigin::Rust {
                stable_crate_id: bc,
                def_path_hash: bp,
                args_digest: bd,
            },
        ) => {
            let ap: &[u8; 16] = ap;
            let bp: &[u8; 16] = bp;
            work.admit(1, size_of::<u64>())?;
            if ac != bc {
                return Ok(false);
            }
            work.admit(16, 0)?;
            if ap != bp {
                return Ok(false);
            }
            digest_equal(ad, bd, work)
        }
        (
            TypeOrigin::Clean {
                decl: an,
                env_digest: ad,
            },
            TypeOrigin::Clean {
                decl: bn,
                env_digest: bd,
            },
        ) => {
            if !work.equal(an, bn)? {
                return Ok(false);
            }
            digest_equal(ad, bd, work)
        }
        (TypeOrigin::Rust { .. }, TypeOrigin::Clean { .. })
        | (TypeOrigin::Clean { .. }, TypeOrigin::Rust { .. }) => Ok(false),
    }
}
fn hex_byte<O: ExecutionObserver>(value: u8, work: &mut Work<'_, '_, O>, output: &mut String) -> R {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    // Both indexes are nibbles in 0..16; fixed two-byte UTF8 is ASCII.
    work.admit(4, 2)?;
    let pair = [HEX[usize::from(value >> 4)], HEX[usize::from(value & 15)]];
    let text = core::str::from_utf8(&pair).map_err(|_| ObservedValueError::InvalidRange)?;
    work.text(text, output)
}
fn digest<O: ExecutionObserver>(
    value: &ProofDigest,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    let ProofDigest { algorithm, bytes } = value;
    let bytes: &[u8; 32] = bytes;
    work.admit(1, size_of::<ProofDigestAlgorithm>())?;
    work.text(
        match algorithm {
            ProofDigestAlgorithm::Sha256 => "sha256:",
            ProofDigestAlgorithm::TrustIrStableV1 => "stablev1:",
        },
        output,
    )?;
    let mut i = 0;
    loop {
        work.admit(1, size_of::<Option<&u8>>())?;
        let Some(byte) = bytes.get(i) else {
            return Ok(());
        };
        hex_byte(*byte, work, output)?;
        work.next(&mut i)?;
    }
}
pub(super) fn write<O: ExecutionObserver>(
    origin: &TypeOrigin,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    work.admit(1, size_of::<&TypeOrigin>())?;
    match origin {
        TypeOrigin::Rust {
            stable_crate_id,
            def_path_hash,
            args_digest,
        } => {
            let path: &[u8; 16] = def_path_hash;
            work.text("rust(crate=0x", output)?;
            work.admit(8, 8)?;
            let bytes = stable_crate_id.to_be_bytes();
            let mut i = 0;
            loop {
                work.admit(1, size_of::<Option<&u8>>())?;
                let Some(byte) = bytes.get(i) else {
                    break;
                };
                hex_byte(*byte, work, output)?;
                work.next(&mut i)?;
            }
            work.text(", path=", output)?;
            let mut i = 0;
            loop {
                work.admit(1, size_of::<Option<&u8>>())?;
                let Some(byte) = path.get(i) else {
                    break;
                };
                hex_byte(*byte, work, output)?;
                work.next(&mut i)?;
            }
            work.text(", args=", output)?;
            digest(args_digest, work, output)?;
            work.text(")", output)
        }
        TypeOrigin::Clean { decl, env_digest } => {
            work.text("clean(decl=", output)?;
            work.quoted(decl, output)?;
            work.text(", env=", output)?;
            digest(env_digest, work, output)?;
            work.text(")", output)
        }
    }
}
