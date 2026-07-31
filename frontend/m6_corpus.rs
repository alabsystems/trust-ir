// M6 CAPSTONE corpus — the REAL, NICHE-ENCODED clean-kernel `Level`.
//
// This is the faithfulness capstone for the `layout_of`-driven frontend. Unlike
// `m3_corpus.rs`'s `Level` (a Box-recursive enum whose discriminant rustc lays
// out as a DIRECT 8-byte tag at offset 0, values 0..4), THIS `Level` carries a
// `Param(Name)` payload whose `Name` provides a NICHE — so rustc NICHE-ENCODES the
// discriminant:
//
//   Level: size 40, align 8.
//   The discriminant is a NICHE in the first word (offset 0, inside Name's first
//   Arc<Name> pointer), NOT a separate tag. `Param` is the UNTAGGED variant (it
//   stores the real Name; its niche word is a real pointer, not a niche value).
//   The other four variants are niche-encoded: in-memory niche tag values
//   Zero=3, Succ=4, Max=5, IMax=6 (`niche_start`-relative), with Param decoded as
//   the Switch DEFAULT. Succ's child sits at offset 8, Max/IMax's at 8 and 16
//   (AFTER the niche word).
//
// A hand-coded `{ tag: i32 @0, p0:@8, p1:@16 }` model would Switch on i32 values
// {0,1,2,3,4} at offset 0; the faithful `layout_of`-recovered `EnumLayout` instead
// reads the tag at offset 0 with the REAL I64 width, Switches on niche values
// {3,4,5,6} with Param as the Switch DEFAULT, and binds children at the recovered
// per-variant offsets.
//
// HONEST SCOPE (FIX 4): the emitted-vs-heap DIFFERENTIAL alone does NOT prove these
// numbers are rustc's — it is SELF-CONSISTENT (the heap builder and the lowered
// predicate BOTH consume the SAME `layout_of`-recovered `EnumLayout`), so any
// internally-consistent layout (even a perturbed one) would still pass 21/21. What
// the differential proves is that the lowered predicate + heap builder AGREE 21/21
// while both driven by the recovered layout. FAITHFULNESS-TO-RUSTC of those numbers
// is PINNED separately by the `--assert-layout` LAYOUT-PIN (see
// `tests/real_lowering_acceptance.rs::real_lowering_m6_niche_level_accepts` and
// `main.rs::assert_m6_niche_level_layout`), which compares the recovered layout to
// the audit-confirmed rustc ground truth and `exit(1)`s on any divergence.
//
// The `is_zero`/`is_nonzero` bodies are VERBATIM from
// clean/crates/clean-kernel/src/level/mod.rs.

// `Name` reproduces the clean-kernel `Name` shape that PROVIDES the niche: a
// struct `{ inner: NameInner, cached_hash: u64 }` whose `NameInner` is an enum
// whose first field is an `Arc<Name>` (a `NonNull` pointer — the niche source).
// This is the VERBATIM clean-kernel `NameInner`/`Name` (the production, non-kani
// definitions), so the niche it provides is the REAL one. The frontend never
// constructs or binds a `Name` (the predicates only `match` on `_` for `Param`),
// so `Name` only needs to exist to make `Level` niche-encoded.
use std::sync::Arc;

pub enum NameInner {
    Anon,
    Str(Arc<Name>, Arc<str>),
    Num(Arc<Name>, u64),
}

pub struct Name {
    #[allow(dead_code)]
    inner: NameInner,
    #[allow(dead_code)]
    cached_hash: u64,
}

// `Box<Level>` children (the design's prescribed Box-layout recursive child); the
// niche is provided by `Param(Name)`, not the children.
pub type LevelArc = Box<Level>;

pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

impl Level {
    // VERBATIM clean-kernel `Level::is_zero`.
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false, // Succ always > 0; Params might be 0 at runtime
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(), // imax(_, 0) = 0
        }
    }

    // VERBATIM clean-kernel `Level::is_nonzero`.
    pub fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false, // Zero is 0; Params might be 0
            Level::Succ(_) => true,                 // succ(l) > 0 for all l
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(), // If l2 > 0, imax reduces to max
        }
    }
}

fn main() {}
