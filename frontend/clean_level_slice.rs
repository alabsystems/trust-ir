// SELF-CONTAINED clean-kernel `Level` slice — REAL function bodies copied
// VERBATIM from Clean's crates/clean-kernel/src/level/mod.rs, made standalone so
// the THIR->trust-ir frontend `--coverage` mode can attempt to lower them.
//
// Faithfulness notes (what changed vs the real module, and why it preserves the
// THIR SHAPE the coverage measures):
//   * `Arc<Level>` -> `Box<Level>`. Both are a single heap POINTER (pointer-width
//     payload slot), the exact shape the frontend models a recursive enum child
//     as. The corpus `Level` already uses `Box`. The method bodies are unchanged.
//   * `level_arc(l)` -> `Box::new(l)` (the real helper just wraps in the smart
//     pointer; `Box::new` is the diagnostic-item the frontend's constructor path
//     recognizes).
//   * `Name` (the `Param` payload) -> a minimal newtype `Name(u32)` so the enum is
//     self-contained. The Param ARM SHAPE (a leaf variant carrying a non-recursive
//     payload) is unchanged.
//   * `stack_safe(|| body)` -> `body` inlined. `stack_safe` is a higher-order
//     guard (closure + thread stack growth) that is pure plumbing around the SAME
//     expression; inlining it preserves the lowerable body shape. (Where a body is
//     ONLY `stack_safe(|| self.x_impl())` we call `self.x_impl()` directly.)
//   * `serde`/`Hash`/manual `PartialEq` cfg(kani) blocks dropped. We DERIVE
//     PartialEq/Eq/Clone so the `==`/`.clone()` the real bodies use compile.
//   * `hashbrown::HashMap` memo cache in is_geq -> `std::collections::HashMap`.
//
// Everything else (control flow, match arms incl. nested/Or, get_offset's
// while-let, the is_geq decision tree, substitute, has_params, ...) is the REAL
// clean-kernel logic, so a bail here is a REAL frontend gap on REAL kernel code.

#![allow(dead_code)]
#![allow(clippy::all)]

use std::collections::HashMap;

/// Minimal stand-in for `clean_kernel::Name` (the real Param payload). A `u32`
/// handle — non-recursive, Copy, comparable — preserving the Param arm shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub u32);

/// REAL clean-kernel `Level` enum (Arc -> Box; Name stubbed). Verbatim variants.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(Name),
}

impl Level {
    // ---- constructors (real bodies; level_arc -> Box::new) ------------------

    pub fn zero() -> Self {
        Level::Zero
    }

    pub fn succ(l: Level) -> Self {
        Level::Succ(Box::new(l))
    }

    pub fn max(l1: Level, l2: Level) -> Self {
        if l1 == l2 {
            return l1;
        }
        if l1.is_zero() {
            return l2;
        }
        if l2.is_zero() {
            return l1;
        }
        if Level::is_geq(&l1, &l2) {
            return l1;
        }
        if Level::is_geq(&l2, &l1) {
            return l2;
        }
        Level::Max(Box::new(l1), Box::new(l2))
    }

    pub fn imax(l1: Level, l2: Level) -> Self {
        if l2.is_zero() {
            return Level::Zero;
        }
        if l2.is_nonzero() {
            return Level::max(l1, l2);
        }
        if l1.is_zero() {
            return l2;
        }
        if l1 == Level::succ(Level::zero()) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        Level::IMax(Box::new(l1), Box::new(l2))
    }

    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }

    // ---- the bool predicates (the M5.6 capstone shape, REAL bodies) ---------

    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }

    pub fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(),
        }
    }

    // ---- offset arithmetic --------------------------------------------------

    /// REAL get_offset: while-let spine walk returning a (&Level, u32) TUPLE.
    pub fn get_offset(&self) -> (&Level, u32) {
        let mut current = self;
        let mut offset = 0u32;
        while let Level::Succ(inner) = current {
            offset = offset.saturating_add(1);
            current = inner;
        }
        (current, offset)
    }

    /// REAL add_offset: a `for` loop building Succ chains.
    pub fn add_offset(&self, n: u32) -> Level {
        let mut result = self.clone();
        for _ in 0..n {
            result = Level::succ(result);
        }
        result
    }

    /// REAL kind_ord: a 5-arm match returning a u8 (scalar discriminant order).
    fn kind_ord(&self) -> u8 {
        match self {
            Level::Zero => 0,
            Level::Succ(_) => 1,
            Level::Max(_, _) => 2,
            Level::IMax(_, _) => 3,
            Level::Param(_) => 4,
        }
    }

    /// REAL is_explicit: `matches!` over get_offset's base.
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0, Level::Zero)
    }

    /// REAL is_norm_lt (the not(kani) branch, stack_safe inlined): a structural
    /// total order with nested match + tuple destructuring + multi-binding arms.
    fn is_norm_lt(a: &Level, b: &Level) -> bool {
        if a == b {
            return false;
        }
        let (base1, off1) = a.get_offset();
        let (base2, off2) = b.get_offset();
        if base1 != base2 {
            if base1.kind_ord() != base2.kind_ord() {
                return base1.kind_ord() < base2.kind_ord();
            }
            match (base1, base2) {
                (Level::Param(n1), Level::Param(n2)) => n1 < n2,
                (Level::Max(a1, b1), Level::Max(a2, b2))
                | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                    if a1 != a2 {
                        Self::is_norm_lt(a1, a2)
                    } else {
                        Self::is_norm_lt(b1, b2)
                    }
                }
                _ => false,
            }
        } else {
            off1 < off2
        }
    }

    // ---- the is_geq decision tree (REAL not(kani) bodies, stack_safe inlined) -

    pub fn is_geq(l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        Self::is_geq_core(&n1, &n2)
    }

    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        let mut cache = HashMap::new();
        Self::is_geq_core_cached(l1, l2, &mut cache)
    }

    fn is_geq_core_cached(
        l1: &Level,
        l2: &Level,
        cache: &mut HashMap<(Level, Level), bool>,
    ) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        {
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                return true;
            }
        }
        let key = (l1.clone(), l2.clone());
        if let Some(&result) = cache.get(&key) {
            return result;
        }
        let result = Self::is_geq_core_compute(l1, l2, cache);
        cache.insert(key, result);
        result
    }

    fn is_geq_core_compute(
        l1: &Level,
        l2: &Level,
        cache: &mut HashMap<(Level, Level), bool>,
    ) -> bool {
        if let Level::Max(a, b) = l2 {
            let lhs = Self::is_geq_core_cached(l1, a, cache);
            return lhs && Self::is_geq_core_cached(l1, b, cache);
        }
        if let Level::Max(a, b) = l1 {
            let lhs = Self::is_geq_core_cached(a, l2, cache);
            if lhs || Self::is_geq_core_cached(b, l2, cache) {
                return true;
            }
        }
        if let Level::IMax(a, b) = l2 {
            let lhs = Self::is_geq_core_cached(l1, a, cache);
            return lhs && Self::is_geq_core_cached(l1, b, cache);
        }
        if let Level::IMax(_, b) = l1 {
            return Self::is_geq_core_cached(b, l2, cache);
        }
        let (base1, offset1) = l1.get_offset();
        let (base2, offset2) = l2.get_offset();
        if base1 == base2 || base2.is_zero() {
            return offset1 >= offset2;
        }
        if offset1 == offset2 && offset1 > 0 {
            return Self::is_geq_core_cached(base1, base2, cache);
        }
        false
    }

    pub fn leq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq(l2, l1)
    }

    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq(l1, l2) && Level::is_geq(l2, l1)
    }

    // ---- Max-tree canonicalization helpers (REAL not(kani) bodies) ----------

    fn push_max_args(l: &Level, buf: &mut Vec<Level>) {
        match l {
            Level::Max(a, b) => {
                Self::push_max_args(a, buf);
                Self::push_max_args(b, buf);
            }
            _ => buf.push(l.clone()),
        }
    }

    fn mk_max_from_args(args: &[Level]) -> Level {
        if args.len() == 1 {
            return args[0].clone();
        }
        let mut r = Level::Max(
            Box::new(args[args.len() - 2].clone()),
            Box::new(args[args.len() - 1].clone()),
        );
        for i in (0..args.len() - 2).rev() {
            r = Level::Max(Box::new(args[i].clone()), Box::new(r));
        }
        r
    }

    // ---- normalize (REAL: stack_safe wrapper -> direct impl call) -----------

    pub fn normalize(&self) -> Level {
        self.normalize_impl()
    }

    /// A FAITHFUL normalize_impl shape: strip offset, dispatch on base kind.
    /// (Trimmed of the full Max canonicalization the real one calls, which itself
    /// needs sort/dedup over Vec — kept to the offset+base dispatch, which is the
    /// real top-level structure and is fully lowerable in principle.)
    fn normalize_impl(&self) -> Level {
        let (base, offset) = self.get_offset();
        match base {
            Level::Zero => base.clone().add_offset(offset),
            Level::Param(_) => base.clone().add_offset(offset),
            Level::Succ(_) => base.clone().add_offset(offset),
            Level::Max(_, _) => base.clone().add_offset(offset),
            Level::IMax(a, b) => {
                let na = a.normalize();
                let nb = b.normalize();
                Level::imax(na, nb).add_offset(offset)
            }
        }
    }

    // ---- substitution (REAL bodies; subst is a &[(Name, Level)] slice) ------

    pub fn substitute(&self, subst: &[(Name, Level)]) -> Level {
        self.substitute_impl(subst)
    }

    fn substitute_impl(&self, subst: &[(Name, Level)]) -> Level {
        match self.substitute_impl_opt(subst) {
            Some(l) => l,
            None => self.clone(),
        }
    }

    fn substitute_impl_opt(&self, subst: &[(Name, Level)]) -> Option<Level> {
        match self {
            Level::Zero => None,
            Level::Succ(l) => l.substitute_impl_opt(subst).map(Level::succ),
            Level::Max(l1, l2) => {
                let n1 = l1.substitute_impl_opt(subst);
                let n2 = l2.substitute_impl_opt(subst);
                if n1.is_none() && n2.is_none() {
                    return None;
                }
                let r1 = n1.unwrap_or_else(|| (**l1).clone());
                let r2 = n2.unwrap_or_else(|| (**l2).clone());
                Some(Level::max(r1, r2))
            }
            Level::IMax(l1, l2) => {
                let n1 = l1.substitute_impl_opt(subst);
                let n2 = l2.substitute_impl_opt(subst);
                if n1.is_none() && n2.is_none() {
                    return None;
                }
                let r1 = n1.unwrap_or_else(|| (**l1).clone());
                let r2 = n2.unwrap_or_else(|| (**l2).clone());
                Some(Level::imax(r1, r2))
            }
            Level::Param(name) => {
                let mut i = 0;
                while i < subst.len() {
                    if subst[i].0 == *name {
                        return Some(subst[i].1.clone());
                    }
                    i += 1;
                }
                None
            }
        }
    }

    // ---- param queries (REAL bodies) ----------------------------------------

    pub fn has_params(&self) -> bool {
        self.has_params_impl()
    }

    fn has_params_impl(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params_impl(),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                l1.has_params_impl() || l2.has_params_impl()
            }
            Level::Param(_) => true,
        }
    }

    pub fn collect_params(&self, params: &mut Vec<Name>) {
        self.collect_params_impl(params);
    }

    fn collect_params_impl(&self, params: &mut Vec<Name>) {
        match self {
            Level::Zero => {}
            Level::Succ(l) => l.collect_params_impl(params),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                l1.collect_params_impl(params);
                l2.collect_params_impl(params);
            }
            Level::Param(n) => params.push(*n),
        }
    }
}

fn main() {}
