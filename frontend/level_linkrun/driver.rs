// Link+run value-check driver for the first-party clean-kernel `Level` slice.
//
// Compiled by the SAME stage1 rustc as the corpus, so `oracle::Level` has the
// identical layout the frontend lowered against. For each first-party fn we call
//   (a) the trust-cg-compiled symbol (via FFI), and
//   (b) the real Rust method (the oracle),
// on identical inputs and structurally compare the results.
//
// Built three times (one binary per non-overlapping closure-object set) via
//   --cfg grp_main | --cfg grp_defeq | --cfg grp_leq
// because is_def_eq/leq/substitute each drag the shared is_geq "family" and so
// cannot co-reside in one link without duplicate symbols.

#![allow(non_snake_case, unused_imports, unused)]
#[path = "oracle.rs"]
mod oracle;
use oracle::{Level, Name};
use std::collections::HashMap;
use std::ffi::c_void;
use std::mem::{forget, MaybeUninit};

#[repr(C)]
struct NameVec { data: *mut u32, len: usize, cap: usize }
extern "C" { #[link_name = "free"] fn libc_free(p: *mut c_void); }

fn zero() -> Level { Level::Zero }
fn param(n: u32) -> Level { Level::Param(Name(n)) }
fn succ(l: Level) -> Level { Level::Succ(Box::new(l)) }
fn nat(k: u32) -> Level { let mut l = Level::Zero; for _ in 0..k { l = succ(l); } l }
fn max(a: Level, b: Level) -> Level { Level::Max(Box::new(a), Box::new(b)) }
fn imax(a: Level, b: Level) -> Level { Level::IMax(Box::new(a), Box::new(b)) }

static mut PASS: u32 = 0;
static mut FAIL: u32 = 0;
fn check(name: &str, input: &str, observed: String, expected: String) {
    let ok = observed == expected;
    unsafe { if ok { PASS += 1 } else { FAIL += 1 } }
    println!("[{}] {:<24} in={:<34} tcg={:<22} oracle={:<22}",
        if ok { "PASS" } else { "FAIL" }, name, input, observed, expected);
}
unsafe fn out_level<F: FnOnce(*mut Level)>(f: F) -> Level {
    let mut m = MaybeUninit::<Level>::uninit();
    f(m.as_mut_ptr());
    m.assume_init()
}

fn main() {
    let group = std::env::args().nth(1).unwrap_or_else(|| "?".into());
    println!("== level link+run value-check  group={} ==", group);
    #[cfg(grp_main)] run_main();
    #[cfg(grp_defeq)] run_defeq();
    #[cfg(grp_leq)] run_leq();
    #[cfg(grp_hash)] run_hash();
    unsafe {
        println!("== SUMMARY group={}: {} pass, {} fail ==", group, PASS, FAIL);
        std::process::exit(if FAIL == 0 { 0 } else { 1 });
    }
}

#[cfg(grp_main)]
extern "C" {
    #[link_name = "Level__zero"]                fn tcg_zero(out: *mut Level);
    #[link_name = "Level__param"]               fn tcg_param(out: *mut Level, name: u32);
    #[link_name = "Level__succ"]                fn tcg_succ(out: *mut Level, inl: *const Level);
    #[link_name = "Level__is_zero"]             fn tcg_is_zero(l: *const Level) -> bool;
    #[link_name = "Level__is_nonzero"]          fn tcg_is_nonzero(l: *const Level) -> bool;
    #[link_name = "Level__has_params"]          fn tcg_has_params(l: *const Level) -> bool;
    #[link_name = "Level__has_params_impl"]     fn tcg_has_params_impl(l: *const Level) -> bool;
    #[link_name = "Level__max"]                 fn tcg_max(out: *mut Level, a: *const Level, b: *const Level);
    #[link_name = "Level__imax"]                fn tcg_imax(out: *mut Level, a: *const Level, b: *const Level);
    #[link_name = "Level__add_offset"]          fn tcg_add_offset(out: *mut Level, s: *const Level, n: u32);
    #[link_name = "Level__get_offset"]          fn tcg_get_offset(out: *mut (*const Level, u32), s: *const Level);
    #[link_name = "Level__normalize"]           fn tcg_normalize(out: *mut Level, s: *const Level);
    #[link_name = "Level__normalize_impl"]      fn tcg_normalize_impl(out: *mut Level, s: *const Level);
    #[link_name = "Level__is_geq"]              fn tcg_is_geq(a: *const Level, b: *const Level) -> bool;
    #[link_name = "Level__is_geq_core"]         fn tcg_is_geq_core(a: *const Level, b: *const Level) -> bool;
    #[link_name = "Level__is_geq_core_cached"]  fn tcg_is_geq_core_cached(a: *const Level, b: *const Level, c: *mut c_void) -> bool;
    #[link_name = "Level__is_geq_core_compute"] fn tcg_is_geq_core_compute(a: *const Level, b: *const Level, c: *mut c_void) -> bool;
    #[link_name = "Level__substitute"]          fn tcg_substitute(out: *mut Level, s: *const Level, subst: *const c_void);
    #[link_name = "Level__substitute_impl"]     fn tcg_substitute_impl(out: *mut Level, s: *const Level, subst: *const c_void);
    #[link_name = "Level__substitute_impl_opt"] fn tcg_substitute_impl_opt(out: *mut Option<Level>, s: *const Level, subst: *const c_void);
    #[link_name = "Level__collect_params"]      fn tcg_collect_params(s: *const Level, v: *mut NameVec);
    #[link_name = "Level__collect_params_impl"] fn tcg_collect_params_impl(s: *const Level, v: *mut NameVec);
    #[link_name = "_Level_as_std__clone__Clone___clone"] fn tcg_level_clone(out: *mut Level, s: *const Level);
    #[link_name = "_Level_as_std__cmp__PartialEq___eq"]  fn tcg_level_eq(a: *const Level, b: *const Level) -> bool;
    #[link_name = "_Name_as_std__clone__Clone___clone"]  fn tcg_name_clone(out: *mut Name, s: *const Name);
    #[link_name = "_Name_as_std__cmp__PartialEq___eq"]   fn tcg_name_eq(a: *const Name, b: *const Name) -> bool;
}

#[cfg(grp_main)]
fn run_main() { unsafe {
    let z = out_level(|o| tcg_zero(o));
    check("zero", "()", format!("{:?}", z), format!("{:?}", Level::zero()));
    let p = out_level(|o| tcg_param(o, 3));
    check("param", "Name(3)", format!("{:?}", p), format!("{:?}", Level::param(Name(3))));
    let a = nat(1); let ap = &a as *const Level; let s = out_level(|o| tcg_succ(o, ap)); forget(a);
    check("succ", "1", format!("{:?}", s), format!("{:?}", Level::succ(nat(1))));

    for (lbl, l) in [("Zero", zero()), ("1", nat(1)), ("Max(0,0)", max(zero(),zero())), ("IMax(P2,0)", imax(param(2),zero()))] {
        let r = tcg_is_zero(&l); check("is_zero", lbl, r.to_string(), l.is_zero().to_string());
    }
    for (lbl, l) in [("1", nat(1)), ("Zero", zero()), ("Max(0,P3)", max(zero(),param(3)))] {
        let r = tcg_is_nonzero(&l); check("is_nonzero", lbl, r.to_string(), l.is_nonzero().to_string());
    }
    for (lbl, l) in [("P3", param(3)), ("2", nat(2)), ("Max(0,P3)", max(zero(),param(3))), ("IMax(1,2)", imax(nat(1),nat(2)))] {
        let r = tcg_has_params(&l); check("has_params", lbl, r.to_string(), l.has_params().to_string());
    }
    for (lbl, l) in [("P3", param(3)), ("Succ(P5)", succ(param(5))), ("Max(0,1)", max(zero(),nat(1)))] {
        let r = tcg_has_params_impl(&l); check("has_params_impl", lbl, r.to_string(), l.has_params_impl().to_string());
    }
    for (lbl, a, b) in [("P3,P5", param(3), param(5)), ("0,P3", zero(), param(3)), ("P3,P3", param(3), param(3)), ("1,2", nat(1), nat(2))] {
        let (oa, ob) = (a.clone(), b.clone());
        let (ap, bp) = (&a as *const Level, &b as *const Level);
        let r = out_level(|o| tcg_max(o, ap, bp)); forget(a); forget(b);
        check("max", lbl, format!("{:?}", r), format!("{:?}", Level::max(oa, ob)));
    }
    for (lbl, a, b) in [("P3,P5", param(3), param(5)), ("P3,0", param(3), zero()), ("1,2", nat(1), nat(2)), ("0,P3", zero(), param(3))] {
        let (oa, ob) = (a.clone(), b.clone());
        let (ap, bp) = (&a as *const Level, &b as *const Level);
        let r = out_level(|o| tcg_imax(o, ap, bp)); forget(a); forget(b);
        check("imax", lbl, format!("{:?}", r), format!("{:?}", Level::imax(oa, ob)));
    }
    for (lbl, l, n) in [("P3", param(3), 3u32), ("Zero", zero(), 2), ("1", nat(1), 4)] {
        let r = out_level(|o| tcg_add_offset(o, &l, n));
        check("add_offset", &format!("{},{}", lbl, n), format!("{:?}", r), format!("{:?}", l.add_offset(n)));
    }
    for (lbl, l) in [("Succ(Succ(P3))", succ(succ(param(3)))), ("Zero", zero()), ("Succ(0)", nat(1))] {
        let mut t = MaybeUninit::<(*const Level, u32)>::uninit();
        tcg_get_offset(t.as_mut_ptr(), &l);
        let (bp, off) = t.assume_init();
        let (ob, ooff) = l.get_offset();
        check("get_offset", lbl, format!("off={} base={:?}", off, &*bp), format!("off={} base={:?}", ooff, ob));
    }
    for (lbl, l) in [("IMax(P3,0)", imax(param(3),zero())), ("Succ(Max(0,0))", succ(max(zero(),zero()))), ("IMax(1,2)", imax(nat(1),nat(2))), ("P3", param(3))] {
        let r = out_level(|o| tcg_normalize(o, &l));
        check("normalize", lbl, format!("{:?}", r), format!("{:?}", l.normalize()));
    }
    for (lbl, l) in [("IMax(P3,P5)", imax(param(3),param(5))), ("Succ(P3)", succ(param(3))), ("Max(0,1)", max(zero(),nat(1)))] {
        let r = out_level(|o| tcg_normalize_impl(o, &l));
        check("normalize_impl", lbl, format!("{:?}", r), format!("{:?}", l.normalize_impl()));
    }
    let geq = [("1,0", nat(1), zero()), ("P3,P3", param(3), param(3)), ("2,1", nat(2), nat(1)), ("P3,P5", param(3), param(5)), ("Max(1,2),1", max(nat(1),nat(2)), nat(1))];
    for (lbl, a, b) in geq.iter() { let r = tcg_is_geq(a, b); check("is_geq", lbl, r.to_string(), Level::is_geq(a, b).to_string()); }
    for (lbl, a, b) in geq.iter() { let r = tcg_is_geq_core(a, b); check("is_geq_core", lbl, r.to_string(), Level::is_geq_core(a, b).to_string()); }
    for (lbl, a, b) in geq.iter() {
        let mut cache = [0u8; 48]; let r = tcg_is_geq_core_cached(a, b, cache.as_mut_ptr() as *mut c_void);
        let mut oc: HashMap<(Level,Level),bool> = HashMap::new();
        check("is_geq_core_cached", lbl, r.to_string(), Level::is_geq_core_cached(a, b, &mut oc).to_string());
    }
    for (lbl, a, b) in geq.iter() {
        let mut cache = [0u8; 48]; let r = tcg_is_geq_core_compute(a, b, cache.as_mut_ptr() as *mut c_void);
        let mut oc: HashMap<(Level,Level),bool> = HashMap::new();
        check("is_geq_core_compute", lbl, r.to_string(), Level::is_geq_core_compute(a, b, &mut oc).to_string());
    }
    for (lbl, l) in [("IMax(P3,Succ(P5))", imax(param(3), succ(param(5)))), ("Max(0,1)", max(zero(),nat(1)))] {
        let r = out_level(|o| tcg_level_clone(o, &l));
        check("Level::clone", lbl, format!("{:?}", r), format!("{:?}", l.clone()));
    }
    for (lbl, a, b) in [("P3,P3", param(3), param(3)), ("P3,P5", param(3), param(5)), ("1,1", nat(1), nat(1)), ("Max(0,1),Max(0,2)", max(zero(),nat(1)), max(zero(),nat(2)))] {
        let r = tcg_level_eq(&a, &b); check("Level::eq", lbl, r.to_string(), (a==b).to_string());
    }
    { let n = Name(42);
      let mut m = MaybeUninit::<Name>::uninit(); tcg_name_clone(m.as_mut_ptr(), &n); let r = m.assume_init();
      check("Name::clone", "Name(42)", format!("{:?}", r), format!("{:?}", n.clone()));
      for (a,b) in [(Name(1),Name(1)),(Name(1),Name(2))] { let r = tcg_name_eq(&a, &b); check("Name::eq", &format!("{:?},{:?}",a,b), r.to_string(), (a==b).to_string()); } }

    let subst: Vec<(Name, Level)> = vec![(Name(3), nat(2)), (Name(5), param(9))];
    let ss: &[(Name, Level)] = &subst;
    let sptr = &ss as *const &[(Name, Level)] as *const c_void;
    // Max(_,P7)/IMax(_,P7): P7 is NOT in subst, so one arm returns None and the
    // enclosing unwrap_or_else INVOKES substitute_impl_opt::{closure#0..3} (the
    // `|| (**l).clone()` fallbacks) — exercising those four closure members.
    for (lbl, l) in [("P3", param(3)), ("Max(P3,P5)", max(param(3),param(5))), ("Succ(P5)", succ(param(5))), ("Zero", zero()), ("IMax(P3,1)", imax(param(3),nat(1))),
                     ("Max(P3,P7)", max(param(3),param(7))), ("Max(P7,P3)", max(param(7),param(3))), ("IMax(P3,P7)", imax(param(3),param(7))), ("IMax(P7,P3)", imax(param(7),param(3)))] {
        let r = out_level(|o| tcg_substitute(o, &l, sptr));
        check("substitute", lbl, format!("{:?}", r), format!("{:?}", l.substitute(ss)));
    }
    for (lbl, l) in [("P3", param(3)), ("Max(P3,P5)", max(param(3),param(5)))] {
        let r = out_level(|o| tcg_substitute_impl(o, &l, sptr));
        check("substitute_impl", lbl, format!("{:?}", r), format!("{:?}", l.substitute_impl(ss)));
    }
    for (lbl, l) in [("P3", param(3)), ("Zero", zero()), ("Succ(P3)", succ(param(3))), ("Max(P3,P5)", max(param(3),param(5)))] {
        let mut m = MaybeUninit::<Option<Level>>::uninit();
        tcg_substitute_impl_opt(m.as_mut_ptr(), &l, sptr);
        check("substitute_impl_opt", lbl, format!("{:?}", m.assume_init()), format!("{:?}", l.substitute_impl_opt(ss)));
    }
    for (lbl, l) in [("Max(P3,IMax(P5,P3))", max(param(3), imax(param(5), param(3)))), ("Succ(P9)", succ(param(9))), ("Zero", zero())] {
        let mut v = NameVec { data: std::ptr::null_mut(), len: 0, cap: 0 };
        tcg_collect_params(&l, &mut v);
        let got: Vec<u32> = (0..v.len).map(|i| *v.data.add(i)).collect();
        let mut ov: Vec<Name> = Vec::new(); l.collect_params(&mut ov);
        check("collect_params", lbl, format!("{:?}", got), format!("{:?}", ov.iter().map(|n| n.0).collect::<Vec<_>>()));
        if !v.data.is_null() { libc_free(v.data as *mut c_void); }
    }
    for (lbl, l) in [("IMax(P3,Max(P5,0))", imax(param(3), max(param(5), zero()))), ("P7", param(7))] {
        let mut v = NameVec { data: std::ptr::null_mut(), len: 0, cap: 0 };
        tcg_collect_params_impl(&l, &mut v);
        let got: Vec<u32> = (0..v.len).map(|i| *v.data.add(i)).collect();
        let mut ov: Vec<Name> = Vec::new(); l.collect_params_impl(&mut ov);
        check("collect_params_impl", lbl, format!("{:?}", got), format!("{:?}", ov.iter().map(|n| n.0).collect::<Vec<_>>()));
        if !v.data.is_null() { libc_free(v.data as *mut c_void); }
    }
}}

#[cfg(grp_defeq)]
extern "C" { #[link_name = "Level__is_def_eq"] fn tcg_is_def_eq(a: *const Level, b: *const Level) -> bool; }
#[cfg(grp_defeq)]
fn run_defeq() { unsafe {
    let cases = [("1,0", nat(1), zero()), ("P3,P3", param(3), param(3)), ("2,1", nat(2), nat(1)), ("P3,P5", param(3), param(5)), ("Max(1,2),Max(2,1)", max(nat(1),nat(2)), max(nat(2),nat(1)))];
    for (lbl, a, b) in cases.iter() { let r = tcg_is_def_eq(a, b); check("is_def_eq", lbl, r.to_string(), Level::is_def_eq(a, b).to_string()); }
}}

#[cfg(grp_leq)]
extern "C" { #[link_name = "Level__leq"] fn tcg_leq(a: *const Level, b: *const Level) -> bool; }
#[cfg(grp_leq)]
fn run_leq() { unsafe {
    let cases = [("0,1", zero(), nat(1)), ("P3,P3", param(3), param(3)), ("1,2", nat(1), nat(2)), ("P5,P3", param(5), param(3)), ("1,Max(1,2)", nat(1), max(nat(1),nat(2)))];
    for (lbl, a, b) in cases.iter() { let r = tcg_leq(a, b); check("leq", lbl, r.to_string(), Level::leq(a, b).to_string()); }
}}

// ---- HASH group -------------------------------------------------------------
// The two std-generic leaves `<u32|isize as Hash>::hash::<DefaultHasher>` are
// provided here in Rust with the exact clean_level_slice-mangled export_name,
// each forwarding to the REAL DefaultHasher::write_* so the SipHash-1-3 bytes
// (and thus finish()) match std exactly.
#[cfg(grp_hash)]
mod hashleaves {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;
    #[export_name = "_RINvXs9_NtNtCs1FFDhjBqhU0_4core4hash5implsmNtB8_4Hash4hashNtNtNtCs5QkB10dUsHY_3std4hash6random13DefaultHasherECskQsKCQTGqGW_17clean_level_slice"]
    pub unsafe extern "C" fn h_u32(val: *const u32, state: *mut DefaultHasher) { (*state).write_u32(*val); }
    #[export_name = "_RINvXsg_NtNtCs1FFDhjBqhU0_4core4hash5implsiNtB8_4Hash4hashNtNtNtCs5QkB10dUsHY_3std4hash6random13DefaultHasherECskQsKCQTGqGW_17clean_level_slice"]
    pub unsafe extern "C" fn h_isize(val: *const isize, state: *mut DefaultHasher) { (*state).write_isize(*val); }
}
#[cfg(grp_hash)]
extern "C" {
    #[link_name = "_Level_as_std__hash__Hash___hash"] fn tcg_level_hash(s: *const Level, h: *mut std::collections::hash_map::DefaultHasher);
    #[link_name = "_Name_as_std__hash__Hash___hash"]  fn tcg_name_hash(s: *const Name, h: *mut std::collections::hash_map::DefaultHasher);
}
#[cfg(grp_hash)]
fn run_hash() { unsafe {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    for (lbl, l) in [("Zero", zero()), ("P3", param(3)), ("Succ(P5)", succ(param(5))), ("Max(P3,IMax(0,P5))", max(param(3), imax(zero(), param(5)))), ("2", nat(2))] {
        let mut h1 = DefaultHasher::new(); tcg_level_hash(&l, &mut h1); let tcg = h1.finish();
        let mut h2 = DefaultHasher::new(); l.hash(&mut h2); let oracle = h2.finish();
        check("Level::hash", lbl, format!("{:016x}", tcg), format!("{:016x}", oracle));
    }
    for n in [Name(0), Name(7), Name(4294967295)] {
        let mut h1 = DefaultHasher::new(); tcg_name_hash(&n, &mut h1); let tcg = h1.finish();
        let mut h2 = DefaultHasher::new(); n.hash(&mut h2); let oracle = h2.finish();
        check("Name::hash", &format!("{:?}", n), format!("{:016x}", tcg), format!("{:016x}", oracle));
    }
}}
