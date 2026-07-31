// Fixture for the MIR-path SPAN-THREADING provenance gate
// (`real_lowering_acceptance.rs::mir_emit_threads_spans`).
//
// `span_probe_sz` is the historically-verified `--mir-emit` shape (the first MIR
// fn verified native == JIT): a recursive Box-ADT fold — a match over a
// recursive enum, payload loads through the faithful layout offsets, and a
// self-recursive Call wired in-module. It exercises statements AND terminators
// (SwitchInt / Call / Return), so the emitted module carries spans from every
// `SourceInfo` threading site.
//
// `main` must CALL it: `--mir-emit` walks `collect_and_partition_mono_items`,
// which only collects REACHABLE mono-items (a dead `pub fn` in a bin crate is
// not collected).

pub enum T {
    Leaf,
    Node(Box<T>, Box<T>),
}

pub fn span_probe_sz(t: &T) -> i64 {
    match t {
        T::Leaf => 1,
        T::Node(a, b) => 1 + span_probe_sz(a) + span_probe_sz(b),
    }
}

fn main() {
    let t = T::Node(Box::new(T::Leaf), Box::new(T::Leaf));
    assert!(span_probe_sz(&t) == 3);
}
