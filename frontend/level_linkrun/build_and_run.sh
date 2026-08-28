#!/bin/zsh
# End-to-end link+run value-check of the first-party clean-kernel `Level` slice
# through the trust-ir -> tMBC -> trust-cg -> native-object -> link -> run path.
#
#   frontend --mir-emit-closure  ->  self-contained textual trust-ir module
#     -> trust-ir convert --from text --to bin  +  tMBC envelope  -> .tmbc
#     -> trust-cg -c                            -> Mach-O object
#     -> link (closure object[s] + runtime.o + Rust driver) + real-method oracle
#     -> run, structurally compare every result to the real Rust method.
#
# Requires: the stage1 toolchain, the trust-ir main-repo CLI (writes binary
# format v37; readers accept v23-v25 and v29-v37), and a
# trust-cg built from the jump-table-fix branch (commit e4455fb).
set -u
# Tool locations — override via env. Defaults: the trust / trust-cg checkouts
# live under $HOME; FE/CLI derive from this script's own location in the repo.
STAGE1=${STAGE1:-$HOME/trust/build/aarch64-apple-darwin/stage1}
FE=${FE:-${0:a:h:h}}                                # this repo's frontend/
CORPUS=$FE/clean_level_slice.rs
CLI=${CLI:-${0:a:h:h:h}/target/release/trust-ir}
CG=${CG:-$HOME/trust-cg/target/release/trust-cg}    # built from e4455fb
HERE=${0:a:h}
OUT=${1:-/tmp/level_linkrun.out}
mkdir -p "$OUT"
export DYLD_FALLBACK_LIBRARY_PATH=$STAGE1/lib/rustlib/aarch64-apple-darwin/lib
export RUSTUP_TOOLCHAIN=
RUSTC=$STAGE1/bin/rustc

emit() { # <fn-substr> <name>
  "$FE/target/release/trust_ir_mir" --mir-emit-closure "$1" "$OUT/$2.trust_ir" \
    --sysroot $STAGE1 -Zno-trust-verify --crate-type=lib "$CORPUS" 2>&1 | grep -E 'EMIT-CLOSURE-(OK|FAIL)'
  "$CLI" convert --from text --to bin "$OUT/$2.trust_ir" "$OUT/$2.bin" >/dev/null
  printf 'tMBC\x01\x00\x00\x00' > "$OUT/$2.tmbc"; cat "$OUT/$2.bin" >> "$OUT/$2.tmbc"
  "$CG" -c "$OUT/$2.tmbc" -o "$OUT/$2.o" 2>&1 | grep -i error
}

echo "== 1. emit closures + trust-cg -c =="
emit "Level::substitute"     substitute
emit "Level::has_params"     has_params
emit "Level::collect_params" collect_params
emit "Level::param"          param
emit "Level::is_def_eq"      is_def_eq
emit "Level::leq"            leq
emit "hash::Hash>::hash"     hash

echo "== 2. oracle module (corpus with methods pub, main stripped) =="
sed -e 's/^    fn /    pub fn /' -e '/^fn main() {}/d' "$CORPUS" > "$HERE/oracle.rs"

echo "== 3. runtime.o (the minimal std-generic leaves) =="
cc -c -O1 "$HERE/runtime.c" -o "$OUT/runtime.o"

echo "== 4. link + run each group =="
cp "$HERE/oracle.rs" "$OUT/oracle.rs"; cp "$HERE/driver.rs" "$OUT/driver.rs"
build() { # <group> <extra .o ...>
  local grp=$1; shift
  $RUSTC -Zno-trust-verify -Copt-level=0 -Awarnings --cfg grp_$grp "$OUT/driver.rs" -o "$OUT/driver_$grp" \
    ${^@/#/-Clink-arg=} 2>/dev/null
  "$OUT/driver_$grp" $grp
}
build main  "$OUT/substitute.o" "$OUT/has_params.o" "$OUT/collect_params.o" "$OUT/param.o" "$OUT/runtime.o"
build defeq "$OUT/is_def_eq.o" "$OUT/runtime.o"
build leq   "$OUT/leq.o" "$OUT/runtime.o"
build hash  "$OUT/hash.o"       # hash leaves are Rust, provided in-driver

echo "== 5. ASan (heap UB) + leaks (macOS) on the runtime =="
cc -g -fsanitize=address "$HERE/asan_harness.c" "$HERE/runtime.c" \
   "$OUT/substitute.o" "$OUT/param.o" "$OUT/collect_params.o" -o "$OUT/asan_harness" 2>/dev/null
ASAN_OPTIONS=abort_on_error=0 "$OUT/asan_harness"
cc -g -O0 "$HERE/asan_harness.c" "$OUT/runtime.o" \
   "$OUT/substitute.o" "$OUT/param.o" "$OUT/collect_params.o" -o "$OUT/leaks_harness" 2>/dev/null
leaks --atExit -- "$OUT/leaks_harness" 2>&1 | grep -iE 'total leaked|0 leaks'
