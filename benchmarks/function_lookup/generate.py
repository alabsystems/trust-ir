#!/usr/bin/env python3
"""Deterministic function-table lookup inputs; no compiler or proof authority.

The native benchmark parses these exact serde-JSON modules. The separate Rust
validation target checks schema/module validity and lossless cold carriers.
"""
import argparse
import hashlib
import json
from pathlib import Path


def node(op, payload, results=()):
    return dict(inst={op: payload}, results=list(results), proofs=[], span=None,
                proof_context=None)


def block(key, params, body):
    return dict(id=key, params=params, body=body)


def function(key, ty, blocks, name=None):
    return dict(id=key, name=name or f"f{key}", ty=ty, entry=0, blocks=blocks,
                proofs=[], calling_conv="C", linkage="External",
                attrs=dict(readonly=False, readnone=False, inlinehint=False,
                           cold=False, params=[], naked=False, target_features=[]),
                summary=None, producer=None, value_names=None, scopes=None,
                source_provenance=None, body_gate=None, display_path=None,
                section=None, visibility="Default")


def signature(params, returns):
    return dict(params=params, returns=returns, is_vararg=False)


def module(bits, count, kind, iterations, sparse=False):
    ids = [0] + ([13 + 17*i for i in range(count-2)] + [4294967295]
                 if sparse and count > 1 else list(range(1, count)))
    target = ids[-1]
    identity = lambda key: function(key, 1, [block(0, [[0, "I32"]],
                                    [node("Return", dict(values=[0]))])])
    functions = [identity(key) for key in ids]
    if kind == "calls":
        functions[0] = function(0, 0, [
            block(0, [], [node("Const", dict(ty="I32", value={"Int": iterations}), [0]),
                          node("Const", dict(ty="I32", value={"Int": 42}), [1]),
                          node("Br", dict(target=1, args=[0, 1]))]),
            block(1, [[2, "I32"], [3, "I32"]],
                  [node("Const", dict(ty="I32", value={"Int": 0}), [4]),
                   node("ICmp", dict(op="Ne", ty="I32", lhs=2, rhs=4), [5]),
                   node("CondBr", dict(cond=5, then_target=2, then_args=[2, 3],
                                       else_target=3, else_args=[3]))]),
            block(2, [[6, "I32"], [7, "I32"]],
                  [node("Call", dict(callee=target, args=[7]), [8]),
                   node("Const", dict(ty="I32", value={"Int": 1}), [9]),
                   node("BinOp", dict(op="Sub", ty="I32", lhs=6, rhs=9), [10]),
                   node("Br", dict(target=1, args=[10, 8]))]),
            block(3, [[11, "I32"]], [node("Return", dict(values=[11]))])])
        types = []
        signatures = [signature([], ["I32"]), signature(["I32"], ["I32"])]
    else:
        seq = {"Sequence": 0}
        functions[0] = function(0, 0, [block(0, [], [
            node("Const", dict(ty=seq, value={"Sequence": [{"Int": 7}]*iterations}), [0]),
            node("SeqMap", dict(ty=seq, seq=0, fwd=target), [1]),
            node("Return", dict(values=[1]))])])
        functions[-1] = function(target, 2, [block(0, [[0, {"RefMut": "I8"}]],
                                                        [node("Return", dict(values=[]))])])
        types = ["I8"]
        signatures = [signature([], [seq]), signature(["I32"], ["I32"]),
                      signature([{"RefMut": "I8"}], [])]
    return dict(name=f"lookup_{bits}_{count}_{kind}_{iterations}_{'sparse' if sparse else 'dense'}",
                functions=functions, structs=[], enums=[], records=[], closure_types=[],
                globals=[], func_types=signatures, types=types, proof_obligations=[],
                proof_certificates=[], target_info=dict(
                    triple="wasm32-unknown-unknown" if bits == 32 else "aarch64-apple-darwin",
                    pointer_size=bits//8, endianness="Little", abi=None,
                    struct_passing="Unclassified"), files=[], obligation_diagnostics=[],
                spec_modules=[], universes=[], predicates=[], global_asm=[], imports=[],
                tuple_layouts=[], completeness=None, drop_glue=[])


def emit(directory):
    directory.mkdir(parents=True, exist_ok=True)
    inventory = []
    # A fixed connected-call count isolates table growth; tiny/zero cases expose
    # preparation overhead. Larger Q is supplied by warm-query repetitions.
    for bits in (32, 64):
        for count in (2, 64, 512, 4096, 16384):
            for kind, iterations in (("calls", 1000), ("seqmap", 64)):
                for sparse in (False, True):
                    m = module(bits, count, kind, iterations, sparse)
                    request = dict(fuel=5000, call_depth=8, batches=[dict(module=m,
                                        runs=[dict(function=0, args=[], float_zero_choices=[])])])
                    path = directory / f"{m['name']}.json"
                    path.write_text(json.dumps(request, separators=(",", ":"))+"\n")
                    inventory.append(dict(path=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                        bytes=path.stat().st_size, bits=bits, count=count, kind=kind,
                        iterations=iterations, sparse=sparse, queries=[m['functions'][-1]['id'],
                        4294967294, 0],
                        warm_queries=100000, cold_preparations=10))
        for kind, n in (("calls", 0), ("calls", 1), ("seqmap", 0), ("seqmap", 1)):
            m=module(bits, 2, kind, n)
            path=directory/f"{m['name']}.json"
            path.write_text(json.dumps(dict(fuel=5000,call_depth=8,batches=[dict(module=m,
                runs=[dict(function=0,args=[],float_zero_choices=[])])]),separators=(",",":"))+"\n")
            inventory.append(dict(path=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                bytes=path.stat().st_size,bits=bits,count=2,kind=kind,iterations=n,sparse=False,
                queries=[1,4294967294,0],warm_queries=100000,cold_preparations=100))
    (directory/"inventory.json").write_text(json.dumps(inventory,indent=2)+"\n")
    print(f"{len(inventory)} deterministic request files")


if __name__ == "__main__":
    p=argparse.ArgumentParser();p.add_argument("directory", type=Path);emit(p.parse_args().directory)
