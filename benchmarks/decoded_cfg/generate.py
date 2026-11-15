#!/usr/bin/env python3
"""Proposed reachable CFG inputs. No validation, timing or compiler authority.

Freeze these bytes and independently validate requests before measurement.
The current publication does not include this future support prototype.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

BASELINE = '1fe526c1848377ce9423297f10458c6bd06f7870'
HELPER = 'benchmarks/function_lookup/generate.py'


def load_helpers(repo, destination):
    raw = subprocess.check_output(['git', 'show', BASELINE + ':' + HELPER], cwd=repo)
    path = destination / 'original-helpers.py'
    path.write_bytes(raw)
    spec = importlib.util.spec_from_file_location('original_lookup_helpers', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module, hashlib.sha256(raw).hexdigest()


def cfg_module(h, bits, count, iterations, sparse):
    ids = ([0] + [13 + 17*i for i in range(count-2)] + [4294967295]
           if sparse and count > 1 else list(range(count)))
    counter = 0

    def fresh():
        nonlocal counter
        result = counter
        counter += 1
        return result

    def const(value):
        reg = fresh()
        return reg, h.node('Const', dict(ty='I32', value={'Int': value}), [reg])

    if count == 1:
        value, instruction = const(42)
        rows = [h.block(ids[0], [], [instruction, h.node('Return', dict(values=[value]))])]
    elif count == 2:
        value, instruction = const(42)
        incoming = fresh()
        rows = [h.block(ids[0], [], [instruction, h.node('Br', dict(target=ids[1], args=[value]))]),
                h.block(ids[1], [[incoming, 'I32']], [h.node('Return', dict(values=[incoming]))])]
    else:
        assert count >= 4
        initial, initial_inst = const(iterations)
        value, value_inst = const(42)
        body_counter, body_value = fresh(), fresh()
        one, one_inst = const(1)
        reduced = fresh()
        exit_counter, exit_value = fresh(), fresh()
        chain_params = [(fresh(), fresh()) for _ in range(count-4)]
        check_counter, check_value = fresh(), fresh()
        zero, zero_inst = const(0)
        condition = fresh()
        first = ids[3] if count > 4 else ids[-1]
        rows = [
            h.block(ids[0], [], [initial_inst, value_inst,
                h.node('Br', dict(target=first, args=[initial, value]))]),
            h.block(ids[1], [[body_counter, 'I32'], [body_value, 'I32']], [one_inst,
                h.node('BinOp', dict(op='Sub', ty='I32', lhs=body_counter, rhs=one), [reduced]),
                h.node('Br', dict(target=ids[-1], args=[reduced, body_value]))]),
            h.block(ids[2], [[exit_counter, 'I32'], [exit_value, 'I32']],
                [h.node('Return', dict(values=[exit_value]))]),
        ]
        for position, (incoming_counter, incoming_value) in enumerate(chain_params, 3):
            rows.append(h.block(ids[position], [[incoming_counter, 'I32'], [incoming_value, 'I32']],
                [h.node('Br', dict(target=ids[position+1], args=[incoming_counter, incoming_value]))]))
        rows.append(h.block(ids[-1], [[check_counter, 'I32'], [check_value, 'I32']], [zero_inst,
            h.node('ICmp', dict(op='Ne', ty='I32', lhs=check_counter, rhs=zero), [condition]),
            h.node('CondBr', dict(cond=condition, then_target=ids[1],
                then_args=[check_counter, check_value], else_target=ids[2],
                else_args=[check_counter, check_value]))]))
    assert len(rows) == count and len({row['id'] for row in rows}) == count
    module = h.module(bits, 2, 'calls', 0)
    label = f'cfg_{bits}_{count}_{iterations}_{"sparse" if sparse else "dense"}'
    module['name'] = label
    module['functions'] = [h.function(0, 0, rows, label)]
    module['func_types'] = [h.signature([], ['I32'])]
    return module, ids


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    h, helper_sha = load_helpers(args.repo, args.directory)
    inventory = []
    for bits in [32, 64]:
        for count in [1, 2, 4, 8, 64, 512, 4096]:
            for iterations in ([0] if count < 4 else [0, 1, 1000]):
                for sparse in ([False] if count == 1 else [False, True]):
                    module, ids = cfg_module(h, bits, count, iterations, sparse)
                    request = dict(fuel=10000, call_depth=8, batches=[dict(module=module,
                        runs=[dict(function=0, args=[], float_zero_choices=[])])])
                    name = module['name'] + '.json'
                    raw = json.dumps(request, separators=(',', ':')).encode()+b'\n'
                    (args.directory/name).write_bytes(raw)
                    inventory.append(dict(path=name, sha256=hashlib.sha256(raw).hexdigest(),
                        bytes=len(raw), bits=bits, blocks=count, iterations=iterations,
                        sparse=sparse, queries=[ids[-1], 4294967294, ids[0]], expected_i32=42))
    receipt = dict(original_product_source=BASELINE, helper_source=HELPER,
                   helper_sha256=helper_sha, cases=inventory,
                   validated=False, native_executed=False, performance_authority=False)
    (args.directory/'inventory.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(dict(proposed_cases=len(inventory), validation='pending', timing='none')))


if __name__ == '__main__':
    main()
