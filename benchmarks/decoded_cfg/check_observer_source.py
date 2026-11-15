#!/usr/bin/env python3
"""Source/input protocol detection only; never invokes Lean or an executable."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess

SUPPORT = 'f871b2227868fb6e81ab7b9907785637be89d99e'
PRODUCT = '348424bd26baea729a9d5c5837730b1356043bdd'
ORIGINAL_INVENTORY = '6d2bf2a528c0c5b3d9fd6f7b8f96dcccf5e1344a054027c22da63fdeaeaeff94'
V2_INVENTORY = 'ab551e29400bdc25ae4cec2875755236473145690dfe1750fd23c4d15c657906'
TARGET = '''-- Optional decoded-CFG phase observer; outside the default proof target.
lean_exe trustir_cfg_bench where
  root := `Tools.DecodedCFGBenchmark
  moreLinkArgs := if System.Platform.isOSX then #["-Wl,-no_data_const"] else #[]

'''
MAPPING_TARGET = '''
-- Correctness-only overlay; not part of the phase observer or default proof target.
lean_exe trustir_cfg_mapping_probe where
  root := `Tools.DecodedCFGMappingProbe
  moreLinkArgs := if System.Platform.isOSX then #["-Wl,-no_data_const"] else #[]
'''
PERIODIC_TARGET = '''
lean_exe trustir_periodic_values where
  root := `TrustIrEval.PeriodicValueTests
  moreLinkArgs := if System.Platform.isOSX then #["-Wl,-no_data_const"] else #[]
'''


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def ordered(text, *markers):
    position = 0
    for marker in markers:
        found = text.find(marker, position)
        assert found >= 0, ('missing or reordered source marker', marker)
        position = found + len(marker)


def functions(source):
    declarations = list(re.finditer(
        r'(?m)^(?:@\[[^\]\n]+\] )?(?:private )?(?:def|structure) (\w+)', source))
    return {row.group(1): source[row.start():declarations[i + 1].start()
            if i + 1 < len(declarations) else len(source)]
            for i, row in enumerate(declarations)}


def source_contract(source, lakefile, old_lakefile):
    anchor = 'lean_exe trustir_byte_images where\n'
    assert old_lakefile.count(anchor) == 1
    expected_lakefile = (old_lakefile.replace(anchor, TARGET + anchor, 1)
                         + MAPPING_TARGET + PERIODIC_TARGET)
    assert lakefile == expected_lakefile
    assert source.count('import ') == 1 and 'import TrustIrEval.Run\n' in source
    f = functions(source)
    sample = f['cfgSample']
    ordered(sample, 'function.cfg ⟨query⟩', '| none => 0', '| some block =>',
            'block.params.length', 'block.body.length', 'block.bodyResultDests.length',
            'block.terminatorResultDests.length')
    assert all(word not in sample for word in ['NatIndex', 'cfgOf', 'contextOf'])
    warm = f['warmCFG']
    ordered(warm, 'IO.mkRef function', 'let start ← IO.monoNanosNow',
            'for _ in [:repetitions] do', 'for query in queries do',
            'cfgSample function query', 'let stop ← IO.monoNanosNow',
            'let retained ← keeper.get', 'retainedChecksum := retained.entryBlock.index')
    assert all(word not in warm for word in ['contextOf', 'TrustIrEval.module', 'cfgOf', 'NatIndex'])
    decode = f['decodeRetained']
    ordered(decode, 'IO.mkRef moduleJSON', 'IO.mkRef (#[] : Array TrustIrEval.Module)',
            'let start ← IO.monoNanosNow', 'for _ in [:count] do', 'input.get',
            'TrustIrEval.module currentJSON', 'modules := modules.push source',
            'keeper.set modules', 'let stop ← IO.monoNanosNow', 'let retained ← keeper.get',
            'retained.foldl', 'decodedSample source')
    prepare = f['preparedCFGContexts']
    ordered(prepare, 'for i in [:count] do', 'contextOf source (8 + i % 2)',
            'contexts := contexts.push context')
    assert all(word not in prepare for word in ['.functions', 'mixedContextSample', 'cfgSample'])
    constructor = f['contextRetained']
    ordered(constructor, 'IO.mkRef (#[] : Array EvalContext)', 'let start ← IO.monoNanosNow',
            'preparedCFGContexts source count', 'keeper.set contexts',
            'let stop ← IO.monoNanosNow', 'let retained ← keeper.get',
            'retained.foldl', 'context.maxCallDepth')
    lifecycle = f['contextLifecycle']
    ordered(lifecycle, 'let start ← IO.monoNanosNow', 'for i in [:count] do',
            'contextOf source (8 + i % 2)', 'mixedContextSample context',
            'let stop ← IO.monoNanosNow')
    assert 'IO.mkRef' not in lifecycle and 'Array EvalContext' not in lifecycle
    main = f['main']
    ordered(main, 'caseMetadata inventory caseKey', 'listField metadata "queries"',
            'let [lastKey, missingKey, firstKey] := queryList',
            'TrustIrEval.module moduleJSON', 'contextOf source 8',
            'let some function := ctx.functions ⟨0⟩', 'let decode ← decodeRetained',
            'let constructor ← contextRetained', 'let lifecycle ← contextLifecycle',
            'let warm ← warmCFG function queries repetitions')
    assert '("warm_loop_repetitions", jnat repetitions)' in main
    assert '("warm_query_count", jnat (repetitions * queries.size))' in main
    for label, value in [('decode_retained', 'decode'), ('context_retained', 'constructor'),
                         ('context_lifecycle', 'lifecycle'), ('warm_cfg', 'warm')]:
        assert f'("{label}", phaseJSON {value})' in main
    assert '("checksum",' not in main
    assert 'fuel != 20000 || depth != 8' in main
    assert source.count('IO.monoNanosNow') == 8
    return True


def negative_controls(source, lakefile, old_lakefile):
    mutants = {
        'warm_constant_result': source.replace('function.cfg ⟨query⟩', '(none : Option BasicBlock)', 1),
        'warm_count_mislabel': source.replace('jnat (repetitions * queries.size)', 'jnat repetitions', 1),
        'lost_constructor_depth_dependency': source.replace('contextOf source (8 + i % 2)', 'contextOf source 8'),
        'warm_context_reconstruction': source.replace('let keeper ← IO.mkRef function',
            'let rebuilt := contextOf arbitrarySource 8\n  let keeper ← IO.mkRef function', 1),
        'missing_phase_checksum': source.replace('("warm_cfg", phaseJSON warm)',
            '("checksum", jnat (warm.checksum + decode.checksum))', 1),
    }
    warm = functions(source)['warmCFG']
    wrong = warm.replace('  let stop ← IO.monoNanosNow\n', '', 1).replace(
        '  let retained ← keeper.get', '  let retained ← keeper.get\n  let stop ← IO.monoNanosNow', 1)
    mutants['warm_retention_read_before_stop'] = source.replace(warm, wrong, 1)
    results = []
    for name, mutant in mutants.items():
        assert mutant != source
        try:
            source_contract(mutant, lakefile, old_lakefile)
        except AssertionError:
            results.append(dict(control=name, source_detector_refused=True))
        else:
            raise AssertionError(('negative source detector accepted', name))
    try:
        source_contract(source, lakefile.replace(TARGET, '@[default_target]\n' + TARGET, 1), old_lakefile)
    except AssertionError:
        results.append(dict(control='observer_default_target', source_detector_refused=True))
    else:
        raise AssertionError('negative source detector accepted observer default target')
    try:
        source_contract(source, lakefile.replace(MAPPING_TARGET,
            '@[default_target]\n' + MAPPING_TARGET, 1), old_lakefile)
    except AssertionError:
        results.append(dict(control='mapping_default_target', source_detector_refused=True))
    else:
        raise AssertionError('negative source detector accepted mapping default target')
    for name, target in [('observer_relocated_under_default', TARGET),
                         ('mapping_relocated_under_default', MAPPING_TARGET)]:
        relocated = lakefile.replace(target, '', 1)
        attribute = '@[default_target]\n'
        assert relocated.count(attribute) == 1
        relocated = relocated.replace(attribute, attribute + target, 1)
        try:
            source_contract(source, relocated, old_lakefile)
        except AssertionError:
            results.append(dict(control=name, source_detector_refused=True))
        else:
            raise AssertionError(('negative source detector accepted relocation', name))
    return results


def check(root):
    source_path = Path('lean/trust_ir-semantics/Tools/DecodedCFGBenchmark.lean')
    lake_path = Path('lean/trust_ir-semantics/lakefile.lean')
    source = (root / source_path).read_text()
    lakefile = (root / lake_path).read_text()
    old_lakefile = subprocess.check_output(['git', 'show', f'{PRODUCT}:{lake_path}'], cwd=root).decode()
    source_contract(source, lakefile, old_lakefile)
    controls = negative_controls(source, lakefile, old_lakefile)
    original_dir = root / 'benchmarks/decoded_cfg/proposed-requests'
    v2_dir = root / 'benchmarks/decoded_cfg/fuel-adjusted-requests'
    original_raw = (original_dir / 'inventory.json').read_bytes()
    v2_raw = (v2_dir / 'inventory.json').read_bytes()
    assert digest(original_raw) == ORIGINAL_INVENTORY and digest(v2_raw) == V2_INVENTORY
    original = json.loads(original_raw)
    v2 = json.loads(v2_raw)
    assert len(original['cases']) == len(v2['cases']) == 66
    sparse = 0
    for before, after in zip(original['cases'], v2['cases']):
        assert before['path'] == after['path']
        old = (original_dir / before['path']).read_bytes()
        new = (v2_dir / after['path']).read_bytes()
        assert digest(old) == before['sha256'] and digest(new) == after['sha256']
        assert new == old.replace(b'"fuel":10000', b'"fuel":20000', 1)
        request = json.loads(new)
        assert request['fuel'] == 20000 and request['call_depth'] == 8
        rows = request['batches'][0]['module']['functions'][0]['blocks']
        keys = [row['id'] for row in rows]
        assert after['queries'] == [keys[-1], 4294967294, keys[0]]
        assert 4294967294 not in keys and len(rows) == after['blocks']
        sparse += after['sparse']
    for rel, original_rel in [
            ('benchmarks/decoded_cfg/generate.py', 'benchmarks/decoded_cfg/generate.py'),
            ('benchmarks/decoded_cfg/proposed-requests/original-helpers.py',
             'benchmarks/decoded_cfg/proposed-requests/original-helpers.py'),
            ('benchmarks/decoded_cfg/derive_reference_fuel.py',
             'benchmarks/decoded_cfg/derive_v2.py'),
            ('crates/trust-ir-conformance/examples/decoded_cfg_inputs.rs',
             'crates/trust-ir-conformance/examples/decoded_cfg_inputs.rs'),
            ('lean/trust_ir-semantics/Tools/FunctionLookupBenchmark.lean',
             'lean/trust_ir-semantics/Tools/FunctionLookupBenchmark.lean')]:
        assert (root / rel).read_bytes() == subprocess.check_output(
            ['git', 'show', f'{SUPPORT}:{original_rel}'], cwd=root)
    ast.parse(Path(__file__).read_text(), filename=__file__)
    return dict(source_marker_checks=True, negative_source_controls=controls,
                original_and_V2_cases_unchanged=66, sparse_cases=sparse,
                observer_sha256=digest((root / source_path).read_bytes()),
                lakefile_sha256=digest((root / lake_path).read_bytes()),
                support_parent=SUPPORT, product_baseline=PRODUCT,
                Lean_elaboration_or_generated_C_check=False,
                executable_or_oracle_or_timing_run=False, performance_or_native_authority=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.root.resolve())
    raw = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(raw)
    print(raw, end='')
