#!/usr/bin/env python3
"""Derive the separately named V2 request cohort without changing V1.

Only the request fuel changes, 10000 -> 20000; every module byte stays fixed.
This is benchmark input, not an interpreter default/cap/policy modification.
No validation, Lean/native oracle execution or timing is performed here.
"""
import argparse
import hashlib
import json
from pathlib import Path

VERSION = 'decoded-cfg-v2-fuel20000'
ORIGINAL_INVENTORY_SHA256 = '6d2bf2a528c0c5b3d9fd6f7b8f96dcccf5e1344a054027c22da63fdeaeaeff94'
ORIGINAL_GENERATOR_SHA256 = '9d02a497ee260d124ed9bf47dee461a93d40741e279ebf5dbfd0a468ff6f3094'


def derive(original, destination):
    raw_inventory = (original / 'inventory.json').read_bytes()
    assert hashlib.sha256(raw_inventory).hexdigest() == ORIGINAL_INVENTORY_SHA256
    inventory = json.loads(raw_inventory)
    assert len(inventory['cases']) == 66
    destination.mkdir(parents=True, exist_ok=False)
    cases = []
    for row in inventory['cases']:
        raw = (original / row['path']).read_bytes()
        assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
        request = json.loads(raw)
        assert request['fuel'] == 10000 and request['call_depth'] == 8
        assert raw.count(b'"fuel":10000') == 1
        updated = raw.replace(b'"fuel":10000', b'"fuel":20000', 1)
        decoded = json.loads(updated)
        decoded['fuel'] = 10000
        assert decoded == request
        assert updated.replace(b'"fuel":20000', b'"fuel":10000', 1) == raw
        (destination / row['path']).write_bytes(updated)
        cases.append(dict(row, sha256=hashlib.sha256(updated).hexdigest(),
                          bytes=len(updated), original_sha256=row['sha256'],
                          fuel=20000, call_depth=8))
    result = dict(cohort_version=VERSION, source_generator_sha256=ORIGINAL_GENERATOR_SHA256,
                  derived_from_inventory_sha256=ORIGINAL_INVENTORY_SHA256,
                  original_product_source=inventory['original_product_source'],
                  helper_source=inventory['helper_source'], helper_sha256=inventory['helper_sha256'],
                  delta='Exact byte substitution of the single request fuel:10000 with fuel:20000',
                  rationale='Largest original reference path needs N+6*iterations+3=10099 instruction ticks',
                  production_caps_or_policy_changed=False, cases=cases,
                  validated=False, native_oracle_executed=False, performance_authority=False)
    (destination / 'inventory.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(version=VERSION, cases=len(cases), delta='fuel only', validation='pending')))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('original', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    derive(args.original, args.destination)
