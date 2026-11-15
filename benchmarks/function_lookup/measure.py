#!/usr/bin/env python3
"""Run the same retained native requests before/after lookup-only changes.

Execute this driver itself under build-slot. Timings include the measured machine
conditions; they are not semantic or native-code correctness authority.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(exe, arguments, out, label):
    before = time.monotonic_ns()
    process = subprocess.run(["/usr/bin/time", "-l", str(exe), *map(str, arguments)],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    elapsed = time.monotonic_ns() - before
    (out / f"{label}.stdout").write_bytes(process.stdout)
    (out / f"{label}.stderr").write_bytes(process.stderr)
    assert process.returncode == 0, (label, process.returncode, process.stderr[-2000:])
    rss = re.search(rb"(\d+)\s+maximum resident set size", process.stderr)
    return dict(label=label, exit=process.returncode, elapsed_ns=elapsed,
                max_rss_bytes=int(rss.group(1)) if rss else None,
                stdout_sha256=hashlib.sha256(process.stdout).hexdigest(),
                result=json.loads(process.stdout))


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--oracle",type=Path,required=True)
    p.add_argument("--bench",type=Path,required=True)
    p.add_argument("--requests",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--repetitions",type=int,default=3)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    inventory=json.loads((a.requests/"inventory.json").read_text())
    # Every original request gets one end-to-end observation. Warm timings use
    # dense tables at each size plus sparse 512/16384 and tiny/empty inputs.
    selected=[r for r in inventory if r['kind']=='calls' and
              (not r['sparse'] or r['count'] in (512,16384))]
    selected += [r for r in inventory if r['kind']=='seqmap' and
                 not r['sparse'] and r['count'] in (2,4096)]
    bookend={r['path']:sha(a.requests/r['path']) for r in inventory}
    start=dict(time_ns=time.time_ns(),platform=subprocess.check_output(['uname','-a']).decode(),
               tool_sha256={str(a.oracle):sha(a.oracle),str(a.bench):sha(a.bench)},
               driver_sha256=sha(Path(__file__)),requests=bookend,
               cpu_count=os.cpu_count(),build_slot_held=os.environ.get('BUILD_SLOT_HELD'),
               process_snapshot=subprocess.check_output(['ps','-Ao','pid,ppid,%cpu,rss,comm']).decode())
    (a.out/'start.json').write_text(json.dumps(start,indent=2)+'\n')
    outcomes=[]
    for row in inventory:
        outcomes.append(run(a.oracle,[a.requests/row['path']],a.out,row['path']+'.oracle'))
        (a.out/'oracle-results.json').write_text(json.dumps(outcomes,indent=2)+'\n')
    measurements=[]
    for repetition in range(a.repetitions):
        for row in selected:
            # Keep baseline work bounded at the largest sizes. Counts are
            # recorded and remain byte-identical between the two stages.
            queries=min(100000,max(2000,40000000//row['count']))
            cold_count=100 if row['count']==2 else 10
            measurements.append(run(a.bench,[a.requests/row['path'],queries,cold_count],
                                    a.out,f"{row['path']}.r{repetition}.bench"))
            (a.out/'measurements.json').write_text(json.dumps(measurements,indent=2)+'\n')
    assert bookend=={r['path']:sha(a.requests/r['path'])for r in inventory}
    (a.out/'end.json').write_text(json.dumps(dict(time_ns=time.time_ns(),request_bookend_equal=True,
                 oracle_cases=len(outcomes),timed_cases=len(measurements),
                 repetitions=a.repetitions),indent=2)+'\n')
    print(f"{len(outcomes)} original oracle observations; {len(measurements)} timed cases")


if __name__=='__main__':main()
