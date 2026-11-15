#!/usr/bin/env python3
"""Check fixed cold carriers against explicit deep values on two saved oracles."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def deep(graph, index):
    node = graph['nodes'][index]
    if node[0] == 'int':
        return ('int',node[1],int(node[2]))
    if node[0] == 'nil':
        return []
    if node[0] == 'cons':
        return [deep(graph,node[1]),*deep(graph,node[2])]
    if node[0] == 'sequence':
        return ('sequence',deep(graph,node[1]))
    raise AssertionError(('unexpected graph kind',node))


def main():
    p=argparse.ArgumentParser();p.add_argument('before',type=Path);p.add_argument('after',type=Path)
    p.add_argument('directory',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    validation=json.loads((a.directory/'validation.json').read_text());results=[]
    for row in validation['cases']:
        request=a.directory/row['path'];source=json.loads(request.read_text())['batches'][0]['module']
        name=source['name'];parts=name.split('_');iterations=int(parts[4]);sequence=parts[3]=='seqmap'
        expected=('sequence',[('int',8,7)]*iterations)if sequence else ('int',32,42)
        outputs=[]
        for stage,exe in [('before',a.before),('after',a.after)]:
            process=subprocess.run([str(exe),str(request)],capture_output=True,check=False)
            assert process.returncode==0,(request,stage,process.stderr)
            result=json.loads(process.stdout);assert len(result)==len(result[0])==1,(request,result)
            verdict=result[0][0];assert list(verdict)==['ok'],(request,stage,verdict)
            graph=verdict['ok']['graph'];assert graph['version']==2 and len(graph['roots'])==1
            assert deep(graph,graph['roots'][0])==expected,(request,stage,verdict)
            (a.output/(row['path']+'.'+stage+'.stdout')).write_bytes(process.stdout)
            (a.output/(row['path']+'.'+stage+'.stderr')).write_bytes(process.stderr)
            outputs.append(process.stdout)
        assert outputs[0]==outputs[1],request
        results.append(dict(path=row['path'],sha256=hashlib.sha256(request.read_bytes()).hexdigest(),
                            exact_before_after_equal=True,deep_expected_value_equal=True))
    summary=dict(validated_cold_cases=len(results),oracle_executions=2*len(results),
                 sparse_checked_text_refusals=validation['checked_text_id_refusals'],
                 before_sha256=hashlib.sha256(a.before.read_bytes()).hexdigest(),
                 after_sha256=hashlib.sha256(a.after.read_bytes()).hexdigest(),cases=results)
    (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(f"{len(results)} validated cold cases: both deep values and exact oracle responses equal")


if __name__=='__main__':main()
