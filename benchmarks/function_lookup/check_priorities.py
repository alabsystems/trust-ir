#!/usr/bin/env python3
"""Raw runtime controls: no validator/admitted-module credit is inferred."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
from generate import module, node


def abi(bits):
    return dict(target=dict(triple='wasm32-unknown-unknown' if bits==32 else 'aarch64-apple-darwin',
                data_layout='',abi='',cpu='',features=[],target_spec='',pointer_bytes=bits//8,little_endian=True),
                frontend=dict(name='lookup-control',revision='raw'),convention='C',lowered_convention='C',
                source_abi='C',can_unwind=False,variadic=False,fixed_count=0,arguments=[],
                result=dict(size=0,align=1,mode='Ignore',bindings=[]))


def cases(bits):
    base=module(bits,2,'seqmap',0)
    def emit(label, m, expected, fuel=5000, depth=8):
        return label,dict(fuel=fuel,call_depth=depth,batches=[dict(module=m,runs=[dict(function=0,args=[])])]),expected
    yield emit('empty_defined',copy.deepcopy(base),'ok')
    m=copy.deepcopy(base);m['functions'][-1]['blocks']=[]
    yield emit('empty_declaration',m,'ok')
    m=copy.deepcopy(base);m['functions'][-1]['blocks'][0]['body'].insert(0,node('Const',dict(ty='I32',value={'Int':7}),[0]))
    yield emit('empty_ignores_metadata_error',m,'ok')
    m1=copy.deepcopy(m);m1['functions'][0]['blocks'][0]['body'][0]['inst']['Const']['value']={'Sequence':[{'Int':7}]}
    yield emit('nonempty_observes_metadata_error',m1,'type_error')
    m=copy.deepcopy(base);m['func_types'][2]['params']=[]
    yield emit('empty_checks_header',m,'type_error')
    yield emit('zero_depth_precedes_bad_header',m,'out_of_fuel',depth=0)
    yield emit('zero_fuel_precedes_bad_header',m,'out_of_fuel',fuel=0)
    m=copy.deepcopy(base);m['func_types'][2]['is_vararg']=True
    yield emit('empty_checks_vararg',m,'type_error')
    m=copy.deepcopy(base);m['functions'][-1]['blocks'][0]['body'].insert(0,node('UnknownLookupControl',{},[1]))
    yield emit('raw_reachable_decode_error',m,'unsupported')
    m=copy.deepcopy(base);m['func_types'][0]['abi']=abi(bits)
    yield emit('typed_abi_refusal',m,'unsupported')
    yield emit('typed_abi_precedes_zero_resources',m,'unsupported',fuel=0,depth=0)
    m=copy.deepcopy(m);m['target_info']['pointer_size']=16
    yield emit('byte_model_precedes_typed_abi',m,'unsupported',fuel=0,depth=0)


def main():
    p=argparse.ArgumentParser();p.add_argument('before',type=Path);p.add_argument('after',type=Path);p.add_argument('output',type=Path);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);reports=[]
    for bits in (32,64):
        for label,request,expected in cases(bits):
            name=f'{bits}_{label}';path=a.output/(name+'.request.json');path.write_text(json.dumps(request,separators=(',',':'))+'\n');outputs=[]
            for stage,exe in [('before',a.before),('after',a.after)]:
                process=subprocess.run([str(exe),str(path)],capture_output=True,check=False)
                assert process.returncode==0,(name,stage,process.stderr)
                value=json.loads(process.stdout);assert len(value)==len(value[0])==1,(name,stage,value)
                assert list(value[0][0])==[expected],(name,stage,expected,value)
                if 'typed_abi' in label and 'byte_model' not in label:
                    assert value[0][0]['unsupported']=='signature_abi.transport_semantics',(name,value)
                if label=='byte_model_precedes_typed_abi':
                    assert value[0][0]['unsupported']=='target.byte_model',(name,value)
                (a.output/(name+'.'+stage+'.stdout')).write_bytes(process.stdout)
                (a.output/(name+'.'+stage+'.stderr')).write_bytes(process.stderr);outputs.append(process.stdout)
            assert outputs[0]==outputs[1],name
            reports.append(dict(label=name,expected=expected,exact_before_after_equal=True,raw_control=True,validated_module_credit=False))
    (a.output/'summary.json').write_text(json.dumps(dict(raw_controls=len(reports),oracle_executions=2*len(reports),cases=reports),indent=2)+'\n')
    print(f'{len(reports)} raw priority controls: expected classification and exact before/after response equal')


if __name__=='__main__':main()
