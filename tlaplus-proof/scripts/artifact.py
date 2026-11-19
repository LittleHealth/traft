#!/usr/bin/env python3
"""Public, resource-bounded entry point for the TRaft proof artifact."""
import argparse
import copy
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from common import PACKAGE, SUPPORT, published_checks, read, registry, sha, validate_sources, write
from prepare_workspace import prepare
from verify_evidence import verify_archives, verify_run
from toolchain_audit import audit_toolchain
from acceptance import PROOF_SYNTAX_ROOTS


def host_check():
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        raise ValueError('Execution requires Linux x86_64; see docs/reproduction.md')


def jar_check(path):
    path=path.resolve()
    lock=read(PACKAGE/'toolchain/toolchain-lock.json')
    if sha(path)!=lock['tla2tools']['sha256']:
        raise ValueError('TLA+ tools JAR does not match the pinned checksum')
    return path


def tools_check(args, output):
    record=read(args.toolchain)
    lock=read(PACKAGE/'toolchain/toolchain-lock.json')['tlapm']
    if record.get('sha256')!=lock['archive_sha256'] or record.get('official_elf_sha256')!=lock['official_elf_sha256'] or record.get('version')!=lock['version']:
        raise ValueError('Tool installation is not the pinned official build')
    executable=Path(record['executable']).resolve()
    if args.tlapm and args.tlapm.resolve()!=executable:
        raise ValueError('--tlapm differs from the audited toolchain record')
    audit=audit_toolchain(args.toolchain)
    if not audit['accepted']:
        raise ValueError('Toolchain audit failed')
    write(output/'toolchain-before.json',audit)
    shutil.copyfile(args.toolchain,output/'toolchain.json')
    return record, executable


def execute(command, logfile, env=None):
    with logfile.open('w') as log:
        result=subprocess.run([str(c) for c in command], stdout=log, stderr=subprocess.STDOUT,
                              env=dict(os.environ,**(env or {})), check=False)
    return result.returncode


def one_tlc(check, output, jar, workspace, env=None):
    model=PACKAGE/check['model']
    if check['overrides']:
        variant=workspace/'variants'/check['id']
        shutil.copytree(workspace/'models',variant)
        for name, source in check['overrides'].items():
            shutil.copyfile(PACKAGE/source,variant/name)
        model=variant/model.name
    runs=output/'checks'/check['id']
    resources=check['resources']
    command=[sys.executable,SUPPORT/'run_checks.py',check['mode']]
    if check['config']: command += [PACKAGE/check['config']]
    command += ['--model',model,'--jar',jar,'--workers',str(resources['workers']),
                '--heap',resources['heap'],'--timeout',str(resources['timeout_seconds']),
                '--max-disk-gb',str(resources['max_disk_gb']),'--output',runs,'--name',check['id']]
    if check['mode']=='simulate':
        command+=['--seed',str(check['seed']),'--depth',str(check['depth']),
                  '--traces',str(int(check['simulate'].split('num=')[-1].split(',')[0]))]
    rc=execute(command,output/(check['id']+'.log'),env)
    found=list(runs.glob('*/result.json'))
    if len(found)!=1:raise ValueError('Missing or ambiguous result for '+check['id'])
    raw=read(found[0])
    accepted=raw['outcome']==check['expected_outcome'] and raw.get('failed_invariant')==check['expected_invariant']
    record={'id':check['id'],'accepted':accepted,'returncode':rc,
            'outcome':raw['outcome'],'failed_invariant':raw.get('failed_invariant'),
            'result':str(found[0].relative_to(output)),'sha256':sha(found[0]),'stats':raw.get('stats',{})}
    print(json.dumps(record),flush=True)
    return record


def run_tlc(args):
    host_check();jar=jar_check(args.jar)
    output=args.output.resolve();workspace=prepare(output/'workspace')
    all_checks=published_checks(); wanted=set(args.check or [r['id'] for r in all_checks])
    if wanted-set(r['id'] for r in all_checks):raise ValueError('Unknown check ID')
    selected=[r for r in all_checks if r['id'] in wanted]
    summary={'kind':'tlc','selected_checks':[r['id'] for r in selected],'checks':[],
             'jar_sha256':sha(jar),'scope':'Only the explicitly selected published checks'}
    for check in selected:
        summary['checks'].append(one_tlc(check,output,jar,workspace))
        write(output/'run-summary.json',summary)
    result=verify_run(output)
    write(output/'verification.json',result)
    print(json.dumps(result),flush=True)
    return 0


def prover_controls(output, workspace, executable, profile):
    parser_log=output/'parser-selftest.log'
    if execute([sys.executable,SUPPORT/'selftest_runner.py'],parser_log):
        raise ValueError('Frozen acceptance-parser selftest failed')
    command=[sys.executable,SUPPORT/'run_proofs.py','--source',workspace/'models',
             '--tlapm',executable,'--runtime-profile',profile,'--output',output/'prover-controls',
             '--timeout','300','ProofToolPositive','ProofToolNegative','ProofToolSMTNegative']
    execute(command,output/'prover-controls.log')
    records={read(p)['module']:read(p) for p in (output/'prover-controls').glob('*/result.json')}
    if set(records)!={'ProofToolPositive','ProofToolNegative','ProofToolSMTNegative'}:
        raise ValueError('Missing prover controls')
    pos=records['ProofToolPositive']
    if pos['outcome']!='proved' or pos['obligations_reported']!=4 or any(v.get('status') not in ('proved','trivial') or v.get('already')!='false' for v in pos['obligations'].values()):
        raise ValueError('Positive prover control failed')
    for name,backend in [('ProofToolNegative','isabelle'),('ProofToolSMTNegative','smt')]:
        r=records[name]
        if r['outcome']!='unproved' or not any(s.get('status')=='failed' and s.get('reason')=='false' and s.get('prover')==backend for s in r['unproved'].values()):
            raise ValueError('Prover negative control was not rejected: '+name)
    return {'accepted':True,'positive_obligations':4,'negative_controls':['isabelle','smt']}


def verifier_controls():
    """Exercise the public verifier with a modified expected result and coverage."""
    from acceptance import proof_status_coverage
    good={'outcome':'proved','obligations_expected':1,'obligations_reported':1,
          'obligations_proved_summary':1,'unproved':{},
          'obligations':{'1':{'status':'proved','already':'false'}}}
    if not proof_status_coverage(good,1):raise ValueError('Verifier positive control failed')
    for mutate in (
        lambda r:r.update(obligations={}),
        lambda r:r['obligations']['1'].update(status='failed'),
        lambda r:r['obligations']['1'].update(already='true'),
        lambda r:r.update(obligations_reported=0),
    ):
        bad=copy.deepcopy(good);mutate(bad)
        if proof_status_coverage(bad,1):raise ValueError('Verifier accepted corrupted proof coverage')
    if proof_status_coverage(good,2):raise ValueError('Verifier accepted missing obligations')
    return {'accepted':True,'rejected_corruptions':5}


def run_selftest(args):
    host_check();jar=jar_check(args.jar)
    output=args.output.resolve();workspace=prepare(output/'workspace')
    record,exe=tools_check(args,output)
    summary={'kind':'selftest','parser_and_prover':prover_controls(output,workspace,exe,record['runtime_profile']),
             'verifier':verifier_controls()}
    selected=[r for r in published_checks() if r['suite']=='source-semantics']
    summary['semantic_probes']=[one_tlc(c,output,jar,workspace) for c in selected]
    if not all(r['accepted'] for r in summary['semantic_probes']):raise ValueError('Semantic probe failed')
    if args.group:
        rc=execute([sys.executable,SUPPORT/'selftest_proof_group.py','--models',workspace/'models',
                    '--tlapm',exe,'--runtime-profile',record['runtime_profile'],
                    '--output',output/'group-controls'],output/'group-controls.log')
        if rc:raise ValueError('Grouped prover control failed')
        summary['group_controls']=read(output/'group-controls/group-selftest.json')
    after=audit_toolchain(args.toolchain)
    before=read(output/'toolchain-before.json')
    if not after['accepted'] or after['toolchain_record_sha256']!=before['toolchain_record_sha256']:
        raise ValueError('Toolchain changed during selftest')
    write(output/'toolchain-after.json',after)
    summary['accepted']=True
    write(output/'selftest-summary.json',summary)
    print(json.dumps(summary),flush=True)
    return 0


def run_proofs(args):
    host_check();jar=jar_check(args.jar)
    output=args.output.resolve();workspace=prepare(output/'workspace')
    record,exe=tools_check(args,output)
    reg=registry(); modules=args.modules or list(reg['checked_modules'])
    if len(modules)!=len(set(modules)) or set(modules)-set(reg['checked_modules']):
        raise ValueError('Proof modules must be distinct registered names')
    controls=prover_controls(output,workspace,exe,record['runtime_profile'])
    roots=list(PROOF_SYNTAX_ROOTS) if args.modules is None else modules
    for module in roots:
        check={'id':'syntax-'+module,'model':'models/'+module+'.tla','config':None,
               'mode':'sany','overrides':{},'expected_outcome':'syntax_ok','expected_invariant':None,
               'resources':{'workers':1,'heap':'2g','timeout_seconds':60,'max_disk_gb':0.1}}
        r=one_tlc(check,output,jar,workspace,{'JAVA_TOOL_OPTIONS':'-DTLA-Library='+record['stdlib']})
        if not r['accepted']:raise ValueError('SANY preflight failed: '+module)
    command=[sys.executable,SUPPORT/'run_proofs.py','--source',workspace/'models',
             '--tlapm',exe,'--runtime-profile',record['runtime_profile'],'--output',output/'proofs',
             '--timeout','300','--composition-timeout','900','--long-composition-timeout','1800',
             '--group-size','1']+modules
    rc=execute(command,output/'proofs.log')
    found={}
    for path in (output/'proofs').glob('*/result.json'):
        raw=read(path)
        if raw['module'] in found:raise ValueError('Repeated proof result')
        found[raw['module']]=path
    rows=[{'module':m,'result':str(found[m].relative_to(output)),'sha256':sha(found[m])}
          for m in modules if m in found]
    write(output/'toolchain-after.json',audit_toolchain(args.toolchain))
    write(output/'run-summary.json',{'kind':'proof','requested_scope':'full' if args.modules is None else 'selected',
          'requested_modules':modules,'modules':rows,'prover_controls':controls,'returncode':rc})
    result=verify_run(output)
    write(output/'verification.json',result)
    print(json.dumps(result),flush=True)
    return 0


def main():
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest='command',required=True)
    v=sub.add_parser('verify');v.add_argument('--assets',type=Path);v.add_argument('--report',type=Path)
    t=sub.add_parser('tlc');t.add_argument('--check',action='append');t.add_argument('--list',action='store_true')
    for parser in (t,sub.add_parser('selftest'),sub.add_parser('prove')):
        parser.add_argument('--jar',type=Path)
        parser.add_argument('--output',type=Path)
        if parser is not t:
            parser.add_argument('--toolchain',type=Path,required=True)
            parser.add_argument('--tlapm',type=Path)
            if parser.prog.endswith('selftest'):parser.add_argument('--group',action='store_true')
            else:parser.add_argument('--modules',nargs='+')
    c=sub.add_parser('check-results');c.add_argument('--run',type=Path,required=True)
    a=p.parse_args()
    try:
        if a.command=='verify':
            result=verify_archives(a.assets) if a.assets else validate_sources()
            if a.report:write(a.report,result)
            print(json.dumps(result));return 0
        if a.command=='check-results':print(json.dumps(verify_run(a.run)));return 0
        if a.command=='tlc' and a.list:
            for r in published_checks():print(r['id'],r['classification'])
            return 0
        if not a.jar or not a.output:p.error('--jar and --output are required for execution')
        if a.output.exists():p.error('Use a new output directory; existing evidence is never overwritten')
        return {'tlc':run_tlc,'prove':run_proofs,'selftest':run_selftest}[a.command](a)
    except (ValueError,KeyError,OSError) as error:
        print(str(error),file=sys.stderr)
        return 2


if __name__=='__main__':
    raise SystemExit(main())
