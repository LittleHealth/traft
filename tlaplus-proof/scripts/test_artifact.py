"""Acceptance regressions using copies of real small runs; no new model search."""
import argparse
import copy
from pathlib import Path
import shutil
import tempfile
from common import PACKAGE, read, sha, validate_sources, write
from verify_evidence import verify_run


def fixture_tlc(source,dest):
    summary=read(source/'run-summary.json')
    row=copy.deepcopy(next(r for r in summary['checks'] if read(source/r['result']).get('config')))
    folder=Path(row['result']).parent
    shutil.copytree(source/folder,dest/folder)
    write(dest/'run-summary.json',dict(summary,selected_checks=[row['id']],checks=[row]))


def fixture_proof(source,dest):
    for name in ('run-summary.json','parser-selftest.log','toolchain-before.json','toolchain-after.json','toolchain.json'):
        shutil.copyfile(source/name,dest/name)
    for name in ('proofs','prover-controls','checks'):
        shutil.copytree(source/name,dest/name)


def update_result(dest,kind,change):
    summary=read(dest/'run-summary.json')
    row=summary['checks' if kind=='tlc' else 'modules'][0]
    path=dest/row['result']
    raw=read(path);change(raw);write(path,raw)
    row['sha256']=sha(path)
    write(dest/'run-summary.json',summary)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tlc-run',type=Path,required=True)
    p.add_argument('--proof-run',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    cases=[]
    def check(name,kind,change,accept=False):
        with tempfile.TemporaryDirectory(prefix='traft-artifact-control-') as tmp:
            dest=Path(tmp)
            (fixture_tlc if kind=='tlc' else fixture_proof)(args.tlc_run if kind=='tlc' else args.proof_run,dest)
            if change:change(dest)
            try:
                verify_run(dest);accepted=True;reason=None
            except (ValueError,KeyError,OSError) as e:
                accepted=False;reason=str(e)
            passed=accepted==accept
            cases.append({'case':name,'passed':passed,'expected_acceptance':accept,'observed_acceptance':accepted,'reason':reason})
            if not passed:raise AssertionError(name)
    check('actual_completed_tlc','tlc',None,True)
    check('wrong_tlc_outcome','tlc',lambda d:update_result(d,'tlc',lambda r:r.update(outcome='timeout')))
    check('wrong_tlc_model','tlc',lambda d:update_result(d,'tlc',lambda r:r.update(model='Different.tla')))
    check('wrong_tlc_tool','tlc',lambda d:update_result(d,'tlc',lambda r:r['toolkit'].update(sha256='0'*64)))
    check('wrong_tlc_config_hash','tlc',lambda d:update_result(d,'tlc',lambda r:r['inputs'][r['config']].update(sha256='0'*64)))
    check('actual_selected_proofs','proof',None,True)
    check('cached_proof_obligation','proof',lambda d:update_result(d,'proof',lambda r:next(iter(r['obligations'].values())).update(already='true')))
    check('missing_proof_obligation','proof',lambda d:update_result(d,'proof',lambda r:r['obligations'].pop(next(iter(r['obligations'])))))
    def claim_full(d):
        s=read(d/'run-summary.json');s['requested_scope']='full';write(d/'run-summary.json',s)
    check('selected_proofs_cannot_claim_full','proof',claim_full)
    def lost_control(d):
        shutil.rmtree(d/'prover-controls')
    check('missing_prover_controls','proof',lost_control)
    for name,mutation,expected in (
        ('exact_frozen_input_inventory',None,True),
        ('unregistered_formal_input',lambda p:(p/'models/Injected.tla').write_text('---- MODULE Injected ----\nX == TRUE\n====\n'),False),
        ('missing_frozen_formal_input',lambda p:(p/'models/TRaftCore.tla').unlink(),False),
    ):
        with tempfile.TemporaryDirectory(prefix='traft-source-control-') as tmp:
            clone=Path(tmp)/'package'
            shutil.copytree(PACKAGE,clone,ignore=shutil.ignore_patterns('__pycache__'))
            if mutation:mutation(clone)
            try:validate_sources(clone);accepted=True;reason=None
            except (ValueError,OSError) as error:accepted=False;reason=str(error)
            passed=accepted==expected
            cases.append({'case':name,'passed':passed,'expected_acceptance':expected,'observed_acceptance':accepted,'reason':reason})
            if not passed:raise AssertionError(name)
    write(args.output,{'accepted':all(c['passed'] for c in cases),'cases':cases})
    print('Acceptance controls passed:',len(cases))


if __name__=='__main__':main()
