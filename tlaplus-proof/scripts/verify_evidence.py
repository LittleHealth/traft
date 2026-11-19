"""Verify complete proof evidence and the declared, completed TLC checks."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile
from functools import lru_cache
from common import PACKAGE, published_checks, read, registry, safe_relative, sha, validate_sources, write
from acceptance import PROOF_SYNTAX_ROOTS, proof_status_coverage
from tla_audit import code_only, holes, local_closure, proof_dependencies, union_parentheses_violations
from toolchain_audit import proof_runtime_matches


@lru_cache(maxsize=None)
def source_proof_errors(path):
    text=path.read_text()
    return bool(holes(text) or union_parentheses_violations(text))


@lru_cache(maxsize=None)
def source_dependencies(models,module):
    return local_closure(models,module),proof_dependencies(models,module)


def formal_result(result, module, expected, source_hashes, tool_audit, models):
    if result.get('module') != module or not proof_status_coverage(result, expected):
        raise ValueError('Proof obligation coverage/status mismatch: ' + module)
    closure,dependencies = source_dependencies(models, module)
    if any('models/'+m+'.tla' not in source_hashes or m+'.tla' not in result.get('input_sha256',{})
           or result['input_sha256'][m+'.tla'] != source_hashes['models/'+m+'.tla'] for m in closure):
        raise ValueError('Proof dependency source mismatch: ' + module)
    if any(source_proof_errors(models/(m+'.tla')) for m in closure):
        raise ValueError('Proof hole or ambiguous UNION: ' + module)
    if not result.get('union_syntax_audited') or not result.get('backend_time_limits_within_60_seconds'):
        raise ValueError('Missing syntax/backend-limit audit: ' + module)
    if not proof_runtime_matches(result, tool_audit):
        raise ValueError('Proof runtime/tool identity mismatch: ' + module)
    return dependencies


def tlc_result(result, check):
    """Check scenario identity and frozen inputs, not just its outcome label."""
    if result.get('outcome')!=check['expected_outcome'] or result.get('failed_invariant')!=check['expected_invariant']:
        raise ValueError('Unexpected TLC result: '+check['id'])
    if result.get('mode')!=check['mode'] or Path(result['model']).name!=Path(check['model']).name:
        raise ValueError('Wrong TLC mode/model: '+check['id'])
    if (Path(result['config']).name if result.get('config') else None)!=(Path(check['config']).name if check['config'] else None):
        raise ValueError('Wrong TLC configuration: '+check['id'])
    lock=read(PACKAGE/'toolchain/toolchain-lock.json')
    if result.get('toolkit',{}).get('sha256')!=lock['tla2tools']['sha256']:
        raise ValueError('TLC tool checksum mismatch: '+check['id'])
    for key in ('workers','heap','timeout_seconds','max_disk_gb'):
        if result.get('resources',{}).get(key)!=check['resources'][key]:
            raise ValueError('TLC resource profile mismatch: '+check['id'])
    source=PACKAGE/Path(check['model']).parent
    inputs=result.get('inputs',{})
    for p in source.glob('*.tla'):
        wanted=PACKAGE/check['overrides'][p.name] if p.name in check['overrides'] else p
        if inputs.get(p.name,{}).get('sha256')!=sha(wanted):
            raise ValueError('TLC source mismatch: '+check['id']+'/'+p.name)
    if check['config'] and inputs.get(Path(check['config']).name,{}).get('sha256')!=sha(PACKAGE/check['config']):
        raise ValueError('TLC configuration hash mismatch: '+check['id'])


def controls_result(output):
    cases=read(output/'parser-selftest.log')
    if not isinstance(cases,list) or not cases or not all(c.get('passed') for c in cases):
        raise ValueError('Acceptance-parser controls did not pass')
    records={}
    for path in (output/'prover-controls').glob('*/result.json'):
        raw=read(path)
        if raw['module'] in records:raise ValueError('Duplicate prover control')
        records[raw['module']]=raw
    if set(records)!={'ProofToolPositive','ProofToolNegative','ProofToolSMTNegative'}:
        raise ValueError('Missing prover control')
    if not proof_status_coverage(records['ProofToolPositive'],4):
        raise ValueError('Positive prover control did not pass')
    for name,backend in [('ProofToolNegative','isabelle'),('ProofToolSMTNegative','smt')]:
        raw=records[name]
        if raw['outcome']!='unproved' or not any(s.get('status')=='failed' and s.get('reason')=='false' and s.get('prover')==backend for s in raw['unproved'].values()):
            raise ValueError('Negative prover control did not reject FALSE')


def run_input_files(path, raw):
    recorded=raw.get('input_sha256') or {n:d['sha256'] for n,d in raw.get('inputs',{}).items()}
    if not recorded:raise ValueError('Missing run input manifest')
    for name,digest in recorded.items():
        file=path.parent/'input'/safe_relative(name)
        if not file.is_file() or sha(file)!=digest:
            raise ValueError('Run input snapshot differs: '+name)


def verify_archives(directory):
    validate_sources()
    assets = read(PACKAGE/'evidence/release-assets.json')['assets']
    archived = {}; all_hashes={}
    file_count=0
    for asset in assets:
        path=directory/safe_relative(asset['name'])
        if not path.is_file() or sha(path)!=asset['sha256']:
            raise ValueError('Release asset hash mismatch: '+asset['name'])
        if not path.name.endswith('.tar.gz'):
            continue
        got={}; manifest=None
        with tarfile.open(path,'r|gz') as archive:
            for item in archive:
                safe_relative(item.name)
                if not item.isfile() or item.name in got or item.name == 'evidence-manifest.json' and manifest is not None:
                    raise ValueError('Unsafe or duplicate release member')
                data=archive.extractfile(item).read()
                if item.name=='evidence-manifest.json':
                    manifest=json.loads(data)
                    continue
                got[item.name]=hashlib.sha256(data).hexdigest()
                if item.name.endswith('/result.json') or Path(item.name).name in ('toolchain-before.json','toolchain-after.json','toolchain.json','source-manifest.json','acceptance.json'):
                    if item.name in archived:
                        raise ValueError('Evidence appears in multiple attachments: '+item.name)
                    archived[item.name]=json.loads(data)
        if not manifest or manifest['files']!=got:
            raise ValueError('Archive member inventory mismatch: '+path.name)
        all_hashes.update(got)
        file_count+=len(got)
    summary=read(PACKAGE/'results/proof-summary.json')
    base='frozen-results/'+summary['frozen_run']+'/'
    if all_hashes.get('source-manifest.json')!=summary['source_manifest_sha256'] or all_hashes.get(base+'acceptance.json')!=summary['original_acceptance_sha256']:
        raise ValueError('Original frozen manifest/acceptance identity mismatch')
    for mapped in read(PACKAGE/'manifests/source-path-map.json')['files']:
        if archived['source-manifest.json']['files'].get(mapped['frozen_path'])!=mapped['sha256']:
            raise ValueError('Public path mapping differs from frozen manifest')
    audit=archived[base+'toolchain-before.json']
    after=archived[base+'toolchain-after.json']
    if not audit.get('accepted') or not after.get('accepted') or not after.get('same_record_as_start') or audit['toolchain_record_sha256']!=after['toolchain_record_sha256'] or audit['toolchain_record_sha256']!=all_hashes[base+'toolchain.json']:
        raise ValueError('Frozen toolchain audit does not close')
    reg=registry(); source_hashes=read(PACKAGE/'manifests/source-files.json')['files']
    rows=read(PACKAGE/'results/proof-modules.json')['modules']
    if {r['module'] for r in rows}!=set(reg['checked_modules']) or len(rows)!=len(reg['checked_modules']):
        raise ValueError('Module registry/result coverage mismatch')
    for row in rows:
        module=row['module']; result=archived[row['result']]
        if all_hashes[row['result']]!=row['result_sha256']:
            raise ValueError('Original proof result hash differs: '+module)
        deps=formal_result(result,module,reg['checked_modules'][module],source_hashes,audit,PACKAGE/'models')
        if set(deps)-set(reg['checked_modules']):
            raise ValueError('Unregistered dependency: '+module)
    for t in reg['required_targets']:
        source=code_only((PACKAGE/'models'/(t['module']+'.tla')).read_text())
        if t['module'] not in reg['checked_modules'] or not re.search(r'\bTHEOREM\s+'+re.escape(t['theorem'])+r'\b',source):
            raise ValueError('Missing registered target: '+str(t))
    for check in published_checks():
        result=archived[check['evidence_result']]
        if all_hashes[check['evidence_result']]!=check['result_sha256']:
            raise ValueError('Original TLC result hash differs: '+check['id'])
        tlc_result(result,check)
    validate_sources()
    return {'accepted':True,'scope':'published archives and complete registered TLAPS chain',
            'archive_files_checked':file_count,'modules':len(rows),
            'obligations':sum(reg['checked_modules'].values()),'targets':len(reg['required_targets']),
            'published_checks':len(published_checks())}


def verify_run(output):
    """Recheck a new run; a selected proof run never becomes a full-chain result."""
    summary=read(output/'run-summary.json')
    if summary['kind']=='tlc':
        validate_sources()
        checks={r['id']:r for r in published_checks()}
        if not summary.get('selected_checks') or len(set(summary['selected_checks']))!=len(summary['selected_checks']):
            raise ValueError('Invalid TLC run selection')
        if [r['id'] for r in summary['checks']]!=summary['selected_checks']:
            raise ValueError('Missing or repeated TLC results')
        for r in summary['checks']:
            raw=read(output/safe_relative(r['result']))
            expected=checks[r['id']]
            if sha(output/r['result'])!=r['sha256']:
                raise ValueError('TLC result does not match expected check: '+r['id'])
            tlc_result(raw,expected)
            run_input_files(output/r['result'],raw)
        return {'accepted':True,'kind':'tlc','checked':len(summary['checks'])}
    if summary['kind']!='proof':
        raise ValueError('Unsupported run kind')
    validate_sources()
    reg=registry(); audit=read(output/'toolchain-before.json'); after=read(output/'toolchain-after.json')
    if not after['accepted'] or audit['toolchain_record_sha256']!=after['toolchain_record_sha256'] or audit['toolchain_record_sha256']!=sha(output/'toolchain.json'):
        raise ValueError('Toolchain changed during proof run')
    source_hashes=read(PACKAGE/'manifests/source-files.json')['files']
    rows=summary['modules']; names=[r['module'] for r in rows]
    if len(names)!=len(set(names)) or names!=summary['requested_modules']:
        raise ValueError('Missing or repeated proof results')
    controls_result(output)
    preflights=list(PROOF_SYNTAX_ROOTS) if summary['requested_scope']=='full' else names
    for name in preflights:
        found=list((output/'checks'/('syntax-'+name)).glob('*/result.json'))
        if len(found)!=1:raise ValueError('Missing or repeated SANY preflight: '+name)
        tlc_result(read(found[0]),{'id':'syntax-'+name,'model':'models/'+name+'.tla',
             'config':None,'mode':'sany','overrides':{},'expected_outcome':'syntax_ok',
             'expected_invariant':None,'resources':{'workers':1,'heap':'2g','timeout_seconds':60,'max_disk_gb':0.1}})
    closure=set()
    for row in rows:
        path=output/safe_relative(row['result'])
        if sha(path)!=row['sha256']:
            raise ValueError('Proof result hash mismatch')
        raw=read(path)
        run_input_files(path,raw)
        closure.update(formal_result(raw,row['module'],reg['checked_modules'][row['module']],source_hashes,audit,PACKAGE/'models'))
    full=set(names)==set(reg['checked_modules']) and not closure-set(names)
    if summary['requested_scope']=='full' and not full:
        raise ValueError('Incomplete full proof dependency coverage')
    return {'accepted':True,'kind':'proof','checked_modules':len(names),
            'full_chain':full,'dependency_modules_not_run':sorted(closure-set(names))}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--assets',type=Path);g.add_argument('--run',type=Path)
    p.add_argument('--report',type=Path)
    a=p.parse_args()
    result=verify_archives(a.assets) if a.assets else verify_run(a.run)
    if a.report:write(a.report,result)
    print(json.dumps(result))
