"""Create separately hashed TLAPS and completed-TLC evidence attachments.

The original evidence archive is read-only. Selected logs/results are copied
byte-for-byte. File selection is explicit; statuses are never rewritten.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import tarfile
from common import PACKAGE, new_directory, published_checks, read, safe_relative, sha, write

ORIGINAL_SHA = '0ce09fcaf81061bfc79945aab3a8c9601e1e5c0cfa1b6ef2943b9d285697caea'
NAMES = ('traft-tlaps-evidence.tar.gz', 'traft-tlc-completed-evidence.tar.gz')


def add(archive, name, data):
    safe_relative(name)
    info = tarfile.TarInfo(name)
    info.size = len(data)
    info.mode = 0o644
    archive.addfile(info, io.BytesIO(data))


def export(source, original_manifest, output):
    if sha(source) != ORIGINAL_SHA:
        raise ValueError('Original frozen evidence archive hash differs')
    expected = read(original_manifest)['files']
    checks = published_checks()
    proof_rows = read(PACKAGE / 'results/proof-modules.json')['modules']
    run = read(PACKAGE / 'results/proof-summary.json')['frozen_run']
    base = 'frozen-results/' + run + '/'
    tlc_prefixes = tuple(str(Path(c['evidence_result']).parent) + '/' for c in checks)
    proof_prefixes = tuple(base + p for p in ('proofs/', 'group-selftest/', 'syntax/', 'source-semantics/tlaps/'))
    proof_files = {'source-manifest.json', 'proof-obligations.json', 'toolchain.json'}
    proof_files |= {base + n for n in (
        'acceptance.json', 'toolchain.json', 'toolchain-before.json', 'toolchain-after.json',
        'environment.json', 'core-source-delta.json', 'client-source-delta.json',
        'parser_selftest.log', 'prover_selftest.log', 'prover_group_selftest.log', 'proofs.log')}
    required_results = {r['result']: r['result_sha256'] for r in proof_rows}
    required_results.update({r['evidence_result']:r['result_sha256'] for r in checks})
    out = new_directory(output)
    hashes = [{}, {}]
    seen = set()
    found = set()
    originals_verified = False
    archives = [tarfile.open(out / n, 'w:gz', compresslevel=6) for n in NAMES]
    try:
        with tarfile.open(source, 'r|gz') as incoming:
            for item in incoming:
                safe_relative(item.name)
                if item.name in seen:
                    raise ValueError('Duplicate original member: ' + item.name)
                seen.add(item.name)
                if item.isdir():
                    continue
                if not item.isfile():
                    raise ValueError('Non-file original archive member')
                if item.name == 'artifact-manifest.json':
                    originals_verified = hashlib.sha256(incoming.extractfile(item).read()).hexdigest() == sha(original_manifest)
                    continue
                slot = 1 if item.name.startswith(tlc_prefixes) else 0 if item.name.startswith(proof_prefixes) or item.name in proof_files else None
                if slot is None:
                    continue
                data = incoming.extractfile(item).read()
                digest = hashlib.sha256(data).hexdigest()
                if expected.get(item.name) != digest:
                    raise ValueError('Original member hash differs: ' + item.name)
                if item.name in required_results:
                    if digest != required_results[item.name]:
                        raise ValueError('Published result selection differs: ' + item.name)
                    found.add(item.name)
                add(archives[slot], item.name, data)
                hashes[slot][item.name] = digest
        if not originals_verified or found != set(required_results):
            raise ValueError('Original manifest or required evidence coverage differs')
        for slot, archive in enumerate(archives):
            report = {'schema':1,'scope':'full_registered_tlaps_chain' if slot==0 else 'published_completed_checks',
                      'original_archive_sha256':ORIGINAL_SHA,'files':hashes[slot]}
            add(archive, 'evidence-manifest.json', (json.dumps(report, indent=2)+'\n').encode())
    finally:
        for archive in archives:
            archive.close()
    assets = [{'name':n,'bytes':(out/n).stat().st_size,'sha256':sha(out/n),
               'files':len(hashes[i]),'scope':'full_registered_tlaps_chain' if i==0 else 'published_completed_checks'}
              for i,n in enumerate(NAMES)]
    write(out/'evidence-manifest.json',{'schema':1,'original_archive_sha256':ORIGINAL_SHA,
          'archives':{n:{'files':hashes[i]} for i,n in enumerate(NAMES)}})
    assets.append({'name':'evidence-manifest.json','bytes':(out/'evidence-manifest.json').stat().st_size,
                   'sha256':sha(out/'evidence-manifest.json'),'scope':'archive_member_hashes'})
    (out/'SHA256SUMS').write_text(''.join(a['sha256']+'  '+a['name']+'\n' for a in assets))
    write(out/'release-assets.json',{'schema':1,'tag':'traft-proof-v1','publication_status':'prepared',
          'source_run':run,'assets':assets})
    print(json.dumps({'output':str(out),'assets':assets}), flush=True)


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--artifact-manifest',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    export(a.archive,a.artifact_manifest,a.output)
