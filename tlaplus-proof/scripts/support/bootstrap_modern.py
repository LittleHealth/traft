#!/usr/bin/env python3
"""Install the pinned official TLAPM and its isolated, signed compatibility runtime.

No system packages or libraries are changed. A completed installation is not a
proof result: run_all.py must check positive/negative controls and every proof.
"""
import argparse
import datetime
import hashlib
import json
import lzma
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
ASSET_URL = 'https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz'
ASSET_SHA = '1fcb037a300929d4bed8539511f65073fc19762abd9cea5260fe91d0f2d617df'
RELEASE_SHA = 'a4dfe9c58d77db89e8b45240d1cc14a3e6dd9159bc29395aebfe6e893594dccb'
PACKAGES_SHA = 'b799a4a5c316a2191dfb4b0f420652391a3bfd29350e43252887d9681c98c7f0'
LIBC_SHA = 'd821b41fc59cb4978ecd53bc83e5c964ac15d305c8d2ac4c8a35aebe55010fb9'
LIBC_NAME = 'libc6_2.39-0ubuntu8.12_amd64.deb'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch(target, url, expected, cached=None):
    if not target.exists():
        temporary = target.with_name(target.name + '.download')
        if cached and cached.is_file():
            shutil.copyfile(cached, temporary)
        else:
            subprocess.run(['curl', '--fail', '--silent', '--show-error', '--location',
                            '--connect-timeout', '10', '--max-time', '180',
                            '--output', str(temporary), url], check=True)
        if digest(temporary) != expected:
            raise ValueError('Downloaded artifact hash mismatch: ' + target.name)
        temporary.replace(target)
    if digest(target) != expected:
        raise ValueError('Artifact hash mismatch: ' + target.name)


def manifest(root):
    return {str(p.relative_to(root)): digest(p)
            for p in sorted(root.rglob('*')) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--asset-cache', type=Path,
                        help='Optional copy of the exact official release tarball.')
    parser.add_argument('--libc-cache', type=Path,
                        help='Optional copy of the exact signed libc6 package.')
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('Run this installer on dq-179, Linux x86_64.')
    root = HERE / 'tools/modern'
    if root.exists():
        parser.error('Use a fresh deployment; existing tool evidence is not overwritten.')
    root.mkdir(parents=True)
    archive = root / 'tlapm.tar.gz'
    fetch(archive, ASSET_URL, ASSET_SHA, args.asset_cache)
    runtime = root / 'runtime'
    runtime.mkdir()
    for name, expected in [('InRelease', RELEASE_SHA), ('Packages.xz', PACKAGES_SHA)]:
        source = HERE / 'tool-runtime' / name
        if digest(source) != expected:
            raise ValueError('Pinned runtime metadata hash mismatch: ' + name)
        shutil.copyfile(source, runtime / name)
    keyring = Path('/usr/share/keyrings/ubuntu-archive-keyring.gpg')
    verified = subprocess.run(['gpgv', '--keyring', str(keyring), str(runtime / 'InRelease')],
                              capture_output=True, text=True, timeout=15)
    (runtime / 'signature-check.log').write_text(verified.stdout + verified.stderr)
    if verified.returncode:
        raise ValueError('Pinned Ubuntu metadata signature did not verify')
    match = re.search(r'^ ([a-f0-9]{64})\s+(\d+)\s+main/binary-amd64/Packages.xz$',
                      (runtime / 'InRelease').read_text(), re.M)
    if not match or match.group(1) != PACKAGES_SHA or int(match.group(2)) != (runtime / 'Packages.xz').stat().st_size:
        raise ValueError('Signed package index mismatch')
    paragraphs = lzma.decompress((runtime / 'Packages.xz').read_bytes()).decode().split('\n\n')
    selected = [p for p in paragraphs if p.startswith('Package: libc6\n')
                and '\nArchitecture: amd64\n' in p]
    if len(selected) != 1:
        raise ValueError('Ambiguous signed libc package')
    fields = dict(line.split(': ', 1) for line in selected[0].splitlines()
                  if ': ' in line and not line.startswith(' '))
    if fields['SHA256'] != LIBC_SHA or Path(fields['Filename']).name != LIBC_NAME:
        raise ValueError('Signed libc package differs from the pinned runtime')
    package = runtime / LIBC_NAME
    fetch(package, 'https://archive.ubuntu.com/ubuntu/' + fields['Filename'], LIBC_SHA, args.libc_cache)
    if package.stat().st_size != int(fields['Size']):
        raise ValueError('Signed libc package size mismatch')
    subprocess.run(['dpkg-deb', '--extract', str(package), str(runtime / 'extracted')],
                   check=True, timeout=30)
    with tarfile.open(archive) as tf:
        for member in tf.getmembers():
            path = Path(member.name)
            if path.is_absolute() or '..' in path.parts or path.parts[0] != 'tlapm':
                raise ValueError('Unsafe official archive path')
            if not (member.isfile() or member.isdir() or member.issym() or member.islnk()):
                raise ValueError('Unsupported archive member')
            if member.issym() or member.islnk():
                link = Path(member.linkname)
                resolved = (root / path.parent / link).resolve() if member.issym() else (root / link).resolve()
                if link.is_absolute() or os.path.commonpath([root.resolve(), resolved]) != str(root.resolve()):
                    raise ValueError('External archive link')
        tf.extractall(root)
    tool = root / 'tlapm'
    original = manifest(tool)
    (root / 'official-files.json').write_text(json.dumps(original, indent=2) + '\n')
    libraries = runtime / 'extracted/usr/lib/x86_64-linux-gnu'
    loader = tool / 'bin/ld-linux-x86-64.so.2'
    shutil.copyfile(libraries / loader.name, loader)
    loader.chmod(0o755)
    # The loader's placement preserves OCaml's relative library/backend lookup.
    # --nofp is mandatory; the executable name reported by OCaml is the loader.
    shim = ('#!/usr/bin/python3\nfrom pathlib import Path\nimport os\nimport sys\n'
            'elf = Path(__file__).with_name(Path(__file__).name + ".official")\n'
            'for key in ["TLAPM_CACHE", "TLAPM_NORMALIZE", "TLAPM_FLATTEN", "LD_LIBRARY_PATH", "LD_PRELOAD"]:\n'
            '    os.environ.pop(key, None)\n'
            'loader = ' + repr(str(loader)) + '\n'
            'libraries = ' + repr(str(libraries)) + '\n'
            'os.execv(loader, [loader, "--library-path", libraries, "--argv0", str(elf), str(elf)] + sys.argv[1:])\n')
    wrapped = []
    for name in ['bin/tlapm', 'lib/tlapm/backends/bin/zenon',
                 'lib/tlapm/backends/bin/ls4', 'lib/tlapm/backends/bin/ptl_to_trp']:
        path = tool / name
        if path.read_bytes()[:4] != b'\x7fELF':
            raise ValueError('Expected official ELF: ' + name)
        path.rename(path.with_name(path.name + '.official'))
        path.write_text(shim)
        path.chmod(0o755)
        wrapped.append(name)
    poly = tool / 'lib/tlapm/backends/Isabelle-install/poly/poly'
    poly.rename(poly.with_name('poly.official'))
    poly.write_text(
        '#!/usr/bin/python3\nfrom pathlib import Path\nimport os\nimport sys\nimport resource\n'
        'if os.environ.get("TRAFT_PROOF_RUNTIME_PROFILE") not in ("polyml-reserved", "tlapm-reserved", "tlapm-4g-resident", "tlapm-8g-resident"):\n'
        '    raise SystemExit("PolyML requires the monitored proof runtime profile")\n'
        'soft, hard = resource.getrlimit(resource.RLIMIT_AS)\n'
        'wanted = 32 * 1024**3\n'
        'if hard < wanted:\n'
        '    raise SystemExit("PolyML virtual-reservation limit unavailable")\n'
        'resource.setrlimit(resource.RLIMIT_AS, (wanted, hard))\n'
        'elf = Path(__file__).with_name("poly.official")\n'
        'os.execv(str(elf), [str(elf), "--minheap", "32", "--maxheap", "512", '
        '"--stackspace", "64", "--gcthreads", "1"] + sys.argv[1:])\n')
    poly.chmod(0o755)
    wrapped.append(str(poly.relative_to(tool)))
    for name in wrapped:
        if digest(tool / (name + '.official')) != original[name]:
            raise ValueError('Official ELF bytes changed')
    versions = {}
    for name, path, flag in [('tlapm', tool / 'bin/tlapm', '--version'),
                            ('z3', tool / 'lib/tlapm/backends/bin/z3', '--version'),
                            ('zenon', tool / 'lib/tlapm/backends/bin/zenon', '-v')]:
        result = subprocess.run([str(path), flag], capture_output=True, text=True, timeout=15)
        if result.returncode:
            raise ValueError('Version probe failed: ' + name)
        versions[name] = (result.stdout + result.stderr).strip()
    if versions['tlapm'] != 'bf665f4':
        raise ValueError('Unexpected official TLAPM version')
    record = {'schema': 2, 'url': ASSET_URL, 'sha256': ASSET_SHA,
              'version': versions['tlapm'], 'versions': versions,
              'source_commit': 'bf665f4d162c1ae5010ca878578cd50a810ec205',
              'host': platform.node(), 'architecture': platform.machine(),
              'executable': str(tool / 'bin/tlapm'), 'tool_root': str(tool),
              'stdlib': str(tool / 'lib/tlapm/stdlib'),
              'runtime_root': str(runtime / 'extracted'),
              'runtime_profile': 'tlapm-8g-resident', 'healthcheck_required': True,
              'tlapm_sha256': digest(tool / 'bin/tlapm'),
              'official_elf_sha256': original['bin/tlapm'],
              'wrapped': wrapped, 'tool_files': manifest(tool),
              'runtime_files': manifest(runtime / 'extracted'),
              'runtime_package': {k: fields[k] for k in ['Package', 'Version', 'Filename', 'Size', 'SHA256']},
              'ubuntu_keyring_sha256': digest(keyring), 'release_signature_returncode': verified.returncode,
              'release_metadata_sha256': RELEASE_SHA, 'package_index_sha256': PACKAGES_SHA,
              'isabelle_identifier': (tool / 'lib/tlapm/backends/Isabelle-install/etc/ISABELLE_IDENTIFIER').read_text().strip(),
              'system_libraries_modified': False, 'package_scripts_executed': False,
              'proof_cache_reused': False, 'full_proof_complete': False,
              'installed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (HERE / 'toolchain.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in ('tool_files', 'runtime_files')}), flush=True)


if __name__ == '__main__':
    main()
