"""Shared file and integrity utilities for the public artifact interfaces."""
import hashlib
import json
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parents[1]
SUPPORT = PACKAGE / 'scripts/support'
sys.path.insert(0, str(SUPPORT))


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def safe_relative(name):
    p = Path(name)
    if not name or p.is_absolute() or '..' in p.parts or '\\' in name:
        raise ValueError('Unsafe relative artifact path: ' + name)
    return p


def validate_sources(package=PACKAGE):
    manifest = read(package / 'manifests/source-files.json')['files']
    declared={n for n in manifest if Path(n).suffix in ('.tla','.cfg')}
    actual={str(p.relative_to(package)) for folder in ('models','configs','baseline','parser-probe')
            for p in (package/folder).rglob('*') if p.is_file() and p.suffix in ('.tla','.cfg')}
    if actual!=declared:
        raise ValueError('Formal input inventory differs; missing='+str(sorted(declared-actual))+
                         ', extra='+str(sorted(actual-declared)))
    for name, expected in manifest.items():
        target = package / safe_relative(name)
        if not target.is_file() or target.is_symlink() or sha(target) != expected:
            raise ValueError('Frozen source mismatch: ' + name)
    mapping = read(package / 'manifests/source-path-map.json')['files']
    if {r['public_path']: r['sha256'] for r in mapping} != manifest:
        raise ValueError('Source mapping and file inventory differ')
    return {'accepted': True, 'mapped_files': len(manifest)}


def registry(package=PACKAGE):
    return read(package / 'manifests/proof-obligations.json')


def published_checks(package=PACKAGE):
    rows = read(package / 'manifests/published-checks.json')['checks']
    if len({r['id'] for r in rows}) != len(rows):
        raise ValueError('Duplicate published check ID')
    return rows


def new_directory(path):
    path = Path(path).resolve()
    path.mkdir(parents=True, exist_ok=False)
    return path
