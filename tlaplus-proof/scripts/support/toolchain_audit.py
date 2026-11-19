"""Hash the installed proof tool, standard library, backends and private libc."""
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_toolchain(record_path):
    record = json.loads(record_path.read_text())
    changed = []
    if record.get('schema') == 2:
        for root_name, files_name in [('tool_root', 'tool_files'), ('runtime_root', 'runtime_files')]:
            root = Path(record[root_name])
            for name, expected in record[files_name].items():
                path = Path(name)
                if path.is_absolute() or '..' in path.parts:
                    raise ValueError('Unsafe tool manifest path')
                target = root / path
                if not target.is_file() or digest(target) != expected:
                    changed.append(str(target))
        recorded = record['tool_files'].get('bin/tlapm.official')
        if recorded != record.get('official_elf_sha256'):
            changed.append('official TLAPM ELF identity')
        count = len(record['tool_files']) + len(record['runtime_files'])
    else:
        # Preserve reproducibility of the original pinned TLAPS 1.5 package.
        executable = Path(record['executable'])
        library = executable.parent.parent / 'lib/tlaps'
        files = {executable: record['tlapm_sha256']}
        files.update({library / name: sha for name, sha in record['standard_library_sha256'].items()})
        files.update({library / 'bin' / name: record[name + '_sha256'] for name in ('z3', 'zenon', 'ls4')})
        changed = [str(p) for p, sha in files.items() if not p.is_file() or digest(p) != sha]
        count = len(files)
    return {'accepted': not changed, 'changed': changed, 'files_checked': count,
            'toolchain_record_sha256': digest(record_path),
            'executable_sha256': digest(Path(record['executable'])),
            'runtime_profile': record.get('runtime_profile', 'standard')}


def proof_runtime_matches(result, audit):
    resources = result.get('resources', {})
    profile = audit.get('runtime_profile')
    expected_address = {'standard': 2, 'polyml-reserved': 2, 'tlapm-reserved': 4,
                        'tlapm-4g-resident': 8, 'tlapm-8g-resident': 16}.get(profile)
    expected_resident = {'tlapm-4g-resident': 4, 'tlapm-8g-resident': 8}.get(profile, 2)
    valid = (expected_address is not None
             and audit.get('accepted') and result.get('tlapm_sha256') == audit.get('executable_sha256')
             and resources.get('runtime_profile') == profile
             and resources.get('threads') == 1 and resources.get('cpu_affinity_max', 3) <= 2
             and resources.get('per_process_address_space_gib') == expected_address
             and not resources.get('diagnostic_only')
             and resources.get('ocaml_runtime_parameters') == 'defaults'
             and result.get('proof_cache_reused') is False)
    if profile != 'standard':
        peak = resources.get('peak_group_resident_bytes_sampled')
        valid = (valid and resources.get('polyml_virtual_address_space_gib') == 32
                 and resources.get('polyml_heap_mib') == 512
                 and resources.get('polyml_gc_threads') == 1
                 and resources.get('group_resident_cap_gib') == expected_resident
                 and isinstance(peak, int) and 0 < peak <= expected_resident * 1024**3)
    return bool(valid)
