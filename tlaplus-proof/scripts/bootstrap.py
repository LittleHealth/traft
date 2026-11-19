"""Install the pinned official TLAPM into a new, private output directory."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
from common import PACKAGE, SUPPORT, new_directory, validate_sources


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--asset-cache', type=Path)
    p.add_argument('--libc-cache', type=Path)
    args = p.parse_args()
    validate_sources()
    out = new_directory(args.output)
    shutil.copyfile(SUPPORT / 'bootstrap_modern.py', out / 'bootstrap_modern.py')
    shutil.copytree(PACKAGE / 'toolchain/runtime', out / 'tool-runtime')
    command = [sys.executable, str(out / 'bootstrap_modern.py')]
    for name in ('asset_cache', 'libc_cache'):
        if getattr(args, name):
            command += ['--' + name.replace('_', '-'), str(getattr(args, name).resolve())]
    return subprocess.run(command, check=False).returncode


if __name__ == '__main__':
    raise SystemExit(main())
