"""Prepare a fresh workspace without changing any formal module bytes."""
import argparse
from pathlib import Path
import shutil
from common import PACKAGE, new_directory, sha, validate_sources, write


def prepare(destination, package=PACKAGE):
    validate_sources(package)
    destination = new_directory(destination)
    shutil.copytree(package / 'models', destination / 'models')
    shutil.copytree(package / 'parser-probe', destination / 'parser-probe')
    shutil.copytree(package / 'baseline', destination / 'baseline')
    write(destination / 'workspace-source.json', {
        'package': str(package),
        'files': {str(p.relative_to(destination)): sha(p)
                  for p in sorted(destination.rglob('*.tla'))}})
    return destination


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    print(prepare(args.output))
