#!/usr/bin/env python3
"""Reject shipped library/challenge roots that shadow dependency top-level entries.

Palomar rejects a Challenge root shared with any dependency directory or .lean
root file. Compare names case-insensitively, stripping .lean from root files.
Missing installed dependencies fail closed. --packages-root lets a staged sync
use the source checkout's installed dependencies without copying their caches.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys

CANONICAL_ROOTS = {'Critical2DKPZ', 'Critical2DKPZStatements', 'Critical2DKPZAudit'}
MATHLIB_RESERVED = {'Counterexamples', 'Archive', 'Cache', 'Wanted', 'Mathlib'}


def inspect(root, packages_root=None):
    root = root.resolve()
    names = set(CANONICAL_ROOTS)
    findings = []
    inventories = {}
    try:
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        if not isinstance(manifest, dict):
            raise ValueError('manifest must be an object')
        packages = manifest['packages']
        if not isinstance(packages, list):
            raise ValueError('packages must be a list')
    except (OSError, ValueError, KeyError) as error:
        return names, inventories, [f'lake-manifest.json: {error}']
    installed = packages_root.resolve() if packages_root else root / manifest.get('packagesDir', '.lake/packages')
    lakefile = root / 'lakefile.lean'
    if lakefile.exists():
        for first, second in re.findall(r'^\s*lean_lib\s+(?:«([^»]+)»|([\w.]+))', lakefile.read_text(), re.M):
            names.add((first or second).split('.')[0])
    for path in root.glob('*.lean'):
        if path.name != 'lakefile.lean':
            names.add(path.stem.split('.')[0])
    for directory, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        if 'comparator.json' not in files:
            continue
        path = Path(directory) / 'comparator.json'
        try:
            config = json.loads(path.read_text())
            challenge = config['challenge_module']
            if not isinstance(challenge, str) or not challenge or any(not p for p in challenge.split('.')):
                raise ValueError('challenge_module must be a nonempty module name')
            names.add(challenge.split('.')[0])
        except (OSError, ValueError, KeyError) as error:
            findings.append(f'{path.relative_to(root)}: {error}')
    reserved = {name.casefold(): f'Mathlib reserved root {name}' for name in MATHLIB_RESERVED}
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get('name'), str):
            findings.append('lake-manifest.json: package without a valid name')
            continue
        name = package['name']
        if not name or Path(name).name != name or name in ('.', '..'):
            findings.append(f'lake-manifest.json: invalid package name {name!r}')
            continue
        path = installed / name
        if not path.is_dir():
            findings.append(f'Missing installed dependency: {name} ({path})')
            continue
        entries = set()
        try:
            for entry in path.iterdir():
                if entry.is_dir():
                    entries.add(entry.name)
                elif entry.is_file() and entry.suffix.casefold() == '.lean':
                    entries.add(entry.name[:-5])
        except OSError as error:
            findings.append(f'Cannot inspect dependency {name}: {error}')
            continue
        inventories[name] = sorted(entries, key=str.casefold)
        for entry in entries:
            key = entry.casefold()
            reserved[key] = reserved.get(key, '') + f'; dependency {name} top-level {entry}'
    for name in sorted(names, key=str.casefold):
        if name.casefold() in reserved:
            findings.append(f'Shipped root {name} collides with {reserved[name.casefold()].lstrip("; ")}')
    return names, inventories, findings


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--packages-root', type=Path)
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    names, inventories, findings = inspect(args.root, args.packages_root)
    result = dict(names=sorted(names), packages=inventories, findings=findings)
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print('Shipped roots: ' + ', '.join(sorted(names)))
        for name, entries in inventories.items():
            print(f'Dependency {name}: ' + ', '.join(entries))
        for finding in findings:
            print('FAIL: ' + finding)
        print(f'TOPLEVEL NAMES: {"FAIL" if findings else "PASS"} '
              f'({len(names)} shipped roots; {len(inventories)} dependency packages; {len(findings)} findings)')
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main())
