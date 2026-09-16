"""Compile locally against an existing, matching Mathlib project without changing it.

Usage: python3 check.py --dependencies /path/to/existing/mathlib/project
Optional positional arguments restrict compilation to named Lean files.
The normal portable build remains `lake exe cache get` followed by `lake build`.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependencies', type=Path, required=True)
    parser.add_argument('--incremental', action='store_true',
                        help='Reuse local outputs newer than their source and local imports.')
    parser.add_argument('files', nargs='*')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    toolchain = (root / 'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')
    compiler = Path.home() / '.elan/toolchains' / toolchain / 'bin/lean'
    packages = args.dependencies.resolve() / '.lake/packages'
    libraries = sorted(packages.glob('*/.lake/build/lib/lean'))
    if not compiler.is_file() or not (packages / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file():
        parser.error('The matching Lean compiler and compiled Mathlib must already be installed.')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    expected = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    actual = subprocess.check_output(
        ['git', '-C', str(packages / 'mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != expected:
        parser.error(f'Mathlib revision mismatch: expected {expected}, found {actual}.')
    output = root / '.lake/build/lib/lean'
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [output, *libraries]))

    # Compile local imports first; unrelated projects are only read.
    done = set()

    def compile_file(relative):
        path = root / relative
        if path in done:
            return
        imported_outputs = []
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for module in line.removeprefix('import ').split():
                    dependency = Path(module.replace('.', '/') + '.lean')
                    if (root / dependency).is_file():
                        compile_file(dependency)
                        imported_outputs.append(output / dependency.with_suffix('.olean'))
        destination = output / Path(relative).with_suffix('.olean')
        destination.parent.mkdir(parents=True, exist_ok=True)
        if args.incremental and destination.is_file():
            newest_input = max(p.stat().st_mtime_ns for p in [path, *imported_outputs])
            if destination.stat().st_mtime_ns >= newest_input:
                done.add(path)
                return
        print(f'Checking {relative}', flush=True)
        subprocess.run([str(compiler), '-DautoImplicit=false', '-o', str(destination), str(path)],
                       cwd=root, env=env, check=True)
        done.add(path)

    for relative in args.files or ['SixVertexUnfolding.lean', 'Statement.lean', 'Audit.lean']:
        compile_file(relative)
    print(f'Checked {len(done)} Lean files.', flush=True)


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
