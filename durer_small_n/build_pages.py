"""Package the generated overview and its public evidence for GitHub Pages."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess


def assemble(destination):
    root = Path(__file__).resolve().parent.parent
    notes = root / 'durer_small_n/notes'
    destination.mkdir(parents=True, exist_ok=True)
    # The overview moves two levels up; update literal and JS-generated links.
    html = (notes / 'status.html').read_text().replace('../../n6/', 'n6/')
    # The user-supplied thesis scan is local, not part of the public repository.
    html = re.sub(
        r'<a href="\.\./\.\./DiBiase%20[^\"]+">(.*?)</a>',
        r'\1 (thesis scan available in the local project)', html,
    )
    (destination / 'index.html').write_text(html)
    for name in ('lemmaF.pdf', 'dibiase_summary.md'):
        shutil.copyfile(notes / name, destination / name)
    shutil.copyfile(root / 'HANDOFF.md', destination / 'HANDOFF.md')
    # Include only tracked research files, never local caches or private inputs.
    tracked = subprocess.check_output(
        ['git', 'ls-files', '-z', 'n6'], cwd=root,
    ).decode().split('\0')
    for name in filter(None, tracked):
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / name, target)
    (destination / '.nojekyll').touch()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    assemble(parser.parse_args().destination)
