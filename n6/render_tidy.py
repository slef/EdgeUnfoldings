"""Render the preserved proof drafts as self-contained reading pages.

Run after editing these Markdown sources. Pandoc is a local authoring tool;
the generated HTML is tracked, so publishing does not install dependencies.
No mathematical content is inferred or altered by this renderer.
"""
from pathlib import Path
import re
import subprocess
import tempfile


STYLE = '''<style>
:root { color-scheme: light; }
html { background:#f7f6f1; color:#20252b; }
body { max-width:58rem; margin:3rem auto; padding:0 1.5rem 4rem;
       font:18px/1.65 Georgia,"Times New Roman",serif; }
h1,h2,h3,nav { font-family:system-ui,sans-serif; line-height:1.3; }
h1 { font-size:2rem; } h2 { margin-top:2.6rem; font-size:1.45rem; }
h3 { margin-top:1.9rem; font-size:1.15rem; }
a { color:#17638a; text-underline-offset:.15em; }
pre { background:#fff; border:1px solid #dcdedc; border-radius:6px;
      padding:1rem; overflow-x:auto; font-size:.88rem; line-height:1.55; }
code { font-family:ui-monospace,"SFMono-Regular",Consolas,monospace; }
blockquote { margin:1.5rem 0; padding:.1rem 1.2rem; border-left:4px solid #78a9ba;
             background:#edf4f5; }
table { width:100%; border-collapse:collapse; font-size:.94rem; }
th,td { text-align:left; vertical-align:top; padding:.6rem; border-bottom:1px solid #ddd; }
th { background:#edf0ee; font-family:system-ui,sans-serif; }
#TOC { font-size:.95rem; background:#fff; border:1px solid #dcdedc;
       border-radius:6px; padding:1rem 1.5rem; }
#TOC ul { padding-left:1.3rem; }
.reading-links { font: .9rem/1.5 system-ui,sans-serif; padding-bottom:1rem;
                 border-bottom:1px solid #dcdedc; }
@media(max-width:600px) { body { margin:1.5rem auto; padding:0 1rem 2rem; font-size:17px; }
                         h1 { font-size:1.6rem; } table { font-size:.8rem; } }
@media print { html { background:white; } body { max-width:none; margin:0; font-size:10pt; }
              pre,blockquote,table { break-inside:avoid; } h2,h3 { break-after:avoid; }
              a { color:inherit; } .reading-links { display:none; } }
</style>'''


def render():
    root = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='tidy-proof-') as directory:
        header = Path(directory)/'header.html'
        header.write_text(STYLE)
        before = Path(directory)/'before.html'
        before.write_text('<nav class="reading-links" aria-label="Proof documents">'
                          '<a href="TIDY_PROOF.html">Main proof</a> · '
                          '<a href="TIDY_CORE.html">Geometric details</a> · '
                          '<a href="PROOF_REVIEW_20260912.md">Review record</a>'
                          '</nav>')
        pages = [('TIDY_PROOF', 'A streamlined proof through six vertices'),
                 ('TIDY_CORE', 'The shared geometric core'),
                 ('PRISM_CAP_RULE', 'Five prism candidates by cap curvature'),
                 ('CASE_A_CAP_BUDGET', 'The optional three-face cap budget'),
                 ('SHARPEST_COFACIAL_FAILURE', 'Why the sharpest cofacial source alone is insufficient'),
                 ('OCTA_FACE_CAP_RULE', 'A shorter curvature-only octahedron proof'),
                 ('TIDY_PROOF_FIRST_REVIEW', 'Earlier preserved seven-candidate draft')]
        for stem, title in pages:
            source = (root/(stem+'.md')).read_text()
            heading, body = source.split('\n', 1)
            if not heading.startswith('# '):
                raise ValueError('Expected one document title before the proof')
            result = subprocess.run([
                'pandoc', '--from=markdown', '--to=html5',
                '--standalone', '--toc', '--toc-depth=2', '--wrap=none',
                '--metadata', 'pagetitle='+title, '--metadata', 'lang=en',
                '--metadata', 'title='+heading[2:],
                '--include-in-header', str(header), '--include-before-body', str(before),
            ], input=body, check=True, capture_output=True, text=True)
            # The reading pages need no remote script. Pandoc's legacy
            # default template includes an IE8-only HTML5 shim.
            html = re.sub(r'\s*<!--\[if lt IE 9\]>.*?<!\[endif\]-->',
                          '', result.stdout, flags=re.S)
            for target, _ in pages:
                html = html.replace('href="'+target+'.md"', 'href="'+target+'.html"')
            (root/(stem+'.html')).write_text(html)
            print(stem+'.html')


if __name__ == '__main__':
    render()
