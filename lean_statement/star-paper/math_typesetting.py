"""Typeset explicitly delimited TeX as static HTML plus accessible MathML."""
from pathlib import Path
import html
import json
import re
import subprocess

INLINE_MATH = re.compile(r"\\\((.*?)\\\)")

class MathTypesetter:
    def __init__(self, texts):
        for text in texts:
            prose = INLINE_MATH.sub('', text)
            if r'\(' in prose or r'\)' in prose:
                raise ValueError('Unbalanced inline math delimiters: ' + text)
        self.formulas = sorted({m[1] for text in texts for m in INLINE_MATH.finditer(text)})
        script = Path(__file__).with_name('render_math.cjs')
        self.rendered = json.loads(subprocess.check_output(
            ['node', str(script)], input=json.dumps(self.formulas), text=True))

    def render(self, text, prose=html.escape):
        pieces = []
        cursor = 0
        for match in INLINE_MATH.finditer(text):
            pieces.append(prose(text[cursor:match.start()]))
            tex = match[1]
            pieces.append('<span class="math-formula" data-tex="' +
                          html.escape(tex, quote=True) + '">' + self.rendered[tex] + '</span>')
            cursor = match.end()
        pieces.append(prose(text[cursor:]))
        return ''.join(pieces)
