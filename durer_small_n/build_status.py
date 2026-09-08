"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
from pathlib import Path
figs = json.load(open('notes/status_figs.json'))
figs['thickness'] = json.load(open('notes/thickness.json'))
for key, filename in [('thesis_df','thesis-DF.svg'),('prism_failure','prism-two-pair.svg')]:
    svg = (Path('../n6/figures') / filename).read_text()
    figs[key] = svg[svg.index('<svg'):].replace('<svg ', '<svg class="net" ', 1)
t = open('notes/status_template.html').read()
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__GLOSS_JS__', open('notes/glossary.js').read()).replace('__WIDGET_JS__', open('notes/widget.js').read()).replace('__UPDATED__', datetime.date.today().isoformat())
open('notes/status.html', 'w').write(t)
print(len(t), "bytes")
