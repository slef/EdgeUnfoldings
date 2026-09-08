"""Build notes/status.html from the template and status_figs.json."""
import json, datetime
figs = json.load(open('notes/status_figs.json'))
t = open('notes/status_template.html').read()
t = t.replace('__FIGS_JSON__', json.dumps(figs)).replace('__UPDATED__', datetime.date.today().isoformat())
open('notes/status.html', 'w').write(t)
print(len(t), "bytes")
