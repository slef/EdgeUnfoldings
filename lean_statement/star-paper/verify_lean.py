from pathlib import Path
import subprocess,re,json,sys
site=Path(__file__).resolve().parent; root=site.parent
deps=sys.argv[1]
# Force this reporting target to run even when its old object file is current.
(site/"CheckExcerpts.lean").touch()
result=subprocess.run([sys.executable,str(root/'check.py'),'--dependencies',deps,'--incremental','star-paper/CheckExcerpts.lean'],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
text=result.stdout
Path('/tmp/star-paper-lean-check.log').write_text(text)
assert result.returncode==0,text
names=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)
manifest=json.loads((site/'source-manifest.json').read_text())
expected=manifest['theorems']
count=manifest['declarations']
assert len(names)==expected,(len(names),expected)
allowed={'propext','Classical.choice','Quot.sound'}
unfinished=set(manifest['unfinished'])
assert unfinished=={'SixVertexUnfolding.every_convex_polyhedron_with_at_most_six_vertices'}
for name,axioms in names:
    actual=set(x.strip() for x in axioms.split(','))
    permitted=allowed | ({'sorryAx'} if name in unfinished else set())
    assert actual<=permitted,(name,axioms)
    assert ('sorryAx' in actual)==(name in unfinished),(name,axioms)
assert set(name for name,_ in names)=={d['qualified'] for d in json.loads((site/'dist/data.js').read_text().removeprefix('window.PAPER_DATA = ').rstrip(';\n'))['declarations'].values() if d['kind']=='theorem'}
assert 'error:' not in text
warnings=[line for line in text.splitlines() if 'warning:' in line]
assert all('Statement.lean:' in line and "declaration uses 'sorry'" in line for line in warnings),warnings
# Strip machine-specific absolute paths, retain all checked types and axiom reports.
text=text.replace(str(root)+'/','')
(site/'dist/verification.txt').write_text(f'Lean declaration check — {manifest["date"]}\nSnapshot: {manifest["revision"]}\n{count} declarations resolved; {expected-len(unfinished)} proved theorem axiom reports checked; {len(unfinished)} explicitly unfinished target.\nProved theorems use only: propext, Classical.choice, Quot.sound.\nThe sole exception is the unfinished main target, explicitly recorded with sorryAx.\n\n'+text)
(site/'verification.json').write_text(json.dumps({'checked':manifest['date'],'revision':manifest['revision'],'declarations':count,'theorems':expected,'proved_theorems':expected-len(unfinished),'unfinished':sorted(unfinished),'axioms':sorted(allowed),'result':'passed'},indent=2)+'\n')
print(f'All {count} displayed declarations resolve; {expected-len(unfinished)} proved theorem audits pass; the one unfinished target is identified separately.')
