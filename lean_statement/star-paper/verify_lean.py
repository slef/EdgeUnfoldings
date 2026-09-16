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
for name,axioms in names:
    assert set(x.strip() for x in axioms.split(','))<=allowed,(name,axioms)
assert 'sorryAx' not in text and 'error:' not in text and 'warning:' not in text
# Strip machine-specific absolute paths, retain all checked types and axiom reports.
text=text.replace(str(root)+'/','')
(site/'dist/verification.txt').write_text(f'Lean declaration check — {manifest["date"]}\nSnapshot: {manifest["revision"]}\n{count} declarations resolved; {expected} theorem axiom reports checked.\nAllowed axioms: propext, Classical.choice, Quot.sound.\n\n'+text)
(site/'verification.json').write_text(json.dumps({'checked':manifest['date'],'revision':manifest['revision'],'declarations':count,'theorems':expected,'axioms':sorted(allowed),'result':'passed'},indent=2)+'\n')
print(f'All {count} displayed declarations resolve; {len(names)} theorem dependency audits pass.')
