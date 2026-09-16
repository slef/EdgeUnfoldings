"""Regenerate the paper's exact Lean excerpts. Run from any directory."""
from pathlib import Path
import re, json, hashlib, subprocess, html

site=Path(__file__).resolve().parent
root=site.parent
dist=site/'dist'
out=dist/'sources'; out.mkdir(exist_ok=True)
annotations=json.loads((site/'annotations.json').read_text())
sources={}; decls={}
rx=re.compile(r'^(?:(?:noncomputable|private|protected) )*(theorem|def|abbrev|structure|inductive) ([\w.]+)',re.M)
for module,name in sorted(set(tuple(r) for a in annotations for r in a['refs'])):
    paths=list((root/'SixVertexUnfolding').rglob(module+'.lean'))
    assert len(paths)==1,(module,paths)
    path=paths[0]; content=path.read_text(); lines=content.splitlines()
    matches=[m for m in rx.finditer(content) if m[2]==name]
    assert len(matches)==1,(module,name)
    m=matches[0]; start=content[:m.start()].count('\n'); kind=m[1]
    # Full declaration ends at the next top-level command/comment or blank line.
    end=start+1
    while end<len(lines) and (lines[end].startswith(' ') or not lines[end].strip()): end+=1
    body='\n'.join(lines[start:end]).rstrip()
    if kind=='theorem':
        assert ':=' in body,(module,name)
        separator = re.search(r':=\s*by\b', body)
        signature=body[:separator.start()].rstrip() if separator else body.split(':=',1)[0].rstrip()
    else: signature=body
    # Capture active namespace and variable blocks, respecting closed namespaces.
    frames=[{'name':'','context':[]}]; i=0
    while i<start:
        line=lines[i]
        if line.startswith('namespace '): frames.append({'name':line[10:].strip(),'context':[]})
        elif line.startswith('section'): frames.append({'name':'','context':[]})
        elif re.match(r'^end(?: |$)',line) and len(frames)>1: frames.pop()
        elif line.startswith(('open ','variable ','include ')):
            block=[line]; j=i+1
            while j<start and lines[j].startswith(' '): block.append(lines[j]); j+=1
            # An include ... in before another declaration does not apply to this one.
            if not line.startswith('include ') or (j<start and all(not x.strip() or x.startswith(('/--','--')) for x in lines[j:start])):
                frames[-1]['context'].append('\n'.join(block))
            i=j-1
        i+=1
    namespace='.'.join(f['name'] for f in frames if f['name'])
    context='\n'.join(f['context'][j] for f in frames for j in range(len(f['context'])))
    key=module+':'+name
    decls[key]=dict(name=name,qualified=namespace+'.'+name,kind=kind,module=module,line=start+1,signature=signature,context=context,namespace=namespace,proofHole=bool(re.search(r'\bsorry\b',body)))
    assert not decls[key]['proofHole'],key
    sources[module]=dict(path=str(path.relative_to(root)),sha256=hashlib.sha256(content.encode()).hexdigest())
    rendered=''.join(f'<span id="L{i}" class="line"><a href="#L{i}" aria-label="Line {i}">{i}</a> {html.escape(l)}</span>\n' for i,l in enumerate(lines,1))
    (out/(module+'.html')).write_text('<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+html.escape(module)+'.lean</title><style>body{margin:2rem;font:16px/1.6 system-ui;color:#18334b}pre{font:14px/1.6 ui-monospace,monospace;overflow:auto}.line{display:block;min-height:1.6em}.line:target{background:#fff0b8}a{color:#52697e}.line a{display:inline-block;width:3em;text-align:right;text-decoration:none}</style><a href="../index.html">← Annotated paper</a><h1>'+html.escape(module)+'.lean</h1><p>'+html.escape(str(path.relative_to(root)))+' · exact source snapshot</p><pre>'+rendered+'</pre></html>')
    (out/(module+'.lean')).write_text(content)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
data=dict(annotations=annotations,declarations=decls,sources=sources,revision=revision,date='2026-09-16',paper=json.loads((site/'paper.json').read_text()),figures=json.loads((site/'figures.json').read_text()))
(dist/'data.js').write_text('window.PAPER_DATA = '+json.dumps(data,ensure_ascii=False,indent=2)+';\n')
# A reproducible audit input; it checks the full elaborated types and dependencies.
checks=['import SixVertexUnfolding']
for d in decls.values():
    checks+=['#check @'+d['qualified']]
    if d['kind']=='theorem': checks+=['#print axioms '+d['qualified']]
(site/'CheckExcerpts.lean').write_text('\n'.join(checks)+'\n')
manifest=dict(revision=revision,date=data['date'],declarations=len(decls),theorems=sum(d['kind']=='theorem' for d in decls.values()),sources=sources)
(site/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(dist/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Exported {len(decls)} declarations from {len(sources)} source files at {revision}.')
