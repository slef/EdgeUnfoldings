"""Static integrity checks for the annotated paper and its bundled source snapshot."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit,unquote
import json,re,hashlib,subprocess
site=Path(__file__).resolve().parent; dist=site/'dist'
class Page(HTMLParser):
    def __init__(self,text):
        super().__init__();self.ids=set();self.links=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'id' in a:
            assert a['id'] not in self.ids,('duplicate ID',a['id'])
            self.ids.add(a['id'])
        for k in ('src','href'):
            if k in a:self.links.append(a[k])
pages={p:Page(p.read_text()) for p in dist.rglob('*.html')}
for path,page in pages.items():
    for link in page.links:
        u=urlsplit(link)
        if u.scheme or u.netloc:continue
        target=(path.parent/unquote(u.path)).resolve() if u.path else path
        assert target.exists(),(path,link)
        if u.fragment and target.suffix=='.html':assert unquote(u.fragment) in pages[target].ids,(path,link)
D=json.loads((dist/'data.js').read_text().removeprefix('window.PAPER_DATA = ').rstrip(';\n'))
assert D['paper']==json.loads((site/'paper.json').read_text())
assert D['annotations']==json.loads((site/'annotations.json').read_text())
annotation_ids={a['id'] for a in D['annotations']}
for annotation in D['annotations']:
    work=annotation['work']
    assert work['status'] in ('complete','todo','beyond')
    assert work['reason'] and (bool(work['remaining'])==(work['status']=='todo'))
    assert set(work['depends_on'])<=annotation_ids
    assert annotation['id'] not in work['depends_on']
    if work['status']=='beyond':assert work['beyond']
    assert 'gap' not in annotation,'Use separate remaining and beyond-milestone obligations'
all_blocks={b['id'] for b in D['paper']}
used=set()
for a in D['annotations']:
    assert set(a['blocks'])<=all_blocks
    assert not used.intersection(a['blocks']);used.update(a['blocks'])
    for ref in a['refs']:assert ':'.join(ref) in D['declarations']
for key,d in D['declarations'].items():
    source=(dist/'sources'/f'{d["module"]}.lean').read_text()
    assert d['signature'] in source,(key,'excerpt changed')
    assert not re.search(r'\blet\s+\w+\s*$',d['signature']),(key,'truncated at let binding')
    assert not d['proofHole']
    assert f'L{d["line"]}' in pages[dist/'sources'/f'{d["module"]}.html'].ids
for module,s in D['sources'].items():
    for path in (site.parent/s['path'],dist/'sources'/f'{module}.lean'):
        assert hashlib.sha256(path.read_bytes()).hexdigest()==s['sha256'],path
for b in D['paper']:
    assert not re.search(r'\b102[1-6]\b',b['text']),'page header inside paragraph'
    assert not any(ord(c)<32 for c in b['text'])
for js in ('app.js','data.js','hovers.js'):subprocess.run(['node','--check',str(dist/js)],check=True)
v=json.loads((site/'verification.json').read_text())
assert v['revision']==D['revision'] and v['declarations']==len(D['declarations'])
assert D['revision'] in (dist/'index.html').read_text()
manifest=json.loads((site/'source-manifest.json').read_text())
assert manifest==json.loads((dist/'source-manifest.json').read_text())
assert manifest['revision']==D['revision'] and manifest['declarations']==v['declarations']
assert v['result']=='passed' and v['theorems']==sum(d['kind']=='theorem' for d in D['declarations'].values())
assert 'sorryAx' not in (dist/'verification.txt').read_text()
print(f'PASS: {len(D["paper"])} passages, {len(D["annotations"])} annotations, {len(D["declarations"])} exact declarations; all local assets, anchors, source hashes and JavaScript syntax valid.')

# Hover markup must preserve every character of the checked excerpts.
H=json.loads((site/'hover-index.json').read_text())
browser_hovers=json.loads((dist/'hovers.js').read_text().removeprefix('window.LEAN_HOVERS = ').rstrip(';\n'))
assert browser_hovers['symbols']==H['symbols']
assert not H['unresolved']
class Excerpts(HTMLParser):
    def __init__(self,text):
        super().__init__(); self.current=None; self.text=[]; self.seen=set(); self.buttons=[]; self.targets=[]; self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if tag=='details' and a.get('class')=='declaration':
            self.targets.append(a)
        if tag=='pre' and 'data-excerpt' in a:
            self.current=a['data-excerpt']; self.text=[]
        if tag=='button' and 'data-symbol' in a:
            assert self.current
            key,field=self.current.rsplit(':',1); d=D['declarations'][key]
            if field=='signature':
                head=re.match(r'(?:noncomputable\s+)?'+re.escape(d['kind'])+r'\s+('+re.escape(d['name'])+r')(?=\s|:)',d['signature'])
                assert head
                position=len(''.join(self.text))
                assert not head.start(1)<=position<head.end(1),(key,'redundant declaration-name hover')
                if d['kind'] in ('structure','inductive'):
                    pattern=r"^  ([^\W\d][\w']*)[ \t]*:" if d['kind']=='structure' else r"^  \| ([^\W\d][\w']*)"
                    for introduced in re.finditer(pattern,d['signature'],re.M):
                        assert not introduced.start(1)<=position<introduced.end(1),(key,'redundant field/constructor hover')
            assert a['data-symbol'] in H['symbols']
            assert a['aria-controls']=='lean-hover' and a['aria-haspopup']=='dialog'
            self.buttons.append(a['data-symbol'])
    def handle_data(self,data):
        if self.current:self.text.append(data)
    def handle_endtag(self,tag):
        if tag=='pre' and self.current:
            key,field=self.current.rsplit(':',1)
            assert ''.join(self.text)==D['declarations'][key][field],self.current
            self.seen.add(self.current); self.current=None
excerpt_page=Excerpts((dist/'index.html').read_text())
for key,d in D['declarations'].items():
    matching=[t for t in excerpt_page.targets if t['data-source-path']==D['sources'][d['module']]['path'] and int(t['data-source-start'])==d['line']]
    assert matching,(key,'missing in-page definition target')
    assert all(int(t['data-source-end'])==d['line']+len(d['signature'].splitlines())-1 for t in matching)
    assert all(t['id'] in pages[dist/'index.html'].ids for t in matching)
keywords=set("theorem def abbrev structure inductive noncomputable private protected where extends variable variables open scoped include namespace end in fun let by if then else match with do return have show from forall Prop Type Type* Sort true false".split())
for key,d in D['declarations'].items():
    for field in ('signature','context'):
        if d[field]: assert key+':'+field in excerpt_page.seen
        expected=[(m.start(),m.end()) for m in re.finditer(r"[^\W\d][\w']*",d[field]) if m[0] not in keywords and m[0]!='_']
        spans=H['references'][key][field]
        assert expected==[(t['start'],t['end']) for t in spans],(key,field)
        assert all(t['symbol'] in H['symbols'] for t in spans)
for card in H['symbols'].values():
    assert card['hover'] and card['definition'] and card['location'],card
    assert card['origin'] in ('This project','Mathlib','Lean core')
    location=card['location']; u=urlsplit(location['href']); target=dist/u.path
    assert target in pages and u.fragment in pages[target].ids,location
    assert u.fragment=='L'+str(location['line'])
for name,origin,path in [('Finset','Mathlib','Mathlib/Data/Finset/Defs.lean'),('convexHull','Mathlib','Mathlib/Analysis/Convex/Hull.lean'),('Fin','Lean core','Init/Prelude.lean')]:
    matches=[c for c in H['symbols'].values() if re.match(r'```lean\n'+name+r'(?:\.\{| |:)',c['hover'])]
    assert matches and all(c['origin']==origin and c['location']['path']==path for c in matches),name
class SourceLines(HTMLParser):
    def __init__(self,text):
        super().__init__(); self.in_line=False;self.in_link=False;self.lines=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        if tag=='span' and dict(attrs).get('class')=='line':self.in_line=True;self.lines.append('')
        if tag=='a':self.in_link=True
    def handle_endtag(self,tag):
        if tag=='span':self.in_line=False
        if tag=='a':self.in_link=False
    def handle_data(self,data):
        if self.in_line and not self.in_link:self.lines[-1]+=data
for key,source in H['sources'].items():
    lines=SourceLines((dist/'hover-sources'/f'{key}.html').read_text()).lines
    reconstructed='\n'.join(line.removeprefix(' ') for line in lines)
    assert source['sha256'] in {hashlib.sha256((reconstructed+end).encode()).hexdigest() for end in ('','\n')},source['path']
logo=(dist/'assets/lean-logo.svg').read_text()
assert '<svg ' in logo and '<script' not in logo and 'lean-mark' not in (dist/'index.html').read_text()
for script in ('collect_hovers.py','build_hovers.py','render.py'):
    compile((site/script).read_text(),str(site/script),'exec')
print(f'PASS: {len(H["symbols"])} contextual hover cards; all name lookups covered, declaration, field and constructor head hovers suppressed, in-page targets valid, excerpts unchanged, {len(H["sources"])} linked source snapshots verified.')

# Every marked formula has both visual typesetting and accessible MathML.
from math_typesetting import INLINE_MATH
class FormulaMarkup(HTMLParser):
    def __init__(self, text):
        super().__init__(); self.formulas=[]; self.math=0; self.tex=[]; self.in_tex=False
        self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs=dict(attrs)
        if 'data-tex' in attrs:self.formulas.append(attrs['data-tex'])
        if tag=='math':self.math+=1
        if tag=='annotation' and attrs.get('encoding')=='application/x-tex':
            self.in_tex=True; self.tex.append('')
    def handle_endtag(self, tag):
        if tag=='annotation':self.in_tex=False
    def handle_data(self, data):
        if self.in_tex:self.tex[-1]+=data
math_page=FormulaMarkup((dist/'index.html').read_text())
assert math_page.formulas==math_page.tex and len(math_page.formulas)==math_page.math
assert math_page.math>0 and 'katex-error' not in (dist/'index.html').read_text()
for text in [b['text'] for b in D['paper']]+list(json.loads((site/'figures.json').read_text()).values()):
    prose=INLINE_MATH.sub('',text)
    assert not re.search('[₀₁₂₃₄₅₆₇₈₉ᵢⱼₓₚₜ₌₋₊παλσθε∑≤⊆∪]',prose),prose
    assert r'\(' not in prose and r'\)' not in prose
    for formula in INLINE_MATH.findall(text):assert formula in math_page.formulas
math_css=dist/'assets/katex/katex.min.css'
for font in re.findall(r'url\(([^)]+)\)',math_css.read_text()):
    assert (math_css.parent/font).is_file(),font
subprocess.run(['node','--check',str(site/'render_math.cjs')],check=True)
print(f'PASS: {math_page.math} formulas typeset with accessible MathML and bundled fonts; paper and caption notation fully marked.')
