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
for js in ('app.js','data.js'):subprocess.run(['node','--check',str(dist/js)],check=True)
v=json.loads((site/'verification.json').read_text())
assert v['result']=='passed' and v['theorems']==sum(d['kind']=='theorem' for d in D['declarations'].values())
assert 'sorryAx' not in (dist/'verification.txt').read_text()
print(f'PASS: {len(D["paper"])} passages, {len(D["annotations"])} annotations, {len(D["declarations"])} exact declarations; all local assets, anchors, source hashes and JavaScript syntax valid.')
