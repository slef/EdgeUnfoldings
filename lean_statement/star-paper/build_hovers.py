"""Build portable editor-style hover data from captured Lean language-server responses."""
from pathlib import Path
from urllib.parse import urlsplit,unquote
import json,re,html,hashlib,collections,argparse,subprocess

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('dependencies',type=Path,help='The same package directory used when capturing hovers')
parser.add_argument('--toolchain',type=Path,help='Lean installation prefix')
parser.add_argument('--input',type=Path,default=Path('/tmp/star-hover-raw.json'))
args=parser.parse_args()
site=Path(__file__).resolve().parent; root=site.parent; dist=site/'dist'; deps=args.dependencies.resolve()
version=(root/'lean-toolchain').read_text().strip()
toolchain=args.toolchain or Path.home()/'.elan/toolchains'/version.replace('/', '--').replace(':', '---')
core=toolchain/'src/lean'
mathlib_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=deps/'mathlib',text=True).strip()
D=json.loads((dist/'data.js').read_text().removeprefix('window.PAPER_DATA = ').rstrip(';\n'))
raw=json.loads(args.input.read_text())
out=dist/'hover-sources';out.mkdir(exist_ok=True)
bundled={};symbols={};positions={};unresolved=[]
def origin_of(path):
 if str(path).startswith('/tmp/star-hover-workspace/'):
  path=root/D['sources'][path.stem]['path']
 if path.is_relative_to(root):return path,'This project',str(path.relative_to(root))
 if path.is_relative_to(core):return path,'Lean core',str(path.relative_to(core))
 if path.is_relative_to(deps):
  relative=path.relative_to(deps);package=relative.parts[0]
  return path,('Mathlib' if package=='mathlib' else package.capitalize()),'/'.join(relative.parts[1:])
 raise ValueError(('unknown definition origin',path))
def bundle(path,origin,relative):
 key=hashlib.sha256((origin+'/'+relative).encode()).hexdigest()[:16]
 if key not in bundled:
  source=path.read_text();lines=source.splitlines()
  numbered='\n'.join(f'<span id="L{i}" class="line"><a href="#L{i}">{i}</a> {html.escape(l)}</span>' for i,l in enumerate(lines,1))
  (out/(key+'.html')).write_text('<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+html.escape(relative)+'</title><style>body{margin:2rem;font:16px/1.6 system-ui;color:#18334b}pre{font:14px/1.6 ui-monospace,monospace;overflow:auto}.line{display:block;min-height:1.6em}.line:target{background:#fff0b8}a{color:#52697e}.line a{display:inline-block;width:3em;text-align:right;text-decoration:none}</style><a href="../index.html">← Annotated paper</a><h1>'+html.escape(relative)+'</h1><p>'+html.escape(origin)+' · bundled source snapshot</p><pre>'+numbered+'</pre></html>')
  bundled[key]={'origin':origin,'path':relative,'sha256':hashlib.sha256(source.encode()).hexdigest()}
 return 'hover-sources/'+key+'.html'
def excerpt(lines,index,local):
 if local:return lines[index].strip()
 start=index
 # Definition links can point to the name in a multiline header.
 while start>0 and lines[start].startswith(' ') and lines[start-1].strip() and not re.match(r'^\s*[\w\']+\s*:',lines[start]):start-=1
 indent=len(lines[index])-len(lines[index].lstrip())
 stop=index+1
 while stop<len(lines):
  line=lines[stop]
  if not line.strip():
   stop+=1
   continue
  if len(line)-len(line.lstrip())<=indent and not line.lstrip().startswith(('| ',':=')):break
  stop+=1
 code='\n'.join(lines[start:stop]).rstrip()
 if re.match(r'\s*(?:private |protected )?theorem\b',code):
  m=re.search(r':=\s*by\b',code)
  code=code[:m.start()].rstrip() if m else code.split(':=',1)[0].rstrip()
 return code

for module,records in raw['records'].items():
 positions[module]={}
 for pos,r in records.items():
  if r['word']=='extends':continue
  content=(r.get('hover') or {}).get('contents',{})
  hover=content.get('value','') if isinstance(content,dict) else str(content)
  record={'hover':hover,'origin':'Lean language','definition':'','location':None,'local':False,'fallback':'Lean did not return declaration information at this position.'}
  targets=r.get('definition') or []
  fallback_local=False
  # Go-to-definition may omit the defining occurrence itself and structure-local
  # binders. Their declaration text supplies the exact location; the type still
  # comes from Lean's hover response.
  if not targets:
   content=(root/D['sources'][module]['path']).read_text();lines_here=content.splitlines(keepends=True)
   binding_path=root/D['sources'][module]['path']
   row,col=map(int,pos.split(':'));line_here=lines_here[row]
   head=re.match(r"^(?:(?:noncomputable|private|protected) )*(?:def|abbrev|theorem|structure|inductive)\s+([\w.]+)",line_here)
   # Lean can omit a target at the defining occurrence of a qualified name,
   # e.g. the `body` token in `def ConvexPolyhedron.body`.
   head_col=len(line_here[:head.start(1)].encode('utf-16-le'))//2 if head else -1
   head_end=len(line_here[:head.end(1)].encode('utf-16-le'))//2 if head else -1
   if head and head_col <= col < head_end:
    found_row=row;found_col=head_col
   else:
    before=''.join(lines_here[:row])+line_here.encode('utf-16-le')[:col*2].decode('utf-16-le')
    structures=list(re.finditer(r'^structure\s+[^\n]+',before,re.M))
    assert structures,(module,pos,r['word'],'Expected a structure-local binding')
    structure_start=structures[-1].start()
    header_end=content.index(' where',structure_start)
    header=content[structure_start:header_end]
    candidates=[]
    # Only declaration binders count, not type ascriptions at later uses.
    for group in re.finditer(r'[({]([^(){}:]+):',header):
     for name in re.finditer(r"[^\W\d][\w']*",group[1]):
      if name[0]==r['word']:candidates.append(structure_start+group.start(1)+name.start())
    for field in re.finditer(r'^  ('+re.escape(r['word'])+r')\s*:',before[structure_start:],re.M):
     candidates.append(structure_start+field.start(1))
    matches=[]
    if candidates:
     assert len(set(candidates))==1,(module,pos,r['word'],candidates)
     at=candidates[0]
    else:
     # These two names are inherited from the explicitly named parent structure.
     assert module=='RegularCutTree' and r['word'] in ('graph','vertices'), (module,pos,r['word'],line_here)
     assert 'extends P.EmbeddedCutGraph a where' in before
     binding_path=root/D['sources']['EmbeddedCutGraph']['path']
     content=binding_path.read_text()
     matches=list(re.finditer(r'^  '+re.escape(r['word'])+r'\s*:',content,re.M))
     assert len(matches)==1
     at=matches[0].start()+2
     record['bindingKind']='Inherited field'
    prefix=content[:at];found_row=prefix.count('\n');found_col=len(prefix.rsplit('\n',1)[-1].encode('utf-16-le'))//2
    fallback_local=True
   targets=[{'targetUri':binding_path.as_uri(),'targetSelectionRange':{'start':{'line':found_row,'character':found_col}}}]
   record['location_method']='source declaration/binding; type from Lean hover'

  if isinstance(targets,dict):targets=[targets]
  if targets:
   target=targets[0];uri=target.get('targetUri',target.get('uri'))
   location=target.get('targetSelectionRange',target.get('range',target.get('targetRange')))
   path,origin,relative=origin_of(Path(unquote(urlsplit(uri).path)))
   line=location['start']['line'];lines=path.read_text().splitlines()
   first=re.search(r'```lean\n([^\n]+)',hover)
   headline=first[1] if first else ''
   local=fallback_local or (origin=='This project' and headline.startswith(r['word']+' :'))
   href=bundle(path,origin,relative)+f'#L{line+1}'
   record.update(origin=origin,definition=excerpt(lines,line,local),location={'path':relative,'line':line+1,'href':href},local=local)
  else:unresolved.append({'module':module,'position':pos,'word':r['word'],'hover':hover})
  key='h'+hashlib.sha256(json.dumps(record,sort_keys=True,ensure_ascii=False).encode()).hexdigest()[:16]
  symbols[key]=record;positions[module][pos]=key
refs={}
for declaration,fields in raw['references'].items():
 module=declaration.split(':')[0]
 refs[declaration]={field:[dict(start=s['start'],end=s['end'],symbol=positions[module][s['position']]) for s in spans if s['position'] in positions[module]] for field,spans in fields.items()}
index={'references':refs,'symbols':symbols,'sources':bundled,'unresolved':unresolved,'toolchain':version,'mathlib':mathlib_revision}
(site/'hover-index.json').write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n')
(dist/'hovers.js').write_text('window.LEAN_HOVERS = '+json.dumps({'symbols':symbols},ensure_ascii=False)+';\n')
counts=collections.Counter(s['origin'] for s in symbols.values())
print(f'{len(symbols)} hover cards; {len(bundled)} source files; {len(unresolved)} positions without a definition link. Origins: {dict(counts)}')
if unresolved:print(json.dumps(unresolved[:20],ensure_ascii=False)[:3500])
