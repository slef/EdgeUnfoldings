"""Capture genuine Lean language-server hovers and definition locations for paper excerpts."""
from pathlib import Path
import os,re,json,subprocess,threading,queue,concurrent.futures,hashlib,time,argparse

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('dependencies',type=Path,help='Directory containing mathlib and other Lake packages')
parser.add_argument('--toolchain',type=Path,help='Lean installation prefix (defaults to the project toolchain in ~/.elan)')
parser.add_argument('--output',type=Path,default=Path('/tmp/star-hover-raw.json'))
args=parser.parse_args()
site=Path(__file__).resolve().parent; root=site.parent; deps=args.dependencies.resolve()
version=(root/'lean-toolchain').read_text().strip()
toolchain=args.toolchain or Path.home()/'.elan/toolchains'/version.replace('/', '--').replace(':', '---')
work=Path('/tmp/star-hover-workspace');work.mkdir(exist_ok=True)
cache=Path('/tmp/star-hover-cache');cache.mkdir(exist_ok=True)
D=json.loads((site/'dist/data.js').read_text().removeprefix('window.PAPER_DATA = ').rstrip(';\n'))
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(str(p) for p in [root/'.lake/build/lib/lean',*sorted(deps.glob('*/.lake/build/lib/lean'))])
env['LEAN_SRC_PATH']=os.pathsep.join(map(str,[root,*sorted(p for p in deps.iterdir() if p.is_dir())]))
keywords=set('theorem def abbrev structure inductive noncomputable private protected where extends variable variables open scoped include namespace end in fun let by if then else match with do return have show from forall Prop Type Type* Sort true false'.split())
token_re=re.compile(r"[^\W\d][\w']*",re.UNICODE)
files={m:(root/v['path']).read_text() for m,v in D['sources'].items()}
positions={m:{} for m in files};references={}
for key,d in D['declarations'].items():
 content=files[d['module']];ranges={}
 for field in ['signature','context']:
  text=d[field];spans=[]
  if field=='signature':
   base=content.index(text);mapping=list(range(base,base+len(text)))
  else:
   mapping=[];cursor=0
   for line in text.splitlines(keepends=True):
    needle=line.rstrip('\n');at=content.index(needle,cursor) if needle else cursor
    mapping.extend(range(at,at+len(line)));cursor=at+len(needle)
  for match in token_re.finditer(text):
   word=match[0]
   if word in keywords or word=='_':continue
   at=mapping[match.start()];before=content[:at];line=before.count('\n')
   col=len(before.rsplit('\n',1)[-1].encode('utf-16-le'))//2
   pos=f'{line}:{col}'
   positions[d['module']][pos]={'line':line,'character':col,'word':word}
   spans.append({'start':match.start(),'end':match.end(),'position':pos})
  ranges[field]=spans
 references[key]=ranges

class Server:
 def __init__(self,module):
  self.p=subprocess.Popen([str(toolchain/'bin/lean'),'--server'],cwd=work,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=open(cache/(module+'.stderr'),'w'))
  self.q=queue.Queue()
  def read():
   try:
    while True:
     line=self.p.stdout.readline()
     if not line:break
     if line.lower().startswith(b'content-length:'):
      n=int(line.split(b':',1)[1]);self.p.stdout.readline();self.q.put(json.loads(self.p.stdout.read(n)))
   finally:self.q.put({'ended':True})
  threading.Thread(target=read,daemon=True).start()
  self.send({'id':'init','method':'initialize','params':{'processId':None,'rootUri':work.as_uri(),'capabilities':{}}})
  while self.read().get('id')!='init':pass
  self.send({'method':'initialized','params':{}})
 def send(self,x):
  x['jsonrpc']='2.0';b=json.dumps(x).encode();self.p.stdin.write(f'Content-Length: {len(b)}\r\n\r\n'.encode()+b);self.p.stdin.flush()
 def read(self):
  while True:
   x=self.q.get(timeout=300)
   if x.get('ended'):raise RuntimeError('Lean server ended')
   if 'method' in x and 'id' in x:
    self.send({'id':x['id'],'result':[{} for _ in x.get('params',{}).get('items',[])] if x['method']=='workspace/configuration' else None})
   else:return x
 def close(self):
  try:self.p.terminate();self.p.wait(timeout=10)
  except: self.p.kill()

def collect(module):
 content=files[module];digest=hashlib.sha256((content+json.dumps(positions[module],sort_keys=True)+str(toolchain)+str(deps)+D['revision']).encode()).hexdigest()
 target=cache/(module+'.json')
 if target.exists():
  old=json.loads(target.read_text())
  if old['digest']==digest:return module,old['records']
 copied=work/(module+'.lean');copied.write_text(content);uri=copied.as_uri()
 server=Server(module);records={};errors=[];started=time.time()
 try:
  server.send({'method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean4','version':1,'text':content}}})
  for pos,meta in positions[module].items():
   records[pos]={'word':meta['word']}
   for kind in ('hover','definition'):
    server.send({'id':pos+'/'+kind,'method':'textDocument/'+kind,'params':{'textDocument':{'uri':uri},'position':{'line':meta['line'],'character':meta['character']}}})
  pending=2*len(records)
  while pending:
   x=server.read()
   if 'id' in x and '/' in str(x['id']):
    pos,kind=x['id'].split('/');records[pos][kind]=x.get('result');pending-=1
    if x.get('error'):errors.append(x['error'])
   elif x.get('method')=='textDocument/publishDiagnostics':
    errors.extend(d for d in x['params']['diagnostics'] if d.get('severity')==1)
  assert not errors,(module,errors[:2])
  target.write_text(json.dumps({'digest':digest,'records':records},ensure_ascii=False))
  print(f'{module}: {len(records)} positions, {sum(bool(r.get("hover")) for r in records.values())} hovers ({round(time.time()-started)}s)',flush=True)
  return module,records
 finally:server.close()

if __name__=='__main__':
 started=time.time();results={}
 # Three isolated Lean workers bound memory while independent modules elaborate.
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
  for module,records in pool.map(collect,files):results[module]=records
 args.output.write_text(json.dumps({'references':references,'records':results},ensure_ascii=False))
 print(f'Complete: {len(results)} modules, {sum(map(len,positions.values()))} token positions, {round(time.time()-started)}s.',flush=True)
