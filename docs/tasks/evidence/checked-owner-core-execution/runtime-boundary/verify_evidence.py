from pathlib import Path
import json,hashlib,gzip
root=Path(__file__).resolve().parent
m=json.loads((root/'provenance.json').read_bytes())
for r in m['originals']+m['derived']:
 b=(root/r['path']).read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
for r in m['derived']:
 h=hashlib.sha256();total=0
 with gzip.open(root/r['path'],'rb') as f:
  while True:
   b=f.read(min(65536,r['decoded_limit']-total+1))
   if not b:break
   total+=len(b);assert total<=r['decoded_limit'];h.update(b)
 assert total==r['decoded']['bytes'] and h.hexdigest()==r['decoded']['sha256']
print(json.dumps({'originals':len(m['originals']),'derived':len(m['derived']),'status':'exact copies and bounded streaming gzip equivalence pass','omissions':len(m['omissions'])}))
