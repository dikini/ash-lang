from pathlib import Path
import gzip,hashlib,json
out=Path(__file__).parent;index=json.loads((out/'index.json').read_text());maps={}
def sha(b):return hashlib.sha256(b).hexdigest()
def load_map(key):
 if key not in maps:
  record=index['maps'][key];value=json.loads(gzip.decompress((out/record['blob']).read_bytes()))
  if record.get('encoding')=='json-map-delta':
   restored=load_map(record['base']).copy()
   for name in value['removed']:del restored[name]
   restored.update(value['changed']);order=record['key_order'];value={name:restored[name] for name in (sorted(restored) if order=='sorted' else order)}
  data=(json.dumps(value,indent=2)+'\n').encode();assert sha(data)==key and len(data)==record['size'] and len(value)==record['entries'];maps[key]=value
 return maps[key]
def expand(value):
 if isinstance(value,dict):
  if set(value)=={'$retained_map'}:return load_map(value['$retained_map'])
  return {key:expand(item) for key,item in value.items()}
 if isinstance(value,list):return [expand(item) for item in value]
 return value
for record in index['records']:
 data=gzip.decompress((out/record['blob']).read_bytes())
 if record['encoding']=='json-map-template':data=(json.dumps(expand(json.loads(data)),indent=2)+'\n').encode()
 assert len(data)==record['size'] and sha(data)==record['sha256']
 original=Path(record['original_path'])
 if original.is_file() and not record.get('path', '').startswith('tested-'):assert data==original.read_bytes()
print(json.dumps({'records':len(index['records']),'maps':len(maps),'blobs':len(list((out/'blobs').iterdir())),'bytes':sum(p.stat().st_size for p in (out/'blobs').iterdir()),'index':sha((out/'index.json').read_bytes())}))
