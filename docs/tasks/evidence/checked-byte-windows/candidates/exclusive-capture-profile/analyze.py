import collections,json,pathlib,re,sys
source=pathlib.Path(sys.argv[1]); reports=[]
for line in source.read_text().splitlines():
 if line.startswith('CAPTURE_CHARGE_PROFILE '):reports.append(json.loads(line.split(' ',1)[1]))
assert len(reports)==1, len(reports)
r=reports[0]; print('report_bytes',len(json.dumps(r,separators=(',',':'))),'overflow',r.get('overflow'),'sessions',len(r.get('sessions',[])))
if r.get('output_overflow'):sys.exit('No profile attribution: output overflow')
for s in r['sessions']:
 sites=[row for row in r['sites'] if row['session']==s['id']]
 assert sum(row['units'] for row in sites)==s['after']-s['before'],s
 print('SESSION',json.dumps({k:v for k,v in s.items() if k!='sizes'},sort_keys=True))
 if not s['restore']:continue
 ops=collections.Counter()
 for row in sites:ops[r['ops'][row['op']]]+=row['units']
 print('OPERATIONS',ops.most_common())
 for row in sorted(sites,key=lambda x:x['units'],reverse=True)[:25]:
  row=dict(row);p=pathlib.Path(row['file']);row['function']='unknown'
  if p.is_file():
   lines=p.read_text().splitlines()[:row['line']]
   for line in reversed(lines):
    match=re.search(r'\bfn ([a-zA-Z_0-9]+)',line)
    if match:row['function']=match.group(1);break
  print('SITE',json.dumps(row,sort_keys=True))
 print('FAILED',json.dumps([row for row in sites if row['failures']],sort_keys=True))
 print('SIZES',json.dumps(s['sizes'],sort_keys=True))
print('ALL_RECONCILED',all(s['reconciles'] for s in r['sessions']))
