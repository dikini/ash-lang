import gdb,json,re,hashlib
active=False
sequence=0
calls=0
MAX=65536

def emit(row):
 global sequence
 sequence+=1
 if sequence>400:
  print('TOPOLOGY '+json.dumps({'error':'row bound exceeded'}));gdb.execute('quit 77')
 print('TOPOLOGY '+json.dumps(dict(sequence=sequence,**row),sort_keys=True))

def pointer(v,depth=0):
 if v.type.code==gdb.TYPE_CODE_PTR:return v
 if depth>8:raise RuntimeError('pointer nesting bound')
 fields={f.name for f in v.type.fields() if f.name}
 for name in ('inner','ptr','pointer','buf'):
  if name in fields:return pointer(v[name],depth+1)
 raise RuntimeError('no backing pointer')

class End(gdb.FinishBreakpoint):
 def __init__(self,frame,meter,restore=False):
  super().__init__(frame,internal=True);self.meter,self.restore=meter,restore
 def stop(self):
  global active
  try:emit({'event':'restore_end' if self.restore else 'candidates_end','used':int(self.meter.dereference()['used']),'limit':int(self.meter.dereference()['limit'])})
  except Exception as e:emit({'error':str(e),'event':'finish'})
  if self.restore:active=False
  return False
class Restore(gdb.Breakpoint):
 def stop(self):
  global active
  active=True
  meter=gdb.parse_and_eval('work');emit({'event':'restore_start','used':int(meter.dereference()['used']),'limit':int(meter.dereference()['limit'])});End(gdb.newest_frame(),meter,True)
  return False
Restore('ash::build::image::PureImage::restore_effect',internal=True)
variants=set('Cleanup Scalar IndependentCallable Slot Unknown Alias Forward Merge MetadataMerge Function Call BorrowedCallReply SourceDataCall Tuple Constructor Project Bind Recursive Match Resource Request Resume Handler Evidence'.split())
class Candidates(gdb.Breakpoint):
 def stop(self):
  global calls
  if not active:return False
  calls+=1
  try:
   selfptr=gdb.parse_and_eval('self');obj=selfptr.dereference();graph=obj['graph'].dereference();exprs=graph['expressions'];slots=obj['slots'];e=int(exprs['len']);s=int(slots['len']);c=int(obj['contexts']['paths']['len']);meter=gdb.parse_and_eval('budget')
   row={'event':'candidates_start','analysis':int(selfptr),'graph':int(obj['graph']),'E':e,'S':s,'C':c,'used':int(meter.dereference()['used']),'limit':int(meter.dereference()['limit'])}
   if min(e,s,c)<0 or max(e,s,c)>MAX:raise RuntimeError('E/S/C exceeds bounded resident-read limit')
   ep=pointer(exprs['buf']);resources=set();unknown=[];names=[]
   for i in range(e):
    text=(ep+i).dereference().format_string(max_depth=1,max_elements=1)
    match=re.match(r'^ash::core::capture::value::Expr::([A-Za-z_]+)(?:[({ ]|$)',text)
    name=match.group(1) if match else None
    if name not in variants:
     if len(unknown)<3:unknown.append({'index':i,'prefix':text[:160]})
     names.append('?')
    else:
     names.append(name)
     if name=='Resource':resources.add(i)
   row['variant_sequence_sha256']=hashlib.sha256(json.dumps(names,separators=(',',':')).encode()).hexdigest();row['unclassified']=names.count('?')
   if unknown:row['unclassified_examples']=unknown
   if not row['unclassified']:
    row['R']=len(resources);sp=pointer(slots['buf']);k=0;keys=[]
    for i in range(s):
     key=(sp+i).dereference()['key'];fields=[f.name for f in key.type.fields() if f.name]
     if len(fields)!=2:raise RuntimeError('slot key does not have exactly two tuple fields')
     expression=int(key[fields[0]]);context=int(key[fields[1]])
     if not 0<=expression<e or not 0<=context<c:raise RuntimeError('slot key out of graph/context bounds')
     if expression in resources:k+=1;keys.append([i,expression,context])
    row['K']=k;row['resource_slot_keys_sha256']=hashlib.sha256(json.dumps(keys,separators=(',',':')).encode()).hexdigest();row['R_times_C']=len(resources)*c
   emit(row);End(gdb.newest_frame(),meter)
  except Exception as e:emit({'event':'candidates_error','error':str(e)})
  return False
Candidates('ash::core::capture::value::Analysis::resource_candidates',internal=True)
def exit(event):emit({'event':'inferior_exit','exit_code':getattr(event,'exit_code',None),'candidate_calls':calls})
gdb.events.exited.connect(exit)
