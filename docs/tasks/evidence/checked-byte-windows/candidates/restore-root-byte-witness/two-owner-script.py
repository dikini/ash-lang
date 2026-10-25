import gdb,json,hashlib
active=False
rows=0
candidate_depth=0
stats={}

def emit(row):
 global rows
 rows+=1
 if rows>400:
  print('AGGREGATE '+json.dumps({'error':'row overflow'}));gdb.execute('quit 77')
 print('AGGREGATE '+json.dumps(dict(sequence=rows,**row),sort_keys=True))

def used(ptr):return int(ptr.dereference()['used'])
def val(expr):return gdb.parse_and_eval(expr)
def number(expr):return int(val(expr))

class End(gdb.FinishBreakpoint):
 def __init__(self,frame,ptr,row,kind):
  super().__init__(frame,internal=True);self.ptr,self.row,self.kind=ptr,row,kind
 def stop(self):
  global active,candidate_depth
  try:
   self.row['after']=used(self.ptr);self.row['inclusive']=self.row['after']-self.row['before']
   if self.kind in ('dependencies','payload'):
    key=(self.row['analysis'],self.kind);record=stats.setdefault(key,{'calls':0,'inclusive':0})
    record['calls']+=1;record['inclusive']+=self.row['inclusive']
   else:emit(dict(event='return',**self.row))
  except Exception as e:emit({'error':str(e),'kind':self.kind})
  if self.kind=='candidates':
   candidate_depth-=1
   for (analysis,kind),record in list(stats.items()):
    if analysis==self.row['analysis']:
     emit(dict(event='candidate_subwork',analysis=analysis,kind=kind,**record));del stats[(analysis,kind)]
  if self.kind=='restore':active=False
  return False

class Start(gdb.Breakpoint):
 def __init__(self,symbol,kind,meter_expr):
  super().__init__(symbol,internal=True);self.kind,self.meter_expr=kind,meter_expr
 def stop(self):
  global active,candidate_depth
  if self.kind=='restore':active=True
  if not active:return False
  if self.kind in ('dependencies','payload') and not candidate_depth:return False
  try:
   ptr=val(self.meter_expr);row={'kind':self.kind,'meter':int(ptr),'before':used(ptr),'limit':int(ptr.dereference()['limit'])}
   frame=gdb.newest_frame();row['caller']=frame.older().name() if frame.older() else None
   if self.kind in ('candidates','dependencies','payload','focused'):
    row['analysis']=number('self');row['graph']=number('self.graph');row['slots']=number('self.slots.len')
   if self.kind=='byte_auth':
    for name in ('registry','sources','modules','context'):row[name]=number(name)
    row['context_value']=str(val('context').dereference())[:500]
   if self.kind=='candidates':candidate_depth+=1
   if self.kind not in ('dependencies','payload'):emit(dict(event='entry',**row))
   End(frame,ptr,row,self.kind)
  except Exception as e:emit({'error':str(e),'kind':self.kind})
  return False

Start('ash::build::image::PureImage::restore_effect','restore','work')
Start('ash::core::validate::source_declarations::builtin_operation::BuiltinForeignSourceAuthentication::new','byte_auth','work')
base='ash::core::capture::value::Analysis::'
for method,kind in [('resource_candidates','candidates'),('dependencies','dependencies'),('source_payload_retains_owner','payload'),('focused','focused')]:Start(base+method,kind,'budget')

class Source(gdb.Breakpoint):
 def stop(self):
  if not active:return False
  try:
   ptr=val('source');source=ptr.dereference();text=source['text']['vec'];length=int(text['len']);rawptr=text['buf']['inner']['ptr']['pointer']
   if length>1048576:raise RuntimeError('source exceeds bounded hash size')
   raw=bytes(gdb.selected_inferior().read_memory(rawptr,length))
   emit({'event':'byte_source','source':int(ptr),'source_id':str(source['id']),'module':str(val('module').dereference()),'text_len':length,'text_address':int(rawptr),'text_sha256':hashlib.sha256(raw).hexdigest()})
  except Exception as e:emit({'error':str(e),'kind':'byte_source'})
  return False
Source('src/core/validate/source_declarations/builtin_operation.rs:39',internal=True)

def finish(event):
 emit({'event':'inferior_exit','exit_code':getattr(event,'exit_code',None),'open_candidates':candidate_depth,'unclosed_subwork':len(stats),'limitations':'resource-slot enum classification and install/focused-copy publication counts omitted; dependency and payload totals overlap inclusively and must not be summed'})
gdb.events.exited.connect(finish)
