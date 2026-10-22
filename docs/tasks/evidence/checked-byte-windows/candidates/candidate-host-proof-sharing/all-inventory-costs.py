import gdb,json
sequence=0
class Done(gdb.FinishBreakpoint):
 def __init__(self,frame,ptr,row):
  super().__init__(frame,internal=True);self.ptr,self.row=ptr,row
 def stop(self):
  self.row['after']=int(self.ptr.dereference()['used']);self.row['cost']=self.row['after']-self.row['before'];print('PROOF '+json.dumps(self.row));return False
class Proof(gdb.Breakpoint):
 def __init__(self,name,label):super().__init__(name,internal=True);self.label=label
 def stop(self):
  global sequence
  sequence+=1;ptr=gdb.parse_and_eval('work');frame=gdb.newest_frame();stack=[];f=frame.older()
  for _ in range(10):
   if f is None:break
   stack.append(f.name());f=f.older()
  row={'sequence':sequence,'label':self.label,'work':int(ptr),'before':int(ptr.dereference()['used']),'limit':int(ptr.dereference()['limit']),'stack':stack}
  for key in ['registry','module','source','ids','self']:
   try:row[key]=str(gdb.parse_and_eval(key))
   except gdb.error:pass
  Done(frame,ptr,row);return False
Proof('ash::foreign::checked_builtins::authenticate_checked_builtins','full_inventory')
Proof('ash::foreign::checked_source::authenticate_codec','codec')
Proof('ash::resolved::ResolvedRegistry::authenticate_scalar_preflights','table')
Proof('ash::build::image::PureImage::restore_effect','restore')
class Refusal(gdb.Breakpoint):
 def stop(self):
  print('ACTUAL BUDGET REFUSAL');print(gdb.execute('bt 35',to_string=True));print(gdb.execute('info args',to_string=True));return False
Refusal('/home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/types.rs:80',internal=True)
