import gdb,json
phase='compile';ordinal=0
class Restored(gdb.FinishBreakpoint):
 def stop(self):
  global phase
  phase='after_restore';return False
class Restore(gdb.Breakpoint):
 def stop(self):
  global phase
  phase='restore';Restored(gdb.newest_frame(),internal=True);return False
class Call(gdb.Breakpoint):
 def stop(self):
  global ordinal
  ordinal+=1;return False
class Copied(gdb.FinishBreakpoint):
 def __init__(self,frame,budget,row):
  super().__init__(frame,internal=True);self.budget,self.row=budget,row
 def stop(self):
  self.row['after']=int(self.budget.dereference()['used']);self.row['cost']=self.row['after']-self.row['before'];print('CALL STATE COPY '+json.dumps(self.row));return False
class Copy(gdb.Breakpoint):
 def stop(self):
  f=gdb.newest_frame();parent=f.older()
  if not parent or 'Analysis::discover_call' not in (parent.name() or ''):return False
  budget=gdb.parse_and_eval('budget');state=gdb.parse_and_eval('self');row={'phase':phase,'ordinal':ordinal,'line':parent.find_sal().line,'state':int(state),'position':str(state.dereference()['position']),'before':int(budget.dereference()['used']),'limit':int(budget.dereference()['limit'])}
  Copied(f,budget,row);return False
Restore('ash::build::image::PureImage::restore_effect',internal=True)
Call('ash::core::capture::control::Analysis::discover_call',internal=True)
Copy('ash::core::capture::control::State::copy',internal=True)
