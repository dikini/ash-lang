import gdb,json
active=False
sequence=0
MAX=400
restore_targets=0
restore_finished=False
root_ptr=None
closure_completed=False

def abort_diagnostic(reason):
 print('DIAGNOSTIC_GUARD_FAILURE '+reason)
 gdb.execute('set confirm off')
 gdb.execute('quit 77')

def require_completed_target():
 if restore_targets != 1 or not restore_finished or not closure_completed:
  abort_diagnostic('missing or unfinished unique restore target')


def emit(row):
 global sequence
 sequence+=1
 if sequence<=MAX:print('PHASE_LEDGER '+json.dumps(dict(sequence=sequence,**row),sort_keys=True))
 elif sequence==MAX+1:print('PHASE_LEDGER '+json.dumps({'overflow':True}))

def value(ptr,kind):
 obj=ptr.dereference()
 if kind=='validator':return int(obj['type_work']['value']['value'])
 return int(obj['used'])

class End(gdb.FinishBreakpoint):
 def __init__(self,frame,ptr,kind,row,restore=False):
  super().__init__(frame,internal=True);self.ptr,self.kind,self.row,self.restore=ptr,kind,row,restore
 def stop(self):
  global active
  try:
   self.row['after']=value(self.ptr,self.kind);self.row['inclusive']=self.row['after']-self.row['before'];emit(self.row)
  except Exception as e:emit({'error':str(e),'label':self.row['label']})
  if self.restore:
   global restore_finished
   restore_finished=True
   active=False
  return False

class Start(gdb.Breakpoint):
 def __init__(self,name,label,meter,kind='budget',restore=False):
  super().__init__(name,internal=True);self.label,self.meter,self.kind,self.restore=label,meter,kind,restore
 def stop(self):
  global active
  if self.restore:
   try:
    global restore_targets,root_ptr
    restore_targets+=1
    frame=gdb.newest_frame()
    caller=frame.older().name() if frame.older() else ''
    ptr=gdb.parse_and_eval(self.meter)
    obj=ptr.dereference()
    old_limit=int(obj['limit']);used=int(obj['used'])
    if restore_targets != 1 or old_limit != 327680 or not 0 <= used < old_limit or caller != 'ash::build::image::source_resource_image::tests::dependent_discard_image_checks_original_facts_under_normal_cumulative_work::{closure#0}':
     abort_diagnostic('target/count/limit/caller mismatch')
    obj['limit'].assign(gdb.Value(655360))
    if int(ptr.dereference()['limit']) != 655360 or int(ptr.dereference()['used']) != used:
     abort_diagnostic('assignment altered used or failed')
    print('DIAGNOSTIC_ROOT_OVERRIDE '+json.dumps({'meter':int(ptr),'used':used,'original_limit':old_limit,'diagnostic_limit':655360,'caller':caller},sort_keys=True))
    root_ptr=ptr
    active=True
   except Exception as error:
    abort_diagnostic('override inspection/assignment failed: '+str(error))
  if not active:return False
  try:
   ptr=gdb.parse_and_eval(self.meter);row={'label':self.label,'meter':int(ptr),'before':value(ptr,self.kind),'kind':self.kind}
   if self.kind=='validator':
    row['context']=str(ptr.dereference()['source_resource_context']);row['limit']=int(ptr.dereference()['type_work_limit'])
   else:row['limit']=int(ptr.dereference()['limit'])
   frame=gdb.newest_frame();row['caller']=frame.older().name() if frame.older() else None
   emit(dict(event='entry',**row));End(frame,ptr,self.kind,row,self.restore)
  except Exception as e:emit({'error':str(e),'label':self.label})
  return False
Start('ash::build::image::PureImage::restore_effect','restore','work',restore=True)
Start('ash::build::image::Decoder::source_templates','templates','self.work')
Start('ash::build::image::Decoder::extended_registry','registry_restore','self.work')
Start('ash::core::validate::validate_effect_modules_with_work','independent_validation','work')
base='ash::core::validate::Validator<ash::core::effect::EffectOperationFamily>::'
for name in ['authenticate_effect_registry_phase','run_effect_with_registry','validate_method_evidence_authority','validate_envelopes','validate_graph','collect_binders','collect_type_binders','validate_method_evidence_type_owners','validate_node_types','validate_effect_nodes','validate_source_owner_request_coverage','validate_source_byte_call_coverage','validate_source_window_coverage','validate_registration_edges','validate_effect_abstraction_shapes','validate_scopes','validate_type_scopes','generic_cell_computations']:
 text=gdb.execute('info functions '+name,to_string=True)
 functions=[]
 for line in text.splitlines():
  if 'static fn '+base+name in line:
   functions.append(line.split('static fn ',1)[1].split('(',1)[0])
 if len(functions)!=1:emit({'setup_error':name,'candidates':functions})
 else:Start("'"+functions[0]+"'",name,'self','validator')

class ClosureCompleted(gdb.Breakpoint):
 def stop(self):
  global closure_completed
  try:
   frame=gdb.newest_frame()
   ptr=gdb.parse_and_eval('work')
   if frame.name() != EXPECTED_CALLER or restore_targets != 1 or not restore_finished or closure_completed or root_ptr is None or int(ptr) != int(root_ptr):
    abort_diagnostic('first closure completion identity/count mismatch')
   obj=ptr.dereference()
   used=int(obj['used']);limit=int(obj['limit'])
   if limit != 655360 or not 0 <= used <= limit:
    abort_diagnostic('first closure completion meter mismatch')
   closure_completed=True
   print('DIAGNOSTIC_CLOSURE_COMPLETED '+json.dumps({'caller':frame.name(),'meter':int(ptr),'used':used,'limit':limit,'scope':'decode+expected facts+structural restore+static library correspondence; first initial closure only'},sort_keys=True))
   require_completed_target()
   gdb.execute('set confirm off')
   gdb.execute('quit 0')
  except Exception as error:
   abort_diagnostic('closure completion inspection failed: '+str(error))
  return False
EXPECTED_CALLER='ash::build::image::source_resource_image::tests::dependent_discard_image_checks_original_facts_under_normal_cumulative_work::{closure#0}'
ClosureCompleted('/home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/build/source_resource_image.rs:3642',internal=True)
