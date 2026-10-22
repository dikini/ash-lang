import gdb,json
active=False
sequence=0
MAX=400

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
  if self.restore:active=False
  return False

class Start(gdb.Breakpoint):
 def __init__(self,name,label,meter,kind='budget',restore=False):
  super().__init__(name,internal=True);self.label,self.meter,self.kind,self.restore=label,meter,kind,restore
 def stop(self):
  global active
  if self.restore:active=True
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
 Start(base+name,name,'self','validator')
