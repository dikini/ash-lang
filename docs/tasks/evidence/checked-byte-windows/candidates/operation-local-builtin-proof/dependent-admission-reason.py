import gdb,json
active=False
hit=False
class Begin(gdb.Breakpoint):
 def stop(self):
  global active
  active=True
  return False
class Failure(gdb.Breakpoint):
 def stop(self):
  global hit
  if not active:return False
  frame=gdb.newest_frame();f=frame;eligible=False
  for _ in range(20):
   if f is None:break
   if 'check_executable_foreign_library_in_program' in (f.name() or ''):eligible=True
   f=f.older()
  if not eligible:return False
  hit=True
  print('DEPENDENT_ADMISSION_REASON '+json.dumps({'reason':str(gdb.parse_and_eval('reason')),'span':str(gdb.parse_and_eval('span'))}))
  print(gdb.execute('bt 12',to_string=True))
  gdb.execute('set confirm off');gdb.execute('quit 0')
Begin('ash::build::image::PureImage::restore_effect',internal=True)
Failure('ash::foreign::checked_source::failure',internal=True)
def require_hit():
 if not hit:gdb.execute('set confirm off');gdb.execute('quit 77')
