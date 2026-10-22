import gdb,json
found=[]
for query in ['extended_registry','source_registry','source_templates']:
 text=gdb.execute('info functions '+query,to_string=True)
 for line in text.splitlines():
  if 'static fn ash::build::image::' in line and 'closure#' in line and '-> ash::build::image::ImageFailure' in line:
   function=line.split('static fn ',1)[1].split('(',1)[0]
   if function not in found:found.append(function)
print('RESTORE_ERROR_CLOSURES '+json.dumps(found))
if not found:
 gdb.execute('set confirm off');gdb.execute('quit 77')
class Failed(gdb.Breakpoint):
 def stop(self):
  print('RESTORE_ERROR_BOUNDARY '+json.dumps({'function':gdb.newest_frame().name()}))
  print(gdb.execute('bt 12',to_string=True))
  print(gdb.execute('info args',to_string=True))
  gdb.execute('set confirm off');gdb.execute('quit 0')
for name in found:Failed("'"+name+"'",internal=True)
