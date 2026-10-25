import gdb
f=gdb.newest_frame()
while f:
 if f.name() and 'checked_byte_window_selective_nonanchor_preflights_preserve_import_and_reexport' in f.name():
  print('BASELINE SELECTIVE CASE '+str(f.read_var('name')));break
 f=f.older()
