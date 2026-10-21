set pagination off
set confirm off
set print thread-events off
set debuginfod enabled off
set auto-load python-scripts off
source /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/etc/gdb_load_rust_pretty_printers.py
break ash::resolved::ExportSummary::authenticate_source_owner_nominal if self.module.value == 0
run elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_canonical_source_retains_originals --exact --nocapture
python
import gdb
frame=gdb.selected_frame()
name=frame.name()
print('DIAGNOSTIC ENTRY',name)
print(gdb.execute('p self.module',to_string=True))
print(gdb.execute('set print elements 5',to_string=True))
print(gdb.execute('set print max-depth 8',to_string=True))
print(gdb.execute('p *owner',to_string=True))
last=[]
for i in range(1500):
    frame=gdb.selected_frame()
    if frame.name()!=name:
        print('DIAGNOSTIC RETURN',frame.name())
        break
    sal=frame.find_sal()
    last.append((sal.symtab.filename if sal.symtab else '?',sal.line))
    gdb.execute('next',to_string=True)
print('DIAGNOSTIC LAST SOURCE LINES',last[-30:])
print(gdb.execute('bt 8',to_string=True))
end
quit
