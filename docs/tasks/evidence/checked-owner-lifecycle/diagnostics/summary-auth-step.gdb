set pagination off
set confirm off
set print thread-events off
set debuginfod enabled off
set auto-load python-scripts off
break ash::resolved::ExportSummary::authenticate_with_provider_commit if self.module.value == 0
run elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_canonical_source_retains_originals --exact --nocapture
python
import gdb
frame=gdb.selected_frame()
name=frame.name()
print('DIAGNOSTIC ENTRY',name)
print(gdb.execute('p self.module',to_string=True))
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
