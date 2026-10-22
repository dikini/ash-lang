import gdb
class Done(gdb.FinishBreakpoint):
    def __init__(self, frame, ptr, before, label):
        super().__init__(frame, internal=True)
        self.ptr, self.before, self.label = ptr, before, label
    def stop(self):
        try:
            after = int(gdb.parse_and_eval(self.ptr + '.used'))
            print('CODEC COST ' + self.label + ' ' + str(after-self.before))
        except Exception as error:
            print('COST ERROR ' + str(error))
        return False
class Codec(gdb.Breakpoint):
    def stop(self):
        caller = gdb.newest_frame().older()
        name = caller.name() if caller else ''
        if name and 'scalar_preflight::CheckedForeignScalarPreflight::authenticate' in name:
            try:
                ptr = '(' + str(gdb.parse_and_eval('work').cast(gdb.lookup_type('unsigned long'))) + ' as *mut ash::types::TypeWorkBudget)'
                work = gdb.parse_and_eval('work').dereference()
                print('CODEC INPUT ' + str(work))
                print('CODEC IDS ' + str(gdb.parse_and_eval('ids')))
                caller.select()
                print('FACT ROLE ' + str(gdb.parse_and_eval('self.role')))
                gdb.newest_frame().select()
            except Exception as error:
                print('ENTRY ERROR ' + str(error))
            return True
        return False
Codec('ash::foreign::checked_source::CheckedForeignCallCodec::authenticate', internal=True)
