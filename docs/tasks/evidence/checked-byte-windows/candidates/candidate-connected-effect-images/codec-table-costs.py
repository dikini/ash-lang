import gdb
active = []
count = 0
class TableDone(gdb.FinishBreakpoint):
    def __init__(self, frame, ptr, before, data):
        super().__init__(frame, internal=True)
        self.ptr, self.before, self.data = ptr, before, data
    def stop(self):
        after = int(self.ptr.dereference()['used'])
        self.data['total'] = after - self.before
        self.data['codec_total'] = sum(cost for role, cost in self.data['rows'])
        print('AUTH TABLE ' + repr(self.data))
        active.remove(self.data)
        return False
class Table(gdb.Breakpoint):
    def stop(self):
        global count
        count += 1
        ptr = gdb.parse_and_eval('work')
        data = {'table':count, 'work':int(ptr), 'registry':int(gdb.parse_and_eval('self')), 'start':int(ptr.dereference()['used']), 'rows':[]}
        active.append(data)
        TableDone(gdb.newest_frame(), ptr, data['start'], data)
        return False
class CodecDone(gdb.FinishBreakpoint):
    def __init__(self, frame, ptr, before, role, data):
        super().__init__(frame, internal=True)
        self.ptr, self.before, self.role, self.data = ptr, before, role, data
    def stop(self):
        after = int(self.ptr.dereference()['used'])
        self.data['rows'].append((self.role, after-self.before))
        return False
class Codec(gdb.Breakpoint):
    def stop(self):
        if not active:
            return False
        frame = gdb.newest_frame()
        caller = frame.older()
        if not caller or 'scalar_preflight::CheckedForeignScalarPreflight::authenticate' not in (caller.name() or ''):
            return False
        ptr = gdb.parse_and_eval('work')
        before = int(ptr.dereference()['used'])
        caller.select()
        role = str(gdb.parse_and_eval('self.role')).split('::')[-1]
        frame.select()
        CodecDone(frame, ptr, before, role, active[-1])
        return False
Table('ash::resolved::ResolvedRegistry::authenticate_scalar_preflights', internal=True)
Codec('ash::foreign::checked_source::CheckedForeignCallCodec::authenticate', internal=True)
