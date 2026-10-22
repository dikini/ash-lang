import gdb
active = []
count = 0
class TableDone(gdb.FinishBreakpoint):
    def __init__(self, frame, ptr, before, data):
        super().__init__(frame, internal=True)
        self.ptr, self.before, self.data = ptr, before, data
    def stop(self):
        self.data['total'] = int(self.ptr.dereference()['used'])-self.before
        print('INVENTORY TABLE ' + repr(self.data))
        active.remove(self.data)
        return False
class Table(gdb.Breakpoint):
    def stop(self):
        global count
        count += 1
        ptr = gdb.parse_and_eval('work')
        data = {'table':count, 'registry':int(gdb.parse_and_eval('self')), 'proofs':[]}
        active.append(data)
        TableDone(gdb.newest_frame(),ptr,int(ptr.dereference()['used']),data)
        return False
class ProofDone(gdb.FinishBreakpoint):
    def __init__(self, frame, ptr, before, row, data):
        super().__init__(frame, internal=True)
        self.ptr, self.before, self.row, self.data = ptr, before, row, data
    def stop(self):
        self.row['cost'] = int(self.ptr.dereference()['used'])-self.before
        self.data['proofs'].append(self.row)
        return False
class Proof(gdb.Breakpoint):
    def stop(self):
        if not active:
            return False
        frame=gdb.newest_frame();caller=frame.older()
        ptr=gdb.parse_and_eval('work')
        row={'caller':caller.name() if caller else '', 'registry':int(gdb.parse_and_eval('registry')), 'module':str(gdb.parse_and_eval('module')), 'source':str(gdb.parse_and_eval('source'))}
        ProofDone(frame,ptr,int(ptr.dereference()['used']),row,active[-1])
        return False
Table('ash::resolved::ResolvedRegistry::authenticate_scalar_preflights', internal=True)
Proof('ash::foreign::checked_builtins::authenticate_checked_builtins', internal=True)
