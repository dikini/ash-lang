import gdb

gdb.execute('set print elements 3')
class Result(gdb.FinishBreakpoint):
    def __init__(self, label):
        super().__init__(gdb.newest_frame(), internal=True)
        self.label = label
    def stop(self):
        try:
            value = str(self.return_value)
        except Exception as error:
            value = '<unavailable: ' + str(error) + '>'
        print('STAGE RESULT ' + self.label + ': ' + value[:700])
        return False
class Stage(gdb.Breakpoint):
    def __init__(self, location, label):
        super().__init__(location, internal=True)
        self.label = label
    def stop(self):
        try:
            context = str(gdb.parse_and_eval('self.source_resource_context'))
            if 'OriginalTemplate' not in context:
                return False
        except Exception:
            pass
        print('STAGE ENTRY ' + self.label)
        if self.label == 'external parameter kind':
            print('IDENTITY ' + str(gdb.parse_and_eval('identity')))
        Result(self.label)
        return False
class Failure(gdb.Breakpoint):
    def stop(self):
        print('ACTUAL declaration registry failure')
        gdb.execute('bt 12')
        gdb.execute('up')
        gdb.execute('info locals')
        return True
Stage('src/core/validate.rs:9140', 'module registry')
Stage('src/core/validate.rs:9906', 'effect registry')
Stage('src/core/validate.rs:16183', 'effect registry phase')
Stage('src/core/validate.rs:11800', 'external parameter kind')
Failure('ash::core::validate::source_declarations::registry', internal=True)
