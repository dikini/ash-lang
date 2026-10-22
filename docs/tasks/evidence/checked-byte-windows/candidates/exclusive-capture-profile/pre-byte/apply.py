from pathlib import Path
import shutil
root=Path.cwd(); out=Path('/tmp/ash-checked-byte-windows/exclusive-profile/pre-byte')
# Save exact uninstrumented product bytes before any overlay.
for name in ['src/types.rs','src/core/capture.rs','src/core/capture/control.rs','src/build/image.rs']:
 p=out/'original'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((root/name).read_bytes())
module=(out/'capture_charge_profile.rs').read_text().replace('const SESSIONS: usize = 16;', 'const SESSIONS: usize = 32;').replace('const SITES: usize = 192;', 'const SITES: usize = 256;').replace('SITES-1', 'SITES-SESSIONS')
module=module.replace('None => { p.overflow = true; SITES-SESSIONS }','None => { p.overflow = true; SITES-SESSIONS+index }')
module=module.replace('if s.session == usize::MAX { *s = Site { session: index, file: at.file(), line: at.line(), op, ..EMPTY }; }','if s.session == usize::MAX { *s = Site { session: index, file: if slot >= SITES-SESSIONS { "overflow" } else { at.file() }, line: if slot >= SITES-SESSIONS { 0 } else { at.line() }, op: if slot >= SITES-SESSIONS { 0 } else { op }, ..EMPTY }; }')
(root/'src/types/capture_charge_profile.rs').write_text(module)
p=root/'src/types.rs';s=p.read_text();s=s.replace('mod owner_arguments;', '#[cfg(test)]\npub(crate) mod capture_charge_profile;\n\nmod owner_arguments;',1)
old='''    pub(crate) fn charge(&mut self, cells: usize) -> Result<(), ()> {
        let next = self.used.checked_add(cells).ok_or(())?;
        if next > self.limit {
            return Err(());
        }
        self.used = next;
        Ok(())
    }'''
new='''    #[cfg_attr(test, track_caller)]
    pub(crate) fn charge(&mut self, cells: usize) -> Result<(), ()> {
        #[cfg(test)]
        let before = self.used;
        let result = (|| {
            let next = self.used.checked_add(cells).ok_or(())?;
            if next > self.limit {
                return Err(());
            }
            self.used = next;
            Ok(())
        })();
        #[cfg(test)]
        capture_charge_profile::observe(self, before, cells, result.is_ok(), std::panic::Location::caller());
        result
    }'''
assert s.count(old)==1;s=s.replace(old,new);p.write_text(s)
def insert(s,name,code,start=0):
 at=s.index('fn '+name+'(',start);at=s.index('{',s.index('->',at))+1;return s[:at]+'\n'+code+s[at:]
p=root/'src/core/capture.rs';s=p.read_text();s=s.replace('fn charge(budget:', '#[cfg_attr(test, track_caller)]\nfn charge(budget:',1)
s=insert(s,'check_control_roots_with_rows','''    #[cfg(test)]
    let _profile = crate::types::capture_charge_profile::begin(budget, graph.code.len(), roots.len());
    #[cfg(test)]
    let _operation = crate::types::capture_charge_profile::operation(8);
''')
# Generic function header requires its full spelling.
at=s.index('fn build_capture_graph<');at=s.index('{',s.index('-> Result',at))+1;s=s[:at]+'''\n    #[cfg(test)]
    let _profile = crate::types::capture_charge_profile::begin(budget, nodes.len(), globals.len());
    #[cfg(test)]
    let _operation = crate::types::capture_charge_profile::operation(9);
'''+s[at:];p.write_text(s)
p=root/'src/core/capture/control.rs';s=p.read_text();start=s.index('impl State {')
for name,tag in [('copy',1),('charge_key',2),('normalize',3),('prune_sorted_heap',4),('prune_after_pop',4),('copy_segment',5)]:
 prefix='edges.len()' if name=='copy_segment' else '0'
 code=f'''        #[cfg(test)]
        let _operation = crate::types::capture_charge_profile::operation({tag});
        #[cfg(test)]
        crate::types::capture_charge_profile::sizes(self.heap.len(), self.cells.len(), {prefix});
''';s=insert(s,name,code,start)
for name,tag,prefix in [('requested_clause',6,'clause.0.prefix.len()'),('discover_call',7,'calls.len()'),('requested',10,'0')]:
 s=insert(s,name,f'''        #[cfg(test)]
        let _operation = crate::types::capture_charge_profile::operation({tag});
        #[cfg(test)]
        crate::types::capture_charge_profile::sizes(state.heap.len(), state.cells.len(), {prefix});
''')
p.write_text(s)
p=root/'src/build/image.rs';s=p.read_text();s=insert(s,'restore_effect','''        #[cfg(test)]
        let _profile_restore = crate::types::capture_charge_profile::restore();
''');p.write_text(s)
