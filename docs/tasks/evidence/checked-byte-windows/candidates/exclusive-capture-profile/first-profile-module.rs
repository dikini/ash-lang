//! Disposable observation only. Removed before product verification.
use super::TypeWorkBudget;
use std::{cell::RefCell, panic::Location};
const SESSIONS: usize = 32;
const SITES: usize = 256;
const OPS: usize = 12;
#[derive(Clone, Copy)]
struct Site {
    session: usize,
    file: &'static str,
    line: u32,
    op: usize,
    calls: usize,
    units: usize,
    failures: usize,
    requested: usize,
}
const EMPTY: Site = Site {
    session: usize::MAX,
    file: "",
    line: 0,
    op: 0,
    calls: 0,
    units: 0,
    failures: 0,
    requested: 0,
};
#[derive(Clone, Copy)]
struct Sizes {
    calls: usize,
    heap: usize,
    cells: usize,
    prefix: usize,
}
const ZERO: Sizes = Sizes {
    calls: 0,
    heap: 0,
    cells: 0,
    prefix: 0,
};
#[derive(Clone, Copy)]
struct Session {
    meter: usize,
    before: usize,
    after: usize,
    limit: usize,
    restore: bool,
    graph: usize,
    roots: usize,
    sizes: [Sizes; OPS],
}
const SESSION: Session = Session {
    meter: 0,
    before: 0,
    after: 0,
    limit: 0,
    restore: false,
    graph: 0,
    roots: 0,
    sizes: [ZERO; OPS],
};
struct Profile {
    active: Option<usize>,
    op: usize,
    restore: bool,
    count: usize,
    overflow: bool,
    sessions: [Session; SESSIONS],
    sites: [Site; SITES],
}
thread_local! { static PROFILE: RefCell<Profile> = const { RefCell::new(Profile { active: None, op: 0, restore: false, count: 0, overflow: false, sessions: [SESSION; SESSIONS], sites: [EMPTY; SITES] }) }; }
fn enabled() -> bool {
    std::env::var_os("ASH_CAPTURE_PROFILE").is_some()
}
pub(crate) struct Scope {
    prior: Option<usize>,
}
pub(crate) fn begin(budget: &TypeWorkBudget, graph: usize, roots: usize) -> Scope {
    if !enabled() {
        return Scope { prior: None };
    }
    PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        let prior = p.active;
        if p.count == SESSIONS {
            p.overflow = true;
            p.active = None;
            return Scope { prior };
        }
        let index = p.count;
        p.count += 1;
        p.sessions[index] = Session {
            meter: budget as *const _ as usize,
            before: budget.used(),
            after: budget.used(),
            limit: budget.limit(),
            restore: p.restore,
            graph,
            roots,
            sizes: [ZERO; OPS],
        };
        p.active = Some(index);
        Scope { prior }
    })
}
impl Drop for Scope {
    fn drop(&mut self) {
        PROFILE.with(|p| p.borrow_mut().active = self.prior);
    }
}
pub(crate) struct Operation {
    prior: usize,
}
pub(crate) fn operation(op: usize) -> Operation {
    PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        let prior = p.op;
        p.op = op;
        Operation { prior }
    })
}
impl Drop for Operation {
    fn drop(&mut self) {
        PROFILE.with(|p| p.borrow_mut().op = self.prior);
    }
}
pub(crate) fn sizes(heap: usize, cells: usize, prefix: usize) {
    PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        if let Some(i) = p.active {
            let op = p.op;
            let s = &mut p.sessions[i].sizes[op];
            s.calls += 1;
            s.heap = s.heap.max(heap);
            s.cells = s.cells.max(cells);
            s.prefix = s.prefix.max(prefix);
        }
    });
}
pub(crate) fn observe(
    budget: &TypeWorkBudget,
    before: usize,
    requested: usize,
    success: bool,
    at: &'static Location<'static>,
) {
    PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        let Some(index) = p.active else {
            return;
        };
        if p.sessions[index].meter != budget as *const _ as usize {
            return;
        }
        p.sessions[index].after = budget.used();
        let op = p.op;
        let found = p.sites[..SITES - SESSIONS].iter().position(|s| {
            s.session == index && s.file == at.file() && s.line == at.line() && s.op == op
        });
        let slot = found.or_else(|| {
            p.sites[..SITES - SESSIONS]
                .iter()
                .position(|s| s.session == usize::MAX)
        });
        let slot = match slot {
            Some(slot) => slot,
            None => {
                p.overflow = true;
                SITES - SESSIONS + index
            }
        };
        let s = &mut p.sites[slot];
        if s.session == usize::MAX {
            *s = Site {
                session: index,
                file: if slot >= SITES - SESSIONS {
                    "overflow"
                } else {
                    at.file()
                },
                line: if slot >= SITES - SESSIONS {
                    0
                } else {
                    at.line()
                },
                op: if slot >= SITES - SESSIONS { 0 } else { op },
                ..EMPTY
            };
        }
        // Overflow keeps exact units but loses caller/session attribution.
        s.calls += 1;
        if success {
            s.units += budget.used() - before;
        } else {
            s.failures += 1;
            s.requested = s.requested.saturating_add(requested);
        }
    });
}
pub(crate) struct Restore {
    prior: bool,
    enabled: bool,
}
pub(crate) fn restore() -> Restore {
    let enabled = enabled();
    PROFILE.with(|p| {
        let mut p = p.borrow_mut();
        let prior = p.restore;
        p.restore = true;
        Restore { prior, enabled }
    })
}
impl Drop for Restore {
    fn drop(&mut self) {
        PROFILE.with(|p| { let mut p = p.borrow_mut(); p.restore = self.prior; if !self.enabled { return; }
    let sessions = (0..p.count).map(|i| { let s = p.sessions[i]; let units: usize = p.sites.iter().filter(|x| x.session == i).map(|x| x.units).sum(); serde_json::json!({"id":i,"meter":s.meter,"before":s.before,"after":s.after,"limit":s.limit,"restore":s.restore,"graph":s.graph,"roots":s.roots,"units":units,"reconciles":units==s.after-s.before,"sizes":s.sizes.iter().enumerate().filter(|(_,s)|s.calls>0).map(|(op,s)|serde_json::json!({"op":op,"calls":s.calls,"max_heap":s.heap,"max_cells":s.cells,"max_prefix":s.prefix})).collect::<Vec<_>>()}) }).collect::<Vec<_>>();
    let sites = p.sites.iter().filter(|s| s.session != usize::MAX).map(|s|serde_json::json!({"session":s.session,"file":s.file,"line":s.line,"op":s.op,"calls":s.calls,"units":s.units,"failures":s.failures,"requested":s.requested})).collect::<Vec<_>>();
    let report = serde_json::json!({"sessions":sessions,"sites":sites,"overflow":p.overflow,"ops":["unclassified","state_copy","state_key","normalize","prune","copy_segment","requested_clause","discover_call","control_roots","build_graph","dispatch","unused"]});
    let text = report.to_string(); if text.len() <= 65536 { eprintln!("CAPTURE_CHARGE_PROFILE {text}"); } else { eprintln!("CAPTURE_CHARGE_PROFILE {{\"output_overflow\":true}}"); }
 });
    }
}
