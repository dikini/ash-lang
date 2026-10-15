//! Input-derived native-phase work allowances. These estimates grant no
//! authority: the existing cumulative checks may still exhaust their meter.

use crate::{module::ModuleId, source::SourceFile, types::TypeWorkBudget};
use std::sync::Arc;

const PREPARATION_PER_CELL: usize = 51;
const STARTUP_PER_BYTE: usize = 22;

fn preparation_total(source_bytes: usize, main_nodes: usize) -> Result<usize, ()> {
    source_bytes
        .checked_add(main_nodes)
        .and_then(|size| size.checked_mul(PREPARATION_PER_CELL))
        .ok_or(())
}

fn size_preparation(
    sources: &[(ModuleId, Arc<SourceFile>)],
    main_nodes: usize,
    work: &mut TypeWorkBudget,
) -> Result<usize, ()> {
    work.charge(1)?;
    let mut bytes = 0usize;
    for (_, source) in sources {
        work.charge(1)?;
        bytes = bytes.checked_add(source.text().len()).ok_or(())?;
    }
    preparation_total(bytes, main_nodes)
}

pub(super) fn preparation(
    sources: &[(ModuleId, Arc<SourceFile>)],
    main_nodes: usize,
) -> Result<TypeWorkBudget, ()> {
    // Both lengths are resident in the admitted compiler input. The finite
    // bootstrap pays the complete sizing loop before the total is admitted.
    let bootstrap = sources.len().checked_add(1).ok_or(())?;
    let mut work = TypeWorkBudget::with_limit(bootstrap);
    let total = size_preparation(sources, main_nodes, &mut work)?;
    work.finish_sizing(total)?;
    Ok(work)
}

pub(super) fn startup(image_bytes: usize, facts_bytes: usize) -> Result<TypeWorkBudget, ()> {
    let total = image_bytes
        .checked_add(facts_bytes)
        .and_then(|bytes| bytes.checked_mul(STARTUP_PER_BYTE))
        .ok_or(())?;
    // Private provisional framing allowance, not authenticated program gas.
    // The caller must finish paid decoding/end-of-input and canonical fact
    // comparison before restoration or native admission, in this SAME meter.
    Ok(TypeWorkBudget::with_limit(total))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_gas_sizing_is_checked_paid_and_carried() {
        let source =
            Arc::new(SourceFile::new("gas.ash", "main : Unit -> Int\nmain () = 42\n").unwrap());
        let sources = [(ModuleId::new(0), source)];
        let total = 51 * (sources[0].1.text().len() + 5);
        let admitted = preparation(&sources, 5).unwrap();
        assert_eq!((admitted.used(), admitted.limit()), (2, total));
        assert!(preparation(&[], 0).is_err());
        assert!(preparation_total(usize::MAX, 1).is_err());
        assert!(preparation_total(usize::MAX / 51 + 1, 0).is_err());
        assert!(startup(usize::MAX, 1).is_err());
        assert!(startup(usize::MAX / 22 + 1, 0).is_err());
        assert_eq!(startup(10, 20).unwrap().limit(), 660);
        assert_eq!(startup(0, 0).unwrap().limit(), 0);
        for prefix in [0, 11, 150] {
            for _ in 0..2 {
                let mut startup_work = startup(10, 20).unwrap();
                startup_work.charge(prefix).unwrap();
                startup_work.charge(660 - prefix - 1).unwrap();
                assert_eq!((startup_work.used(), startup_work.limit()), (659, 660));
                startup_work.charge(1).unwrap();
                assert!(startup_work.charge(1).is_err());
                assert_eq!((startup_work.used(), startup_work.limit()), (660, 660));
            }
            let mut short = TypeWorkBudget::with_limit(prefix + 1);
            short.charge(prefix).unwrap();
            assert!(size_preparation(&sources, 5, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + 2);
                exact.charge(prefix).unwrap();
                assert_eq!(size_preparation(&sources, 5, &mut exact).unwrap(), total);
                exact.finish_sizing(total).unwrap();
                assert_eq!(exact.used(), prefix + 2);
                exact.charge(exact.remaining()).unwrap();
                assert!(exact.charge(1).is_err());
            }
        }
        let mut spent = TypeWorkBudget::with_limit(10);
        spent.charge(10).unwrap();
        assert!(spent.finish_sizing(9).is_err());
        assert_eq!((spent.used(), spent.limit()), (10, 10));
    }
}
