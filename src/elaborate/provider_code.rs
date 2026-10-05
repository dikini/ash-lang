//! Temporary availability of original checked code during compiler preparation.
//!
//! This map does not grant provider authority. Instance preparation must match
//! the returned code against its independently admitted original certificate.
//! Nothing in this map is retained by an executable Core descriptor.

use std::{cell::RefCell, collections::HashMap, rc::Rc, sync::Arc};

type CheckedProviderCodes = HashMap<ModuleId, Arc<CheckedProviderGroup>>;

use super::{TypeError, invalid_state, provider::CheckedProviderGroup, type_resource};
use crate::{module::ModuleId, types::TypeWorkBudget};

#[derive(Debug, Default)]
pub(crate) struct ProviderCodeAvailability {
    codes: Option<Rc<RefCell<CheckedProviderCodes>>>,
}

impl ProviderCodeAvailability {
    /// Shares compiler preparation availability without copying the checked
    /// graph or constructing authority from its declarations.
    pub(crate) fn clone_with_budget(&self, work: &mut TypeWorkBudget) -> Result<Self, TypeError> {
        if let Some(codes) = &self.codes {
            work.charge(1).map_err(|()| type_resource())?;
            Ok(Self {
                codes: Some(Rc::clone(codes)),
            })
        } else {
            Ok(Self::default())
        }
    }

    /// The caller supplies a completed checked module's original code. A
    /// second route to that defining module must retain the same allocation.
    pub(crate) fn retain(
        &mut self,
        module: ModuleId,
        code: &Arc<CheckedProviderGroup>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        if code.module() != module || code.contracts().module() != module {
            return Err(invalid_state());
        }
        if self.codes.is_none() {
            work.charge(2).map_err(|()| type_resource())?;
            let mut codes = HashMap::new();
            codes.try_reserve(1).map_err(|_| type_resource())?;
            codes.insert(module, Arc::clone(code));
            self.codes = Some(Rc::new(RefCell::new(codes)));
            return Ok(());
        }
        let mut codes = self
            .codes
            .as_ref()
            .ok_or_else(invalid_state)?
            .try_borrow_mut()
            .map_err(|_| invalid_state())?;
        if let Some(previous) = codes.get(&module) {
            return if Arc::ptr_eq(previous, code) {
                Ok(())
            } else {
                Err(invalid_state())
            };
        }
        work.charge(1).map_err(|()| type_resource())?;
        codes.try_reserve(1).map_err(|_| type_resource())?;
        codes.insert(module, Arc::clone(code));
        Ok(())
    }

    /// Retains code for temporary specialization. Module lookup is merely
    /// availability; the consumer still authenticates the original contract.
    pub(crate) fn code(
        &self,
        module: ModuleId,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<Arc<CheckedProviderGroup>>, TypeError> {
        let Some(codes) = &self.codes else {
            return Ok(None);
        };
        work.charge(1).map_err(|()| type_resource())?;
        let codes = codes.try_borrow().map_err(|_| invalid_state())?;
        let Some(code) = codes.get(&module) else {
            return Ok(None);
        };
        work.charge(1).map_err(|()| type_resource())?;
        Ok(Some(Arc::clone(code)))
    }
}
