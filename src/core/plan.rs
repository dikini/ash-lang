//! Untrusted coordinates for one bounded, validator-owned ledger query.
//! These values are nominations, never prechecked summaries or permission.
use super::{
    DefinitionCandidate, InitializationConstructors, InitializationRole, NodeId,
    RegistrationConstructors, RegistrationDefinitions,
};
use super::{
    acknowledgement::{AcknowledgementConstructors, AcknowledgementDefinitions},
    closure::{ClosureConstructors, ClosureDefinitions},
    driver::{DriverNomination, ReceiveNomination},
    retirement::{RetirementConstructors, RetirementDefinitions},
};

pub(in crate::core) struct RegistrationNomination {
    pub(in crate::core) call: NodeId,
    pub(in crate::core) result_match: NodeId,
    pub(in crate::core) definitions: RegistrationDefinitions,
    pub(in crate::core) constructors: RegistrationConstructors,
}

pub(in crate::core) enum TransitionNomination {
    Closure {
        call: NodeId,
        definitions: ClosureDefinitions,
        constructors: ClosureConstructors,
    },
    Retirement {
        call: NodeId,
        definitions: RetirementDefinitions,
        constructors: RetirementConstructors,
    },
    Acknowledgement {
        call: NodeId,
        definitions: AcknowledgementDefinitions,
        constructors: AcknowledgementConstructors,
    },
}

pub(in crate::core) struct LedgerPlan<'a> {
    pub(in crate::core) owner: NodeId,
    pub(in crate::core) side: u8,
    pub(in crate::core) initialization_call: NodeId,
    pub(in crate::core) initialization: DefinitionCandidate,
    pub(in crate::core) initialization_constructors: InitializationConstructors,
    pub(in crate::core) initialization_role: InitializationRole,
    pub(in crate::core) initialization_binding: Option<NodeId>,
    pub(in crate::core) registrations: &'a [RegistrationNomination],
    pub(in crate::core) transitions: &'a [TransitionNomination],
    pub(in crate::core) drivers: &'a [DriverNomination<'a>],
    pub(in crate::core) receives: &'a [ReceiveNomination],
}
