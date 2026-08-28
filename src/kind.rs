//! Total kind synthesis for resolved monotypes.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::Deref,
};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    interface::InterfaceId,
    resolved::{
        CanonicalNominalKind, ResolvedConstructor, ResolvedDefinition, ResolvedDefinitionKind,
        ResolvedExpr, ResolvedExprKind, ResolvedImplementation, ResolvedInterfaceDeclaration,
        ResolvedLocalDeclaration, ResolvedModuleParts, ResolvedRecursiveMember, ResolvedRegistry,
        ResolvedRequirement, ResolvedType, ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
    },
    source::Span,
    types::{
        InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget,
        charge_kind_descendants, charge_kind_with_charge, clone_arrows_with_budget,
        clone_kind_with_budget, render_kind_with_budget, same_kind_with_budget,
        same_kind_with_charge,
    },
};

static TYPE_KIND: Kind = Kind::Type;

/// Minimal charging seam for the total kind-synthesis engine.
///
/// Resolved checking supplies [`TypeWorkBudget`]. Linked evidence validation
/// supplies its graph-wide constraint ledger without importing that layer into
/// the kind module.
pub(crate) trait KindWorkLedger {
    fn charge(&mut self, work: usize) -> Result<(), ()>;
}

impl KindWorkLedger for TypeWorkBudget {
    fn charge(&mut self, work: usize) -> Result<(), ()> {
        TypeWorkBudget::charge(self, work)
    }
}

enum SynthesisLedger<'a> {
    Resolved(&'a mut TypeWorkBudget),
    BodyFree(&'a mut dyn KindWorkLedger),
}

impl KindWorkLedger for SynthesisLedger<'_> {
    fn charge(&mut self, work: usize) -> Result<(), ()> {
        match self {
            Self::Resolved(budget) => budget.charge(work),
            Self::BodyFree(budget) => budget.charge(work),
        }
    }
}

impl SynthesisLedger<'_> {
    fn resolved_budget(&mut self, span: Span) -> Result<&mut TypeWorkBudget, KindFailure> {
        match self {
            Self::Resolved(budget) => Ok(*budget),
            Self::BodyFree(_) => Err(KindFailure::internal(
                span,
                "body-free kind synthesis attempted to retain a source diagnostic",
            )),
        }
    }
}

/// The semantic reason that prevented resolved kind checking.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KindReason {
    /// A value-type boundary received a constructor-kinded monotype.
    ExpectedType,
    /// An application function did not synthesize an arrow kind.
    NotApplicable,
    /// An application or interface argument had the wrong kind.
    Argument,
}

impl fmt::Display for KindReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ExpectedType => "kind.expected-type",
            Self::NotApplicable => "kind.not-applicable",
            Self::Argument => "kind.argument",
        })
    }
}

/// One structured failure from the resolved kind-checking stage.
#[derive(Debug, Eq, PartialEq)]
pub struct KindError {
    diagnostic: Diagnostic<KindReason>,
    expectation: KindExpectation,
    found: Option<Kind>,
}

/// The structured kind shape demanded by one source rule.
#[derive(Debug, Eq, PartialEq)]
pub enum KindExpectation {
    /// One exact semantic kind is required.
    Exact(Kind),
    /// An applicable kind with this exact domain is required; its codomain is existential.
    Function { domain: Kind },
}

impl KindError {
    /// Returns the structured diagnostic fields and causal labels.
    #[must_use]
    pub const fn diagnostic(&self) -> &Diagnostic<KindReason> {
        &self.diagnostic
    }

    /// Returns the expected semantic kind for a source kind mismatch.
    #[must_use]
    pub const fn expected_kind(&self) -> Option<&Kind> {
        match &self.expectation {
            KindExpectation::Exact(kind) => Some(kind),
            KindExpectation::Function { .. } => None,
        }
    }

    /// Returns the complete structured expectation, including existential function shape.
    #[must_use]
    pub const fn expectation(&self) -> &KindExpectation {
        &self.expectation
    }

    /// Returns the found semantic kind for a source kind mismatch.
    #[must_use]
    pub const fn found_kind(&self) -> Option<&Kind> {
        self.found.as_ref()
    }
}

impl Deref for KindError {
    type Target = Diagnostic<KindReason>;

    fn deref(&self) -> &Self::Target {
        self.diagnostic()
    }
}

impl fmt::Display for KindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.diagnostic.render_plain())
    }
}

impl std::error::Error for KindError {}

/// A failure from total resolved kind checking.
#[derive(Debug, Eq, PartialEq)]
pub enum KindFailure {
    /// Ash source violated one of the three kinding rules.
    Source(Box<KindError>),
    /// The stage exhausted its owning type-work ledger.
    Resource(KindStageFailure),
    /// Resolved input or a canonical kind environment was forged or incomplete.
    Internal(KindStageFailure),
}

impl KindFailure {
    fn resource(span: Span, message: impl Into<String>) -> Self {
        Self::Resource(KindStageFailure {
            span,
            message: message.into(),
        })
    }

    fn internal(span: Span, message: impl Into<String>) -> Self {
        Self::Internal(KindStageFailure {
            span,
            message: message.into(),
        })
    }

    /// Reports whether this is one of the three source-owned kind rejections.
    #[must_use]
    pub const fn is_source_rejection(&self) -> bool {
        matches!(self, Self::Source(_))
    }

    /// Returns the stage-stable reason code.
    #[must_use]
    pub fn reason_code(&self) -> String {
        match self {
            Self::Source(error) => error.reason.to_string(),
            Self::Resource(_) => "kind.resource-exhausted".into(),
            Self::Internal(_) => "kind.internal-state".into(),
        }
    }
}

impl fmt::Display for KindFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(error) => error.fmt(formatter),
            Self::Resource(failure) | Self::Internal(failure) => failure.fmt(formatter),
        }
    }
}

impl std::error::Error for KindFailure {}

/// Causal data for a non-source failure in the resolved kind stage.
#[derive(Debug, Eq, PartialEq)]
pub struct KindStageFailure {
    /// Source span whose resolved fact was being processed.
    pub span: Span,
    /// Stable stage-owned explanation.
    pub message: String,
}

impl fmt::Display for KindStageFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

#[derive(Clone, Copy)]
struct KindFact<'a> {
    kind: &'a Kind,
    retained_mirrors: Option<RetainedKindMirrors<'a>>,
    origin: Option<Span>,
    occurrence: Span,
}

#[derive(Clone, Copy)]
enum RetainedKindMirrors<'a> {
    Two(&'a Kind, &'a Kind),
}

struct NominalKindFact {
    kind: Kind,
    origin: Span,
}

#[derive(Clone, Copy)]
struct InterfaceKindFact<'a> {
    kind: &'a Kind,
    origin: Span,
}

/// Fixed kind environments used by the total synthesis judgment.
///
/// Resolved declaration checking leaves `omega` empty. Task 6 supplies fixed
/// inference entries to the same engine before inference variables enter a
/// type.
pub(crate) struct KindEnvironments<'a> {
    delta: HashMap<TypeVariableId, KindFact<'a>>,
    omega: HashMap<InferenceVariableId, KindFact<'a>>,
    xi: HashMap<NominalTypeId, NominalKindFact>,
    iota: HashMap<InterfaceId, InterfaceKindFact<'a>>,
}

impl<'a> KindEnvironments<'a> {
    pub(crate) fn new() -> Self {
        Self {
            delta: HashMap::new(),
            omega: HashMap::new(),
            xi: HashMap::new(),
            iota: HashMap::new(),
        }
    }

    pub(crate) fn contains_declared(&self, identity: TypeVariableId) -> bool {
        self.delta.contains_key(&identity)
    }

    pub(crate) fn contains_inference(&self, identity: InferenceVariableId) -> bool {
        self.omega.contains_key(&identity)
    }

    pub(crate) fn contains_nominal(&self, identity: NominalTypeId) -> bool {
        self.xi.contains_key(&identity)
    }

    pub(crate) fn insert_declared(
        &mut self,
        identity: TypeVariableId,
        kind: &'a Kind,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                origin,
                "declaration kind environment exceeded its type-work budget",
            )
        })?;
        if self.delta.contains_key(&identity) {
            return Err(KindFailure::internal(
                origin,
                "an owner binder list repeats a type-variable identity",
            ));
        }
        self.delta.try_reserve(1).map_err(|_| {
            KindFailure::resource(
                origin,
                "declaration kind environment could not reserve storage",
            )
        })?;
        self.delta.insert(
            identity,
            KindFact {
                kind,
                retained_mirrors: None,
                origin: Some(origin),
                occurrence: origin,
            },
        );
        Ok(())
    }

    fn clear_declared(&mut self) {
        self.delta.clear();
    }

    fn install_owner_parameters(
        &mut self,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.clear_declared();
        for parameter in parameters {
            self.insert_declared(
                parameter.id,
                &parameter.kind,
                parameter.origin.primary_span(),
                budget,
            )?;
        }
        Ok(())
    }

    fn install_owner_pairs(
        &mut self,
        parameters: &'a [(TypeVariableId, Kind)],
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.clear_declared();
        for (identity, kind) in parameters {
            self.insert_declared(*identity, kind, origin, budget)?;
        }
        Ok(())
    }

    /// Installs one linked owner's canonical binder identities in their retained
    /// order. The registry supplies the immutable defining kinds; no global
    /// type-variable map traversal or kind inference is involved.
    pub(crate) fn install_canonical_owner_ids(
        &mut self,
        registry: &'a crate::resolved::ResolvedRegistry,
        parameters: &[TypeVariableId],
        budget: &mut TypeWorkBudget,
        span: Span,
    ) -> Result<(), KindFailure> {
        self.clear_declared();
        for identity in parameters {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "linked owner-binder lookup exceeded its type-work budget",
                )
            })?;
            let parameter = registry.type_variable(*identity).ok_or_else(|| {
                KindFailure::internal(span, "a linked owner binder has no canonical registry fact")
            })?;
            self.insert_declared(
                *identity,
                &parameter.kind,
                parameter.origin.primary_span(),
                budget,
            )?;
        }
        Ok(())
    }

    /// Installs checked and source implementation-head record mirrors together.
    pub(crate) fn install_canonical_owner_records_with_source(
        &mut self,
        registry: &'a crate::resolved::ResolvedRegistry,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        source_parameters: &'a [crate::resolved::ResolvedTypeVariable],
        budget: &mut TypeWorkBudget,
        span: Span,
    ) -> Result<(), KindFailure> {
        if parameters.len() != source_parameters.len() {
            return Err(KindFailure::internal(
                span,
                "linked implementation-head mirrors retain different binder counts",
            ));
        }
        self.clear_declared();
        for (parameter, source) in parameters.iter().zip(source_parameters) {
            if parameter.id != source.id {
                return Err(KindFailure::internal(
                    span,
                    "linked implementation-head mirrors retain different binder identities",
                ));
            }
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "linked owner-binder lookup exceeded its type-work budget",
                )
            })?;
            let canonical = registry.type_variable(parameter.id).ok_or_else(|| {
                KindFailure::internal(span, "a linked owner binder has no canonical registry fact")
            })?;
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "declaration kind environment exceeded its type-work budget",
                )
            })?;
            if self.delta.contains_key(&parameter.id) {
                return Err(KindFailure::internal(
                    span,
                    "an owner binder list repeats a type-variable identity",
                ));
            }
            self.delta.try_reserve(1).map_err(|_| {
                KindFailure::resource(
                    span,
                    "declaration kind environment could not reserve storage",
                )
            })?;
            self.delta.insert(
                parameter.id,
                KindFact {
                    kind: &canonical.kind,
                    retained_mirrors: Some(RetainedKindMirrors::Two(&parameter.kind, &source.kind)),
                    origin: Some(canonical.origin.primary_span()),
                    occurrence: span,
                },
            );
        }
        Ok(())
    }

    /// Installs a checked scheme pair plus the independently retained source
    /// binder Kind. Both mirrors are authenticated against the canonical
    /// registry Kind when the binder occurs in the paired value type.
    pub(crate) fn install_canonical_owner_pairs_with_source(
        &mut self,
        registry: &'a crate::resolved::ResolvedRegistry,
        parameters: &'a [(TypeVariableId, Kind)],
        source_parameters: &'a [crate::resolved::ResolvedTypeVariable],
        budget: &mut TypeWorkBudget,
        span: Span,
    ) -> Result<(), KindFailure> {
        if parameters.len() != source_parameters.len() {
            return Err(KindFailure::internal(
                span,
                "a linked source and checked scheme retain different binder counts",
            ));
        }
        self.clear_declared();
        for ((identity, retained_kind), source) in parameters.iter().zip(source_parameters) {
            if *identity != source.id {
                return Err(KindFailure::internal(
                    span,
                    "a linked source and checked scheme retain different binder identities",
                ));
            }
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "linked owner-binder lookup exceeded its type-work budget",
                )
            })?;
            let parameter = registry.type_variable(*identity).ok_or_else(|| {
                KindFailure::internal(span, "a linked owner binder has no canonical registry fact")
            })?;
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "declaration kind environment exceeded its type-work budget",
                )
            })?;
            if self.delta.contains_key(identity) {
                return Err(KindFailure::internal(
                    span,
                    "an owner binder list repeats a type-variable identity",
                ));
            }
            self.delta.try_reserve(1).map_err(|_| {
                KindFailure::resource(
                    span,
                    "declaration kind environment could not reserve storage",
                )
            })?;
            self.delta.insert(
                *identity,
                KindFact {
                    kind: &parameter.kind,
                    retained_mirrors: Some(RetainedKindMirrors::Two(retained_kind, &source.kind)),
                    origin: Some(parameter.origin.primary_span()),
                    occurrence: span,
                },
            );
        }
        Ok(())
    }

    pub(crate) fn insert_inference(
        &mut self,
        identity: InferenceVariableId,
        kind: &'a Kind,
        origin: Option<Span>,
        budget: &mut TypeWorkBudget,
        causal_span: Span,
    ) -> Result<(), KindFailure> {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                causal_span,
                "inference kind environment exceeded its type-work budget",
            )
        })?;
        if self.omega.contains_key(&identity) {
            return Err(KindFailure::internal(
                causal_span,
                "an inference variable has more than one fixed kind",
            ));
        }
        self.omega.try_reserve(1).map_err(|_| {
            KindFailure::resource(
                causal_span,
                "inference kind environment could not reserve storage",
            )
        })?;
        if self
            .omega
            .insert(
                identity,
                KindFact {
                    kind,
                    retained_mirrors: None,
                    origin,
                    occurrence: causal_span,
                },
            )
            .is_some()
        {
            return Err(KindFailure::internal(
                causal_span,
                "an inference variable has more than one fixed kind",
            ));
        }
        Ok(())
    }

    /// Synthesizes a monotype kind against fixed environments without source
    /// provenance. Malformed types therefore remain internal-stage failures.
    pub(crate) fn synthesize_body_free_kind<'environment>(
        &'environment self,
        ty: &Type,
        fallback_span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<&'environment Kind, KindFailure>
    where
        'a: 'environment,
    {
        self.synthesize(ty, None, fallback_span, budget)
            .map(|fact| fact.kind)
    }

    /// Checks one inference-free monotype against an exact canonical kind,
    /// charging synthesis and comparison to the operation that owns the
    /// semantic comparison.
    pub(crate) fn expect_body_free_exact_kind_with_ledger(
        &self,
        ty: &Type,
        expected: &Kind,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found =
            self.synthesize_with_ledger(ty, None, None, None, None, None, span, &mut ledger)?;
        let equal =
            same_kind_with_charge(expected, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free exact-kind authentication exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free monotype has the wrong canonical kind",
            ))
        }
    }

    /// Checks a body-free linked value monotype with traversal and Kind
    /// comparison charged to the caller's owning ledger.
    pub(crate) fn expect_body_free_value_type_with_ledger(
        &self,
        ty: &Type,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found =
            self.synthesize_with_ledger(ty, None, None, None, None, None, span, &mut ledger)?;
        let equal =
            same_kind_with_charge(&TYPE_KIND, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free value kind checking exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free value scheme does not end at kind Type",
            ))
        }
    }

    /// Checks a physical body-free constructor scheme while authenticating
    /// its independently retained payload against the outer function domain
    /// in the same Kind-synthesis walk.
    pub(crate) fn expect_body_free_constructor_value_type_with_ledger(
        &self,
        value_type: &Type,
        payload: Option<&Type>,
        owner_parameters: &[crate::resolved::ResolvedTypeVariable],
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let root_domain_mirror = match (payload, value_type) {
            (Some(payload), Type::Function(_, _)) => Some(payload),
            (None, _) => None,
            (Some(_), _) => {
                return Err(KindFailure::internal(
                    span,
                    "a payload constructor scheme does not have an outer function",
                ));
            }
        };
        budget.charge(owner_parameters.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "body-free constructor owner-variable storage exceeded its owning work budget",
            )
        })?;
        let mut allowed_variables = HashSet::new();
        allowed_variables
            .try_reserve(owner_parameters.len())
            .map_err(|_| {
                KindFailure::resource(
                    span,
                    "body-free constructor owner-variable storage could not reserve capacity",
                )
            })?;
        allowed_variables.extend(owner_parameters.iter().map(|parameter| parameter.id));
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found = self.synthesize_with_ledger(
            value_type,
            None,
            None,
            root_domain_mirror,
            Some(&allowed_variables),
            None,
            span,
            &mut ledger,
        )?;
        let equal =
            same_kind_with_charge(&TYPE_KIND, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free constructor kind checking exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free constructor scheme does not end at kind Type",
            ))
        }
    }

    /// Checks one body-free interface method in a single type walk. The
    /// method must be a function, may mention only its owning interface
    /// parameter and declared method parameters, must mention the interface
    /// parameter, and must end at kind `Type`.
    pub(crate) fn expect_body_free_interface_method_with_ledger(
        &self,
        ty: &Type,
        parameter: TypeVariableId,
        method_parameters: &[TypeVariableId],
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        if !matches!(ty, Type::Function(_, _)) {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface method is not a function",
            ));
        }
        let parameter_count = method_parameters.len().checked_add(1).ok_or_else(|| {
            KindFailure::resource(
                span,
                "body-free interface-method variable count exceeded its owning work budget",
            )
        })?;
        let retained_work = parameter_count.checked_mul(2).ok_or_else(|| {
            KindFailure::resource(
                span,
                "body-free interface-method variable work exceeded its owning budget",
            )
        })?;
        budget.charge(retained_work).map_err(|()| {
            KindFailure::resource(
                span,
                "body-free interface-method variable storage exceeded its owning work budget",
            )
        })?;
        let mut allowed = HashSet::new();
        allowed.try_reserve(parameter_count).map_err(|_| {
            KindFailure::resource(
                span,
                "body-free interface-method variable storage could not reserve capacity",
            )
        })?;
        allowed.insert(parameter);
        for method_parameter in method_parameters {
            if !allowed.insert(*method_parameter) {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface method repeats a type parameter",
                ));
            }
        }
        let mut visited = HashSet::new();
        visited.try_reserve(parameter_count).map_err(|_| {
            KindFailure::resource(
                span,
                "body-free interface-method coverage could not reserve capacity",
            )
        })?;
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found = self.synthesize_with_ledger(
            ty,
            None,
            None,
            None,
            Some(&allowed),
            Some(&mut visited),
            span,
            &mut ledger,
        )?;
        if visited.len() != parameter_count
            || !visited.contains(&parameter)
            || method_parameters
                .iter()
                .any(|method_parameter| !visited.contains(method_parameter))
        {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface method does not use exactly its declared parameters",
            ));
        }
        let equal =
            same_kind_with_charge(&TYPE_KIND, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free interface-method kind checking exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free interface method does not end at kind Type",
            ))
        }
    }

    /// Checks a linked checked value type together with its retained source
    /// type, and requires every installed owner binder to occur. Structural
    /// comparison is fused into kind synthesis so no second deep type walk is
    /// retained.
    pub(crate) fn expect_body_free_paired_value_type_with_ledger(
        &self,
        checked: &Type,
        source: &Type,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let mut visited = HashSet::new();
        budget.charge(self.delta.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "linked owner-binder coverage exceeded its owning work budget",
            )
        })?;
        visited.try_reserve(self.delta.len()).map_err(|_| {
            KindFailure::resource(
                span,
                "linked owner-binder coverage could not reserve storage",
            )
        })?;
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found = self.synthesize_with_ledger(
            checked,
            None,
            Some(source),
            None,
            None,
            Some(&mut visited),
            span,
            &mut ledger,
        )?;
        if visited.len() != self.delta.len() {
            return Err(KindFailure::internal(
                span,
                "a linked value scheme retains an unused owner binder",
            ));
        }
        let equal =
            same_kind_with_charge(&TYPE_KIND, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free value kind checking exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free value scheme does not end at kind Type",
            ))
        }
    }

    /// Checks one checked value type and requires every installed Kind mirror
    /// to be exercised by an owner-binder occurrence.
    pub(crate) fn expect_body_free_exact_owner_value_type_with_ledger(
        &self,
        ty: &Type,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let mut visited = HashSet::new();
        budget.charge(self.delta.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "linked owner-binder coverage exceeded its owning work budget",
            )
        })?;
        visited.try_reserve(self.delta.len()).map_err(|_| {
            KindFailure::resource(
                span,
                "linked owner-binder coverage could not reserve storage",
            )
        })?;
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found = self.synthesize_with_ledger(
            ty,
            None,
            None,
            None,
            None,
            Some(&mut visited),
            span,
            &mut ledger,
        )?;
        if visited.len() != self.delta.len() {
            return Err(KindFailure::internal(
                span,
                "a linked value scheme retains an unused owner binder",
            ));
        }
        let equal =
            same_kind_with_charge(&TYPE_KIND, found.kind, || ledger.charge(1)).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free value kind checking exceeded its owning work budget",
                )
            })?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free value scheme does not end at kind Type",
            ))
        }
    }

    pub(crate) fn insert_nominal(
        &mut self,
        identity: NominalTypeId,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        if self.xi.contains_key(&identity) {
            charge_lookup_attempt(origin, budget)?;
            return Err(KindFailure::internal(
                origin,
                "a nominal type has more than one canonical kind",
            ));
        }

        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                origin,
                "nominal environment-record retention exceeded its type-work budget",
            )
        })?;
        self.xi.try_reserve(1).map_err(|_| {
            KindFailure::resource(origin, "nominal kind environment could not reserve storage")
        })?;
        let kind = clone_arrows_with_budget(
            parameters.iter().map(|parameter| &parameter.kind),
            Kind::Type,
            budget,
        )
        .map_err(|()| {
            KindFailure::resource(
                origin,
                "nominal kind retention exceeded its type-work budget",
            )
        })?;
        self.xi.insert(identity, NominalKindFact { kind, origin });
        Ok(())
    }

    pub(crate) fn insert_frozen_nominal(
        &mut self,
        identity: NominalTypeId,
        kind: &Kind,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        if self.xi.contains_key(&identity) {
            charge_lookup_attempt(origin, budget)?;
            return Err(KindFailure::internal(
                origin,
                "a nominal type has more than one canonical kind",
            ));
        }

        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                origin,
                "nominal environment-record retention exceeded its type-work budget",
            )
        })?;
        self.xi.try_reserve(1).map_err(|_| {
            KindFailure::resource(origin, "nominal kind environment could not reserve storage")
        })?;
        let kind = clone_kind_with_budget(kind, budget).map_err(|()| {
            KindFailure::resource(
                origin,
                "nominal kind retention exceeded its type-work budget",
            )
        })?;
        self.xi.insert(identity, NominalKindFact { kind, origin });
        Ok(())
    }

    pub(crate) fn insert_interface(
        &mut self,
        identity: InterfaceId,
        kind: &'a Kind,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                origin,
                "interface kind environment exceeded its type-work budget",
            )
        })?;
        if let Some(existing) = self.iota.get(&identity) {
            let equal = same_kind_with_budget(existing.kind, kind, budget).map_err(|()| {
                KindFailure::resource(
                    origin,
                    "interface kind authentication exceeded its type-work budget",
                )
            })?;
            if !equal || existing.origin != origin {
                return Err(KindFailure::internal(
                    origin,
                    "an interface has conflicting canonical parameter kinds",
                ));
            }
            return Ok(());
        }
        self.iota.try_reserve(1).map_err(|_| {
            KindFailure::resource(
                origin,
                "interface kind environment could not reserve storage",
            )
        })?;
        self.iota
            .insert(identity, InterfaceKindFact { kind, origin });
        Ok(())
    }

    pub(crate) fn expect_requirement(
        &self,
        interface: InterfaceId,
        argument: &ResolvedType,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        let Some(expected) = self.iota.get(&interface) else {
            charge_lookup_attempt(argument.span, budget)?;
            return Err(KindFailure::internal(
                argument.span,
                "an interface occurrence has no canonical parameter kind",
            ));
        };
        self.expect_interface_argument(argument, expected.kind, expected.origin, budget)
    }

    pub(crate) fn expect_value_type(
        &self,
        resolved: &ResolvedType,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.expect_value_type_parts(&resolved.ty, &resolved.provenance, resolved.span, budget)
    }

    pub(crate) fn expect_value_type_parts(
        &self,
        ty: &Type,
        provenance: &ResolvedTypeProvenance,
        span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        let found = self.synthesize(ty, Some(provenance), span, budget)?;
        let equal = same_kind_with_budget(&TYPE_KIND, found.kind, budget).map_err(|()| {
            KindFailure::resource(
                span,
                "value-type kind checking exceeded its type-work budget",
            )
        })?;
        if equal {
            return Ok(());
        }
        Err(KindFailure::Source(Box::new(structured_error(
            KindReason::ExpectedType,
            found.occurrence,
            "this value type must have kind Type",
            &TYPE_KIND,
            found.kind,
            found
                .origin
                .map(|origin| (origin, "the found kind is fixed by this declaration")),
            budget,
        )?)))
    }

    pub(crate) fn expect_interface_argument(
        &self,
        argument: &ResolvedType,
        expected: &'a Kind,
        expected_origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        let found = self.synthesize(
            &argument.ty,
            Some(&argument.provenance),
            argument.span,
            budget,
        )?;
        let equal = same_kind_with_budget(expected, found.kind, budget).map_err(|()| {
            KindFailure::resource(
                argument.span,
                "interface-argument kind checking exceeded its type-work budget",
            )
        })?;
        if equal {
            return Ok(());
        }
        Err(KindFailure::Source(Box::new(structured_error(
            KindReason::Argument,
            argument.span,
            "this interface argument has the wrong kind",
            expected,
            found.kind,
            Some((
                expected_origin,
                "the interface parameter kind is declared here",
            )),
            budget,
        )?)))
    }

    fn expect_body_free_value_type(
        &self,
        ty: &Type,
        span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        let found = self.synthesize(ty, None, span, budget)?;
        let equal = same_kind_with_budget(&TYPE_KIND, found.kind, budget).map_err(|()| {
            KindFailure::resource(
                span,
                "body-free value kind checking exceeded its type-work budget",
            )
        })?;
        if equal {
            return Ok(());
        }
        Err(KindFailure::internal(
            span,
            "a checked body-free value scheme does not end at kind Type",
        ))
    }

    pub(crate) fn expect_body_free_interface_argument_with_ledger(
        &self,
        interface: InterfaceId,
        ty: &Type,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let Some(expected) = self.iota.get(&interface) else {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free interface-kind lookup exceeded its owning work budget",
                )
            })?;
            return Err(KindFailure::internal(
                span,
                "a body-free interface occurrence has no canonical parameter kind",
            ));
        };
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found =
            self.synthesize_with_ledger(ty, None, None, None, None, None, span, &mut ledger)?;
        let equal = same_kind_with_charge(expected.kind, found.kind, || ledger.charge(1)).map_err(
            |()| {
                KindFailure::resource(
                    span,
                    "body-free interface kind authentication exceeded its owning work budget",
                )
            },
        )?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free interface argument has the wrong kind",
            ))
        }
    }

    /// Checks an implementation head and proves that every installed rigid
    /// owner binder occurs in the authenticated head argument.
    pub(crate) fn expect_body_free_exact_owner_interface_argument_with_ledger(
        &self,
        interface: InterfaceId,
        ty: &Type,
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        let Some(expected) = self.iota.get(&interface) else {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "body-free interface-kind lookup exceeded its owning work budget",
                )
            })?;
            return Err(KindFailure::internal(
                span,
                "a body-free interface occurrence has no canonical parameter kind",
            ));
        };
        let mut visited = HashSet::new();
        budget.charge(self.delta.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "linked implementation-head coverage exceeded its owning work budget",
            )
        })?;
        visited.try_reserve(self.delta.len()).map_err(|_| {
            KindFailure::resource(
                span,
                "linked implementation-head coverage could not reserve storage",
            )
        })?;
        let mut ledger = SynthesisLedger::BodyFree(budget);
        let found = self.synthesize_with_ledger(
            ty,
            None,
            None,
            None,
            None,
            Some(&mut visited),
            span,
            &mut ledger,
        )?;
        if visited.len() != self.delta.len() {
            return Err(KindFailure::internal(
                span,
                "a linked implementation head retains an unused rigid binder",
            ));
        }
        let equal = same_kind_with_charge(expected.kind, found.kind, || ledger.charge(1)).map_err(
            |()| {
                KindFailure::resource(
                    span,
                    "body-free interface kind authentication exceeded its owning work budget",
                )
            },
        )?;
        if equal {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "a checked body-free interface argument has the wrong kind",
            ))
        }
    }

    fn expect_body_free_interface_argument(
        &self,
        interface: InterfaceId,
        ty: &Type,
        span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.expect_body_free_interface_argument_with_ledger(interface, ty, span, budget)
    }

    fn synthesize<'environment>(
        &'environment self,
        ty: &Type,
        provenance: Option<&ResolvedTypeProvenance>,
        fallback_span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<KindFact<'environment>, KindFailure>
    where
        'a: 'environment,
    {
        let mut ledger = SynthesisLedger::Resolved(budget);
        self.synthesize_with_ledger(
            ty,
            provenance,
            None,
            None,
            None,
            None,
            fallback_span,
            &mut ledger,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn synthesize_with_ledger<'environment>(
        &'environment self,
        ty: &Type,
        provenance: Option<&ResolvedTypeProvenance>,
        type_mirror: Option<&Type>,
        root_function_domain_mirror: Option<&Type>,
        allowed_variables: Option<&HashSet<TypeVariableId>>,
        mut visited_variables: Option<&mut HashSet<TypeVariableId>>,
        fallback_span: Span,
        budget: &mut SynthesisLedger<'_>,
    ) -> Result<KindFact<'environment>, KindFailure>
    where
        'a: 'environment,
    {
        enum State<'t, 'kind> {
            Visit(&'t Type, Option<&'t Type>, Option<usize>),
            Complete(KindFact<'kind>),
        }

        enum Continuation<'t, 'kind> {
            ApplicationFunction {
                argument: &'t Type,
                argument_mirror: Option<&'t Type>,
                argument_root: Option<usize>,
                span: Span,
                argument_span: Span,
            },
            ApplicationArgument {
                function: KindFact<'kind>,
                span: Span,
                argument_span: Span,
            },
            Tuple {
                remaining: std::slice::Iter<'t, Type>,
                remaining_mirrors: Option<std::slice::Iter<'t, Type>>,
                roots: Option<std::slice::Iter<'t, usize>>,
                span: Span,
            },
            FunctionDomain {
                codomain: &'t Type,
                codomain_mirror: Option<&'t Type>,
                codomain_root: Option<usize>,
                span: Span,
            },
            FunctionCodomain {
                span: Span,
            },
        }

        macro_rules! push_continuation {
            ($work:expr, $task:expr, $span:expr) => {{
                budget.charge(1).map_err(|()| {
                    KindFailure::resource(
                        $span,
                        "kind-synthesis continuation retention exceeded its owning work budget",
                    )
                })?;
                $work.try_reserve(1).map_err(|_| {
                    KindFailure::resource(
                        $span,
                        "kind-synthesis continuation retention could not reserve storage",
                    )
                })?;
                $work.push($task);
            }};
        }

        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                fallback_span,
                "kind-synthesis current-state retention exceeded its owning work budget",
            )
        })?;
        let mut current = State::Visit(
            ty,
            type_mirror,
            provenance.map(ResolvedTypeProvenance::root),
        );
        let mut root_function_domain_mirror = root_function_domain_mirror;
        let mut at_root = true;
        let mut work = Vec::<Continuation<'_, 'environment>>::new();
        loop {
            current = match current {
                State::Visit(ty, type_mirror, root) => {
                    let domain_override = if at_root {
                        at_root = false;
                        root_function_domain_mirror.take()
                    } else {
                        None
                    };
                    let node = match (provenance, root) {
                        (Some(provenance), Some(root)) => {
                            let Some(node) = provenance.nodes().get(root) else {
                                charge_lookup_attempt(fallback_span, budget)?;
                                return Err(KindFailure::internal(
                                    fallback_span,
                                    "a resolved type has invalid provenance",
                                ));
                            };
                            Some(node)
                        }
                        (None, None) => None,
                        _ => {
                            charge_lookup_attempt(fallback_span, budget)?;
                            return Err(KindFailure::internal(
                                fallback_span,
                                "a resolved type has mismatched provenance ownership",
                            ));
                        }
                    };
                    let span = node.map_or(fallback_span, provenance_node_span);
                    match ty {
                        Type::Int | Type::Bool | Type::Unit => {
                            charge_synthesis_cell(span, budget)?;
                            let mirror_matches = matches!(
                                (ty, type_mirror),
                                (Type::Int, None | Some(Type::Int))
                                    | (Type::Bool, None | Some(Type::Bool))
                                    | (Type::Unit, None | Some(Type::Unit))
                            );
                            if !mirror_matches {
                                return Err(KindFailure::internal(
                                    span,
                                    "a linked source type does not match its checked value type",
                                ));
                            }
                            require_fact_node(node, span, budget)?;
                            State::Complete(KindFact {
                                kind: &TYPE_KIND,
                                retained_mirrors: None,
                                origin: None,
                                occurrence: span,
                            })
                        }
                        Type::Variable(identity) => {
                            if type_mirror
                                .is_some_and(|mirror| !matches!(mirror, Type::Variable(found) if found == identity))
                            {
                                charge_lookup_attempt(span, budget)?;
                                return Err(KindFailure::internal(
                                    span,
                                    "a linked source type does not match its checked value type",
                                ));
                            }
                            require_fact_node(node, span, budget)?;
                            charge_lookup_attempt(span, budget)?;
                            if allowed_variables.is_some_and(|allowed| !allowed.contains(identity))
                            {
                                return Err(KindFailure::internal(
                                    span,
                                    "a body-free constructor scheme references a non-owner variable",
                                ));
                            }
                            if let Some(visited) = visited_variables.as_deref_mut() {
                                visited.insert(*identity);
                            }
                            let mut fact = *self.delta.get(identity).ok_or_else(|| {
                                KindFailure::internal(
                                    span,
                                    "a resolved type variable has no canonical kind",
                                )
                            })?;
                            authenticate_kind_descendants_with_ledger(
                                fact.kind,
                                fact.retained_mirrors,
                                budget,
                            )
                            .map_err(|failure| {
                                match failure {
                                    LinkedKindMirrorFailure::Resource => KindFailure::resource(
                                        span,
                                        "declaration kind lookup exceeded its type-work budget",
                                    ),
                                    LinkedKindMirrorFailure::Mismatch => KindFailure::internal(
                                        span,
                                        "a linked retained binder Kind does not match its canonical registry fact",
                                    ),
                                }
                            })?;
                            fact.occurrence = span;
                            State::Complete(fact)
                        }
                        Type::Inference(identity) => {
                            if type_mirror
                                .is_some_and(|mirror| !matches!(mirror, Type::Inference(found) if found == identity))
                            {
                                charge_lookup_attempt(span, budget)?;
                                return Err(KindFailure::internal(
                                    span,
                                    "a linked source type does not match its checked value type",
                                ));
                            }
                            require_fact_node(node, span, budget)?;
                            charge_lookup_attempt(span, budget)?;
                            let mut fact = *self.omega.get(identity).ok_or_else(|| {
                                KindFailure::internal(
                                    span,
                                    "an inference variable has no fixed kind",
                                )
                            })?;
                            charge_kind_descendants_with_ledger(fact.kind, budget).map_err(
                                |()| {
                                    KindFailure::resource(
                                        span,
                                        "inference kind lookup exceeded its type-work budget",
                                    )
                                },
                            )?;
                            fact.occurrence = span;
                            State::Complete(fact)
                        }
                        Type::Nominal(identity) => {
                            if type_mirror
                                .is_some_and(|mirror| !matches!(mirror, Type::Nominal(found) if found == identity))
                            {
                                charge_lookup_attempt(span, budget)?;
                                return Err(KindFailure::internal(
                                    span,
                                    "a linked source type does not match its checked value type",
                                ));
                            }
                            require_fact_node(node, span, budget)?;
                            charge_lookup_attempt(span, budget)?;
                            let fact = self.xi.get(identity).ok_or_else(|| {
                                KindFailure::internal(span, "a nominal type has no canonical kind")
                            })?;
                            charge_kind_descendants_with_ledger(&fact.kind, budget).map_err(
                                |()| {
                                    KindFailure::resource(
                                        span,
                                        "nominal kind lookup exceeded its type-work budget",
                                    )
                                },
                            )?;
                            State::Complete(KindFact {
                                kind: &fact.kind,
                                retained_mirrors: None,
                                origin: Some(fact.origin),
                                occurrence: span,
                            })
                        }
                        Type::Tuple(elements) => {
                            charge_synthesis_cell(span, budget)?;
                            let mirror_elements = match type_mirror {
                                None => None,
                                Some(Type::Tuple(mirrors)) if mirrors.len() == elements.len() => {
                                    Some(mirrors)
                                }
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a linked source type does not match its checked value type",
                                    ));
                                }
                            };
                            let roots = match node {
                                Some(ResolvedTypeProvenanceNode::Tuple { elements, .. }) => {
                                    Some(elements.iter())
                                }
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a resolved tuple has non-tuple provenance",
                                    ));
                                }
                                None => None,
                            };
                            if roots
                                .as_ref()
                                .is_some_and(|roots| elements.len() != roots.len())
                            {
                                return Err(KindFailure::internal(
                                    span,
                                    "a resolved tuple has incomplete provenance",
                                ));
                            }
                            let mut remaining = elements.iter();
                            let mut remaining_mirrors =
                                mirror_elements.map(|mirrors| mirrors.iter());
                            let mut roots = roots;
                            if let Some(first) = remaining.next() {
                                let first_mirror =
                                    remaining_mirrors.as_mut().and_then(Iterator::next);
                                let first_root = roots.as_mut().and_then(Iterator::next).copied();
                                if provenance.is_some() && first_root.is_none() {
                                    charge_lookup_attempt(span, budget)?;
                                    return Err(KindFailure::internal(
                                        span,
                                        "a resolved tuple has incomplete child provenance",
                                    ));
                                }
                                push_continuation!(
                                    work,
                                    Continuation::Tuple {
                                        remaining,
                                        remaining_mirrors,
                                        roots,
                                        span,
                                    },
                                    span
                                );
                                State::Visit(first, first_mirror, first_root)
                            } else {
                                State::Complete(KindFact {
                                    kind: &TYPE_KIND,
                                    retained_mirrors: None,
                                    origin: None,
                                    occurrence: span,
                                })
                            }
                        }
                        Type::Application(function, argument) => {
                            charge_synthesis_cell(span, budget)?;
                            let (function_mirror, argument_mirror) = match type_mirror {
                                None => (None, None),
                                Some(Type::Application(function, argument)) => {
                                    (Some(function.as_ref()), Some(argument.as_ref()))
                                }
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a linked source type does not match its checked value type",
                                    ));
                                }
                            };
                            let (function_root, argument_root, argument_span) = match node {
                                Some(ResolvedTypeProvenanceNode::Application {
                                    function,
                                    argument,
                                    argument_span,
                                    ..
                                }) => (Some(*function), Some(*argument), *argument_span),
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a resolved application has non-application provenance",
                                    ));
                                }
                                None => (None, None, span),
                            };
                            push_continuation!(
                                work,
                                Continuation::ApplicationFunction {
                                    argument,
                                    argument_mirror,
                                    argument_root,
                                    span,
                                    argument_span,
                                },
                                span
                            );
                            State::Visit(function, function_mirror, function_root)
                        }
                        Type::Function(domain, codomain) => {
                            charge_synthesis_cell(span, budget)?;
                            let (mut domain_mirror, codomain_mirror) = match type_mirror {
                                None => (None, None),
                                Some(Type::Function(domain, codomain)) => {
                                    (Some(domain.as_ref()), Some(codomain.as_ref()))
                                }
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a linked source type does not match its checked value type",
                                    ));
                                }
                            };
                            if domain_override.is_some() {
                                if domain_mirror.is_some() {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a linked constructor domain has two retained mirrors",
                                    ));
                                }
                                domain_mirror = domain_override;
                            }
                            let (domain_root, codomain_root) = match node {
                                Some(ResolvedTypeProvenanceNode::Function {
                                    domain,
                                    codomain,
                                    ..
                                }) => (Some(*domain), Some(*codomain)),
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a resolved function has non-function provenance",
                                    ));
                                }
                                None => (None, None),
                            };
                            push_continuation!(
                                work,
                                Continuation::FunctionDomain {
                                    codomain,
                                    codomain_mirror,
                                    codomain_root,
                                    span,
                                },
                                span
                            );
                            State::Visit(domain, domain_mirror, domain_root)
                        }
                        Type::Forall(_, _) => {
                            charge_synthesis_cell(span, budget)?;
                            if type_mirror
                                .is_some_and(|mirror| !matches!(mirror, Type::Forall(_, _)))
                            {
                                return Err(KindFailure::internal(
                                    span,
                                    "a linked source type does not match its checked value type",
                                ));
                            }
                            return Err(KindFailure::internal(
                                span,
                                "a rank-1 scheme entered the resolved monotype kind judgment",
                            ));
                        }
                    }
                }
                State::Complete(found) => {
                    let Some(continuation) = work.pop() else {
                        return Ok(found);
                    };
                    match continuation {
                        Continuation::Tuple {
                            mut remaining,
                            mut remaining_mirrors,
                            mut roots,
                            span,
                        } => {
                            let equal =
                                same_kind_with_charge(&TYPE_KIND, found.kind, || budget.charge(1))
                                    .map_err(|()| {
                                        KindFailure::resource(
                                            found.occurrence,
                                            "tuple kind checking exceeded its type-work budget",
                                        )
                                    })?;
                            if !equal {
                                if provenance.is_none() {
                                    return Err(KindFailure::internal(
                                        found.occurrence,
                                        "a checked body-free tuple element has the wrong kind",
                                    ));
                                }
                                let diagnostic_budget = budget.resolved_budget(found.occurrence)?;
                                return Err(KindFailure::Source(Box::new(structured_error(
                                    KindReason::ExpectedType,
                                    found.occurrence,
                                    "a tuple element must have kind Type",
                                    &TYPE_KIND,
                                    found.kind,
                                    found.origin.map(|origin| {
                                        (origin, "the found kind is fixed by this declaration")
                                    }),
                                    diagnostic_budget,
                                )?)));
                            }
                            if let Some(next) = remaining.next() {
                                let next_mirror =
                                    remaining_mirrors.as_mut().and_then(Iterator::next);
                                let root = roots.as_mut().and_then(Iterator::next).copied();
                                if provenance.is_some() && root.is_none() {
                                    charge_lookup_attempt(span, budget)?;
                                    return Err(KindFailure::internal(
                                        span,
                                        "a resolved tuple has incomplete child provenance",
                                    ));
                                }
                                work.push(Continuation::Tuple {
                                    remaining,
                                    remaining_mirrors,
                                    roots,
                                    span,
                                });
                                State::Visit(next, next_mirror, root)
                            } else {
                                State::Complete(KindFact {
                                    kind: &TYPE_KIND,
                                    retained_mirrors: None,
                                    origin: None,
                                    occurrence: span,
                                })
                            }
                        }
                        Continuation::ApplicationFunction {
                            argument,
                            argument_mirror,
                            argument_root,
                            span,
                            argument_span,
                        } => {
                            work.push(Continuation::ApplicationArgument {
                                function: found,
                                span,
                                argument_span,
                            });
                            State::Visit(argument, argument_mirror, argument_root)
                        }
                        Continuation::ApplicationArgument {
                            function,
                            span,
                            argument_span,
                        } => {
                            let Kind::Arrow(domain, codomain) = function.kind else {
                                if provenance.is_none() {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a checked body-free type applies a non-function kind",
                                    ));
                                }
                                let diagnostic_budget = budget.resolved_budget(span)?;
                                return Err(KindFailure::Source(Box::new(not_applicable_error(
                                    KindReason::NotApplicable,
                                    span,
                                    "this type does not have a function kind",
                                    found.kind,
                                    function.kind,
                                    function.origin.map(|origin| {
                                        (
                                            origin,
                                            "the applied type's kind is fixed by this declaration",
                                        )
                                    }),
                                    diagnostic_budget,
                                )?)));
                            };
                            let equal = same_kind_with_charge(domain, found.kind, || {
                                budget.charge(1)
                            })
                            .map_err(|()| {
                                KindFailure::resource(
                                    argument_span,
                                    "type-application kind checking exceeded its type-work budget",
                                )
                            })?;
                            if !equal {
                                if provenance.is_none() {
                                    return Err(KindFailure::internal(
                                        argument_span,
                                        "a checked body-free type application has the wrong argument kind",
                                    ));
                                }
                                let diagnostic_budget = budget.resolved_budget(argument_span)?;
                                return Err(KindFailure::Source(Box::new(structured_error(
                                    KindReason::Argument,
                                    argument_span,
                                    "this type argument has the wrong kind",
                                    domain,
                                    found.kind,
                                    function.origin.map(|origin| {
                                        (
                                            origin,
                                            "the applied type's parameter kind is declared here",
                                        )
                                    }),
                                    diagnostic_budget,
                                )?)));
                            }
                            State::Complete(KindFact {
                                kind: codomain,
                                retained_mirrors: None,
                                origin: function.origin,
                                occurrence: span,
                            })
                        }
                        Continuation::FunctionDomain {
                            codomain,
                            codomain_mirror,
                            codomain_root,
                            span,
                        } => {
                            let equal =
                                same_kind_with_charge(&TYPE_KIND, found.kind, || budget.charge(1))
                                    .map_err(|()| {
                                        KindFailure::resource(
                                            found.occurrence,
                                            "function kind checking exceeded its type-work budget",
                                        )
                                    })?;
                            if !equal {
                                if provenance.is_none() {
                                    return Err(KindFailure::internal(
                                        found.occurrence,
                                        "a checked body-free function component has the wrong kind",
                                    ));
                                }
                                let diagnostic_budget = budget.resolved_budget(found.occurrence)?;
                                return Err(KindFailure::Source(Box::new(structured_error(
                                    KindReason::ExpectedType,
                                    found.occurrence,
                                    "this function domain must have kind Type",
                                    &TYPE_KIND,
                                    found.kind,
                                    found.origin.map(|origin| {
                                        (origin, "the found kind is fixed by this declaration")
                                    }),
                                    diagnostic_budget,
                                )?)));
                            }
                            work.push(Continuation::FunctionCodomain { span });
                            State::Visit(codomain, codomain_mirror, codomain_root)
                        }
                        Continuation::FunctionCodomain { span } => {
                            let equal =
                                same_kind_with_charge(&TYPE_KIND, found.kind, || budget.charge(1))
                                    .map_err(|()| {
                                        KindFailure::resource(
                                            found.occurrence,
                                            "function kind checking exceeded its type-work budget",
                                        )
                                    })?;
                            if !equal {
                                if provenance.is_none() {
                                    return Err(KindFailure::internal(
                                        found.occurrence,
                                        "a checked body-free function component has the wrong kind",
                                    ));
                                }
                                let diagnostic_budget = budget.resolved_budget(found.occurrence)?;
                                return Err(KindFailure::Source(Box::new(structured_error(
                                    KindReason::ExpectedType,
                                    found.occurrence,
                                    "this function codomain must have kind Type",
                                    &TYPE_KIND,
                                    found.kind,
                                    found.origin.map(|origin| {
                                        (origin, "the found kind is fixed by this declaration")
                                    }),
                                    diagnostic_budget,
                                )?)));
                            }
                            State::Complete(KindFact {
                                kind: &TYPE_KIND,
                                retained_mirrors: None,
                                origin: None,
                                occurrence: span,
                            })
                        }
                    }
                }
            };
        }
    }
}

/// Builds the smallest canonical body-free kind environment needed by one
/// interface operation. Discovery follows the supplied roots and is therefore
/// independent of unrelated registry width.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CanonicalEnvironmentFailure {
    ConstraintResource,
    TypeResource,
    InvalidState,
}

pub(crate) fn canonical_body_free_environments<'a>(
    registry: &'a ResolvedRegistry,
    owner_parameters: &[TypeVariableId],
    roots: &[&Type],
    _span: Span,
    discovery_budget: &mut impl KindWorkLedger,
    retention_budget: &mut TypeWorkBudget,
) -> Result<KindEnvironments<'a>, CanonicalEnvironmentFailure> {
    let mut environments = KindEnvironments::new();
    for identity in owner_parameters {
        discovery_budget
            .charge(1)
            .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
        let parameter = registry
            .type_variable(*identity)
            .ok_or(CanonicalEnvironmentFailure::InvalidState)?;
        environments
            .insert_declared(
                *identity,
                &parameter.kind,
                parameter.origin.primary_span(),
                retention_budget,
            )
            .map_err(map_canonical_environment_retention_failure)?;
    }

    let mut pending = Vec::new();
    discovery_budget
        .charge(roots.len())
        .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
    pending
        .try_reserve(roots.len())
        .map_err(|_| CanonicalEnvironmentFailure::ConstraintResource)?;
    pending.extend(roots.iter().rev().copied());

    while let Some(ty) = pending.pop() {
        discovery_budget
            .charge(1)
            .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
        match ty {
            Type::Int | Type::Bool | Type::Unit => {}
            Type::Variable(identity) => {
                discovery_budget
                    .charge(1)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                if environments.contains_declared(*identity) {
                    continue;
                }
                discovery_budget
                    .charge(1)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                let parameter = registry
                    .type_variable(*identity)
                    .ok_or(CanonicalEnvironmentFailure::InvalidState)?;
                environments
                    .insert_declared(
                        *identity,
                        &parameter.kind,
                        parameter.origin.primary_span(),
                        retention_budget,
                    )
                    .map_err(map_canonical_environment_retention_failure)?;
            }
            Type::Nominal(identity) => {
                discovery_budget
                    .charge(1)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                if environments.contains_nominal(*identity) {
                    continue;
                }
                discovery_budget
                    .charge(1)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                match registry
                    .nominal_kind(*identity)
                    .ok_or(CanonicalEnvironmentFailure::InvalidState)?
                {
                    CanonicalNominalKind::Parameters { parameters, origin } => environments
                        .insert_nominal(*identity, parameters, origin, retention_budget)
                        .map_err(map_canonical_environment_retention_failure)?,
                    CanonicalNominalKind::Frozen { kind, origin } => environments
                        .insert_frozen_nominal(*identity, kind, origin, retention_budget)
                        .map_err(map_canonical_environment_retention_failure)?,
                }
            }
            Type::Tuple(elements) => {
                discovery_budget
                    .charge(elements.len())
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| CanonicalEnvironmentFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                discovery_budget
                    .charge(2)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| CanonicalEnvironmentFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Inference(_) | Type::Forall(_, _) => {
                return Err(CanonicalEnvironmentFailure::InvalidState);
            }
        }
    }
    Ok(environments)
}

fn map_canonical_environment_retention_failure(
    failure: KindFailure,
) -> CanonicalEnvironmentFailure {
    match failure {
        KindFailure::Resource(_) => CanonicalEnvironmentFailure::TypeResource,
        KindFailure::Internal(_) | KindFailure::Source(_) => {
            CanonicalEnvironmentFailure::InvalidState
        }
    }
}

pub(crate) fn canonical_type_variable_kind<'a>(
    registry: &'a ResolvedRegistry,
    identity: TypeVariableId,
    span: Span,
    budget: &mut impl KindWorkLedger,
) -> Result<&'a Kind, KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            span,
            "canonical type-binder kind lookup exceeded its owning work budget",
        )
    })?;
    registry
        .type_variable(identity)
        .map(|parameter| &parameter.kind)
        .ok_or_else(|| KindFailure::internal(span, "a canonical type-binder kind is missing"))
}

/// Checks every resolved type boundary before a resolved module is published.
pub(crate) fn check_resolved_module_with_budget<'a>(
    module: &'a ResolvedModuleParts,
    constructor_payload_provenance: &'a [Vec<crate::resolve::ConstructorPayloadProvenance>],
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    authenticate_declaration_order(module, constructor_payload_provenance, budget)?;
    let mut environments = KindEnvironments::new();
    for nominal in module.registry.nominals() {
        let parameters = required_lookup(
            module.registry.canonical_nominal_parameters(nominal.id),
            nominal.origin.primary_span(),
            "a local nominal has no canonical parameter slice",
            budget,
        )?;
        authenticate_owner_parameters(&module.registry, parameters, budget)?;
        environments.insert_nominal(
            nominal.id,
            parameters,
            nominal.origin.primary_span(),
            budget,
        )?;
    }
    for interface in &module.interfaces {
        authenticate_owner_parameters(
            &module.registry,
            std::slice::from_ref(&interface.parameter),
            budget,
        )?;
        environments.insert_interface(
            interface.id,
            &interface.parameter.kind,
            interface.parameter.origin.primary_span(),
            budget,
        )?;
    }

    authenticate_imported_environments(module, &mut environments, budget)?;

    for declaration in &module.declaration_order {
        let outcome = match *declaration {
            crate::resolved::ResolvedDeclarationIndex::Type(index) => {
                let nominal = required_lookup(
                    module.registry.nominals().get(index),
                    module.span,
                    "declaration order contains an invalid nominal index",
                    budget,
                )?;
                let parameters = required_lookup(
                    module.registry.canonical_nominal_parameters(nominal.id),
                    nominal.origin.primary_span(),
                    "a local nominal has no canonical parameter slice",
                    budget,
                )?;
                environments.install_owner_parameters(parameters, budget)?;
                let payload_provenance = required_lookup(
                    constructor_payload_provenance.get(index),
                    nominal.origin.primary_span(),
                    "a nominal has no declaration-ordered payload provenance",
                    budget,
                )?;
                if payload_provenance.len() != nominal.constructors.len() {
                    charge_lookup_attempt(nominal.origin.primary_span(), budget)?;
                    return Err(KindFailure::internal(
                        nominal.origin.primary_span(),
                        "a nominal has incomplete constructor payload provenance",
                    ));
                }
                for (constructor_id, payload_provenance) in
                    nominal.constructors.iter().zip(payload_provenance)
                {
                    budget.charge(1).map_err(|()| {
                        KindFailure::resource(
                            nominal.origin.primary_span(),
                            "constructor provenance authentication exceeded its type-work budget",
                        )
                    })?;
                    if payload_provenance.constructor != *constructor_id {
                        return Err(KindFailure::internal(
                            nominal.origin.primary_span(),
                            "constructor payload provenance is paired with the wrong identity",
                        ));
                    }
                    let constructor = required_lookup(
                        module.registry.constructor(*constructor_id),
                        nominal.origin.primary_span(),
                        "a nominal names a missing canonical constructor",
                        budget,
                    )?;
                    if constructor.id != *constructor_id || constructor.owner != nominal.id {
                        return Err(KindFailure::internal(
                            constructor.origin.primary_span(),
                            "canonical constructor ownership disagrees with its nominal",
                        ));
                    }
                    check_constructor_payload(
                        constructor,
                        payload_provenance,
                        &environments,
                        budget,
                    )?;
                }
                DeclarationKindOutcome::Checked
            }
            crate::resolved::ResolvedDeclarationIndex::Interface(index) => {
                let interface = required_lookup(
                    module.interfaces.get(index),
                    module.span,
                    "declaration order contains an invalid interface index",
                    budget,
                )?;
                check_interface(interface, &module.registry, &mut environments, budget)?
            }
            crate::resolved::ResolvedDeclarationIndex::Global(index) => {
                let definition = required_lookup(
                    module.definitions.get(index),
                    module.span,
                    "declaration order contains an invalid global index",
                    budget,
                )?;
                check_definition(definition, &module.registry, &mut environments, budget)?
            }
            crate::resolved::ResolvedDeclarationIndex::Implementation(index) => {
                let implementation = required_lookup(
                    module.implementations.get(index),
                    module.span,
                    "declaration order contains an invalid implementation index",
                    budget,
                )?;
                check_implementation(implementation, &module.registry, &mut environments, budget)?
            }
        };
        if outcome == DeclarationKindOutcome::Deferred {
            return Ok(());
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum DeclarationKindOutcome {
    /// This declaration is completely checked by the resolved-kind stage.
    Checked,
    /// A later semantic stage owns an earlier source rejection, so kind
    /// checking must not inspect any subsequent declaration.
    Deferred,
}

fn authenticate_declaration_order(
    module: &ResolvedModuleParts,
    constructor_payload_provenance: &[Vec<crate::resolve::ConstructorPayloadProvenance>],
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut next_type = 0;
    let mut next_interface = 0;
    let mut next_global = 0;
    let mut next_implementation = 0;
    for declaration in &module.declaration_order {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                module.span,
                "declaration-order authentication exceeded its type-work budget",
            )
        })?;
        let ordered = match *declaration {
            crate::resolved::ResolvedDeclarationIndex::Type(index) => {
                let ordered = index == next_type && index < module.registry.nominals().len();
                next_type = next_type.saturating_add(1);
                ordered
            }
            crate::resolved::ResolvedDeclarationIndex::Interface(index) => {
                let ordered = index == next_interface && index < module.interfaces.len();
                next_interface = next_interface.saturating_add(1);
                ordered
            }
            crate::resolved::ResolvedDeclarationIndex::Global(index) => {
                let ordered = index == next_global && index < module.definitions.len();
                next_global = next_global.saturating_add(1);
                ordered
            }
            crate::resolved::ResolvedDeclarationIndex::Implementation(index) => {
                let ordered = index == next_implementation && index < module.implementations.len();
                next_implementation = next_implementation.saturating_add(1);
                ordered
            }
        };
        if !ordered {
            return Err(KindFailure::internal(
                module.span,
                "declaration order contains a duplicate or out of source order index",
            ));
        }
    }

    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            module.span,
            "declaration-order coverage authentication exceeded its type-work budget",
        )
    })?;
    if next_type != module.registry.nominals().len()
        || next_interface != module.interfaces.len()
        || next_global != module.definitions.len()
        || next_implementation != module.implementations.len()
    {
        return Err(KindFailure::internal(
            module.span,
            "declaration order under-covers local declarations",
        ));
    }

    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            module.span,
            "constructor-provenance cardinality authentication exceeded its type-work budget",
        )
    })?;
    if constructor_payload_provenance.len() != module.registry.nominals().len() {
        return Err(KindFailure::internal(
            module.span,
            "constructor payload provenance has the wrong outer cardinality",
        ));
    }
    Ok(())
}

fn authenticate_imported_environments<'a>(
    module: &'a ResolvedModuleParts,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let imported = &module.imported;
    for nominal in imported.nominals() {
        if nominal.parameter_count != nominal.parameters.len() {
            return Err(KindFailure::internal(
                nominal.origin.primary_span(),
                "an imported nominal has an incomplete canonical parameter slice",
            ));
        }
        authenticate_unique_parameter_ids(
            &nominal.parameters,
            nominal.origin.primary_span(),
            budget,
        )?;
        environments.insert_nominal(
            nominal.id,
            &nominal.parameters,
            nominal.origin.primary_span(),
            budget,
        )?;
    }
    for imported_interface in imported.interface_imports() {
        let interface = &imported_interface.fact;
        environments.insert_interface(
            interface.id,
            &interface.parameter.kind,
            interface.parameter.origin.primary_span(),
            budget,
        )?;
    }

    for imported_interface in imported.interface_imports() {
        let interface = &imported_interface.fact;
        environments
            .install_owner_parameters(std::slice::from_ref(&interface.parameter), budget)?;
        for method in &interface.methods {
            environments.expect_body_free_value_type(method.value_type(), method.span, budget)?;
        }
    }

    for global in imported.globals() {
        let span = global.origin.primary_span();
        environments.install_owner_pairs(&global.scheme.type_parameters, span, budget)?;
        environments.expect_body_free_value_type(&global.scheme.value_type, span, budget)?;
        for requirement in &global.scheme.requirements {
            environments.expect_body_free_interface_argument(
                requirement.interface,
                requirement.argument(),
                requirement.span,
                budget,
            )?;
        }
    }

    for implementation in imported.implementations() {
        let fact = &implementation.fact;
        environments.install_owner_parameters(&fact.head_parameters, budget)?;
        environments.expect_body_free_interface_argument(
            fact.interface,
            fact.argument(),
            fact.span,
            budget,
        )?;
        for prerequisite in &fact.prerequisites {
            environments.expect_body_free_interface_argument(
                prerequisite.interface,
                prerequisite.argument(),
                prerequisite.span,
                budget,
            )?;
        }
        for method in &fact.methods {
            environments.install_owner_pairs(
                &method.scheme.type_parameters,
                method.span,
                budget,
            )?;
            environments.expect_body_free_value_type(
                &method.scheme.value_type,
                method.span,
                budget,
            )?;
            for requirement in &method.scheme.requirements {
                environments.expect_body_free_interface_argument(
                    requirement.interface,
                    requirement.argument(),
                    requirement.span,
                    budget,
                )?;
            }
        }
    }
    Ok(())
}

fn check_constructor_payload(
    constructor: &ResolvedConstructor,
    provenance: &crate::resolve::ConstructorPayloadProvenance,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    match (&constructor.payload, provenance.fields.as_slice()) {
        (None, []) => Ok(()),
        (Some(payload), [field]) => environments.expect_value_type_parts(
            payload,
            field,
            field
                .span()
                .unwrap_or_else(|| constructor.origin.primary_span()),
            budget,
        ),
        (Some(Type::Tuple(elements)), fields) if elements.len() == fields.len() => {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    constructor.origin.primary_span(),
                    "constructor tuple kind synthesis exceeded its type-work budget",
                )
            })?;
            for (element, field) in elements.iter().zip(fields) {
                environments.expect_value_type_parts(
                    element,
                    field,
                    field
                        .span()
                        .unwrap_or_else(|| constructor.origin.primary_span()),
                    budget,
                )?;
            }
            same_kind_with_budget(&TYPE_KIND, &TYPE_KIND, budget).map_err(|()| {
                KindFailure::resource(
                    constructor.origin.primary_span(),
                    "constructor tuple value-type check exceeded its type-work budget",
                )
            })?;
            Ok(())
        }
        _ => Err(KindFailure::internal(
            constructor.origin.primary_span(),
            "a constructor payload and its moved provenance disagree",
        )),
    }
}

fn check_interface<'a>(
    interface: &'a ResolvedInterfaceDeclaration,
    registry: &crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    let mut interface_only = false;
    for method in &interface.methods {
        if method.has_explicit_type_parameters && method.type_parameters.is_empty() {
            charge_lookup_attempt(method.span, budget)?;
            return Err(KindFailure::internal(
                method.span,
                "a resolved explicit method binder list is empty",
            ));
        }
        authenticate_owner_parameters(registry, &method.type_parameters, budget)?;
        if method.has_explicit_type_parameters {
            environments
                .install_owner_parameters(std::slice::from_ref(&interface.parameter), budget)?;
            for parameter in &method.type_parameters {
                environments.insert_declared(
                    parameter.id,
                    &parameter.kind,
                    parameter.origin.primary_span(),
                    budget,
                )?;
            }
            interface_only = false;
        } else {
            if !interface_only {
                environments
                    .install_owner_parameters(std::slice::from_ref(&interface.parameter), budget)?;
                interface_only = true;
            }
            if !method.type_parameters.is_empty() {
                return Ok(DeclarationKindOutcome::Deferred);
            }
        }
        environments.expect_value_type(&method.annotation, budget)?;
    }
    Ok(DeclarationKindOutcome::Checked)
}

fn check_requirement(
    requirement: &ResolvedRequirement,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    environments.expect_requirement(requirement.interface.id, &requirement.argument, budget)
}

fn check_definition<'a>(
    definition: &'a ResolvedDefinition,
    registry: &crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global) => {
            authenticate_owner_parameters(registry, &global.interface.type_parameters, budget)?;
            environments.install_owner_parameters(&global.interface.type_parameters, budget)?;
            environments.expect_value_type(&global.interface.annotation, budget)?;
            let mut determined = Vec::new();
            collect_type_variables(
                &global.interface.annotation.ty,
                global.interface.annotation.span,
                &mut determined,
                budget,
            )?;
            for requirement in &global.interface.requirements {
                if requirement_has_undetermined_variable(requirement, &determined, budget)? {
                    return Ok(DeclarationKindOutcome::Deferred);
                }
                check_requirement(requirement, environments, budget)?;
            }
            for equation in &global.equations {
                check_expression_annotations(&equation.body, environments, budget)?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            authenticate_owner_parameters(registry, &global.header.type_parameters, budget)?;
            environments.install_owner_parameters(&global.header.type_parameters, budget)?;
            let mut determined = Vec::new();
            for parameter in &global.header.parameters {
                environments.expect_value_type(&parameter.annotation, budget)?;
                collect_type_variables(
                    &parameter.annotation.ty,
                    parameter.annotation.span,
                    &mut determined,
                    budget,
                )?;
            }
            environments.expect_value_type(&global.header.result_type, budget)?;
            collect_type_variables(
                &global.header.result_type.ty,
                global.header.result_type.span,
                &mut determined,
                budget,
            )?;
            for requirement in &global.header.requirements {
                if requirement_has_undetermined_variable(requirement, &determined, budget)? {
                    return Ok(DeclarationKindOutcome::Deferred);
                }
                check_requirement(requirement, environments, budget)?;
            }
            check_block_annotations(&global.body, environments, budget)?;
        }
    }
    Ok(DeclarationKindOutcome::Checked)
}

fn collect_type_variables(
    ty: &Type,
    span: Span,
    output: &mut Vec<TypeVariableId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut work = Vec::new();
    push_determination_work(&mut work, ty, span, budget)?;
    while let Some(ty) = work.pop() {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                span,
                "global determination discovery exceeded its type-work budget",
            )
        })?;
        match ty {
            Type::Variable(identity) => {
                if !contains_type_variable_with_budget(output, *identity, span, budget)? {
                    budget.charge(1).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "global determination retention exceeded its type-work budget",
                        )
                    })?;
                    output.try_reserve(1).map_err(|_| {
                        KindFailure::resource(
                            span,
                            "global determination retention could not reserve storage",
                        )
                    })?;
                    output.push(*identity);
                }
            }
            Type::Tuple(elements) => {
                for element in elements.iter().rev() {
                    push_determination_work(&mut work, element, span, budget)?;
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                push_determination_work(&mut work, argument, span, budget)?;
                push_determination_work(&mut work, function, span, budget)?;
            }
            Type::Forall(_, _) => {
                return Err(KindFailure::internal(
                    span,
                    "a rank-1 scheme entered global determination discovery",
                ));
            }
            Type::Int | Type::Bool | Type::Unit | Type::Inference(_) | Type::Nominal(_) => {}
        }
    }
    Ok(())
}

fn push_determination_work<'a>(
    work: &mut Vec<&'a Type>,
    ty: &'a Type,
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            span,
            "global determination work scheduling exceeded its type-work budget",
        )
    })?;
    work.try_reserve(1).map_err(|_| {
        KindFailure::resource(
            span,
            "global determination work scheduling could not reserve storage",
        )
    })?;
    work.push(ty);
    Ok(())
}

fn requirement_has_undetermined_variable(
    requirement: &ResolvedRequirement,
    determined: &[TypeVariableId],
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    let mut variables = Vec::new();
    collect_type_variables(
        &requirement.argument.ty,
        requirement.argument.span,
        &mut variables,
        budget,
    )?;
    for identity in variables {
        if !contains_type_variable_with_budget(
            determined,
            identity,
            requirement.argument.span,
            budget,
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn contains_type_variable_with_budget(
    variables: &[TypeVariableId],
    sought: TypeVariableId,
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    for identity in variables {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                span,
                "global determination membership exceeded its type-work budget",
            )
        })?;
        if *identity == sought {
            return Ok(true);
        }
    }
    Ok(false)
}

fn check_implementation<'a>(
    implementation: &'a ResolvedImplementation,
    registry: &crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    authenticate_owner_parameters(registry, &implementation.head_parameters, budget)?;
    authenticate_owner_parameters(
        registry,
        &implementation.prerequisite_only_parameters,
        budget,
    )?;
    environments.install_owner_parameters(&implementation.head_parameters, budget)?;
    environments.expect_requirement(
        implementation.interface.id,
        &implementation.argument,
        budget,
    )?;
    if !implementation.prerequisite_only_parameters.is_empty() {
        return Ok(DeclarationKindOutcome::Deferred);
    }
    for prerequisite in &implementation.prerequisites {
        check_requirement(prerequisite, environments, budget)?;
    }
    for group in &implementation.method_groups {
        for equation in &group.equations {
            check_expression_annotations(&equation.body, environments, budget)?;
        }
    }
    Ok(DeclarationKindOutcome::Checked)
}

fn authenticate_owner_parameters(
    registry: &crate::resolved::ResolvedRegistry,
    parameters: &[crate::resolved::ResolvedTypeVariable],
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    if parameters.is_empty() {
        return Ok(());
    }
    authenticate_unique_parameter_ids(
        parameters,
        parameters
            .first()
            .expect("nonempty owner parameters have a first binder")
            .origin
            .primary_span(),
        budget,
    )?;
    for parameter in parameters {
        let span = parameter.origin.primary_span();
        let canonical = registry.type_variable(parameter.id).ok_or_else(|| {
            KindFailure::internal(
                span,
                "a declaration binder has no canonical registry record",
            )
        })?;
        let same_kind =
            same_kind_with_budget(&canonical.kind, &parameter.kind, budget).map_err(|()| {
                KindFailure::resource(
                    span,
                    "canonical binder-kind authentication exceeded its type-work budget",
                )
            })?;
        if canonical.id != parameter.id
            || canonical.spelling != parameter.spelling
            || canonical.origin.primary_span() != span
            || !same_kind
        {
            return Err(KindFailure::internal(
                span,
                "a declaration binder conflicts with its canonical registry record",
            ));
        }
    }
    Ok(())
}

fn authenticate_unique_parameter_ids(
    parameters: &[crate::resolved::ResolvedTypeVariable],
    fallback_span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    budget.charge(parameters.len()).map_err(|()| {
        KindFailure::resource(
            fallback_span,
            "canonical binder authentication exceeded its type-work budget",
        )
    })?;
    let mut identities = HashSet::new();
    identities.try_reserve(parameters.len()).map_err(|_| {
        KindFailure::resource(
            fallback_span,
            "canonical binder authentication could not reserve identity storage",
        )
    })?;
    for parameter in parameters {
        if !identities.insert(parameter.id) {
            return Err(KindFailure::internal(
                parameter.origin.primary_span(),
                "an owner binder list repeats a type-variable identity",
            ));
        }
    }
    Ok(())
}

fn check_block_annotations(
    block: &crate::resolved::ResolvedBlock,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut work = Vec::new();
    schedule_block_work(&mut work, block, budget)?;
    check_expression_work(work, environments, budget)
}

fn check_expression_annotations(
    expression: &ResolvedExpr,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut work = Vec::new();
    push_body_work(
        &mut work,
        BodyWork::Expression(expression),
        expression.span,
        budget,
    )?;
    check_expression_work(work, environments, budget)
}

#[derive(Clone, Copy)]
enum BodyWork<'a> {
    Expression(&'a ResolvedExpr),
    Declaration(&'a ResolvedLocalDeclaration),
    RecursiveMember(&'a ResolvedRecursiveMember),
}

fn check_expression_work<'a>(
    mut work: Vec<BodyWork<'a>>,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    while let Some(item) = work.pop() {
        let span = body_work_span(item);
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                span,
                "resolved body kind traversal exceeded its type-work budget",
            )
        })?;
        match item {
            BodyWork::Declaration(declaration) => match declaration {
                ResolvedLocalDeclaration::Binding(binding) => {
                    if let Some(annotation) = &binding.annotation {
                        environments.expect_value_type(annotation, budget)?;
                    }
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&binding.initializer),
                        binding.initializer.span,
                        budget,
                    )?;
                }
                ResolvedLocalDeclaration::Recursive(group) => {
                    for member in group.members.iter().rev() {
                        push_body_work(
                            &mut work,
                            BodyWork::RecursiveMember(member),
                            member.span,
                            budget,
                        )?;
                    }
                }
            },
            BodyWork::RecursiveMember(member) => {
                environments.expect_value_type(&member.annotation, budget)?;
                push_body_work(
                    &mut work,
                    BodyWork::Expression(&member.initializer),
                    member.initializer.span,
                    budget,
                )?;
            }
            BodyWork::Expression(expression) => match &expression.kind {
                ResolvedExprKind::Tuple(elements) => {
                    for element in elements.iter().rev() {
                        push_body_work(
                            &mut work,
                            BodyWork::Expression(element),
                            element.span,
                            budget,
                        )?;
                    }
                }
                ResolvedExprKind::Apply(application) => {
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&application.argument),
                        application.argument.span,
                        budget,
                    )?;
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&application.function),
                        application.function.span,
                        budget,
                    )?;
                }
                ResolvedExprKind::Add(binary)
                | ResolvedExprKind::Multiply(binary)
                | ResolvedExprKind::Equal(binary) => {
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&binary.right),
                        binary.right.span,
                        budget,
                    )?;
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&binary.left),
                        binary.left.span,
                        budget,
                    )?;
                }
                ResolvedExprKind::Block(block) => {
                    schedule_block_work(&mut work, block, budget)?;
                }
                ResolvedExprKind::Function(function) => {
                    schedule_block_work(&mut work, &function.body, budget)?;
                }
                ResolvedExprKind::Match(match_expression) => {
                    for arm in match_expression.arms.iter().rev() {
                        push_body_work(
                            &mut work,
                            BodyWork::Expression(&arm.body),
                            arm.body.span,
                            budget,
                        )?;
                    }
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&match_expression.scrutinee),
                        match_expression.scrutinee.span,
                        budget,
                    )?;
                }
                ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Occurrence(_)
                | ResolvedExprKind::Constructor(_) => {}
            },
        }
    }
    Ok(())
}

fn schedule_block_work<'a>(
    work: &mut Vec<BodyWork<'a>>,
    block: &'a crate::resolved::ResolvedBlock,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    push_body_work(
        work,
        BodyWork::Expression(block.result.as_ref()),
        block.result.span,
        budget,
    )?;
    for declaration in block.declarations.iter().rev() {
        push_body_work(
            work,
            BodyWork::Declaration(declaration),
            local_declaration_span(declaration),
            budget,
        )?;
    }
    Ok(())
}

fn push_body_work<'a>(
    work: &mut Vec<BodyWork<'a>>,
    item: BodyWork<'a>,
    span: Span,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            span,
            "resolved body kind scheduling exceeded its type-work budget",
        )
    })?;
    work.try_reserve(1).map_err(|_| {
        KindFailure::resource(
            span,
            "resolved body kind scheduling could not reserve storage",
        )
    })?;
    work.push(item);
    Ok(())
}

fn local_declaration_span(declaration: &ResolvedLocalDeclaration) -> Span {
    match declaration {
        ResolvedLocalDeclaration::Binding(binding) => binding.span,
        ResolvedLocalDeclaration::Recursive(group) => group.span,
    }
}

fn body_work_span(item: BodyWork<'_>) -> Span {
    match item {
        BodyWork::Expression(expression) => expression.span,
        BodyWork::Declaration(declaration) => local_declaration_span(declaration),
        BodyWork::RecursiveMember(member) => member.span,
    }
}

fn structured_error(
    reason: KindReason,
    span: Span,
    message: impl Into<String>,
    expected: &Kind,
    found: &Kind,
    related: Option<(Span, &'static str)>,
    budget: &mut TypeWorkBudget,
) -> Result<KindError, KindFailure> {
    let retained_expected = match clone_kind_with_budget(expected, budget) {
        Ok(kind) => kind,
        Err(()) => {
            return Err(KindFailure::resource(
                span,
                "kind diagnostic retention exceeded its type-work budget",
            ));
        }
    };
    let retained_found = match clone_kind_with_budget(found, budget) {
        Ok(kind) => kind,
        Err(()) => {
            return Err(KindFailure::resource(
                span,
                "kind diagnostic retention exceeded its type-work budget",
            ));
        }
    };
    let expected_text = match render_kind_with_budget(&retained_expected, budget) {
        Ok(rendered) => rendered,
        Err(()) => {
            return Err(KindFailure::resource(
                span,
                "kind diagnostic rendering exceeded its type-work budget",
            ));
        }
    };
    let found_text = match render_kind_with_budget(&retained_found, budget) {
        Ok(rendered) => rendered,
        Err(()) => {
            return Err(KindFailure::resource(
                span,
                "kind diagnostic rendering exceeded its type-work budget",
            ));
        }
    };
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    if let Some((related, related_message)) = related.filter(|(related, _)| *related != span) {
        diagnostic
            .related
            .push(SourceLabel::new(related, related_message));
    }
    diagnostic.expected = Some(expected_text);
    diagnostic.found = Some(found_text);
    Ok(KindError {
        diagnostic,
        expectation: KindExpectation::Exact(retained_expected),
        found: Some(retained_found),
    })
}

fn charge_synthesis_cell(span: Span, budget: &mut impl KindWorkLedger) -> Result<(), KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            span,
            "resolved kind synthesis exceeded its type-work budget",
        )
    })
}

fn charge_kind_descendants_with_ledger(
    kind: &Kind,
    budget: &mut SynthesisLedger<'_>,
) -> Result<(), ()> {
    if let SynthesisLedger::Resolved(type_work) = budget {
        return charge_kind_descendants(kind, type_work);
    }
    match kind {
        Kind::Type => Ok(()),
        Kind::Arrow(domain, codomain) => {
            charge_kind_with_charge(domain, || budget.charge(1))?;
            charge_kind_with_charge(codomain, || budget.charge(1))
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinkedKindMirrorFailure {
    Resource,
    Mismatch,
}

fn authenticate_kind_descendants_with_ledger(
    canonical: &Kind,
    retained_mirrors: Option<RetainedKindMirrors<'_>>,
    budget: &mut SynthesisLedger<'_>,
) -> Result<(), LinkedKindMirrorFailure> {
    let Some(retained_mirrors) = retained_mirrors else {
        return charge_kind_descendants_with_ledger(canonical, budget)
            .map_err(|()| LinkedKindMirrorFailure::Resource);
    };

    let RetainedKindMirrors::Two(first, second) = retained_mirrors;
    let second = Some(second);
    if second.is_some() {
        budget
            .charge(1)
            .map_err(|()| LinkedKindMirrorFailure::Resource)?;
    }

    let mut current = (canonical, first, second);
    let mut pending = Vec::new();
    loop {
        match current {
            (Kind::Type, Kind::Type, None | Some(Kind::Type)) => {}
            (
                Kind::Arrow(canonical_domain, canonical_codomain),
                Kind::Arrow(first_domain, first_codomain),
                second,
            ) => {
                let (second_domain, second_codomain) = match second {
                    None => (None, None),
                    Some(Kind::Arrow(domain, codomain)) => {
                        (Some(domain.as_ref()), Some(codomain.as_ref()))
                    }
                    Some(Kind::Type) => return Err(LinkedKindMirrorFailure::Mismatch),
                };
                budget
                    .charge(1)
                    .map_err(|()| LinkedKindMirrorFailure::Resource)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| LinkedKindMirrorFailure::Resource)?;
                pending.push((
                    canonical_codomain.as_ref(),
                    first_codomain.as_ref(),
                    second_codomain,
                ));
                budget
                    .charge(1)
                    .map_err(|()| LinkedKindMirrorFailure::Resource)?;
                if second_domain.is_some() {
                    budget
                        .charge(1)
                        .map_err(|()| LinkedKindMirrorFailure::Resource)?;
                }
                current = (
                    canonical_domain.as_ref(),
                    first_domain.as_ref(),
                    second_domain,
                );
                continue;
            }
            _ => return Err(LinkedKindMirrorFailure::Mismatch),
        }

        let Some(next) = pending.pop() else {
            return Ok(());
        };
        budget
            .charge(1)
            .map_err(|()| LinkedKindMirrorFailure::Resource)?;
        if next.2.is_some() {
            budget
                .charge(1)
                .map_err(|()| LinkedKindMirrorFailure::Resource)?;
        }
        current = next;
    }
}

fn charge_lookup_attempt(span: Span, budget: &mut impl KindWorkLedger) -> Result<(), KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            span,
            "kind environment lookup exceeded its type-work budget",
        )
    })
}

fn required_lookup<T>(
    value: Option<T>,
    span: Span,
    message: &'static str,
    budget: &mut TypeWorkBudget,
) -> Result<T, KindFailure> {
    match value {
        Some(value) => Ok(value),
        None => {
            charge_lookup_attempt(span, budget)?;
            Err(KindFailure::internal(span, message))
        }
    }
}

fn not_applicable_error(
    reason: KindReason,
    span: Span,
    message: impl Into<String>,
    domain: &Kind,
    found: &Kind,
    related: Option<(Span, &'static str)>,
    budget: &mut TypeWorkBudget,
) -> Result<KindError, KindFailure> {
    let retained_domain = clone_kind_with_budget(domain, budget).map_err(|()| {
        KindFailure::resource(
            span,
            "kind diagnostic retention exceeded its type-work budget",
        )
    })?;
    let retained_found = clone_kind_with_budget(found, budget).map_err(|()| {
        KindFailure::resource(
            span,
            "kind diagnostic retention exceeded its type-work budget",
        )
    })?;
    let domain_text = render_kind_with_budget(&retained_domain, budget).map_err(|()| {
        KindFailure::resource(
            span,
            "kind diagnostic rendering exceeded its type-work budget",
        )
    })?;
    let found_text = render_kind_with_budget(&retained_found, budget).map_err(|()| {
        KindFailure::resource(
            span,
            "kind diagnostic rendering exceeded its type-work budget",
        )
    })?;
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    if let Some((related, related_message)) = related.filter(|(related, _)| *related != span) {
        diagnostic
            .related
            .push(SourceLabel::new(related, related_message));
    }
    diagnostic.expected = Some(format!("{domain_text} -> _"));
    diagnostic.found = Some(found_text);
    Ok(KindError {
        diagnostic,
        expectation: KindExpectation::Function {
            domain: retained_domain,
        },
        found: Some(retained_found),
    })
}

fn provenance_node_span(node: &ResolvedTypeProvenanceNode) -> Span {
    match node {
        ResolvedTypeProvenanceNode::Fact(span)
        | ResolvedTypeProvenanceNode::Tuple { span, .. }
        | ResolvedTypeProvenanceNode::Function { span, .. }
        | ResolvedTypeProvenanceNode::Application { span, .. } => *span,
    }
}

fn require_fact_node(
    node: Option<&ResolvedTypeProvenanceNode>,
    span: Span,
    budget: &mut impl KindWorkLedger,
) -> Result<(), KindFailure> {
    if node.is_none() || matches!(node, Some(ResolvedTypeProvenanceNode::Fact(_))) {
        Ok(())
    } else {
        charge_lookup_attempt(span, budget)?;
        Err(KindFailure::internal(
            span,
            "an atomic resolved type has structural provenance",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        interface::{InterfaceId, MethodId},
        module::ModuleId,
        resolved::{
            ImportedFacts, ResolvedApplicationExpr, ResolvedBlock, ResolvedConstructor,
            ResolvedDeclarationIndex, ResolvedExportCandidate, ResolvedExpr, ResolvedExprKind,
            ResolvedInterfaceDeclaration, ResolvedInterfaceMethod, ResolvedNominalType,
            ResolvedRegistry, ResolvedType, ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
            ResolvedTypeVariable, discard_resolved_expression_iteratively,
        },
        source::{ByteRange, Origin, SourceFile},
        types::{ConstructorId, TypeVariableId},
    };
    use std::sync::Arc;

    fn span() -> Span {
        let source = Box::leak(Box::new(
            SourceFile::new("kind-engine.ash", "x").expect("the fixture should fit"),
        ));
        source
            .span(ByteRange::new(0, 1).expect("the range is ordered"))
            .expect("the range belongs to the fixture")
    }

    fn deep_kind(depth: usize) -> Kind {
        let mut kind = Kind::Type;
        for _ in 0..depth {
            kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
        }
        kind
    }

    fn fact_type(ty: Type, span: Span) -> ResolvedType {
        ResolvedType {
            ty,
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: Origin::Source(span),
            span,
        }
    }

    fn method_fixture(
        span: Span,
        methods: Vec<(Box<[ResolvedTypeVariable]>, bool, Type)>,
    ) -> (ResolvedRegistry, ResolvedInterfaceDeclaration) {
        let module = ModuleId::new(0);
        let interface_id = InterfaceId::new(module, 0);
        let parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 0),
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let mut canonical = vec![parameter.clone()];
        canonical.extend(
            methods
                .iter()
                .flat_map(|(parameters, _, _)| parameters.iter().cloned()),
        );
        let methods = methods
            .into_iter()
            .enumerate()
            .map(
                |(index, (type_parameters, has_explicit_type_parameters, ty))| {
                    ResolvedInterfaceMethod {
                        id: MethodId::new(interface_id, index as u32),
                        spelling: format!("method_{index}"),
                        annotation: fact_type(ty, span),
                        type_parameters,
                        has_explicit_type_parameters,
                        origin: Origin::Source(span),
                        span,
                    }
                },
            )
            .collect::<Vec<_>>()
            .into_boxed_slice();
        (
            ResolvedRegistry::new(Vec::new(), Vec::new()).with_additional_type_variables(canonical),
            ResolvedInterfaceDeclaration {
                id: interface_id,
                public: false,
                spelling: "Fixture".into(),
                parameter,
                methods,
                origin: Origin::Source(span),
                span,
            },
        )
    }

    #[test]
    fn absent_method_lists_preserve_predecessor_owner_install_accounting() {
        let span = span();
        let parameter = TypeVariableId::resolved(ModuleId::new(0), 0);
        let (registry, one_method) =
            method_fixture(span, vec![(Box::new([]), false, Type::Variable(parameter))]);
        let mut environments = KindEnvironments::new();
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_interface(&one_method, &registry, &mut environments, &mut measured),
            Ok(DeclarationKindOutcome::Checked)
        ));
        let one_method_work = measured.used();

        let (registry, two_methods) = method_fixture(
            span,
            vec![
                (Box::new([]), false, Type::Variable(parameter)),
                (Box::new([]), false, Type::Variable(parameter)),
            ],
        );
        let predecessor_work = one_method_work
            .checked_sub(1)
            .and_then(|method_work| method_work.checked_mul(2))
            .and_then(|method_work| method_work.checked_add(1))
            .expect("the predecessor accounting formula should fit");
        let mut environments = KindEnvironments::new();
        let mut exact = TypeWorkBudget::with_limit(predecessor_work);
        check_interface(&two_methods, &registry, &mut environments, &mut exact)
            .expect("one owner install plus both unchanged methods should fit exactly");
        assert_eq!(exact.used(), predecessor_work);
    }

    #[test]
    fn following_methods_cannot_see_an_explicit_predecessor_local() {
        let span = span();
        let module = ModuleId::new(0);
        let local = ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 1),
            spelling: "B".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let (registry, interface) = method_fixture(
            span,
            vec![
                (
                    vec![local.clone()].into_boxed_slice(),
                    true,
                    Type::Variable(local.id),
                ),
                (Box::new([]), false, Type::Variable(local.id)),
            ],
        );
        let mut environments = KindEnvironments::new();
        let mut budget = TypeWorkBudget::unbounded();
        let error = match check_interface(&interface, &registry, &mut environments, &mut budget) {
            Err(error) => error,
            Ok(_) => panic!("the following absent-list method must not inherit B"),
        };
        assert!(matches!(error, KindFailure::Internal(_)));
        assert!(
            error
                .to_string()
                .contains("type variable has no canonical kind"),
            "found: {error}",
        );
    }

    #[test]
    fn method_parameter_state_rejects_explicit_empty_and_preserves_valid_states() {
        let span = span();
        let module = ModuleId::new(0);
        let interface_parameter = TypeVariableId::resolved(module, 0);

        let (registry, forged) = method_fixture(
            span,
            vec![(Box::new([]), true, Type::Variable(interface_parameter))],
        );
        let mut environments = KindEnvironments::new();
        let mut budget = TypeWorkBudget::unbounded();
        let error = match check_interface(&forged, &registry, &mut environments, &mut budget) {
            Err(error) => error,
            Ok(_) => panic!("an explicit empty method binder state must be rejected"),
        };
        assert!(matches!(error, KindFailure::Internal(_)));
        assert!(
            error
                .to_string()
                .contains("explicit method binder list is empty"),
            "found: {error}",
        );

        let local = ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 1),
            spelling: "B".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        for (parameters, explicit, expected) in [
            (
                Box::new([]) as Box<[ResolvedTypeVariable]>,
                false,
                DeclarationKindOutcome::Checked,
            ),
            (
                vec![local.clone()].into_boxed_slice(),
                false,
                DeclarationKindOutcome::Deferred,
            ),
            (
                vec![local.clone()].into_boxed_slice(),
                true,
                DeclarationKindOutcome::Checked,
            ),
        ] {
            let ty = if explicit {
                Type::Variable(local.id)
            } else {
                Type::Variable(interface_parameter)
            };
            let (registry, interface) = method_fixture(span, vec![(parameters, explicit, ty)]);
            let mut environments = KindEnvironments::new();
            let mut budget = TypeWorkBudget::unbounded();
            let outcome = check_interface(&interface, &registry, &mut environments, &mut budget)
                .expect("each representable method parameter state should pass kind admission");
            assert!(
                matches!(
                    (outcome, expected),
                    (
                        DeclarationKindOutcome::Checked,
                        DeclarationKindOutcome::Checked
                    ) | (
                        DeclarationKindOutcome::Deferred,
                        DeclarationKindOutcome::Deferred
                    )
                ),
                "the valid method state must retain its expected outcome",
            );
        }
    }

    #[test]
    fn retained_kind_mirror_continuations_are_exact_for_both_deep_spines() {
        const DEPTH: usize = 32_768;
        const EXACT_WORK: usize = 5 * DEPTH + 1;

        #[derive(Clone, Copy)]
        enum Spine {
            Left,
            Right,
        }

        fn kind(spine: Spine, late_mismatch: bool) -> Kind {
            match spine {
                Spine::Right => {
                    let mut kind = if late_mismatch {
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                    } else {
                        Kind::Type
                    };
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                }
                Spine::Left => {
                    let mut kind = Kind::Type;
                    for index in 0..DEPTH {
                        let codomain = if late_mismatch && index == DEPTH - 1 {
                            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                        } else {
                            Kind::Type
                        };
                        kind = Kind::Arrow(Box::new(kind), Box::new(codomain));
                    }
                    kind
                }
            }
        }

        fn authenticate(
            canonical: &Kind,
            first: &Kind,
            second: &Kind,
            limit: usize,
        ) -> (Result<(), LinkedKindMirrorFailure>, usize) {
            let mut budget = crate::interface::InterfaceConstraintBudget::with_limit(limit);
            let result = {
                let mut ledger = SynthesisLedger::BodyFree(&mut budget);
                authenticate_kind_descendants_with_ledger(
                    canonical,
                    Some(RetainedKindMirrors::Two(first, second)),
                    &mut ledger,
                )
            };
            (result, budget.used())
        }

        std::thread::Builder::new()
            .name("deep-retained-kind-mirrors".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                for spine in [Spine::Right, Spine::Left] {
                    let canonical = kind(spine, false);
                    let first = kind(spine, false);
                    let second = kind(spine, false);
                    assert_eq!(
                        authenticate(&canonical, &first, &second, EXACT_WORK - 1),
                        (Err(LinkedKindMirrorFailure::Resource), EXACT_WORK - 1),
                    );
                    assert_eq!(
                        authenticate(&canonical, &first, &second, EXACT_WORK),
                        (Ok(()), EXACT_WORK),
                    );
                    drop(canonical);
                    drop(first);
                    drop(second);

                    let canonical = kind(spine, false);
                    let first = kind(spine, false);
                    let second = kind(spine, true);
                    assert_eq!(
                        authenticate(&canonical, &first, &second, EXACT_WORK - 1),
                        (Err(LinkedKindMirrorFailure::Resource), EXACT_WORK - 1),
                    );
                    assert_eq!(
                        authenticate(&canonical, &first, &second, EXACT_WORK),
                        (Err(LinkedKindMirrorFailure::Mismatch), EXACT_WORK),
                    );
                    drop(canonical);
                    drop(first);
                    drop(second);
                }
            })
            .expect("the deep retained-mirror worker should start")
            .join()
            .expect("both retained Kind spines must authenticate and tear down on 256 KiB");
    }

    fn unit_expression(span: Span) -> ResolvedExpr {
        ResolvedExpr {
            kind: ResolvedExprKind::Unit,
            span,
        }
    }

    fn empty_module_parts(span: Span) -> ResolvedModuleParts {
        ResolvedModuleParts {
            module: ModuleId::new(0),
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: Vec::new(),
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate: ResolvedExportCandidate::default(),
            span,
        }
    }

    fn assert_exact_internal(
        parts: &ResolvedModuleParts,
        provenance: &[Vec<crate::resolve::ConstructorPayloadProvenance>],
        message: &str,
    ) {
        let mut measured = TypeWorkBudget::unbounded();
        let failure = check_resolved_module_with_budget(parts, provenance, &mut measured)
            .expect_err("the forged module must be rejected");
        assert!(matches!(failure, KindFailure::Internal(_)));
        assert!(failure.to_string().contains(message), "found: {failure}");
        let exact_work = measured.used();
        assert!(
            exact_work > 0,
            "every failed lookup/authentication is charged"
        );

        let mut short = TypeWorkBudget::with_limit(exact_work - 1);
        assert!(matches!(
            check_resolved_module_with_budget(parts, provenance, &mut short),
            Err(KindFailure::Resource(_))
        ));
        let mut exact = TypeWorkBudget::with_limit(exact_work);
        let failure = check_resolved_module_with_budget(parts, provenance, &mut exact)
            .expect_err("the exact budget reaches the internal invariant failure");
        assert!(matches!(failure, KindFailure::Internal(_)));
        assert_eq!(exact.used(), exact_work);
    }

    #[test]
    fn fixed_environment_lookups_are_exact_and_missing_entries_are_charged() {
        let span = span();
        let declared = TypeVariableId::new(0);
        let missing = TypeVariableId::new(1);
        let inference = InferenceVariableId::new(0);
        let nominal = NominalTypeId::new(ModuleId::new(0), 0);
        let interface = InterfaceId::new(ModuleId::new(0), 0);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let parameter = ResolvedTypeVariable {
            id: declared,
            spelling: "F".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let mut environments = KindEnvironments::new();
        environments
            .insert_declared(declared, &kind, span, &mut TypeWorkBudget::unbounded())
            .expect("the declared entry should install");
        environments
            .insert_inference(
                inference,
                &kind,
                Some(span),
                &mut TypeWorkBudget::unbounded(),
                span,
            )
            .expect("the fixed inference entry should install");
        // XI retains one environment record, one result Type root, the copied
        // parameter Kind, and one Arrow: 1 + 1 + 1 + 1 = 4.
        let mut xi_exact = TypeWorkBudget::with_limit(4);
        environments
            .insert_nominal(
                nominal,
                std::slice::from_ref(&parameter),
                span,
                &mut xi_exact,
            )
            .expect("the exact XI retention budget should fit");
        assert_eq!(xi_exact.used(), 4);
        environments
            .insert_interface(interface, &kind, span, &mut TypeWorkBudget::unbounded())
            .expect("the IOTA entry should install");

        for ty in [
            Type::Variable(declared),
            Type::Inference(inference),
            Type::Nominal(nominal),
        ] {
            let kind_nodes = match ty {
                Type::Nominal(_) => 3,
                _ => 3,
            };
            // W(atomic) reuses one current-state slot for the Visit and result.
            let exact_work = kind_nodes + 1;
            let mut exact = TypeWorkBudget::with_limit(exact_work);
            assert!(environments.synthesize(&ty, None, span, &mut exact).is_ok());
            assert_eq!(exact.used(), exact_work);
            let mut short = TypeWorkBudget::with_limit(exact_work - 1);
            assert!(matches!(
                environments.synthesize(&ty, None, span, &mut short),
                Err(KindFailure::Resource(_))
            ));
        }

        // One scheduled Visit plus one failed lookup attempt.
        let mut missing_budget = TypeWorkBudget::with_limit(2);
        assert!(matches!(
            environments.synthesize(&Type::Variable(missing), None, span, &mut missing_budget,),
            Err(KindFailure::Internal(_))
        ));
        assert_eq!(missing_budget.used(), 2);

        let empty = KindEnvironments::new();
        let mut omega_budget = TypeWorkBudget::with_limit(2);
        assert!(matches!(
            empty.synthesize(
                &Type::Inference(InferenceVariableId::new(9)),
                None,
                span,
                &mut omega_budget,
            ),
            Err(KindFailure::Internal(_))
        ));
        assert_eq!(omega_budget.used(), 2);
        let mut iota_budget = TypeWorkBudget::with_limit(1);
        assert!(matches!(
            empty.expect_body_free_interface_argument(
                InterfaceId::new(ModuleId::new(0), 9),
                &Type::Int,
                span,
                &mut iota_budget,
            ),
            Err(KindFailure::Internal(_))
        ));
        assert_eq!(iota_budget.used(), 1);
    }

    #[test]
    fn malformed_body_free_kinds_and_duplicate_environments_are_internal() {
        let span = span();
        let identity = TypeVariableId::new(0);
        let nominal = NominalTypeId::new(ModuleId::new(0), 0);
        let type_kind = Kind::Type;
        let mut environments = KindEnvironments::new();
        environments
            .insert_declared(identity, &type_kind, span, &mut TypeWorkBudget::unbounded())
            .expect("the first DELTA entry should install");
        assert!(matches!(
            environments.insert_declared(
                identity,
                &type_kind,
                span,
                &mut TypeWorkBudget::unbounded(),
            ),
            Err(KindFailure::Internal(_))
        ));
        environments
            .insert_nominal(nominal, &[], span, &mut TypeWorkBudget::unbounded())
            .expect("the first XI entry should install");
        assert!(matches!(
            environments.insert_nominal(nominal, &[], span, &mut TypeWorkBudget::unbounded(),),
            Err(KindFailure::Internal(_))
        ));

        let application =
            Type::Application(Box::new(Type::Variable(identity)), Box::new(Type::Int));
        assert!(matches!(
            environments.synthesize(&application, None, span, &mut TypeWorkBudget::unbounded(),),
            Err(KindFailure::Internal(_))
        ));

        let empty_tuple_argument =
            Type::Application(Box::new(Type::Int), Box::new(Type::Tuple(Box::new([]))));
        assert!(matches!(
            environments.synthesize(
                &empty_tuple_argument,
                None,
                span,
                &mut TypeWorkBudget::unbounded(),
            ),
            Err(KindFailure::Internal(_))
        ));
    }

    #[test]
    fn deep_fixed_kind_lookup_is_stack_safe_and_exact() {
        const DEPTH: usize = 32_768;
        std::thread::Builder::new()
            .name("deep-kind-lookup".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let span = span();
                let kind = deep_kind(DEPTH);
                let nodes = 2 * DEPTH + 1;
                let identity = TypeVariableId::new(0);
                let mut environments = KindEnvironments::new();
                environments
                    .insert_declared(identity, &kind, span, &mut TypeWorkBudget::unbounded())
                    .expect("the deep DELTA entry should install");
                // S(variable)=|DELTA(v)| and one current-state slot is reused
                // for the Visit and result.
                let exact_work = nodes + 1;
                let mut exact = TypeWorkBudget::with_limit(exact_work);
                assert!(
                    environments
                        .synthesize(&Type::Variable(identity), None, span, &mut exact)
                        .is_ok()
                );
                assert_eq!(exact.used(), exact_work);
                let mut short = TypeWorkBudget::with_limit(exact_work - 1);
                assert!(matches!(
                    environments.synthesize(&Type::Variable(identity), None, span, &mut short,),
                    Err(KindFailure::Resource(_))
                ));
            })
            .expect("the deep lookup thread should start")
            .join()
            .expect("deep lookup and teardown should stay on the explicit stacks");
    }

    #[test]
    fn synthesis_work_storage_is_exact_for_left_deep_applications_and_wide_tuples() {
        const DEPTH: usize = 32_768;
        const WIDTH: usize = 32_768;
        std::thread::Builder::new()
            .name("deep-wide-kind-synthesis".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let span = span();
                let nominal = NominalTypeId::new(ModuleId::new(0), 0);
                let parameters = (0..DEPTH)
                    .map(|index| ResolvedTypeVariable {
                        id: TypeVariableId::new(index as u32),
                        spelling: format!("A{index}"),
                        kind: Kind::Type,
                        origin: Origin::Source(span),
                    })
                    .collect::<Vec<_>>();
                let mut environments = KindEnvironments::new();
                environments
                    .insert_nominal(nominal, &parameters, span, &mut TypeWorkBudget::unbounded())
                    .expect("the application constructor kind should install");

                let mut application = Type::Nominal(nominal);
                for _ in 0..DEPTH {
                    application = Type::Application(Box::new(application), Box::new(Type::Int));
                }
                // S=5D+1: the 2D+1-node XI result, D argument nodes, D
                // application nodes, and D domain comparisons. W retains one
                // reusable current-state slot plus D application continuations.
                // Total: 6D+2.
                const APPLICATION_WORK: usize = 6 * DEPTH + 2;
                let mut short = TypeWorkBudget::with_limit(APPLICATION_WORK - 1);
                assert!(matches!(
                    environments.synthesize(&application, None, span, &mut short),
                    Err(KindFailure::Resource(_))
                ));
                let mut exact = TypeWorkBudget::with_limit(APPLICATION_WORK);
                assert!(
                    environments
                        .synthesize(&application, None, span, &mut exact)
                        .is_ok()
                );
                assert_eq!(exact.used(), APPLICATION_WORK);

                let tuple = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
                // S=1+N and P=N. W retains one reusable current-state slot and
                // one tuple continuation: total 2N+3.
                const TUPLE_WORK: usize = 2 * WIDTH + 3;
                let mut short = TypeWorkBudget::with_limit(TUPLE_WORK - 1);
                assert!(matches!(
                    environments.synthesize(&tuple, None, span, &mut short),
                    Err(KindFailure::Resource(_))
                ));
                let mut exact = TypeWorkBudget::with_limit(TUPLE_WORK);
                assert!(
                    environments
                        .synthesize(&tuple, None, span, &mut exact)
                        .is_ok()
                );
                assert_eq!(exact.used(), TUPLE_WORK);
                crate::types::discard_type_iteratively(tuple);
                crate::types::discard_type_iteratively(application);
            })
            .expect("the deep/wide synthesis thread should start")
            .join()
            .expect("synthesis and teardown should remain within 256 KiB");
    }

    #[test]
    fn function_synthesis_and_source_diagnostic_retention_have_exact_formulas() {
        let span = span();
        let environments = KindEnvironments::new();
        let function = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));
        // S(function)=1 + S(Int)+P(Type,Type) + S(Bool)+P(Type,Type)=5.
        // W retains one reusable current-state slot and one continuation: 7.
        const FUNCTION_WORK: usize = 7;
        let mut short = TypeWorkBudget::with_limit(FUNCTION_WORK - 1);
        assert!(matches!(
            environments.synthesize(&function, None, span, &mut short),
            Err(KindFailure::Resource(_))
        ));
        let mut exact = TypeWorkBudget::with_limit(FUNCTION_WORK);
        assert!(
            environments
                .synthesize(&function, None, span, &mut exact)
                .is_ok()
        );
        assert_eq!(exact.used(), FUNCTION_WORK);

        let nominal = NominalTypeId::new(ModuleId::new(0), 0);
        let parameter = ResolvedTypeVariable {
            id: TypeVariableId::new(0),
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let mut environments = KindEnvironments::new();
        environments
            .insert_nominal(
                nominal,
                std::slice::from_ref(&parameter),
                span,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the diagnostic nominal kind should install");
        let provenance =
            ResolvedTypeProvenance::new(vec![ResolvedTypeProvenanceNode::Fact(span)], 0);
        // S(nominal)=3 and W(atomic)=1; the failed Type comparison is 1.
        // The diagnostic then clones 1+3 Kind nodes and renders 1+3 nodes:
        // 3 + 1 + 1 + 4 + 4 = 13.
        const DIAGNOSTIC_WORK: usize = 13;
        let mut short = TypeWorkBudget::with_limit(DIAGNOSTIC_WORK - 1);
        assert!(matches!(
            environments.expect_value_type_parts(
                &Type::Nominal(nominal),
                &provenance,
                span,
                &mut short,
            ),
            Err(KindFailure::Resource(_))
        ));
        let mut exact = TypeWorkBudget::with_limit(DIAGNOSTIC_WORK);
        let failure = environments
            .expect_value_type_parts(&Type::Nominal(nominal), &provenance, span, &mut exact)
            .expect_err("the exact diagnostic budget should retain the source failure");
        assert!(matches!(failure, KindFailure::Source(_)));
        assert_eq!(exact.used(), DIAGNOSTIC_WORK);
    }

    #[test]
    fn expression_work_is_exact_and_deep_traversal_is_stack_safe() {
        const DEPTH: usize = 32_768;
        std::thread::Builder::new()
            .name("deep-kind-body-work".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let span = span();
                let environments = KindEnvironments::new();
                let mut expression = unit_expression(span);
                for _ in 0..DEPTH {
                    expression = ResolvedExpr {
                        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                            function: Box::new(expression),
                            argument: Box::new(unit_expression(span)),
                        }),
                        span,
                    };
                }
                // Every one of 2D+1 expressions is scheduled and visited.
                const EXACT_WORK: usize = 2 * (2 * DEPTH + 1);
                let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert!(matches!(
                    check_expression_annotations(&expression, &environments, &mut short),
                    Err(KindFailure::Resource(_))
                ));
                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                assert!(
                    check_expression_annotations(&expression, &environments, &mut exact).is_ok()
                );
                assert_eq!(exact.used(), EXACT_WORK);
                discard_resolved_expression_iteratively(expression);
            })
            .expect("the deep body-work thread should start")
            .join()
            .expect("deep body scheduling, traversal, and teardown should stay iterative");
    }

    #[test]
    fn nested_block_results_are_scheduled_once() {
        let span = span();
        let expression = ResolvedExpr {
            kind: ResolvedExprKind::Block(ResolvedBlock {
                declarations: Vec::new(),
                result: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Block(ResolvedBlock {
                        declarations: Vec::new(),
                        result: Box::new(unit_expression(span)),
                        span,
                    }),
                    span,
                }),
                span,
            }),
            span,
        };
        // The outer block, inner block, and unit result are each scheduled
        // and visited exactly once: 3 * 2 = 6.
        const EXACT_WORK: usize = 6;
        let environments = KindEnvironments::new();
        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            check_expression_annotations(&expression, &environments, &mut short),
            Err(KindFailure::Resource(_))
        ));
        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        assert!(check_expression_annotations(&expression, &environments, &mut exact).is_ok());
        assert_eq!(exact.used(), EXACT_WORK);
    }

    #[test]
    fn module_gate_charges_missing_indexes_and_authenticates_constructor_pairing() {
        let span = span();
        let module = ModuleId::new(0);
        let nominal_id = NominalTypeId::new(module, 0);
        let first_id = ConstructorId::new(nominal_id, 0);
        let second_id = ConstructorId::new(nominal_id, 1);
        let origin = Origin::Source(span);

        let mut missing_parameters = empty_module_parts(span);
        missing_parameters.registry = Arc::new(ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal_id,
                spelling: "MissingParameters".into(),
                constructors: Vec::new().into_boxed_slice(),
                origin: origin.clone(),
            }],
            Vec::new(),
        ));
        missing_parameters.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &missing_parameters,
            &[Vec::new()],
            "no canonical parameter slice",
        );

        let mut invalid_order = empty_module_parts(span);
        invalid_order.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(&invalid_order, &[], "out of source order index");

        let nominal = |constructors: Vec<ConstructorId>| ResolvedNominalType {
            id: nominal_id,
            spelling: "Pairing".into(),
            constructors: constructors.into_boxed_slice(),
            origin: origin.clone(),
        };
        let constructor = |id| ResolvedConstructor {
            id,
            owner: nominal_id,
            spelling: "C".into(),
            payload: None,
            origin: origin.clone(),
        };

        let mut missing_group = empty_module_parts(span);
        missing_group.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal(Vec::new())], Vec::new())
                .with_type_parameters(vec![(nominal_id, Vec::new())]),
        );
        missing_group.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &missing_group,
            &[],
            "payload provenance has the wrong outer cardinality",
        );

        let mut missing_record = empty_module_parts(span);
        missing_record.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal(vec![first_id])], vec![constructor(first_id)])
                .with_type_parameters(vec![(nominal_id, Vec::new())]),
        );
        missing_record.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &missing_record,
            &[Vec::new()],
            "incomplete constructor payload provenance",
        );

        let mut missing_constructor = empty_module_parts(span);
        missing_constructor.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal(vec![first_id])], Vec::new())
                .with_type_parameters(vec![(nominal_id, Vec::new())]),
        );
        missing_constructor.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &missing_constructor,
            &[vec![crate::resolve::ConstructorPayloadProvenance {
                constructor: first_id,
                fields: Vec::new(),
            }]],
            "missing canonical constructor",
        );

        let mut permuted = empty_module_parts(span);
        permuted.registry = Arc::new(
            ResolvedRegistry::new(
                vec![nominal(vec![first_id, second_id])],
                vec![constructor(first_id), constructor(second_id)],
            )
            .with_type_parameters(vec![(nominal_id, Vec::new())]),
        );
        permuted.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &permuted,
            &[vec![
                crate::resolve::ConstructorPayloadProvenance {
                    constructor: second_id,
                    fields: Vec::new(),
                },
                crate::resolve::ConstructorPayloadProvenance {
                    constructor: first_id,
                    fields: Vec::new(),
                },
            ]],
            "paired with the wrong identity",
        );
    }

    #[test]
    fn declaration_order_is_a_complete_exact_and_atomic_partition() {
        fn nominal_parts(count: usize, span: Span) -> ResolvedModuleParts {
            let module = ModuleId::new(0);
            let nominals = (0..count)
                .map(|index| ResolvedNominalType {
                    id: NominalTypeId::new(module, index as u32),
                    spelling: format!("T{index}"),
                    constructors: Vec::new().into_boxed_slice(),
                    origin: Origin::Source(span),
                })
                .collect::<Vec<_>>();
            let parameters = nominals
                .iter()
                .map(|nominal| (nominal.id, Vec::new()))
                .collect::<Vec<_>>();
            let mut parts = empty_module_parts(span);
            parts.registry = Arc::new(
                ResolvedRegistry::new(nominals, Vec::new()).with_type_parameters(parameters),
            );
            parts
        }

        let span = span();
        let provenance = [Vec::new(), Vec::new()];

        let mut omitted = nominal_parts(2, span);
        omitted.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(&omitted, &provenance, "under-covers local declarations");

        let mut duplicate = nominal_parts(2, span);
        duplicate.declaration_order = vec![
            ResolvedDeclarationIndex::Type(0),
            ResolvedDeclarationIndex::Type(0),
        ];
        assert_exact_internal(&duplicate, &provenance, "out of source order");

        let mut out_of_order = nominal_parts(2, span);
        out_of_order.declaration_order = vec![
            ResolvedDeclarationIndex::Type(1),
            ResolvedDeclarationIndex::Type(0),
        ];
        assert_exact_internal(&out_of_order, &provenance, "out of source order");

        let empty = empty_module_parts(span);
        assert_exact_internal(
            &empty,
            &[Vec::new()],
            "payload provenance has the wrong outer cardinality",
        );

        let mut valid = nominal_parts(2, span);
        valid.declaration_order = vec![
            ResolvedDeclarationIndex::Type(0),
            ResolvedDeclarationIndex::Type(1),
        ];
        // Declaration-order authentication visits two retained entries, one
        // final partition fact, and one provenance-cardinality fact. XI then
        // retains one environment record and one Type root per nominal:
        // 2 + 1 + 1 + 2 * (1 + 1) = 8.
        const EXACT_WORK: usize = 8;
        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            check_resolved_module_with_budget(&valid, &provenance, &mut short),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(valid.declaration_order.len(), 2);
        assert_eq!(valid.registry.nominals().len(), 2);

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        check_resolved_module_with_budget(&valid, &provenance, &mut exact)
            .expect("the complete declaration partition should fit exactly");
        assert_eq!(exact.used(), EXACT_WORK);
    }

    #[test]
    fn canonical_owner_authentication_precedes_declaration_consumers() {
        let span = span();
        let module = ModuleId::new(0);
        let nominal_id = NominalTypeId::new(module, 0);
        let identity = TypeVariableId::resolved(module, 0);
        let origin = Origin::Source(span);
        let parameter = ResolvedTypeVariable {
            id: identity,
            spelling: "A".into(),
            kind: Kind::Type,
            origin: origin.clone(),
        };
        let nominal = ResolvedNominalType {
            id: nominal_id,
            spelling: "Owner".into(),
            constructors: Vec::new().into_boxed_slice(),
            origin: origin.clone(),
        };

        let mut duplicate = empty_module_parts(span);
        duplicate.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal.clone()], Vec::new()).with_type_parameters(vec![(
                nominal_id,
                vec![parameter.clone(), parameter.clone()],
            )]),
        );
        duplicate.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &duplicate,
            &[Vec::new()],
            "repeats a type-variable identity",
        );

        let forged = ResolvedTypeVariable {
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            ..parameter.clone()
        };
        let mut order_collision = empty_module_parts(span);
        order_collision.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal], Vec::new())
                .with_type_parameters(vec![(nominal_id, vec![parameter])])
                .with_additional_type_variables([forged]),
        );
        order_collision.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        assert_exact_internal(
            &order_collision,
            &[Vec::new()],
            "binder conflicts with its canonical registry record",
        );
    }

    #[test]
    fn kind_gate_failure_dismantles_unpublished_deep_module_parts_iteratively() {
        const DEPTH: usize = 32_768;
        std::thread::Builder::new()
            .name("kind-gate-admission-teardown".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let span = span();
                let module = ModuleId::new(0);
                let nominal_id = NominalTypeId::new(module, 0);
                let constructor_id = ConstructorId::new(nominal_id, 0);
                let origin = Origin::Source(span);
                let mut payload = Type::Int;
                for _ in 0..DEPTH {
                    payload = Type::Application(Box::new(payload), Box::new(Type::Int));
                }
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal_id,
                        spelling: "Deep".into(),
                        constructors: Box::new([constructor_id]),
                        origin: origin.clone(),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor_id,
                        owner: nominal_id,
                        spelling: "Deep".into(),
                        payload: Some(payload),
                        origin,
                    }],
                )
                .with_type_parameters(vec![(nominal_id, Vec::new())]);
                let mut parts = empty_module_parts(span);
                parts.registry = Arc::new(registry);
                parts.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
                let mut budget = TypeWorkBudget::unbounded();
                assert!(matches!(
                    check_resolved_module_with_budget(&parts, &[], &mut budget),
                    Err(KindFailure::Internal(_))
                ));
                drop(parts);
            })
            .expect("the admission teardown thread should start")
            .join()
            .expect("kind failure must dismantle unpublished parts within 256 KiB");
    }
}
