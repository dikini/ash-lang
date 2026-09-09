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
        ResolvedExpr, ResolvedExprKind, ResolvedImplementation, ResolvedInterfaceApplication,
        ResolvedInterfaceDeclaration, ResolvedLocalDeclaration, ResolvedModuleParts,
        ResolvedNominalDeclarationKind, ResolvedRecursiveMember, ResolvedRegistry, ResolvedType,
        ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
    },
    source::Span,
    types::{
        EffectRow, InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget,
        charge_kind_descendants, charge_kind_with_charge, clone_arrows_with_budget,
        clone_kind_with_budget, render_kind_with_budget, same_effect_rows_with_charge,
        same_kind_with_budget, same_kind_with_charge,
    },
};

static TYPE_KIND: Kind = Kind::Type;

pub(crate) fn binder_kind_is_admitted(kind: &Kind, allow_effect_row: bool) -> bool {
    match kind {
        Kind::Type => true,
        Kind::EffectRow => allow_effect_row,
        Kind::Arrow(_, _) => {
            let mut work = vec![kind];
            while let Some(kind) = work.pop() {
                match kind {
                    Kind::Type => {}
                    Kind::EffectRow => return false,
                    Kind::Arrow(domain, codomain) => {
                        work.push(codomain);
                        work.push(domain);
                    }
                }
            }
            true
        }
    }
}

/// Minimal charging seam for the total kind-synthesis engine.
///
/// Resolved checking supplies [`TypeWorkBudget`]. Linked evidence validation
/// supplies its graph-wide constraint ledger without importing that layer into
/// the kind module.
pub(crate) trait KindWorkLedger {
    fn charge(&mut self, work: usize) -> Result<(), ()>;
}

#[derive(Clone, Copy)]
pub(crate) enum BodyFreeInterfaceMethodSeed<'a> {
    AllInterfaceParameters,
    Determined(&'a [TypeVariableId]),
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
    pub(crate) fn message(&self) -> Option<crate::message::Message<'_>> {
        let found = self.diagnostic.found.as_deref()?;
        Some(match self.diagnostic.reason {
            KindReason::ExpectedType => crate::message::Message::kind_expected_type(found),
            KindReason::NotApplicable => crate::message::Message::kind_not_applicable(found),
            KindReason::Argument => {
                crate::message::Message::kind_argument(self.diagnostic.expected.as_deref()?, found)
            }
        })
    }

    pub(crate) fn related_message(
        &self,
    ) -> Option<(crate::message::Message<'_>, &'static str, &str)> {
        match self.diagnostic.reason {
            KindReason::Argument => {
                let expected = self.diagnostic.expected.as_deref()?;
                Some((
                    crate::message::Message::kind_required_declaration(expected),
                    "required_kind_declaration",
                    expected,
                ))
            }
            KindReason::ExpectedType | KindReason::NotApplicable => {
                let found = self.diagnostic.found.as_deref()?;
                Some((
                    crate::message::Message::kind_found_declaration(found),
                    "found_kind_declaration",
                    found,
                ))
            }
        }
    }

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
    pub(crate) fn resource_presentation(&self) -> Option<(Span, crate::message::Message<'static>)> {
        let Self::Resource(failure) = self else {
            return None;
        };
        Some((failure.span, crate::message::Message::kind_resources()))
    }

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
    parameters: &'a [crate::resolved::ResolvedTypeVariable],
    determination: Option<InterfaceKindDetermination<'a>>,
}

#[derive(Clone, Copy)]
enum InterfaceKindDetermination<'a> {
    Resolved(&'a crate::resolved::ResolvedInterfaceDetermination),
    Checked(&'a crate::interface::DeterminationKey),
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
    effects: Option<HashMap<crate::types::EffectId, &'a [crate::resolved::ResolvedTypeVariable]>>,
}

impl<'a> KindEnvironments<'a> {
    pub(crate) fn new() -> Self {
        Self {
            delta: HashMap::new(),
            omega: HashMap::new(),
            xi: HashMap::new(),
            iota: HashMap::new(),
            effects: None,
        }
    }

    fn install_effects(
        &mut self,
        registry: &'a crate::resolved::ResolvedRegistry,
        local: &'a [crate::resolved::ResolvedEffectDeclaration],
        imported: impl Iterator<Item = &'a crate::resolved::ResolvedEffectDeclaration>,
        budget: &mut TypeWorkBudget,
        span: Span,
    ) -> Result<(), KindFailure> {
        let mut effects = HashMap::new();
        for source in local {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-kind registry authentication exceeded its type-work budget",
                )
            })?;
            effects.try_reserve(1).map_err(|_| {
                KindFailure::resource(span, "effect-kind registry could not reserve storage")
            })?;
            let effect = registry.effect(source.id).ok_or_else(|| {
                KindFailure::internal(span, "a local effect has no canonical registry fact")
            })?;
            if effects
                .insert(effect.id, effect.parameters.as_ref())
                .is_some()
            {
                return Err(KindFailure::internal(
                    span,
                    "the checked effect registry repeats a canonical identity",
                ));
            }
        }
        for effect in imported {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-kind registry authentication exceeded its type-work budget",
                )
            })?;
            effects.try_reserve(1).map_err(|_| {
                KindFailure::resource(span, "effect-kind registry could not reserve storage")
            })?;
            if effects
                .insert(effect.id, effect.parameters.as_ref())
                .is_some()
            {
                return Err(KindFailure::internal(
                    span,
                    "the checked effect registry repeats a canonical identity",
                ));
            }
        }
        self.effects = (!effects.is_empty()).then_some(effects);
        Ok(())
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
        if !binder_kind_is_admitted(kind, true) {
            return Err(KindFailure::internal(
                origin,
                "EffectRow cannot occur beneath a kind arrow",
            ));
        }
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
            if !binder_kind_is_admitted(&parameter.kind, false) {
                return Err(KindFailure::internal(
                    parameter.origin.primary_span(),
                    "this owner cannot bind an EffectRow parameter",
                ));
            }
            self.insert_declared(
                parameter.id,
                &parameter.kind,
                parameter.origin.primary_span(),
                budget,
            )?;
        }
        Ok(())
    }

    fn extend_owner_parameters(
        &mut self,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        for (installed, parameter) in parameters.iter().enumerate() {
            if !binder_kind_is_admitted(&parameter.kind, false) {
                self.remove_owner_parameter_extension(&parameters[..installed]);
                return Err(KindFailure::internal(
                    parameter.origin.primary_span(),
                    "this owner cannot bind an EffectRow parameter",
                ));
            }
            if let Err(failure) = self.insert_declared(
                parameter.id,
                &parameter.kind,
                parameter.origin.primary_span(),
                budget,
            ) {
                self.remove_owner_parameter_extension(&parameters[..installed]);
                return Err(failure);
            }
        }
        Ok(())
    }

    fn remove_owner_parameter_extension(
        &mut self,
        parameters: &[crate::resolved::ResolvedTypeVariable],
    ) {
        for parameter in parameters {
            self.delta.remove(&parameter.id);
        }
    }

    fn install_scheme_parameters(
        &mut self,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.clear_declared();
        for parameter in parameters {
            if !binder_kind_is_admitted(&parameter.kind, true) {
                return Err(KindFailure::internal(
                    parameter.origin.primary_span(),
                    "EffectRow cannot occur beneath a kind arrow",
                ));
            }
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
        allow_effect_row: bool,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.clear_declared();
        for (identity, kind) in parameters {
            if !binder_kind_is_admitted(kind, allow_effect_row) {
                return Err(KindFailure::internal(
                    origin,
                    if allow_effect_row {
                        "EffectRow cannot occur beneath a kind arrow"
                    } else {
                        "this owner cannot bind an EffectRow parameter"
                    },
                ));
            }
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
            if !binder_kind_is_admitted(&parameter.kind, false)
                || !binder_kind_is_admitted(&source.kind, false)
            {
                return Err(KindFailure::internal(
                    span,
                    "an implementation owner cannot bind an EffectRow parameter",
                ));
            }
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

    /// Checks one body-free interface method in a single type walk. The method
    /// must be a function, may mention only its owning interface parameters and
    /// declared method parameters, must mention every required interface seed
    /// and method parameter, and must end at kind `Type`.
    pub(crate) fn expect_body_free_interface_method_with_ledger(
        &self,
        ty: &Type,
        interface_parameters: &[TypeVariableId],
        seed: BodyFreeInterfaceMethodSeed<'_>,
        method_parameters: &[TypeVariableId],
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        if ty.function_view().is_none() {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface method is not a function",
            ));
        }
        if interface_parameters.is_empty() {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface method has an empty required seed",
            ));
        }
        let parameter_count = method_parameters
            .len()
            .checked_add(interface_parameters.len())
            .ok_or_else(|| {
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
        for parameter in interface_parameters {
            if !allowed.insert(*parameter) {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface repeats a type parameter",
                ));
            }
        }
        for method_parameter in method_parameters {
            if !allowed.insert(*method_parameter) {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface method repeats a type parameter",
                ));
            }
        }
        if let BodyFreeInterfaceMethodSeed::Determined(required) = seed {
            if required.is_empty() || required.len() >= interface_parameters.len() {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface has an empty or complete determinant seed",
                ));
            }
            let mut next_interface = 0;
            for required_parameter in required {
                let mut found = false;
                while let Some(parameter) = interface_parameters.get(next_interface) {
                    budget.charge(1).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "body-free interface determinant authentication exceeded its owning work budget",
                        )
                    })?;
                    next_interface += 1;
                    if parameter == required_parameter {
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Err(KindFailure::internal(
                        span,
                        "a checked body-free interface seed is not a unique declaration-order subset",
                    ));
                }
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
        let missing_interface_parameter = match seed {
            BodyFreeInterfaceMethodSeed::AllInterfaceParameters => interface_parameters
                .iter()
                .any(|parameter| !visited.contains(parameter)),
            BodyFreeInterfaceMethodSeed::Determined(required) => {
                let mut missing = false;
                for parameter in required {
                    ledger.charge(1).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "body-free interface determinant coverage exceeded its owning work budget",
                        )
                    })?;
                    if !visited.contains(parameter) {
                        missing = true;
                        break;
                    }
                }
                missing
            }
        };
        if missing_interface_parameter
            || method_parameters
                .iter()
                .any(|method_parameter| !visited.contains(method_parameter))
        {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface method omits a required parameter",
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

    /// Checks a paired global value type while permitting only the
    /// independently authenticated dependent-only binders supplied by the
    /// caller to remain absent from that value type.
    pub(crate) fn expect_body_free_paired_global_value_type_with_ledger(
        &self,
        checked: &Type,
        source: &Type,
        allowed_unused: &[TypeVariableId],
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
        self.authenticate_global_owner_coverage(&visited, allowed_unused, span, &mut ledger)?;
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

    /// Checks an operational global value type with the same authenticated
    /// dependent-only exception as the paired equational path.
    pub(crate) fn expect_body_free_exact_global_value_type_with_ledger(
        &self,
        ty: &Type,
        allowed_unused: &[TypeVariableId],
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
        self.authenticate_global_owner_coverage(&visited, allowed_unused, span, &mut ledger)?;
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

    fn authenticate_global_owner_coverage(
        &self,
        visited: &HashSet<TypeVariableId>,
        allowed_unused: &[TypeVariableId],
        span: Span,
        budget: &mut impl KindWorkLedger,
    ) -> Result<(), KindFailure> {
        budget.charge(allowed_unused.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "linked dependent-only binder retention exceeded its owning work budget",
            )
        })?;
        let mut allowed = HashSet::new();
        allowed.try_reserve(allowed_unused.len()).map_err(|_| {
            KindFailure::resource(
                span,
                "linked dependent-only binder retention could not reserve storage",
            )
        })?;
        for identity in allowed_unused {
            if !self.delta.contains_key(identity) || !allowed.insert(*identity) {
                return Err(KindFailure::internal(
                    span,
                    "a linked global has an invalid dependent-only binder allowance",
                ));
            }
        }
        budget.charge(self.delta.len()).map_err(|()| {
            KindFailure::resource(
                span,
                "linked global owner-binder coverage exceeded its owning work budget",
            )
        })?;
        if self
            .delta
            .keys()
            .any(|identity| !visited.contains(identity) && !allowed.contains(identity))
        {
            return Err(KindFailure::internal(
                span,
                "a linked value scheme retains an unused owner binder",
            ));
        }
        Ok(())
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
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.insert_interface_with_determination(identity, parameters, None, origin, budget)
    }

    fn insert_interface_with_determination(
        &mut self,
        identity: InterfaceId,
        parameters: &'a [crate::resolved::ResolvedTypeVariable],
        determination: Option<InterfaceKindDetermination<'a>>,
        origin: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        if parameters.is_empty() {
            return Err(KindFailure::internal(
                origin,
                "an interface has no canonical parameter records",
            ));
        }
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                origin,
                "interface kind environment exceeded its type-work budget",
            )
        })?;
        if let Some(existing) = self.iota.get(&identity) {
            if existing.parameters.len() != parameters.len() {
                return Err(KindFailure::internal(
                    origin,
                    "an interface has conflicting canonical parameter counts",
                ));
            }
            for (existing, parameter) in existing.parameters.iter().zip(parameters) {
                let equal = same_kind_with_budget(&existing.kind, &parameter.kind, budget)
                    .map_err(|()| {
                        KindFailure::resource(
                            origin,
                            "interface kind authentication exceeded its type-work budget",
                        )
                    })?;
                if existing.id != parameter.id
                    || existing.origin.primary_span() != parameter.origin.primary_span()
                    || !equal
                {
                    return Err(KindFailure::internal(
                        origin,
                        "an interface has conflicting canonical parameter records",
                    ));
                }
            }
            return Ok(());
        }
        self.iota.try_reserve(1).map_err(|_| {
            KindFailure::resource(
                origin,
                "interface kind environment could not reserve storage",
            )
        })?;
        self.iota.insert(
            identity,
            InterfaceKindFact {
                parameters,
                determination,
            },
        );
        Ok(())
    }

    pub(crate) fn expect_value_type(
        &self,
        resolved: &ResolvedType,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.expect_value_type_parts(&resolved.ty, &resolved.provenance, resolved.span, budget)
    }

    pub(crate) fn expect_computation_type(
        &self,
        value: &ResolvedType,
        effects: &EffectRow,
        effect_argument_provenance: &[ResolvedTypeProvenance],
        effect_argument_roots: &[usize],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.expect_value_type(value, budget)?;
        let mut ledger = SynthesisLedger::Resolved(budget);
        self.authenticate_effect_row(
            effects,
            effect_argument_provenance,
            effect_argument_roots,
            value.span,
            &mut ledger,
        )
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
        arguments: &[Type],
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
        if arguments.len() != expected.parameters.len() {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface application has the wrong argument count",
            ));
        }
        let mut ledger = SynthesisLedger::BodyFree(budget);
        for (argument, parameter) in arguments.iter().zip(expected.parameters) {
            let found = self.synthesize_with_ledger(
                argument,
                None,
                None,
                None,
                None,
                None,
                span,
                &mut ledger,
            )?;
            let equal = same_kind_with_charge(&parameter.kind, found.kind, || ledger.charge(1))
                .map_err(|()| {
                    KindFailure::resource(
                        span,
                        "body-free interface kind authentication exceeded its owning work budget",
                    )
                })?;
            if !equal {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface argument has the wrong kind",
                ));
            }
        }
        Ok(())
    }

    /// Checks an implementation head and proves that every installed rigid
    /// owner binder occurs in the authenticated head argument.
    pub(crate) fn expect_body_free_exact_owner_interface_argument_with_ledger(
        &self,
        interface: InterfaceId,
        arguments: &[Type],
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
        if arguments.len() != expected.parameters.len() {
            return Err(KindFailure::internal(
                span,
                "a checked body-free interface application has the wrong argument count",
            ));
        }
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
        for (argument, parameter) in arguments.iter().zip(expected.parameters) {
            let found = self.synthesize_with_ledger(
                argument,
                None,
                None,
                None,
                None,
                Some(&mut visited),
                span,
                &mut ledger,
            )?;
            let equal = same_kind_with_charge(&parameter.kind, found.kind, || ledger.charge(1))
                .map_err(|()| {
                    KindFailure::resource(
                        span,
                        "body-free interface kind authentication exceeded its owning work budget",
                    )
                })?;
            if !equal {
                return Err(KindFailure::internal(
                    span,
                    "a checked body-free interface argument has the wrong kind",
                ));
            }
        }
        if visited.len() != self.delta.len() {
            return Err(KindFailure::internal(
                span,
                "a linked implementation head retains an unused rigid binder",
            ));
        }
        Ok(())
    }

    fn expect_body_free_interface_argument(
        &self,
        interface: InterfaceId,
        arguments: &[Type],
        span: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), KindFailure> {
        self.expect_body_free_interface_argument_with_ledger(interface, arguments, span, budget)
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
        visited_variables: Option<&mut HashSet<TypeVariableId>>,
        fallback_span: Span,
        budget: &mut SynthesisLedger<'_>,
    ) -> Result<KindFact<'environment>, KindFailure>
    where
        'a: 'environment,
    {
        self.authenticate_effect_rows(ty, provenance, fallback_span, budget)?;
        self.synthesize_core_with_ledger(
            ty,
            provenance,
            provenance.map(ResolvedTypeProvenance::root),
            type_mirror,
            root_function_domain_mirror,
            allowed_variables,
            visited_variables,
            fallback_span,
            budget,
        )
    }

    fn authenticate_effect_rows<'environment>(
        &'environment self,
        ty: &Type,
        provenance: Option<&ResolvedTypeProvenance>,
        span: Span,
        budget: &mut SynthesisLedger<'_>,
    ) -> Result<(), KindFailure>
    where
        'a: 'environment,
    {
        let Some(effects) = &self.effects else {
            return Ok(());
        };
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                span,
                "effect-row authentication exceeded its owning work budget",
            )
        })?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| {
            KindFailure::resource(
                span,
                "effect-row authentication could not reserve traversal storage",
            )
        })?;
        pending.push((ty, provenance.map(ResolvedTypeProvenance::root)));
        self.authenticate_effect_type_queue(effects, provenance, span, budget, pending)
    }

    fn authenticate_effect_row<'environment>(
        &'environment self,
        row: &EffectRow,
        argument_provenance: &[ResolvedTypeProvenance],
        argument_roots: &[usize],
        span: Span,
        budget: &mut SynthesisLedger<'_>,
    ) -> Result<(), KindFailure>
    where
        'a: 'environment,
    {
        if row.is_empty() {
            if !argument_provenance.is_empty() || !argument_roots.is_empty() {
                return Err(KindFailure::internal(
                    span,
                    "a pure computation retained effect-argument provenance",
                ));
            }
            return Ok(());
        }
        self.authenticate_effect_row_tail(row, None, None, span, budget)?;
        let Some(effects) = &self.effects else {
            return Ok(());
        };
        let mut roots = argument_roots.iter();
        for instance in row.known() {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-row identity lookup exceeded its owning work budget",
                )
            })?;
            let parameters = effects.get(&instance.effect()).ok_or_else(|| {
                KindFailure::internal(span, "an effect row names no canonical checked declaration")
            })?;
            if parameters.len() != instance.arguments().len() {
                return Err(KindFailure::internal(
                    span,
                    "an effect row has the wrong canonical argument count",
                ));
            }
            for (argument, parameter) in instance.arguments().iter().zip(parameters.iter()) {
                let provenance = roots
                    .next()
                    .and_then(|root| argument_provenance.get(*root))
                    .ok_or_else(|| {
                        KindFailure::internal(
                            span,
                            "a computation row has incomplete effect-argument provenance",
                        )
                    })?;
                let found = self.synthesize_with_ledger(
                    argument,
                    Some(provenance),
                    None,
                    None,
                    None,
                    None,
                    span,
                    budget,
                )?;
                let equal = same_kind_with_charge(&parameter.kind, found.kind, || budget.charge(1))
                    .map_err(|()| {
                        KindFailure::resource(
                            found.occurrence,
                            "effect-argument kind checking exceeded its owning work budget",
                        )
                    })?;
                if !equal {
                    let diagnostic_budget = budget.resolved_budget(found.occurrence)?;
                    return Err(KindFailure::Source(Box::new(structured_error(
                        KindReason::Argument,
                        found.occurrence,
                        "this effect argument has the wrong kind",
                        &parameter.kind,
                        found.kind,
                        Some((
                            parameter.origin.primary_span(),
                            "the effect parameter kind is declared here",
                        )),
                        diagnostic_budget,
                    )?)));
                }
            }
        }
        if roots.next().is_some() || argument_provenance.len() != argument_roots.len() {
            return Err(KindFailure::internal(
                span,
                "a computation row has surplus effect-argument provenance",
            ));
        }
        Ok(())
    }

    fn authenticate_effect_type_queue<'environment>(
        &'environment self,
        effects: &HashMap<crate::types::EffectId, &'a [crate::resolved::ResolvedTypeVariable]>,
        provenance: Option<&ResolvedTypeProvenance>,
        span: Span,
        budget: &mut SynthesisLedger<'_>,
        mut pending: Vec<(&Type, Option<usize>)>,
    ) -> Result<(), KindFailure>
    where
        'a: 'environment,
    {
        while let Some((ty, root)) = pending.pop() {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-row authentication exceeded its owning work budget",
                )
            })?;
            let node = match (provenance, root) {
                (Some(provenance), Some(root)) => provenance.nodes().get(root),
                (None, None) => None,
                _ => {
                    return Err(KindFailure::internal(
                        span,
                        "an effect-bearing type has mismatched provenance ownership",
                    ));
                }
            };
            match ty {
                Type::Tuple(elements) => {
                    let roots = match node {
                        Some(ResolvedTypeProvenanceNode::Tuple {
                            elements: roots, ..
                        }) if roots.len() == elements.len() => Some(roots.as_ref()),
                        Some(_) => {
                            return Err(KindFailure::internal(
                                span,
                                "an effect-bearing tuple has incomplete provenance",
                            ));
                        }
                        None => None,
                    };
                    budget.charge(elements.len()).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication exceeded its owning work budget",
                        )
                    })?;
                    pending.try_reserve(elements.len()).map_err(|_| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication could not reserve traversal storage",
                        )
                    })?;
                    pending.extend(
                        elements
                            .iter()
                            .enumerate()
                            .map(|(index, element)| (element, roots.map(|roots| roots[index]))),
                    );
                }
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    let (function_root, argument_root) = match (ty, node) {
                        (
                            Type::Application(_, _),
                            Some(ResolvedTypeProvenanceNode::Application {
                                function,
                                argument,
                                ..
                            }),
                        ) => (Some(*function), Some(*argument)),
                        (
                            Type::Function(_, _),
                            Some(ResolvedTypeProvenanceNode::Function {
                                domain,
                                codomain,
                                effect_arguments,
                                ..
                            }),
                        ) if effect_arguments.is_empty() => (Some(*domain), Some(*codomain)),
                        (_, Some(_)) => {
                            return Err(KindFailure::internal(
                                span,
                                "an effect-bearing type has mismatched structural provenance",
                            ));
                        }
                        (_, None) => (None, None),
                    };
                    budget.charge(2).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication exceeded its owning work budget",
                        )
                    })?;
                    pending.try_reserve(2).map_err(|_| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication could not reserve traversal storage",
                        )
                    })?;
                    pending.push((function, function_root));
                    pending.push((argument, argument_root));
                }
                Type::EffectfulFunction(domain, computation) => {
                    let (domain_root, codomain_root, argument_roots) = match node {
                        Some(ResolvedTypeProvenanceNode::Function {
                            domain,
                            codomain,
                            effect_arguments,
                            ..
                        }) if effect_arguments.len() == computation.effect_argument_count() => (
                            Some(*domain),
                            Some(*codomain),
                            Some(effect_arguments.as_ref()),
                        ),
                        Some(_) => {
                            return Err(KindFailure::internal(
                                span,
                                "an effectful function has incomplete provenance",
                            ));
                        }
                        None => (None, None, None),
                    };
                    self.authenticate_effect_row_into(
                        computation.effects(),
                        effects,
                        provenance,
                        argument_roots,
                        span,
                        budget,
                        &mut pending,
                    )?;
                    budget.charge(2).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication exceeded its owning work budget",
                        )
                    })?;
                    pending.try_reserve(2).map_err(|_| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication could not reserve traversal storage",
                        )
                    })?;
                    pending.push((domain, domain_root));
                    pending.push((computation.value(), codomain_root));
                }
                Type::Forall(_, body) => {
                    budget.charge(1).map_err(|()| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication exceeded its owning work budget",
                        )
                    })?;
                    pending.try_reserve(1).map_err(|_| {
                        KindFailure::resource(
                            span,
                            "effect-row authentication could not reserve traversal storage",
                        )
                    })?;
                    pending.push((body, None));
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Variable(_)
                | Type::Inference(_)
                | Type::Nominal(_) => {}
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn authenticate_effect_row_into<'environment, 'row>(
        &'environment self,
        row: &'row EffectRow,
        effects: &HashMap<crate::types::EffectId, &'a [crate::resolved::ResolvedTypeVariable]>,
        provenance: Option<&ResolvedTypeProvenance>,
        argument_roots: Option<&[usize]>,
        span: Span,
        budget: &mut SynthesisLedger<'_>,
        pending: &mut Vec<(&'row Type, Option<usize>)>,
    ) -> Result<(), KindFailure>
    where
        'a: 'environment,
    {
        let mut roots = argument_roots.map(<[usize]>::iter);
        for instance in row.known() {
            budget.charge(1).map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-row identity lookup exceeded its owning work budget",
                )
            })?;
            let parameters = effects.get(&instance.effect()).ok_or_else(|| {
                KindFailure::internal(span, "an effect row names no canonical checked declaration")
            })?;
            if parameters.len() != instance.arguments().len() {
                return Err(KindFailure::internal(
                    span,
                    "an effect row has the wrong canonical argument count",
                ));
            }
            for (argument, parameter) in instance.arguments().iter().zip(parameters.iter()) {
                let argument_root = match roots.as_mut() {
                    Some(roots) => Some(*roots.next().ok_or_else(|| {
                        KindFailure::internal(
                            span,
                            "an effect row has incomplete argument provenance",
                        )
                    })?),
                    None => None,
                };
                let found = self.synthesize_core_with_ledger(
                    argument,
                    provenance,
                    argument_root,
                    None,
                    None,
                    None,
                    None,
                    span,
                    budget,
                )?;
                let equal = same_kind_with_charge(&parameter.kind, found.kind, || budget.charge(1))
                    .map_err(|()| {
                        KindFailure::resource(
                            span,
                            "effect-argument kind checking exceeded its owning work budget",
                        )
                    })?;
                if !equal {
                    if provenance.is_none() {
                        return Err(KindFailure::internal(
                            span,
                            "an effect row argument has the wrong canonical kind",
                        ));
                    }
                    let diagnostic_budget = budget.resolved_budget(found.occurrence)?;
                    return Err(KindFailure::Source(Box::new(structured_error(
                        KindReason::Argument,
                        found.occurrence,
                        "this effect argument has the wrong kind",
                        &parameter.kind,
                        found.kind,
                        Some((
                            parameter.origin.primary_span(),
                            "the effect parameter kind is declared here",
                        )),
                        diagnostic_budget,
                    )?)));
                }
                budget.charge(1).map_err(|()| {
                    KindFailure::resource(
                        span,
                        "effect-row authentication exceeded its owning work budget",
                    )
                })?;
                pending.try_reserve(1).map_err(|_| {
                    KindFailure::resource(
                        span,
                        "effect-row authentication could not reserve traversal storage",
                    )
                })?;
                pending.push((argument, argument_root));
            }
        }
        if roots.is_some_and(|mut roots| roots.next().is_some()) {
            return Err(KindFailure::internal(
                span,
                "an effect row has surplus argument provenance",
            ));
        }
        Ok(())
    }

    fn authenticate_effect_row_tail<'environment>(
        &'environment self,
        row: &EffectRow,
        allowed_variables: Option<&HashSet<TypeVariableId>>,
        visited_variables: Option<&mut HashSet<TypeVariableId>>,
        span: Span,
        budget: &mut SynthesisLedger<'_>,
    ) -> Result<(), KindFailure>
    where
        'a: 'environment,
    {
        let Some(tail) = row.tail() else {
            return Ok(());
        };
        let fact = match tail.variable() {
            crate::types::EffectRowVariable::Rigid(identity) => {
                if allowed_variables.is_some_and(|allowed| !allowed.contains(&identity)) {
                    return Err(KindFailure::internal(
                        span,
                        "an effect row references a non-owner tail",
                    ));
                }
                if let Some(visited) = visited_variables {
                    visited.insert(identity);
                }
                self.delta.get(&identity).ok_or_else(|| {
                    KindFailure::internal(span, "an effect-row tail has no canonical binder kind")
                })?
            }
            crate::types::EffectRowVariable::Inference(identity) => {
                self.omega.get(&identity).ok_or_else(|| {
                    KindFailure::internal(span, "an effect-row tail has no fixed inference kind")
                })?
            }
        };
        let is_row = same_kind_with_charge(fact.kind, &Kind::EffectRow, || budget.charge(1))
            .map_err(|()| {
                KindFailure::resource(
                    span,
                    "effect-row tail kind checking exceeded its work budget",
                )
            })?;
        if is_row {
            Ok(())
        } else {
            Err(KindFailure::internal(
                span,
                "an effect-row tail does not have kind EffectRow",
            ))
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn synthesize_core_with_ledger<'environment>(
        &'environment self,
        ty: &Type,
        provenance: Option<&ResolvedTypeProvenance>,
        provenance_root: Option<usize>,
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
        let mut current = State::Visit(ty, type_mirror, provenance_root);
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
                        Type::Function(_, _) | Type::EffectfulFunction(_, _) => {
                            let (domain, codomain) = match ty {
                                Type::Function(domain, codomain) => {
                                    (domain.as_ref(), codomain.as_ref())
                                }
                                Type::EffectfulFunction(domain, codomain) => {
                                    (domain.as_ref(), codomain.value())
                                }
                                _ => unreachable!(),
                            };
                            charge_synthesis_cell(span, budget)?;
                            let (mut domain_mirror, codomain_mirror) = match type_mirror {
                                None => (None, None),
                                Some(Type::Function(domain, codomain)) => {
                                    (Some(domain.as_ref()), Some(codomain.as_ref()))
                                }
                                Some(Type::EffectfulFunction(domain, codomain)) => {
                                    (Some(domain.as_ref()), Some(codomain.value()))
                                }
                                Some(_) => {
                                    return Err(KindFailure::internal(
                                        span,
                                        "a linked source type does not match its checked value type",
                                    ));
                                }
                            };
                            if let Type::EffectfulFunction(_, computation) = ty {
                                if let Some(Type::EffectfulFunction(_, mirror)) = type_mirror {
                                    let equal = same_effect_rows_with_charge(
                                        computation.effects(),
                                        mirror.effects(),
                                        |work| budget.charge(work),
                                    )
                                    .map_err(|()| {
                                        KindFailure::resource(
                                            span,
                                            "computation-row authentication exceeded its owning work budget",
                                        )
                                    })?;
                                    if !equal {
                                        return Err(KindFailure::internal(
                                            span,
                                            "a linked source computation row does not match its checked row",
                                        ));
                                    }
                                }
                                self.authenticate_effect_row_tail(
                                    computation.effects(),
                                    allowed_variables,
                                    visited_variables.as_deref_mut(),
                                    span,
                                    budget,
                                )?;
                            }
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
                                    effect_arguments,
                                    ..
                                }) if match ty {
                                    Type::Function(_, _) => effect_arguments.is_empty(),
                                    Type::EffectfulFunction(_, computation) => {
                                        effect_arguments.len()
                                            == computation.effect_argument_count()
                                    }
                                    _ => false,
                                } =>
                                {
                                    (Some(*domain), Some(*codomain))
                                }
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
            Type::EffectfulFunction(domain, codomain) => {
                if let Some(tail) = codomain.effects().tail() {
                    let crate::types::EffectRowVariable::Rigid(identity) = tail.variable() else {
                        return Err(CanonicalEnvironmentFailure::InvalidState);
                    };
                    if !environments.contains_declared(identity) {
                        discovery_budget
                            .charge(1)
                            .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                        let parameter = registry
                            .type_variable(identity)
                            .ok_or(CanonicalEnvironmentFailure::InvalidState)?;
                        environments
                            .insert_declared(
                                identity,
                                &parameter.kind,
                                parameter.origin.primary_span(),
                                retention_budget,
                            )
                            .map_err(map_canonical_environment_retention_failure)?;
                    }
                }
                let children = codomain.effect_argument_count().saturating_add(2);
                discovery_budget
                    .charge(children)
                    .map_err(|()| CanonicalEnvironmentFailure::ConstraintResource)?;
                pending
                    .try_reserve(children)
                    .map_err(|_| CanonicalEnvironmentFailure::ConstraintResource)?;
                codomain.extend_effect_arguments(&mut pending);
                pending.push(codomain.value());
                pending.push(domain);
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
    environments.install_effects(
        &module.registry,
        &module.effects,
        module.imported.effects(),
        budget,
        module.span,
    )?;
    for nominal in module
        .registry
        .nominals()
        .iter()
        .chain(module.registry.lexical_nominals())
    {
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
    let mut has_invalid_determination = false;
    for interface in &module.interfaces {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                interface.span,
                "interface declaration-shape authentication exceeded its type-work budget",
            )
        })?;
        if interface.parameters.is_empty() {
            return Err(KindFailure::internal(
                interface.span,
                "a resolved interface has no type parameters",
            ));
        }
        if !interface_determination_is_total(interface, budget)? {
            has_invalid_determination = true;
        }
        authenticate_owner_parameters(&module.registry, &interface.parameters, budget)?;
        environments.insert_interface_with_determination(
            interface.id,
            &interface.parameters,
            interface
                .determination
                .as_ref()
                .map(InterfaceKindDetermination::Resolved),
            interface.span,
            budget,
        )?;
    }

    authenticate_imported_environments(module, &mut environments, budget)?;
    let all_application_arities_complete =
        preflight_interface_application_kinds(module, &mut environments, budget)?;
    if !all_application_arities_complete || has_invalid_determination {
        return Ok(());
    }

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
                if nominal.declaration_kind == ResolvedNominalDeclarationKind::Newtype {
                    let [constructor_id] = nominal.constructors.as_ref() else {
                        return Err(KindFailure::internal(
                            nominal.origin.primary_span(),
                            "a newtype does not retain exactly one constructor identity",
                        ));
                    };
                    let [payload_provenance] = payload_provenance.as_slice() else {
                        return Err(KindFailure::internal(
                            nominal.origin.primary_span(),
                            "a newtype does not retain exactly one representation provenance",
                        ));
                    };
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
                        "a newtype names a missing canonical constructor",
                        budget,
                    )?;
                    if constructor.owner != nominal.id || constructor.payload.is_some() {
                        return Err(KindFailure::internal(
                            constructor.origin.primary_span(),
                            "a newtype constructor retains an ordinary payload",
                        ));
                    }
                    let [field] = payload_provenance.fields.as_slice() else {
                        return Err(KindFailure::internal(
                            constructor.origin.primary_span(),
                            "a newtype representation does not retain exactly one field provenance",
                        ));
                    };
                    let representation = nominal.representation.as_ref().ok_or_else(|| {
                        KindFailure::internal(
                            nominal.origin.primary_span(),
                            "a newtype does not retain its canonical representation",
                        )
                    })?;
                    environments.expect_value_type_parts(
                        representation,
                        field,
                        field
                            .span()
                            .unwrap_or_else(|| constructor.origin.primary_span()),
                        budget,
                    )?;
                } else {
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
            crate::resolved::ResolvedDeclarationIndex::Effect(index) => {
                let effect = required_lookup(
                    module.effects.get(index),
                    module.span,
                    "declaration order contains an invalid effect index",
                    budget,
                )?;
                check_effect(effect, &module.registry, &mut environments, budget)?
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
        match outcome {
            DeclarationKindOutcome::Checked => {}
            DeclarationKindOutcome::Deferred => return Ok(()),
        }
    }

    Ok(())
}

fn check_lexical_newtype<'a>(
    nominal: &'a crate::resolved::ResolvedNominalType,
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let parameters = required_lookup(
        registry.canonical_nominal_parameters(nominal.id),
        nominal.origin.primary_span(),
        "a lexical nominal has no canonical parameter slice",
        budget,
    )?;
    authenticate_owner_parameters(registry, parameters, budget)?;
    if nominal.declaration_kind != ResolvedNominalDeclarationKind::Newtype
        || !nominal.id.is_lexical()
    {
        return Err(KindFailure::internal(
            nominal.origin.primary_span(),
            "a lexical nominal fact is not a lexical newtype",
        ));
    }
    let [constructor_id] = nominal.constructors.as_ref() else {
        return Err(KindFailure::internal(
            nominal.origin.primary_span(),
            "a lexical newtype does not retain exactly one constructor identity",
        ));
    };
    let constructor = required_lookup(
        registry.constructor(*constructor_id),
        nominal.origin.primary_span(),
        "a lexical newtype names a missing canonical constructor",
        budget,
    )?;
    if constructor.owner != nominal.id || constructor.payload.is_some() {
        return Err(KindFailure::internal(
            constructor.origin.primary_span(),
            "a lexical newtype constructor has invalid ownership or payload",
        ));
    }
    let representation = nominal.representation.as_ref().ok_or_else(|| {
        KindFailure::internal(
            nominal.origin.primary_span(),
            "a lexical newtype does not retain its canonical representation",
        )
    })?;
    let provenance = nominal.representation_provenance.as_ref().ok_or_else(|| {
        KindFailure::internal(
            nominal.origin.primary_span(),
            "a lexical newtype does not retain representation provenance",
        )
    })?;
    environments.extend_owner_parameters(parameters, budget)?;
    let result = environments.expect_value_type_parts(
        representation,
        provenance,
        provenance
            .span()
            .unwrap_or_else(|| constructor.origin.primary_span()),
        budget,
    );
    environments.remove_owner_parameter_extension(parameters);
    result
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
    let mut next_effect = 0;
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
            crate::resolved::ResolvedDeclarationIndex::Effect(index) => {
                let ordered = index == next_effect && index < module.effects.len();
                next_effect = next_effect.saturating_add(1);
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
        || next_effect != module.effects.len()
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
        environments.insert_interface_with_determination(
            interface.id,
            &interface.parameters,
            interface
                .determination()
                .map(InterfaceKindDetermination::Checked),
            interface.span,
            budget,
        )?;
    }

    for imported_interface in imported.interface_imports() {
        let interface = &imported_interface.fact;
        for method in &interface.methods {
            authenticate_unique_parameter_ids(
                method.type_parameters(),
                method.origin.primary_span(),
                budget,
            )?;
            environments.install_owner_parameters(&interface.parameters, budget)?;
            for parameter in method.type_parameters() {
                if !binder_kind_is_admitted(&parameter.kind, false) {
                    return Err(KindFailure::internal(
                        parameter.origin.primary_span(),
                        "an interface method cannot bind an EffectRow parameter",
                    ));
                }
                environments.insert_declared(
                    parameter.id,
                    &parameter.kind,
                    parameter.origin.primary_span(),
                    budget,
                )?;
            }
            environments.expect_body_free_value_type(method.value_type(), method.span, budget)?;
        }
    }

    for global in imported.globals() {
        let span = global.origin.primary_span();
        environments.install_owner_pairs(&global.scheme.type_parameters, span, true, budget)?;
        environments.expect_body_free_value_type(&global.scheme.value_type, span, budget)?;
        for requirement in &global.scheme.requirements {
            environments.expect_body_free_interface_argument(
                requirement.interface(),
                requirement.arguments(),
                requirement.span,
                budget,
            )?;
        }
    }

    for implementation in imported.implementations() {
        let fact = &implementation.fact;
        environments.install_owner_parameters(&fact.head_parameters, budget)?;
        environments.expect_body_free_interface_argument(
            fact.interface(),
            fact.arguments(),
            fact.span,
            budget,
        )?;
        for prerequisite in &fact.prerequisites {
            environments.expect_body_free_interface_argument(
                prerequisite.interface(),
                prerequisite.arguments(),
                prerequisite.span,
                budget,
            )?;
        }
        for method in &fact.methods {
            environments.install_owner_pairs(
                &method.scheme.type_parameters,
                method.span,
                false,
                budget,
            )?;
            environments.expect_body_free_value_type(
                &method.scheme.value_type,
                method.span,
                budget,
            )?;
            for requirement in &method.scheme.requirements {
                environments.expect_body_free_interface_argument(
                    requirement.interface(),
                    requirement.arguments(),
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
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            interface.span,
            "interface declaration-shape authentication exceeded its type-work budget",
        )
    })?;
    if interface.parameters.is_empty() {
        return Err(KindFailure::internal(
            interface.span,
            "a resolved interface has no type parameters",
        ));
    }
    if !interface_determination_is_total(interface, budget)? {
        return Ok(DeclarationKindOutcome::Deferred);
    }
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
            environments.install_owner_parameters(&interface.parameters, budget)?;
            for parameter in &method.type_parameters {
                if !binder_kind_is_admitted(&parameter.kind, false) {
                    return Err(KindFailure::internal(
                        parameter.origin.primary_span(),
                        "an interface method cannot bind an EffectRow parameter",
                    ));
                }
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
                environments.install_owner_parameters(&interface.parameters, budget)?;
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

fn check_effect<'a>(
    effect: &'a crate::resolved::ResolvedEffectDeclaration,
    registry: &crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    authenticate_owner_parameters(registry, &effect.parameters, budget)?;
    environments.install_owner_parameters(&effect.parameters, budget)?;
    for operation in &effect.operations {
        environments.expect_value_type(&operation.annotation, budget)?;
    }
    Ok(DeclarationKindOutcome::Checked)
}

fn interface_determination_is_total(
    interface: &ResolvedInterfaceDeclaration,
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    let Some(determination) = &interface.determination else {
        return Ok(true);
    };
    crate::resolved::resolved_determination_is_total(&interface.parameters, determination, |work| {
        budget.charge(work)
    })
    .map_err(|()| {
        KindFailure::resource(
            determination.span,
            "interface determination authentication exceeded its type-work budget",
        )
    })
}

#[derive(Clone, Copy)]
struct CompleteInterfaceApplication<'application, 'kind> {
    arguments: &'application [ResolvedType],
    parameters: &'kind [crate::resolved::ResolvedTypeVariable],
    determination: Option<InterfaceKindDetermination<'kind>>,
}

fn authenticate_interface_application<'application, 'kind>(
    application: &'application ResolvedInterfaceApplication,
    environments: &KindEnvironments<'kind>,
    budget: &mut TypeWorkBudget,
) -> Result<Option<CompleteInterfaceApplication<'application, 'kind>>, KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            application.span,
            "interface-application shape authentication exceeded its type-work budget",
        )
    })?;
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            application.span,
            "interface kind membership authentication exceeded its type-work budget",
        )
    })?;
    let expected = environments
        .iota
        .get(&application.interface.id)
        .ok_or_else(|| {
            KindFailure::internal(
                application.span,
                "a resolved interface application has no canonical interface-kind entry",
            )
        })?;
    if application.arguments.len() != expected.parameters.len() {
        return Ok(None);
    }
    Ok(Some(CompleteInterfaceApplication {
        arguments: &application.arguments,
        parameters: expected.parameters,
        determination: expected.determination,
    }))
}

fn check_interface_application_kinds(
    application: CompleteInterfaceApplication<'_, '_>,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let CompleteInterfaceApplication {
        arguments,
        parameters,
        ..
    } = application;
    for (argument, parameter) in arguments.iter().zip(parameters) {
        environments.expect_interface_argument(
            argument,
            &parameter.kind,
            parameter.origin.primary_span(),
            budget,
        )?;
    }
    Ok(())
}

fn preflight_interface_application_kinds<'a>(
    module: &'a ResolvedModuleParts,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    let mut saw_application = false;
    let all_arity_complete =
        visit_interface_applications(module, budget, |application, budget| {
            saw_application = true;
            Ok(authenticate_interface_application(application, environments, budget)?.is_some())
        })?;
    if !all_arity_complete {
        // Elaboration owns the source-facing interface.argument-count
        // diagnostic. No positional argument kind may preempt it.
        return Ok(false);
    }
    if !saw_application {
        return Ok(true);
    }

    check_interface_application_kinds_in_owner_environments(module, environments, budget)?;
    Ok(true)
}

fn check_interface_application_kinds_in_owner_environments<'a>(
    module: &'a ResolvedModuleParts,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let check = |application: &ResolvedInterfaceApplication,
                 environments: &KindEnvironments<'a>,
                 budget: &mut TypeWorkBudget| {
        let application = authenticate_interface_application(application, environments, budget)?
            .ok_or_else(|| {
                KindFailure::internal(
                    application.span,
                    "an interface application changed arity between kind preflight passes",
                )
            })?;
        check_interface_application_kinds(application, environments, budget)
    };
    for declaration in &module.declaration_order {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                module.span,
                "interface-application kind preflight traversal exceeded its type-work budget",
            )
        })?;
        match *declaration {
            crate::resolved::ResolvedDeclarationIndex::Type(_)
            | crate::resolved::ResolvedDeclarationIndex::Interface(_)
            | crate::resolved::ResolvedDeclarationIndex::Effect(_) => {}
            crate::resolved::ResolvedDeclarationIndex::Global(index) => {
                let definition = module.definitions.get(index).ok_or_else(|| {
                    KindFailure::internal(
                        module.span,
                        "interface-application kind preflight found an invalid global index",
                    )
                })?;
                let (parameters, requirements) = match &definition.kind {
                    ResolvedDefinitionKind::Equational(global) => (
                        &global.interface.type_parameters,
                        &global.interface.requirements,
                    ),
                    ResolvedDefinitionKind::InlineOperational(global) => {
                        (&global.header.type_parameters, &global.header.requirements)
                    }
                };
                authenticate_owner_parameters(&module.registry, parameters, budget)?;
                environments.install_scheme_parameters(parameters, budget)?;
                for requirement in requirements.iter() {
                    check(&requirement.application, environments, budget)?;
                }
            }
            crate::resolved::ResolvedDeclarationIndex::Implementation(index) => {
                let implementation = module.implementations.get(index).ok_or_else(|| {
                    KindFailure::internal(
                        module.span,
                        "interface-application kind preflight found an invalid implementation index",
                    )
                })?;
                authenticate_owner_parameters(
                    &module.registry,
                    &implementation.head_parameters,
                    budget,
                )?;
                authenticate_owner_parameters(
                    &module.registry,
                    &implementation.prerequisite_only_parameters,
                    budget,
                )?;
                environments.install_owner_parameters(&implementation.head_parameters, budget)?;
                check(&implementation.head, environments, budget)?;
                for parameter in &implementation.prerequisite_only_parameters {
                    if !binder_kind_is_admitted(&parameter.kind, false) {
                        return Err(KindFailure::internal(
                            parameter.origin.primary_span(),
                            "this owner cannot bind an EffectRow parameter",
                        ));
                    }
                    environments.insert_declared(
                        parameter.id,
                        &parameter.kind,
                        parameter.origin.primary_span(),
                        budget,
                    )?;
                }
                for prerequisite in &implementation.prerequisites {
                    check(&prerequisite.application, environments, budget)?;
                }
            }
        }
    }
    Ok(())
}

fn visit_interface_applications(
    module: &ResolvedModuleParts,
    budget: &mut TypeWorkBudget,
    mut visit: impl FnMut(
        &ResolvedInterfaceApplication,
        &mut TypeWorkBudget,
    ) -> Result<bool, KindFailure>,
) -> Result<bool, KindFailure> {
    for declaration in &module.declaration_order {
        budget.charge(1).map_err(|()| {
            KindFailure::resource(
                module.span,
                "interface-application preflight traversal exceeded its type-work budget",
            )
        })?;
        match *declaration {
            crate::resolved::ResolvedDeclarationIndex::Type(_)
            | crate::resolved::ResolvedDeclarationIndex::Interface(_)
            | crate::resolved::ResolvedDeclarationIndex::Effect(_) => {}
            crate::resolved::ResolvedDeclarationIndex::Global(index) => {
                let definition = module.definitions.get(index).ok_or_else(|| {
                    KindFailure::internal(
                        module.span,
                        "interface-application preflight found an invalid global index",
                    )
                })?;
                let requirements = match &definition.kind {
                    ResolvedDefinitionKind::Equational(global) => &global.interface.requirements,
                    ResolvedDefinitionKind::InlineOperational(global) => {
                        &global.header.requirements
                    }
                };
                for requirement in requirements.iter() {
                    if !visit(&requirement.application, budget)? {
                        return Ok(false);
                    }
                }
            }
            crate::resolved::ResolvedDeclarationIndex::Implementation(index) => {
                let implementation = module.implementations.get(index).ok_or_else(|| {
                    KindFailure::internal(
                        module.span,
                        "interface-application preflight found an invalid implementation index",
                    )
                })?;
                if !visit(&implementation.head, budget)? {
                    return Ok(false);
                }
                for prerequisite in &implementation.prerequisites {
                    if !visit(&prerequisite.application, budget)? {
                        return Ok(false);
                    }
                }
            }
        }
    }
    Ok(true)
}

fn check_definition<'a>(
    definition: &'a ResolvedDefinition,
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global) => {
            authenticate_owner_parameters(registry, &global.interface.type_parameters, budget)?;
            environments.install_scheme_parameters(&global.interface.type_parameters, budget)?;
            environments.expect_value_type(&global.interface.annotation, budget)?;
            let mut determined = Vec::new();
            collect_type_variables(
                &global.interface.annotation.ty,
                global.interface.annotation.span,
                &mut determined,
                budget,
            )?;
            for requirement in &global.interface.requirements {
                let Some(checked) = authenticate_interface_application(
                    &requirement.application,
                    environments,
                    budget,
                )?
                else {
                    return Ok(DeclarationKindOutcome::Deferred);
                };
                if requirement_has_undetermined_variable(
                    checked,
                    requirement.application.span,
                    &determined,
                    budget,
                )? {
                    return Ok(DeclarationKindOutcome::Deferred);
                }
                check_interface_application_kinds(checked, environments, budget)?;
            }
            for equation in &global.equations {
                check_expression_annotations(&equation.body, registry, environments, budget)?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            authenticate_owner_parameters(registry, &global.header.type_parameters, budget)?;
            environments.install_scheme_parameters(&global.header.type_parameters, budget)?;
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
            environments.expect_computation_type(
                &global.header.result_type,
                &global.header.result_effects,
                &global.header.result_effect_argument_provenance,
                &global.header.result_effect_argument_roots,
                budget,
            )?;
            collect_type_variables(
                &global.header.result_type.ty,
                global.header.result_type.span,
                &mut determined,
                budget,
            )?;
            for requirement in &global.header.requirements {
                let Some(checked) = authenticate_interface_application(
                    &requirement.application,
                    environments,
                    budget,
                )?
                else {
                    return Ok(DeclarationKindOutcome::Deferred);
                };
                if requirement_has_undetermined_variable(
                    checked,
                    requirement.application.span,
                    &determined,
                    budget,
                )? {
                    return Ok(DeclarationKindOutcome::Deferred);
                }
                check_interface_application_kinds(checked, environments, budget)?;
            }
            check_block_annotations(&global.body, registry, environments, budget)?;
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
            Type::EffectfulFunction(domain, codomain) => {
                if let Some(tail) = codomain.effects().tail() {
                    let crate::types::EffectRowVariable::Rigid(identity) = tail.variable() else {
                        return Err(KindFailure::internal(
                            span,
                            "row inference entered global determination discovery",
                        ));
                    };
                    if !contains_type_variable_with_budget(output, identity, span, budget)? {
                        budget.charge(1).map_err(|()| {
                            KindFailure::resource(
                                span,
                                "global row-tail determination retention exceeded its type-work budget",
                            )
                        })?;
                        output.try_reserve(1).map_err(|_| {
                            KindFailure::resource(
                                span,
                                "global row-tail determination could not reserve storage",
                            )
                        })?;
                        output.push(identity);
                    }
                }
                for argument in codomain.effect_arguments() {
                    push_determination_work(&mut work, argument, span, budget)?;
                }
                push_determination_work(&mut work, codomain.value(), span, budget)?;
                push_determination_work(&mut work, domain, span, budget)?;
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
    requirement: CompleteInterfaceApplication<'_, '_>,
    span: Span,
    determined: &[TypeVariableId],
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    match requirement.determination {
        None => {
            for position in 0..requirement.arguments.len() {
                if requirement_argument_has_undetermined_variable(
                    requirement.arguments,
                    position,
                    span,
                    determined,
                    budget,
                )? {
                    return Ok(true);
                }
            }
        }
        Some(InterfaceKindDetermination::Resolved(determination)) => {
            let mut next = 0;
            for (position, parameter) in requirement.parameters.iter().enumerate() {
                budget.charge(1).map_err(|()| {
                    KindFailure::resource(
                        span,
                        "global determinant-position authentication exceeded its type-work budget",
                    )
                })?;
                if determination
                    .determinant
                    .parameters
                    .get(next)
                    .is_some_and(|candidate| candidate.id == parameter.id)
                {
                    if requirement_argument_has_undetermined_variable(
                        requirement.arguments,
                        position,
                        span,
                        determined,
                        budget,
                    )? {
                        return Ok(true);
                    }
                    next += 1;
                }
            }
            if next != determination.determinant.parameters.len() {
                return Err(KindFailure::internal(
                    span,
                    "an authenticated source determination has an invalid key",
                ));
            }
        }
        Some(InterfaceKindDetermination::Checked(determination)) => {
            let mut previous = None;
            for &position in determination.positions() {
                budget.charge(1).map_err(|()| {
                    KindFailure::resource(
                        span,
                        "global determinant-position authentication exceeded its type-work budget",
                    )
                })?;
                if previous.is_some_and(|previous| previous >= position) {
                    return Err(KindFailure::internal(
                        span,
                        "an authenticated summary determination has an invalid key",
                    ));
                }
                previous = Some(position);
                if requirement_argument_has_undetermined_variable(
                    requirement.arguments,
                    position,
                    span,
                    determined,
                    budget,
                )? {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

fn requirement_argument_has_undetermined_variable(
    arguments: &[ResolvedType],
    position: usize,
    span: Span,
    determined: &[TypeVariableId],
    budget: &mut TypeWorkBudget,
) -> Result<bool, KindFailure> {
    let argument = arguments.get(position).ok_or_else(|| {
        KindFailure::internal(
            span,
            "an authenticated determinant position is outside its complete application",
        )
    })?;
    let mut variables = Vec::new();
    collect_type_variables(&argument.ty, argument.span, &mut variables, budget)?;
    for identity in variables {
        if !contains_type_variable_with_budget(determined, identity, argument.span, budget)? {
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
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<DeclarationKindOutcome, KindFailure> {
    let Some(head) =
        authenticate_interface_application(&implementation.head, environments, budget)?
    else {
        return Ok(DeclarationKindOutcome::Deferred);
    };
    authenticate_owner_parameters(registry, &implementation.head_parameters, budget)?;
    authenticate_owner_parameters(
        registry,
        &implementation.prerequisite_only_parameters,
        budget,
    )?;
    environments.install_owner_parameters(&implementation.head_parameters, budget)?;
    check_interface_application_kinds(head, environments, budget)?;
    if !implementation.prerequisite_only_parameters.is_empty() {
        return Ok(DeclarationKindOutcome::Deferred);
    }
    for prerequisite in &implementation.prerequisites {
        let Some(checked) =
            authenticate_interface_application(&prerequisite.application, environments, budget)?
        else {
            return Ok(DeclarationKindOutcome::Deferred);
        };
        check_interface_application_kinds(checked, environments, budget)?;
    }
    for group in &implementation.method_groups {
        for equation in &group.equations {
            check_expression_annotations(&equation.body, registry, environments, budget)?;
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

fn check_block_annotations<'a>(
    block: &'a crate::resolved::ResolvedBlock,
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut work = Vec::new();
    schedule_block_work(&mut work, block, registry, budget)?;
    check_expression_work(work, registry, environments, budget)
}

fn check_expression_annotations<'a>(
    expression: &'a ResolvedExpr,
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    let mut work = Vec::new();
    push_body_work(
        &mut work,
        BodyWork::Expression(expression),
        expression.span,
        budget,
    )?;
    check_expression_work(work, registry, environments, budget)
}

#[derive(Clone, Copy)]
enum BodyWork<'a> {
    Expression(&'a ResolvedExpr),
    ResourceBody(&'a crate::resolved::ResolvedResourceExpr),
    ResourceExit(&'a crate::resolved::ResolvedTypeVariable),
    Declaration(&'a ResolvedLocalDeclaration),
    LexicalNewtype(&'a crate::resolved::ResolvedNominalType),
    RecursiveMember(&'a ResolvedRecursiveMember),
}

fn check_expression_work<'a>(
    mut work: Vec<BodyWork<'a>>,
    registry: &'a crate::resolved::ResolvedRegistry,
    environments: &mut KindEnvironments<'a>,
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
                ResolvedLocalDeclaration::Evidence(source) => {
                    if let Some(application) = authenticate_interface_application(
                        &source.application,
                        environments,
                        budget,
                    )? {
                        check_interface_application_kinds(application, environments, budget)?;
                    }
                    budget.charge(source.method_groups.len()).map_err(|()| {
                        KindFailure::resource(
                            source.span,
                            "lexical method-group kind traversal exceeded its type-work budget",
                        )
                    })?;
                    for equation in source
                        .method_groups
                        .iter()
                        .rev()
                        .flat_map(|group| group.equations.iter().rev())
                    {
                        push_body_work(
                            &mut work,
                            BodyWork::Expression(&equation.body),
                            equation.body.span,
                            budget,
                        )?;
                    }
                }
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
                ResolvedLocalDeclaration::Newtype(_) => {
                    unreachable!("lexical nominal markers are scheduled with their facts")
                }
            },
            BodyWork::LexicalNewtype(nominal) => {
                check_lexical_newtype(nominal, registry, environments, budget)?;
            }
            BodyWork::RecursiveMember(member) => {
                environments.expect_value_type(&member.annotation, budget)?;
                push_body_work(
                    &mut work,
                    BodyWork::Expression(&member.initializer),
                    member.initializer.span,
                    budget,
                )?;
            }
            BodyWork::ResourceBody(resource) => {
                let parameters = std::slice::from_ref(&resource.identity);
                authenticate_owner_parameters(registry, parameters, budget)?;
                if resource.identity.kind != Kind::Type {
                    return Err(KindFailure::internal(
                        span,
                        "a resource identity must have kind Type",
                    ));
                }
                environments.extend_owner_parameters(parameters, budget)?;
                push_body_work(
                    &mut work,
                    BodyWork::ResourceExit(&resource.identity),
                    span,
                    budget,
                )?;
                push_body_work(
                    &mut work,
                    BodyWork::Expression(&resource.body),
                    span,
                    budget,
                )?;
            }
            BodyWork::ResourceExit(identity) => {
                environments.remove_owner_parameter_extension(std::slice::from_ref(identity));
            }
            BodyWork::Expression(expression) => match &expression.kind {
                ResolvedExprKind::Cleanup(cleanup) => {
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&cleanup.action),
                        cleanup.action.span,
                        budget,
                    )?;
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&cleanup.body),
                        cleanup.body.span,
                        budget,
                    )?;
                }
                ResolvedExprKind::Resource(resource) => {
                    push_body_work(
                        &mut work,
                        BodyWork::ResourceBody(resource),
                        expression.span,
                        budget,
                    )?;
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&resource.initializer),
                        resource.initializer.span,
                        budget,
                    )?;
                }
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
                    schedule_block_work(&mut work, block, registry, budget)?;
                }
                ResolvedExprKind::Function(function) => {
                    schedule_block_work(&mut work, &function.body, registry, budget)?;
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
                ResolvedExprKind::Perform(request) => push_body_work(
                    &mut work,
                    BodyWork::Expression(&request.operand),
                    request.operand.span,
                    budget,
                )?,
                ResolvedExprKind::Handle(handler) => {
                    if handler.hook_root.is_some() || handler.hook_registration.is_some() {
                        check_hook_target_kind(&handler.effect, environments, budget)?;
                    }
                    for clause in handler.clauses.iter().rev() {
                        push_body_work(
                            &mut work,
                            BodyWork::Expression(&clause.body),
                            clause.body.span,
                            budget,
                        )?;
                    }
                    push_body_work(
                        &mut work,
                        BodyWork::Expression(&handler.body),
                        handler.body.span,
                        budget,
                    )?;
                }
                ResolvedExprKind::Resume(resume) => push_body_work(
                    &mut work,
                    BodyWork::Expression(&resume.value),
                    resume.value.span,
                    budget,
                )?,
                ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Occurrence(_)
                | ResolvedExprKind::Constructor(_)
                | ResolvedExprKind::Discard(_) => {}
            },
        }
    }
    Ok(())
}

fn check_hook_target_kind(
    target: &crate::resolved::ResolvedEffectInstance,
    environments: &KindEnvironments<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    budget.charge(1).map_err(|()| {
        KindFailure::resource(
            target.span,
            "hook target kind lookup exceeded its type-work budget",
        )
    })?;
    let parameters = environments
        .effects
        .as_ref()
        .and_then(|effects| effects.get(&target.instance.effect()))
        .ok_or_else(|| {
            KindFailure::internal(
                target.span,
                "a hook target has no canonical effect declaration",
            )
        })?;
    // Elaboration owns the existing source-facing instance arity diagnostic.
    if parameters.len() != target.instance.arguments().len() {
        return Ok(());
    }
    if target.argument_provenance.len() != target.instance.arguments().len() {
        return Err(KindFailure::internal(
            target.span,
            "a hook target has incomplete argument provenance",
        ));
    }
    for ((argument, provenance), parameter) in target
        .instance
        .arguments()
        .iter()
        .zip(target.argument_provenance.iter())
        .zip(parameters.iter())
    {
        let span = provenance.span().ok_or_else(|| {
            KindFailure::internal(target.span, "a hook argument has no source occurrence")
        })?;
        let found = environments.synthesize(argument, Some(provenance), span, budget)?;
        if !same_kind_with_budget(&parameter.kind, found.kind, budget).map_err(|()| {
            KindFailure::resource(
                span,
                "hook argument kind comparison exceeded its type-work budget",
            )
        })? {
            return Err(KindFailure::Source(Box::new(structured_error(
                KindReason::Argument,
                span,
                "this effect argument has the wrong kind",
                &parameter.kind,
                found.kind,
                Some((
                    parameter.origin.primary_span(),
                    "the effect parameter kind is declared here",
                )),
                budget,
            )?)));
        }
    }
    Ok(())
}

fn schedule_block_work<'a>(
    work: &mut Vec<BodyWork<'a>>,
    block: &'a crate::resolved::ResolvedBlock,
    registry: &'a crate::resolved::ResolvedRegistry,
    budget: &mut TypeWorkBudget,
) -> Result<(), KindFailure> {
    push_body_work(
        work,
        BodyWork::Expression(block.result.as_ref()),
        block.result.span,
        budget,
    )?;
    for declaration in block.declarations.iter().rev() {
        let item = match declaration {
            ResolvedLocalDeclaration::Newtype(owner) => {
                let nominal = required_lookup(
                    registry.nominal(*owner),
                    block.span,
                    "a lexical nominal marker names a missing canonical fact",
                    budget,
                )?;
                BodyWork::LexicalNewtype(nominal)
            }
            _ => BodyWork::Declaration(declaration),
        };
        push_body_work(work, item, body_work_span(item), budget)?;
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
        ResolvedLocalDeclaration::Evidence(source) => source.span,
        ResolvedLocalDeclaration::Binding(binding) => binding.span,
        ResolvedLocalDeclaration::Recursive(group) => group.span,
        ResolvedLocalDeclaration::Newtype(_) => {
            unreachable!("local newtypes are not scheduled as expression annotations")
        }
    }
}

fn body_work_span(item: BodyWork<'_>) -> Span {
    match item {
        BodyWork::Expression(expression) => expression.span,
        BodyWork::ResourceBody(resource) => resource.acquisition.span,
        BodyWork::ResourceExit(identity) => identity.origin.primary_span(),
        BodyWork::Declaration(declaration) => local_declaration_span(declaration),
        BodyWork::LexicalNewtype(nominal) => nominal.origin.primary_span(),
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
        Kind::Type | Kind::EffectRow => Ok(()),
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
            (Kind::Type, Kind::Type, None | Some(Kind::Type))
            | (Kind::EffectRow, Kind::EffectRow, None | Some(Kind::EffectRow)) => {}
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
                    Some(Kind::Type | Kind::EffectRow) => {
                        return Err(LinkedKindMirrorFailure::Mismatch);
                    }
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
    #[test]
    fn kind_resource_presentation_retains_stage_and_span() {
        use crate::{
            message::{Catalogue, Locale},
            presentation::{compile_kind_failure, write_human, write_json},
        };
        let source = crate::source::SourceFile::new("kind-resource.ash", "Int").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 3).unwrap())
            .unwrap();
        let error = KindFailure::resource(span, "ignored legacy wording");
        let view = compile_kind_failure(&error, &[&source]).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(!output.contains("ignored"));
            if locale == Locale::English {
                assert!(
                    output.contains("The compiler ran out of resources while checking type kinds.")
                );
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["facts"][0]["value"], "kind-checking");
        assert_eq!(json["facts"][1]["value"], "type-work");
        assert_eq!(json["labels"][0]["relationship"], "kind_checking_site");
        assert!(compile_kind_failure(&error, &[]).is_err());
        assert!(compile_kind_failure(&KindFailure::internal(span, "ignored"), &[&source]).is_err());
    }

    #[test]
    fn kind_presentation_does_not_invent_an_absent_declaration() {
        let source = crate::source::SourceFile::new("kind.ash", "Int").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 3).unwrap())
            .unwrap();
        let error = not_applicable_error(
            KindReason::NotApplicable,
            span,
            "legacy wording",
            &Kind::Type,
            &Kind::Type,
            None,
            &mut TypeWorkBudget::with_limit(100),
        )
        .unwrap();
        let view = crate::presentation::compile_kind_diagnostic(&error, &[&source]).unwrap();
        let mut output = Vec::new();
        crate::presentation::write_json(&mut output, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["labels"].as_array().unwrap().len(), 1);
        assert_eq!(json["facts"][0]["value"], "Type -> _");
        assert_eq!(json["facts"][0]["kind"], "kind-pattern");
    }

    use crate::{
        interface::{ImplId, InterfaceId, MethodId, RequirementId, RequirementOwner},
        module::ModuleId,
        resolved::{
            Binder, BinderId, ImportedFacts, ResolvedApplicationExpr, ResolvedBlock,
            ResolvedConstructor, ResolvedDeclarationIndex, ResolvedDefinition,
            ResolvedDeterminationParameter, ResolvedDeterminationSide, ResolvedEquationalGlobal,
            ResolvedExportCandidate, ResolvedExpr, ResolvedExprKind, ResolvedExternalInterface,
            ResolvedImplementation, ResolvedInterfaceApplication, ResolvedInterfaceDeclaration,
            ResolvedInterfaceDetermination, ResolvedInterfaceMethod, ResolvedInterfaceOccurrence,
            ResolvedNominalType, ResolvedRegistry, ResolvedRequirement, ResolvedType,
            ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
            discard_resolved_expression_iteratively,
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

    fn interface_application(
        interface: InterfaceId,
        argument_count: usize,
        span: Span,
    ) -> ResolvedInterfaceApplication {
        ResolvedInterfaceApplication {
            interface: ResolvedInterfaceOccurrence {
                id: interface,
                spelling: "Relation".into(),
                origin: Origin::Source(span),
            },
            arguments: (0..argument_count)
                .map(|_| fact_type(Type::Int, span))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            span,
        }
    }

    fn requirement(
        owner: RequirementOwner,
        declaration: u32,
        interface: InterfaceId,
        argument_count: usize,
        span: Span,
    ) -> ResolvedRequirement {
        ResolvedRequirement {
            id: RequirementId::new(owner, declaration),
            application: interface_application(interface, argument_count, span),
        }
    }

    fn equational_definition(
        binder: BinderId,
        requirements: Vec<ResolvedRequirement>,
        span: Span,
    ) -> ResolvedDefinition {
        ResolvedDefinition {
            kind: ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                interface: ResolvedExternalInterface {
                    name: Binder {
                        id: binder,
                        spelling: "global".into(),
                        origin: Origin::Source(span),
                    },
                    annotation: fact_type(Type::Int, span),
                    requirements: requirements.into_boxed_slice(),
                    type_parameters: Box::new([]),
                    span,
                },
                equations: Vec::new(),
            }),
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
                parameters: vec![parameter].into_boxed_slice(),
                determination: None,
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
            .checked_sub(2)
            .and_then(|method_work| method_work.checked_mul(2))
            .and_then(|method_work| method_work.checked_add(2))
            .expect("the predecessor accounting formula should fit");
        let mut environments = KindEnvironments::new();
        let mut exact = TypeWorkBudget::with_limit(predecessor_work);
        check_interface(&two_methods, &registry, &mut environments, &mut exact)
            .expect("one owner install plus both unchanged methods should fit exactly");
        assert_eq!(exact.used(), predecessor_work);
    }

    #[test]
    fn relational_interface_shape_is_charged_in_environment_and_declaration_passes() {
        let span = span();
        let module = ModuleId::new(0);
        let interface_id = InterfaceId::new(module, 0);
        let parameters = (0..2)
            .map(|index| ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, index),
                spelling: format!("P{index}"),
                kind: Kind::Type,
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>();
        let mut parts = empty_module_parts(span);
        parts.registry = Arc::new(
            ResolvedRegistry::new(Vec::new(), Vec::new())
                .with_additional_type_variables(parameters.clone()),
        );
        parts.interfaces = vec![ResolvedInterfaceDeclaration {
            id: interface_id,
            public: false,
            spelling: "Relation".into(),
            parameters: parameters.into_boxed_slice(),
            determination: None,
            methods: Box::new([]),
            origin: Origin::Source(span),
            span,
        }];
        parts.declaration_order = vec![ResolvedDeclarationIndex::Interface(0)];

        // Declaration order costs three cells. Environment admission then
        // owns one shape cell, two unique-binder cells, two canonical Kind
        // comparisons, and one IOTA insertion. The global arity preflight
        // visits the interface declaration once; with no applications, it
        // skips the positional-kind pass. Ordinary declaration consumption
        // then visits the interface once more.
        const EXACT_WORK: usize = 3 + (1 + 2 + 2 + 1) + 1 + 1;
        let mut one_short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            check_resolved_module_with_budget(&parts, &[], &mut one_short),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(one_short.used(), EXACT_WORK - 1);

        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
            check_resolved_module_with_budget(&parts, &[], &mut exact)
                .expect("the exact relational kind boundary should be reusable");
            assert_eq!(exact.used(), EXACT_WORK);
        }
    }

    #[test]
    fn lexical_kind_walk_precharges_even_empty_method_groups() {
        let span = span();
        let module = ModuleId::new(0);
        let interface = InterfaceId::new(module, 0);
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 0),
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        for group_count in [0, 1, 64] {
            let declaration = ResolvedLocalDeclaration::Evidence(Box::new(
                crate::resolved::ResolvedLexicalEvidence {
                    acquisition: None,
                    checked: crate::interface::LexicalEvidenceSlot::default(),
                    id: crate::interface::LexicalEvidenceId::new(module, 0),
                    application: interface_application(interface, 1, span),
                    method_groups: (0..group_count)
                        .map(|index| crate::resolved::ResolvedImplementationMethodGroup {
                            contextual_parameters: Box::new([]),
                            method: Some(MethodId::new(interface, index as u32)),
                            identity: None,
                            binder: Binder {
                                id: BinderId::resolved(module, index as u32),
                                spelling: "method".into(),
                                origin: Origin::Source(span),
                            },
                            equations: Box::new([]),
                            span,
                        })
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    span,
                },
            ));
            let mut environments = KindEnvironments::new();
            environments
                .insert_interface(
                    interface,
                    std::slice::from_ref(&parameter),
                    span,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("canonical interface kind entry");
            let ResolvedLocalDeclaration::Evidence(source) = &declaration else {
                unreachable!();
            };
            let mut header_work = TypeWorkBudget::unbounded();
            let header = authenticate_interface_application(
                &source.application,
                &environments,
                &mut header_work,
            )
            .expect("complete header")
            .expect("matching arity");
            check_interface_application_kinds(header, &environments, &mut header_work)
                .expect("valid argument kind");
            // One declaration, the unchanged header, G groups, no equation edges.
            let exact_work = 1 + header_work.used() + group_count;
            let mut short = TypeWorkBudget::with_limit(exact_work - 1);
            assert!(matches!(
                check_expression_work(
                    vec![BodyWork::Declaration(&declaration)],
                    &registry,
                    &mut environments,
                    &mut short,
                ),
                Err(KindFailure::Resource(_))
            ));
            let mut exact = TypeWorkBudget::with_limit(exact_work);
            check_expression_work(
                vec![BodyWork::Declaration(&declaration)],
                &registry,
                &mut environments,
                &mut exact,
            )
            .expect("fresh exact retry of group scheduling");
            assert_eq!(exact.used(), exact_work);
        }
        let mut empty = TypeWorkBudget::with_limit(0);
        let mut environments = KindEnvironments::new();
        check_expression_work(Vec::new(), &registry, &mut environments, &mut empty)
            .expect("empty predecessor performs no work");
        assert_eq!(empty.used(), 0);
    }

    fn assert_valid_application_preflight_has_an_exact_retryable_boundary() {
        let span = span();
        let module = ModuleId::new(0);
        let binder = BinderId::resolved(module, 0);
        let (registry, interface) = method_fixture(span, Vec::new());
        let interface_id = interface.id;
        let definition = equational_definition(
            binder,
            vec![requirement(
                RequirementOwner::Global(binder),
                0,
                interface_id,
                1,
                span,
            )],
            span,
        );
        let mut parts = empty_module_parts(span);
        parts.registry = Arc::new(registry);
        parts.interfaces = vec![interface];
        parts.definitions = vec![definition];
        parts.declaration_order = vec![
            ResolvedDeclarationIndex::Interface(0),
            ResolvedDeclarationIndex::Global(0),
        ];
        let preflight = |budget: &mut TypeWorkBudget| {
            let mut environments = KindEnvironments::new();
            environments.insert_interface(
                interface_id,
                &parts.interfaces[0].parameters,
                span,
                &mut TypeWorkBudget::unbounded(),
            )?;
            preflight_interface_application_kinds(&parts, &mut environments, budget)
        };

        // The arity and positional-kind passes each visit two declarations
        // and authenticate one application shape plus its IOTA membership
        // (eight). Positional synthesis and exact Type-kind comparison add
        // three more.
        const EXACT_WORK: usize = 11;
        let mut measured = TypeWorkBudget::unbounded();
        assert_eq!(preflight(&mut measured), Ok(true));
        assert_eq!(measured.used(), EXACT_WORK);

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            preflight(&mut short),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(short.used(), EXACT_WORK - 1);

        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
            assert_eq!(preflight(&mut exact), Ok(true));
            assert_eq!(exact.used(), EXACT_WORK);
        }
    }

    #[test]
    fn global_application_shape_and_membership_prefixes_are_exact() {
        let span = span();
        let module = ModuleId::new(0);
        let binder = BinderId::resolved(module, 0);
        let interface = InterfaceId::new(module, 0);
        let parameters = [
            ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, 0),
                spelling: "Left".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, 1),
                spelling: "Right".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
        ];
        let install_relation = || {
            let mut environments = KindEnvironments::new();
            environments
                .insert_interface(
                    interface,
                    &parameters,
                    span,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("the two-position interface kind should install");
            environments
        };
        let base = equational_definition(binder, Vec::new(), span);
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_definition(
                &base,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut KindEnvironments::new(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        let base_work = measured.used();

        let accepted = equational_definition(
            binder,
            vec![requirement(
                RequirementOwner::Global(binder),
                0,
                interface,
                2,
                span,
            )],
            span,
        );
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_definition(
                &accepted,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        let accepted_work = measured.used();
        assert!(accepted_work > base_work);
        let mut one_short = TypeWorkBudget::with_limit(accepted_work - 1);
        assert!(matches!(
            check_definition(
                &accepted,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut one_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(one_short.used(), accepted_work - 1);
        let mut exact = TypeWorkBudget::with_limit(accepted_work);
        assert!(matches!(
            check_definition(
                &accepted,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut exact,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        assert_eq!(exact.used(), accepted_work);

        let wrong_arity = equational_definition(
            binder,
            vec![requirement(
                RequirementOwner::Global(binder),
                0,
                interface,
                1,
                span,
            )],
            span,
        );
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_definition(
                &wrong_arity,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Deferred)
        ));
        let arity_work = measured.used();
        let mut one_short = TypeWorkBudget::with_limit(arity_work - 1);
        assert!(matches!(
            check_definition(
                &wrong_arity,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut one_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(one_short.used(), arity_work - 1);
        let mut exact = TypeWorkBudget::with_limit(arity_work);
        assert!(matches!(
            check_definition(
                &wrong_arity,
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                &mut install_relation(),
                &mut exact,
            ),
            Ok(DeclarationKindOutcome::Deferred)
        ));
        assert_eq!(exact.used(), arity_work);

        assert_valid_application_preflight_has_an_exact_retryable_boundary();
    }

    #[test]
    fn determined_global_deferral_reads_only_authenticated_key_positions() {
        // The source-key path scans both canonical parameters (2), schedules
        // and visits the selected variable (2), retains its discovered
        // identity (1), and checks value-type membership (1).
        const EXACT_WORK: usize = 6;
        let span = span();
        let module = ModuleId::new(9_811);
        let key = TypeVariableId::resolved(module, 0);
        let dependent = TypeVariableId::resolved(module, 1);
        let parameters = [
            ResolvedTypeVariable {
                id: key,
                spelling: "Key".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: dependent,
                spelling: "Value".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
        ];
        let occurrence = |parameter: &ResolvedTypeVariable| ResolvedDeterminationParameter {
            id: parameter.id,
            spelling: parameter.spelling.clone(),
            origin: Origin::Source(span),
        };
        let determination = ResolvedInterfaceDetermination {
            determinant: ResolvedDeterminationSide {
                parameters: Box::new([occurrence(&parameters[0])]),
                span,
            },
            dependent: ResolvedDeterminationSide {
                parameters: Box::new([occurrence(&parameters[1])]),
                span,
            },
            span,
        };
        let arguments = [
            fact_type(Type::Variable(key), span),
            fact_type(Type::Variable(dependent), span),
        ];
        let application = |determination| CompleteInterfaceApplication {
            arguments: &arguments,
            parameters: &parameters,
            determination,
        };

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            requirement_has_undetermined_variable(
                application(Some(InterfaceKindDetermination::Resolved(&determination))),
                span,
                &[key],
                &mut short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(short.used(), EXACT_WORK - 1);

        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
            assert_eq!(
                requirement_has_undetermined_variable(
                    application(Some(InterfaceKindDetermination::Resolved(&determination))),
                    span,
                    &[key],
                    &mut exact,
                ),
                Ok(false),
                "a dependent-only binder must not defer a determined global",
            );
            assert_eq!(exact.used(), EXACT_WORK);
        }

        assert_eq!(
            requirement_has_undetermined_variable(
                application(None),
                span,
                &[key],
                &mut TypeWorkBudget::unbounded(),
            ),
            Ok(true),
            "the no-edge predecessor must still require every argument variable",
        );
        assert_eq!(
            requirement_has_undetermined_variable(
                application(Some(InterfaceKindDetermination::Resolved(&determination))),
                span,
                &[dependent],
                &mut TypeWorkBudget::unbounded(),
            ),
            Ok(true),
            "an absent key binder must still defer the global",
        );
    }

    #[test]
    fn implementation_head_and_wide_prerequisite_shape_prefixes_are_exact() {
        const PREREQUISITE_COUNT: usize = 32;
        let span = span();
        let module = ModuleId::new(0);
        let interface = InterfaceId::new(module, 0);
        let implementation_id = ImplId::new(module, 0);
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let relational_parameters = [
            ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, 0),
                spelling: "Left".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, 1),
                spelling: "Right".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
        ];
        let install_relational_interface = || {
            let mut environments = KindEnvironments::new();
            environments
                .insert_interface(
                    interface,
                    &relational_parameters,
                    span,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("the two-position interface kind should install");
            environments
        };

        let relational_head = ResolvedImplementation {
            id: implementation_id,
            public: false,
            head: interface_application(interface, 2, span),
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_implementation(
                &relational_head,
                &registry,
                &mut install_relational_interface(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        let relational_head_work = measured.used();
        let mut one_short = TypeWorkBudget::with_limit(relational_head_work - 1);
        assert!(matches!(
            check_implementation(
                &relational_head,
                &registry,
                &mut install_relational_interface(),
                &mut one_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(one_short.used(), relational_head_work - 1);
        let mut exact = TypeWorkBudget::with_limit(relational_head_work);
        assert!(matches!(
            check_implementation(
                &relational_head,
                &registry,
                &mut install_relational_interface(),
                &mut exact,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        assert_eq!(exact.used(), relational_head_work);

        let make_implementation = |include_invalid: bool| ResolvedImplementation {
            id: implementation_id,
            public: false,
            head: interface_application(interface, 1, span),
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: (0..if include_invalid {
                PREREQUISITE_COUNT
            } else {
                PREREQUISITE_COUNT - 1
            })
                .map(|index| {
                    requirement(
                        RequirementOwner::Impl(implementation_id),
                        index as u32,
                        interface,
                        if include_invalid && index + 1 == PREREQUISITE_COUNT {
                            2
                        } else {
                            1
                        },
                        span,
                    )
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            method_groups: Box::new([]),
            span,
        };
        let interface_parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(interface.module(), 0),
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let install_interface = || {
            let mut environments = KindEnvironments::new();
            environments
                .insert_interface(
                    interface,
                    std::slice::from_ref(&interface_parameter),
                    span,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("the test interface should install");
            environments
        };

        let valid_prefix = make_implementation(false);
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_implementation(
                &valid_prefix,
                &registry,
                &mut install_interface(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Checked)
        ));
        let prefix_work = measured.used();

        let late_invalid = make_implementation(true);
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            check_implementation(
                &late_invalid,
                &registry,
                &mut install_interface(),
                &mut measured,
            ),
            Ok(DeclarationKindOutcome::Deferred)
        ));
        let late_arity_work = measured.used();
        assert!(late_arity_work > prefix_work);
        let mut one_short = TypeWorkBudget::with_limit(late_arity_work - 1);
        assert!(matches!(
            check_implementation(
                &late_invalid,
                &registry,
                &mut install_interface(),
                &mut one_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(one_short.used(), late_arity_work - 1);

        let mut exact = TypeWorkBudget::with_limit(late_arity_work);
        assert!(matches!(
            check_implementation(
                &late_invalid,
                &registry,
                &mut install_interface(),
                &mut exact,
            ),
            Ok(DeclarationKindOutcome::Deferred)
        ));
        assert_eq!(exact.used(), late_arity_work);
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
            effects: Vec::new(),
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
        let interface_parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(interface.module(), 0),
            spelling: "F".into(),
            kind: kind.clone(),
            origin: Origin::Source(span),
        };
        environments
            .insert_interface(
                interface,
                std::slice::from_ref(&interface_parameter),
                span,
                &mut TypeWorkBudget::unbounded(),
            )
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
                &[Type::Int],
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
    fn effect_row_binders_are_limited_to_schemes_and_generalized_locals() {
        let span = span();
        let row = crate::resolved::ResolvedTypeVariable {
            id: TypeVariableId::new(0),
            spelling: "Effects".into(),
            kind: Kind::EffectRow,
            origin: Origin::Source(span),
        };
        let arrow = crate::resolved::ResolvedTypeVariable {
            id: TypeVariableId::new(1),
            spelling: "Constructor".into(),
            kind: Kind::Arrow(Box::new(Kind::EffectRow), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        };

        let mut environments = KindEnvironments::new();
        assert!(
            environments
                .install_scheme_parameters(
                    std::slice::from_ref(&row),
                    &mut TypeWorkBudget::unbounded()
                )
                .is_ok(),
            "global and eligible generalized-local schemes admit a root row binder",
        );
        assert!(
            environments
                .install_owner_parameters(
                    std::slice::from_ref(&row),
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err(),
            "currently representable nominal, interface, and implementation owners share the restricted gate",
        );
        let method_parameters = [(row.id, Kind::EffectRow)];
        assert!(
            environments
                .install_owner_pairs(
                    &method_parameters,
                    span,
                    false,
                    &mut TypeWorkBudget::unbounded(),
                )
                .is_err(),
            "method and implementation scheme mirrors remain restricted",
        );
        assert!(
            environments
                .install_scheme_parameters(
                    std::slice::from_ref(&arrow),
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err(),
            "EffectRow is never admitted below a kind arrow",
        );

        // Effect and operation declaration carriers enter with their syntax
        // checkpoint; that checkpoint must route them through the same
        // restricted owner gate rather than the scheme gate above.
    }

    #[test]
    fn implementation_prerequisite_only_parameters_reject_effect_rows_during_preflight() {
        let span = span();
        let module = ModuleId::new(0);
        let row = ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 1),
            spelling: "Effects".into(),
            kind: Kind::EffectRow,
            origin: Origin::Source(span),
        };
        let (registry, interface) = method_fixture(span, Vec::new());
        let interface_id = interface.id;
        let implementation = ResolvedImplementation {
            id: ImplId::new(module, 0),
            public: false,
            head: interface_application(interface_id, 1, span),
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([row.clone()]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let mut parts = empty_module_parts(span);
        parts.registry = Arc::new(registry.with_additional_type_variables(vec![row]));
        parts.interfaces = vec![interface];
        parts.implementations = vec![implementation];
        parts.declaration_order = vec![
            ResolvedDeclarationIndex::Interface(0),
            ResolvedDeclarationIndex::Implementation(0),
        ];
        let mut environments = KindEnvironments::new();
        environments
            .insert_interface(
                interface_id,
                &parts.interfaces[0].parameters,
                span,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the fixture interface should install");

        assert!(matches!(
            preflight_interface_application_kinds(
                &parts,
                &mut environments,
                &mut TypeWorkBudget::unbounded(),
            ),
            Err(KindFailure::Internal(_))
        ));
    }

    #[test]
    fn body_free_interface_method_separates_allowed_variables_from_required_seed() {
        let span = span();
        let key = TypeVariableId::new(0);
        let dependent = TypeVariableId::new(1);
        let method = TypeVariableId::new(2);
        let undeclared = TypeVariableId::new(3);
        let type_kind = Kind::Type;
        let mut environments = KindEnvironments::new();
        for identity in [key, dependent, method] {
            environments
                .insert_declared(identity, &type_kind, span, &mut TypeWorkBudget::unbounded())
                .expect("the method fixture binder should install");
        }
        let function = |variables: &[TypeVariableId]| {
            Type::Function(
                Box::new(Type::Tuple(
                    variables
                        .iter()
                        .copied()
                        .map(Type::Variable)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                )),
                Box::new(Type::Int),
            )
        };
        let check =
            |ty: &Type, seed: BodyFreeInterfaceMethodSeed<'_>, budget: &mut TypeWorkBudget| {
                environments.expect_body_free_interface_method_with_ledger(
                    ty,
                    &[key, dependent],
                    seed,
                    &[method],
                    span,
                    budget,
                )
            };

        let omitted_dependent = function(&[key, method]);
        let present_dependent = function(&[key, dependent, method]);
        let missing_method = function(&[key]);
        let undeclared_variable = function(&[key, method, undeclared]);
        let mut no_edge_measured = TypeWorkBudget::unbounded();
        check(
            &present_dependent,
            BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
            &mut no_edge_measured,
        )
        .expect("the no-edge predecessor should require and accept every interface parameter");
        let no_edge_work = no_edge_measured.used();
        assert_eq!(no_edge_work, 21);
        let mut no_edge_short = TypeWorkBudget::with_limit(no_edge_work - 1);
        assert!(matches!(
            check(
                &present_dependent,
                BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
                &mut no_edge_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(no_edge_short.used(), no_edge_work - 1);
        let mut no_edge_exact = TypeWorkBudget::with_limit(no_edge_work);
        check(
            &present_dependent,
            BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
            &mut no_edge_exact,
        )
        .expect("the exact no-edge predecessor budget should remain unchanged");
        assert_eq!(no_edge_exact.used(), no_edge_work);

        let mut determined_present_measured = TypeWorkBudget::unbounded();
        check(
            &present_dependent,
            BodyFreeInterfaceMethodSeed::Determined(&[key]),
            &mut determined_present_measured,
        )
        .expect("a dependent may remain present in a determined method");
        assert_eq!(
            determined_present_measured.used(),
            no_edge_work + 2,
            "one determinant comparison and one determinant coverage lookup are additional work",
        );
        let mut determined_present_short =
            TypeWorkBudget::with_limit(determined_present_measured.used() - 1);
        assert!(matches!(
            check(
                &present_dependent,
                BodyFreeInterfaceMethodSeed::Determined(&[key]),
                &mut determined_present_short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(
            determined_present_short.used(),
            determined_present_measured.used() - 1,
        );
        let mut determined_present_exact =
            TypeWorkBudget::with_limit(determined_present_measured.used());
        check(
            &present_dependent,
            BodyFreeInterfaceMethodSeed::Determined(&[key]),
            &mut determined_present_exact,
        )
        .expect("the exact charged determinant-seed budget should fit");
        assert_eq!(
            determined_present_exact.used(),
            determined_present_measured.used(),
        );

        let mut measured = TypeWorkBudget::unbounded();
        check(
            &omitted_dependent,
            BodyFreeInterfaceMethodSeed::Determined(&[key]),
            &mut measured,
        )
        .expect("a dependent may be absent from a determined method");
        let exact_work = measured.used();
        let mut short = TypeWorkBudget::with_limit(exact_work - 1);
        assert!(matches!(
            check(
                &omitted_dependent,
                BodyFreeInterfaceMethodSeed::Determined(&[key]),
                &mut short,
            ),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(short.used(), exact_work - 1);
        let mut exact = TypeWorkBudget::with_limit(exact_work);
        check(
            &omitted_dependent,
            BodyFreeInterfaceMethodSeed::Determined(&[key]),
            &mut exact,
        )
        .expect("the exact determined-method kind budget should fit");
        assert_eq!(exact.used(), exact_work);

        for (seed, ty) in [
            (
                BodyFreeInterfaceMethodSeed::Determined(&[]),
                &omitted_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[key, dependent]),
                &present_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
                &omitted_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[key]),
                &missing_method,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[key, key]),
                &omitted_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[dependent, key]),
                &present_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[method]),
                &omitted_dependent,
            ),
            (
                BodyFreeInterfaceMethodSeed::Determined(&[key]),
                &undeclared_variable,
            ),
        ] {
            assert!(matches!(
                check(ty, seed, &mut TypeWorkBudget::unbounded()),
                Err(KindFailure::Internal(_))
            ));
        }
    }

    #[test]
    fn body_free_interface_method_accepts_a_closed_effectful_function() {
        let span = span();
        let parameter = TypeVariableId::new(0);
        let type_kind = Kind::Type;
        let mut environments = KindEnvironments::new();
        environments
            .insert_declared(
                parameter,
                &type_kind,
                span,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the interface parameter should install");
        let method = Type::function_computation(
            Type::Variable(parameter),
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    crate::types::EffectId::new(ModuleId::new(0), 0),
                    Box::new([]),
                )),
            ),
        );

        environments
            .expect_body_free_interface_method_with_ledger(
                &method,
                &[parameter],
                BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
                &[],
                span,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("a closed latent row remains a valid method value type");
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
                let registry = crate::resolved::ResolvedRegistry::default();
                let mut environments = KindEnvironments::new();
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
                    check_expression_annotations(
                        &expression,
                        &registry,
                        &mut environments,
                        &mut short,
                    ),
                    Err(KindFailure::Resource(_))
                ));
                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                assert!(
                    check_expression_annotations(
                        &expression,
                        &registry,
                        &mut environments,
                        &mut exact,
                    )
                    .is_ok()
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
        let registry = crate::resolved::ResolvedRegistry::default();
        let mut environments = KindEnvironments::new();
        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            check_expression_annotations(&expression, &registry, &mut environments, &mut short,),
            Err(KindFailure::Resource(_))
        ));
        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        assert!(
            check_expression_annotations(&expression, &registry, &mut environments, &mut exact,)
                .is_ok()
        );
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
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
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
            representation_provenance: None,
            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
            representation: None,
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
    fn newtype_payload_provenance_identity_is_authenticated_before_representation_work() {
        let span = span();
        let module = ModuleId::new(0);
        let nominal_id = NominalTypeId::new(module, 0);
        let constructor_id = ConstructorId::new(nominal_id, 0);
        let forged_constructor_id = ConstructorId::new(nominal_id, 1);
        let origin = Origin::Source(span);
        let nominal = ResolvedNominalType {
            representation_provenance: Some(crate::resolved::ResolvedTypeProvenance::new(
                vec![crate::resolved::ResolvedTypeProvenanceNode::Fact(span)],
                0,
            )),
            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Newtype,
            representation: Some(Type::Nominal(nominal_id)),
            id: nominal_id,
            spelling: "Loop".into(),
            constructors: vec![constructor_id].into_boxed_slice(),
            origin: origin.clone(),
        };
        let constructor = ResolvedConstructor {
            id: constructor_id,
            owner: nominal_id,
            spelling: "Loop".into(),
            payload: None,
            origin,
        };
        let mut parts = empty_module_parts(span);
        parts.registry = Arc::new(
            ResolvedRegistry::new(vec![nominal], vec![constructor])
                .with_type_parameters(vec![(nominal_id, Vec::new())]),
        );
        parts.declaration_order = vec![ResolvedDeclarationIndex::Type(0)];
        let provenance = [vec![crate::resolve::ConstructorPayloadProvenance {
            constructor: forged_constructor_id,
            fields: vec![crate::resolved::ResolvedTypeProvenance::new(
                vec![crate::resolved::ResolvedTypeProvenanceNode::Fact(span)],
                0,
            )],
        }]];

        assert_exact_internal(
            &parts,
            &provenance,
            "constructor payload provenance is paired with the wrong identity",
        );
    }

    #[test]
    fn declaration_order_is_a_complete_exact_and_atomic_partition() {
        fn nominal_parts(count: usize, span: Span) -> ResolvedModuleParts {
            let module = ModuleId::new(0);
            let nominals = (0..count)
                .map(|index| ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
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
        // retains one environment record and one Type root per nominal. The
        // unconditional application-arity stage visits both declarations and,
        // after seeing no applications, skips positional kinding:
        // 2 + 1 + 1 + 2 * (1 + 1) + 2 = 10.
        const EXACT_WORK: usize = 10;
        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            check_resolved_module_with_budget(&valid, &provenance, &mut short),
            Err(KindFailure::Resource(_))
        ));
        assert_eq!(valid.declaration_order.len(), 2);
        assert_eq!(valid.registry.nominals().len(), 2);

        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
            check_resolved_module_with_budget(&valid, &provenance, &mut exact)
                .expect("the complete declaration partition should fit exactly and retry");
            assert_eq!(exact.used(), EXACT_WORK);
        }
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
            representation_provenance: None,
            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
            representation: None,
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
                        representation_provenance: None,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                        representation: None,
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
