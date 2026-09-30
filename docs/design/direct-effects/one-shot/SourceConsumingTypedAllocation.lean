import SourceConsumingBoundGeneration
import SourceConsumingStoredBounds
import SourceAnnotatedAllocationData

/-! The retained declaration route supplies the existing typed allocator.
Explicit bounds use source admission and finite capture checks. Inherited
recipes reuse the established capture proof for arbitrary retained source.
Both routes preserve the recorded packet and existing ownership result. -/
namespace Ash.OneShot.SourceAnnotatedAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local Pending)

theorem capture_typed_data_from_bounds_at_selected {hints : Hints scope} {forest : Forest hints}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted world required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (storedKnown : stored.handlerAt requested = some ⟨handler, packet⟩)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase))
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) packet.plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes forest actualSaved actualWaiting)
    (actualSelected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held packet.plans
      parameter binder code.erase bodies)
    (captureSource : packet.admission = .bounded → SourceConsumingCaptureInput.Source world forest actualSaved actualWaiting)
    (checked : ∀ bounded, (captureSource bounded).Check outward actions
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner packet.bounds code.erase.requiredActions actualCut closeOutside)
    (supplied : SourceContextualHints.checkRequirements actualWaitingScope (required handler.erase) = true) :
    ∃ resumeEffects closeEffects, ∃ currentBounds : SourcePlanBounds.Annotation world (bodies owner),
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed _ actualSaved actualWaiting
        resumeEffects closeEffects bodies ∧
      currentBounds.Admitted ∧
      (packet.admission = .bounded →
        ∃ annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner)
            (.live (owner := owner) actualSaved actualWaiting),
          SourcePlanBounds.ofCode annotation = currentBounds ∧ annotation.Valid outward
            (actions.insert owner code.erase.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)) ∧
      (packet.admission = .inherited → currentBounds = .absent) ∧
      (stored.capture physical owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer handler.scope).Admitted
        world required := by
  cases storedAdmitted.handlerAt storedKnown with
  | bounded route annotations admitted =>
      obtain ⟨annotation, valid, boundsAdmitted⟩ :=
        SourceConsumingCaptureInput.Source.capture_annotation_admitted admitted (captureSource route) (owner := owner)
          (actions := actions) (phases := OwnerPhaseTransitions.available (ownedTickets whole.erase))
          actualCut actualSelected (checked route) supplied
      obtain ⟨resumeEffects, closeEffects, resume, close, data⟩ :=
        capture_typed_data_at_selected physical matched source selected found rowAvailable declared request retained
          fresh absent operationKnown actualCut actualSelected annotation valid
      refine ⟨resumeEffects, closeEffects, SourcePlanBounds.ofCode annotation, resume, close, data, boundsAdmitted,
        (fun _ => ⟨annotation, rfl, valid⟩), ?_, storedAdmitted.capture physical⟩
      intro impossible
      cases route.symm.trans impossible
  | inherited route recipes =>
      obtain ⟨resumeEffects, closeEffects, resume, close, data⟩ :=
        capture_typed_data_at_cut physical matched source selected found rowAvailable declared request retained
          fresh absent operationKnown (by
            intro capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
            exact SourceScheduledAllocationData.capture_requirements_from_recipe physical.erase matched recipes
              clauseModes selected.erase found declared request retained retained.compatible fresh absent cut chosen)
          actualCut actualSelected
      have bodyDeclared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature (bodies owner)) := by
        cases data with
        | checked matched current pending source => exact SourceScheduledSourceInterfaces.declared_of_local current
      refine ⟨resumeEffects, closeEffects, .absent, resume, close, data, .absent bodyDeclared, ?_,
        (fun _ => rfl), storedAdmitted.capture physical⟩
      intro impossible
      cases route.symm.trans impossible

theorem capture_typed_data_from_bounds {hints : Hints scope} {forest : Forest hints}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted world required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (storedKnown : stored.handlerAt requested = some ⟨handler, packet⟩)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase))
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) packet.plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes forest actualSaved actualWaiting)
    (actualSelected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held packet.plans
      parameter binder code.erase bodies)
    (captureSource : packet.admission = .bounded → SourceConsumingCaptureInput.Source world forest actualSaved actualWaiting)
    (checked : ∀ bounded, (captureSource bounded).Check outward actions
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner packet.bounds code.erase.requiredActions actualCut closeOutside)
    (supplied : SourceContextualHints.checkRequirements actualWaitingScope (required handler.erase) = true) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      ∃ savedHints : Hints capturedScope, ∃ waitingHints : Hints tailScope,
      ∃ savedForest : Forest savedHints, ∃ waitingForest : Forest waitingHints,
      scope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler.erase)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed family
        savedForest waitingForest resumeEffects closeEffects ∧
      (stored.capture physical owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer handler.scope).Admitted
        world required := by
  obtain ⟨resumeEffects, closeEffects, currentBounds, resume, close, data, _, _, _, preserved⟩ :=
    capture_typed_data_from_bounds_at_selected physical matched stored storedAdmitted packet storedKnown clauseModes source
      selected found rowAvailable declared request retained fresh absent operationKnown actualCut actualSelected captureSource checked supplied
  exact ⟨_, _, resumeEffects, closeEffects, _, _, _, actualSaved, actualWaiting,
    actualCut.erase.reconstruct_scope, actualCut.erase.hints, actualCut.forest, actualCut.erase.lookup,
    resume, close, actualSelected.lookup, data.forget, preserved⟩

end Ash.OneShot.SourceAnnotatedAllocationData

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_from_bounds

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_from_bounds_at_selected
