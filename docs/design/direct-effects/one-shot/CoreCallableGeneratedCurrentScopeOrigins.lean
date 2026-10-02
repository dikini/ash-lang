import CoreCallableGeneratedSiteConsumers

/-! Dynamic occurrence evidence is produced only at actual evaluate controls.
Returned resume endpoints retain their actual restored prefix without a path claim. -/
namespace Ash.OneShot.CoreCallableGeneratedChronology
open CoreSyntax CoreMachine CoreTranslation CoreStrictStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableRunningOccurrence
open ScopedExpressions ScopedExecution

def EvaluatingScopeOrigin (current : Endpoint graph) : Prop :=
  match current.state.control with
  | .evaluate _ _ => CurrentScopeOrigin graph current.owners current.focus.scope current.physical
  | .returned _ | .discard _ _ => True

def SavedMapScopeOrigins (current : Endpoint graph) : Prop :=
  ∀ mapped ∈ current.maps,
    CurrentScopeOrigin graph mapped.1 current.focus.scope current.physical

structure EvaluatedScopeOrigins (current : Endpoint graph) : Prop where
  evaluating : EvaluatingScopeOrigin current
  maps : SavedMapScopeOrigins current

theorem EvaluatedScopeOrigins.at {graph : Graph} {current : Endpoint graph}
    (origins : EvaluatedScopeOrigins current)
    (control : current.state.control = .evaluate site environment) :
    CurrentScopeOrigin graph current.owners current.focus.scope current.physical := by
  simpa only [EvaluatingScopeOrigin,control] using origins.evaluating

private theorem singleton_origin {graph : Graph} {current : Endpoint graph}
    (origins : EvaluatedScopeOrigins current) (same : current.maps = [(owners,frame)]) :
    CurrentScopeOrigin graph owners current.focus.scope current.physical :=
  origins.maps (owners,frame) (by simp [same])

private theorem prepend_handler
    (origin : CurrentScopeOrigin graph owners scope physical) :
    CurrentScopeOrigin graph owners scope (.handlerBoundary site environment activation :: physical) := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path =>
    exact .clause canonical (.skip _ (by intro _ _ _ _ _ impossible; cases impossible) path)

theorem started_evaluating_scope
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target) :
    EvaluatedScopeOrigins (started start) := by
  refine ⟨?_,?_⟩
  · change CurrentScopeOrigin graph cleanupOwners .none _
    exact .inactive (CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical start.installed.origin)
  · simp [SavedMapScopeOrigins,started]

/-- Descent consumes the preceding evaluate origin. Saved-map restoration uses
its exact dynamic occurrence at this current physical suffix. -/
theorem Operation.evaluating_scope {graph : Graph} {before after : Endpoint graph}
    (operation : Operation before after created discharged) (origins : EvaluatedScopeOrigins before) :
    EvaluatedScopeOrigins after := by
  cases operation with
  | cleanup input =>
    have parent : CurrentScopeOrigin graph before.owners input.data.scope before.physical := by
      simpa only [input.empty.focus] using origins.at input.control
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,cleanup_result,CoreCallableGeneralCleanupRegistration.registeredState] using
        CoreCallableCleanupOrigins.CurrentScopeOrigin.prepend_cleanup parent
    · simp [SavedMapScopeOrigins,cleanup_result]
  | bind input =>
    have parent : CurrentScopeOrigin graph input.owners input.plain.scope before.physical := by
      simpa only [input.ownersSame,input.empty.focus] using origins.at input.control
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,bind_result] using
        CurrentScopeOrigin.prepend_plain parent input.past.saved.saved.related
    · simp [SavedMapScopeOrigins,bind_result]
  | beta input =>
    refine ⟨?_,?_⟩
    · change CurrentScopeOrigin graph [] .none before.physical
      exact .inactive (.empty graph)
    · simp [SavedMapScopeOrigins,beta_result]
  | bindReturn input =>
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,bind_return_result] using input.past.saved.saved.origin
    · simp [SavedMapScopeOrigins,bind_return_result]
  | handler input =>
    have parent : CurrentScopeOrigin graph input.owners input.data.scope before.physical := by
      simpa only [input.ownersSame,input.empty.focus] using origins.at input.control
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,handler_result] using
        prepend_handler (site := input.site) (environment := input.environment) (activation := input.data.activation) parent
    · simp [SavedMapScopeOrigins,handler_result]
  | handlerReturn input =>
    refine ⟨?_,?_⟩
    · simp [EvaluatingScopeOrigin,handler_return_result,input.control]
    · simp [SavedMapScopeOrigins,handler_return_result]
  | literal input =>
    refine ⟨?_,origins.maps⟩
    simp [EvaluatingScopeOrigin,literal_result]
  | entry input =>
    have parent := origins.at input.control
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,entry_result] using parent
    · simpa [SavedMapScopeOrigins,entry_result] using parent
  | swap input =>
    have saved := singleton_origin origins input.maps
    refine ⟨?_,?_⟩
    · simpa only [EvaluatingScopeOrigin,swap_result] using saved
    · simpa [SavedMapScopeOrigins,swap_result] using saved
  | tuple input =>
    refine ⟨?_,?_⟩
    · simp [EvaluatingScopeOrigin,tuple_result]
    · simp [SavedMapScopeOrigins,tuple_result]
  | capture input =>
    have canonical := CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical
      (location before input.index).installation.origin
    refine ⟨?_,?_⟩
    · change CurrentScopeOrigin graph
        (⟨(location before input.index).installation.handler,input.selectedClause.owner,ticket graph input.selectedClause.owner⟩ ::
          (location before input.index).owners)
        (.ticket (ticket graph input.selectedClause.owner) before.state.nextOwner)
        (.clauseBoundary (location before input.index).installation.handler input.selectedClause.owner
          (location before input.index).data.activation before.state.nextOwner
          (some ((location before input.index).inside ++ [.handlerBoundary (location before input.index).site
            (location before input.index).environment (location before input.index).data.activation])) ::
          (location before input.index).outside)
      exact .clause canonical (.hit _)
    · simp [SavedMapScopeOrigins,capture_result]
  | resume input =>
    refine ⟨?_,?_⟩
    · simp [EvaluatingScopeOrigin,resume_result,CoreGeneralCaptureResume.resumeAfter]
    · simp [SavedMapScopeOrigins,resume_result]
  | spentReturn input =>
    refine ⟨?_,?_⟩
    · simp [EvaluatingScopeOrigin,spent_return_result,CoreGeneralRestoration.observedState]
    · simp [SavedMapScopeOrigins,spent_return_result]

theorem Generated.current_evaluating_scope {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (run : Generated start current count created discharged) :
    EvaluatedScopeOrigins current := by
  induction run with
  | initial => exact started_evaluating_scope _
  | next earlier operation ih => exact operation.evaluating_scope ih

#print axioms EvaluatedScopeOrigins.at
#print axioms started_evaluating_scope
#print axioms Operation.evaluating_scope
#print axioms Generated.current_evaluating_scope
end Ash.OneShot.CoreCallableGeneratedChronology
