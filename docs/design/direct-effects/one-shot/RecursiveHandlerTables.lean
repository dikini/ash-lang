import RecursiveClauseUsage

/-!
Handler-table registration preserves the existing recursive source forest.
Agreement is required at retained activation names, including dormant captures;
the established activation traversal supplies the finite freshness boundary.
-/

namespace Ash.OneShot.RecursiveHandlerTables
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open CallableProtectionFrames (Tables)
open RecursiveRequirements (Requirements Checked)
open SourceTemplates (Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveClosing (PlanTemplate)

theorem frame_entry_congr
    (agree : ∀ handler, handler.activation ∈ frame.erase.activation → first handler = second handler) :
    OwnerPhases.frameEntry first frame = OwnerPhases.frameEntry second frame := by
  cases frame with
  | handler handler => simp only [OwnerPhases.frameEntry, agree handler List.mem_cons_self]
  | plain | cell | armed | running | unwinding | closing | retiring => rfl

theorem context_congr
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    OwnerPhases.ofStack first stack = OwnerPhases.ofStack second stack := by
  induction stack with
  | nil => rfl
  | push frame tail ih =>
      have head := frame_entry_congr (frame := frame)
        (fun handler member => agree handler (List.mem_append_left _ member))
      have rest := ih (fun handler member => agree handler (List.mem_append_right _ member))
      simp only [OwnerPhases.ofStack, head, rest]
  | live owner input answer saved caller tail ihSaved ihTail =>
      have rest := ihTail (fun handler member => agree handler (List.mem_append_right _ member))
      simp only [OwnerPhases.ofStack, rest]
  | spent owner answer caller tail ih => exact congrArg (List.cons (.spent owner)) (ih agree)

theorem segment_congr
    (source : Segment operations policy contracts first world stack input output demand requirements records)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    Segment operations policy contracts second world stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push head tail ih =>
      have next := fun handler member => agree handler (List.mem_append_right _ member)
      have same := context_congr next
      simpa only [same] using SourceTemplates.Segment.push head (ih next)
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held
        (ihSaved (fun handler member => agree handler (List.mem_append_left _ member)))
        (ihTail (fun handler member => agree handler (List.mem_append_right _ member)))
  | spent known annotation scopeKnown tail ih => exact .spent known annotation scopeKnown (ih agree)

/-- Reuse table transport for any retained frame evidence. The transfer premise
    only sees registry agreement at that frame's actual activation. -/
theorem annotated_segment_congr
    (source : RecursiveCapture.AnnotatedSegment predicate operations policy contracts first world
      stack input output demand requirements records)
    (transfer : ∀ entry input output demand requirements,
      (∀ handler, handler.activation ∈ entry.erase.activation → first handler = second handler) →
      predicate entry input output demand requirements → nextPredicate entry input output demand requirements)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    RecursiveCapture.AnnotatedSegment nextPredicate operations policy contracts second world
      stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push current head tail ih =>
      have next := fun handler member => agree handler (List.mem_append_right _ member)
      have same := context_congr next
      have changed := transfer _ _ _ _ _ (fun handler member => agree handler (List.mem_append_left _ member)) current
      simpa only [same] using RecursiveCapture.AnnotatedSegment.push changed head (ih next)
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held
        (ihSaved (fun handler member => agree handler (List.mem_append_left _ member)))
        (ihTail (fun handler member => agree handler (List.mem_append_right _ member)))
  | spent known annotation scopeKnown tail ih => exact .spent known annotation scopeKnown (ih agree)

/-- Executable closing plans contain no handler frames. Their interpretation
    prefixes therefore do not depend on the handler-table registry. -/
theorem closing_context_congr (first second : Tables) (scope : Scope) (plan : List CloseEntry) :
    OwnerPhases.ofStack first (closeControl scope plan) = OwnerPhases.ofStack second (closeControl scope plan) := by
  induction plan with
  | nil => rfl
  | cons entry tail ih => cases entry <;>
      simp only [closeControl, CloseEntry.frame, OwnerPhases.ofStack, OwnerPhases.frameEntry,
        ExecFrame.erase, ActionData.erase, ProtectionContexts.frameProtected] <;> rw [ih]

theorem template_congr
    (source : PlanTemplate operations policy contracts first world scope plan raw requirements) :
    PlanTemplate operations policy contracts second world scope plan raw requirements := by
  induction source with
  | nil => exact .nil
  | release rest ih => simpa only [closing_context_congr first second] using PlanTemplate.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => simpa only [closing_context_congr first second] using PlanTemplate.invoke callback ih

theorem records_congr
    (source : Records operations policy contracts first world stack records) :
    Records operations policy contracts second world stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external outside saved rest ihSaved ihRest => exact .external outside ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest =>
      exact .close built internal (template_congr template) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem configuration_congr
    (source : SourceTemplates.Configuration operations policy contracts first world scope code stack output demand requirements records)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    SourceTemplates.Configuration operations policy contracts second world scope code stack output demand requirements records := by
  cases source with
  | checked current scopeTyped pending =>
      have same := context_congr agree
      simpa only [same] using SourceTemplates.Configuration.checked current scopeTyped (segment_congr pending agree)

theorem checked_state_congr
    (source : CheckedState operations policy contracts first world outside scope code stack output demand row)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    CheckedState operations policy contracts second world outside scope code stack output demand row := by
  cases source with
  | checked source closing unique evaluated accepted =>
      exact .checked (configuration_congr source agree) (records_congr closing) unique evaluated accepted

/-- Activation labels distinguish runtime occurrences; the same table has the
    same residual action at any label. -/
theorem handler_layer_activation (effect : Instance) (table : List (Nat × ClauseContract))
    (first second : Nat) (raw : Footprint) :
    ProtectionResiduals.throughLayer (.handler effect first table) raw =
      ProtectionResiduals.throughLayer (.handler effect second table) raw := by
  induction raw with
  | nil => rfl
  | cons request rest ih => simp only [ProtectionResiduals.throughLayer, ProtectionResiduals.demandThrough, ih]

theorem export_activation (front tail : OwnerPhases.Context) (before : OwnerPhaseTransitions.Phases) :
    OwnerSource.exportAt (front ++ .ordinary (.handler effect first table) :: tail) before raw =
      OwnerSource.exportAt (front ++ .ordinary (.handler effect second table) :: tail) before raw := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, ProtectionResiduals.residual_append]
  cases exported : ProtectionResiduals.residualize (OwnerPhaseTransitions.project front before) raw with
  | none => rfl
  | some row => simp only [OwnerPhaseTransitions.project, ProtectionResiduals.residualize, handler_layer_activation effect table first second]

theorem selection_replace_ordinary
    (selected : OwnerPhases.Consumes owner (front ++ .ordinary first :: tail) waiting) :
    ∃ next, OwnerPhases.Consumes owner (front ++ .ordinary second :: tail) next := by
  have existsFirst : (OwnerPhases.consume owner (front ++ .ordinary first :: tail)).isSome = true := by
    rw [OwnerPhases.consumes_sound selected]; rfl
  rw [ResourceRequirements.ordinary_consume_middle,
    ← ResourceRequirements.ordinary_consume_middle front tail owner second] at existsFirst
  cases found : OwnerPhases.consume owner (front ++ .ordinary second :: tail) with
  | none => simp [found] at existsFirst
  | some next => exact ⟨next, OwnerPhases.consumes_complete found⟩

/-- Reuse the recursive check, including authenticated invocation bodies, when
    replacing a source checking label with a fresh runtime activation. -/
theorem checked_activation
    (checked : Checked store original before requirements row)
    (split : original = front ++ .ordinary (.handler effect first table) :: tail) :
    Checked store (front ++ .ordinary (.handler effect second table) :: tail) before requirements row := by
  induction checked generalizing front tail with
  | request exported =>
      apply Checked.request
      rw [← List.append_assoc, ← export_activation (first := first) (second := second)]
      simpa only [split, List.append_assoc] using exported
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke known ready selected next ih =>
      rename_i key demand body phases nearer current waiting output
      obtain ⟨waiting, selection⟩ := selection_replace_ordinary (second := .handler effect second table)
        (front := nearer ++ front) (tail := tail) (by simpa only [split, List.append_assoc] using selected)
      have preserved := ih (front := nearer ++ front) (tail := tail) (by simp only [split, List.append_assoc])
      exact .invoke known ready (by simpa only [List.append_assoc] using selection)
        (by simpa only [List.append_assoc] using preserved)
  | sequence left right ihLeft ihRight => exact .sequence (ihLeft split) (ihRight split)
  | emitAfter body exported ih =>
      apply Checked.emitAfter (ih split)
      rw [← List.append_assoc, ← export_activation (first := first) (second := second)]
      simpa only [split, List.append_assoc] using exported
  | choice left right ihLeft ihRight => exact .choice (ihLeft split) (ihRight split)

/-- Installation assigns the supplied table to its fresh activation. Existing
    annotations at other activation names retain their interpretation. -/
def register (tables : Tables) (activation : Nat) (clauses : List (Nat × ClauseContract)) : Tables :=
  fun handler => if handler.activation = activation then clauses else tables handler

theorem registered_lookup (same : handler.activation = activation) :
    register tables activation clauses handler = clauses := by simp [register, same]

theorem register_agrees {stack : Stack}
    (fresh : activation ∉ stack.erase.activations) :
    ∀ handler, handler.activation ∈ stack.erase.activations →
      tables handler = register tables activation clauses handler := by
  intro handler member
  have different : handler.activation ≠ activation := fun same => fresh (same ▸ member)
  simp [register, different]

theorem register_preserves
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (fresh : activation ∉ stack.erase.activations) :
    CheckedState operations policy contracts (register tables activation clauses) world outside scope code stack output demand row :=
  checked_state_congr source (register_agrees fresh)

/-- Reuse the existing fresh-name theorem and lifetime support bound. The chosen
    activation is fresh for history and its registration preserves all records. -/
theorem fresh_registration
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (retained : stack.erase.activations ⊆ history) (clauses : List (Nat × ClauseContract)) :
    ∃ activation, activation ∉ history ∧
      CheckedState operations policy contracts (register tables activation clauses) world outside scope code stack output demand row := by
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
  exact ⟨activation, fresh, register_preserves source (fun member => fresh (retained member))⟩

/-- The lifetime invariant already bounds every retained activation count. -/
theorem history_support (history : NameHistory state activations) :
    state.configuration.stack.erase.activations ⊆ activations := by
  intro activation member
  have positive := List.count_pos_iff.mpr member
  have bound := history.handlers activation
  apply List.count_pos_iff.mp
  omega

theorem registration_from_history
    (source : CheckedState operations policy contracts tables world outside state.configuration.scope
      state.configuration.expression state.configuration.stack output demand row)
    (history : NameHistory state activations) (clauses : List (Nat × ClauseContract)) :
    ∃ activation, activation ∉ activations ∧
      CheckedState operations policy contracts (register tables activation clauses) world outside
        state.configuration.scope state.configuration.expression state.configuration.stack output demand row :=
  fresh_registration source (history_support history) clauses

/-- Construct handler entry from the body, clause ports and ordered body check.
    Full declaration admission must still derive the supplied table and checks. -/
theorem handler_entry_with_frame
    (body : SourceTemplates.Expression operations policy contracts world (effect :: residual) scope Environment.empty
      code answer bodyDemand bodyRequirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (clausesTyped : ScopedPorts.ClausesTyped operations.ports world ScopedPorts.TypeEnv.empty effect answer.port residual clauses)
    (coverage : ScopedPorts.Covers operations.ports effect clauses)
    (clauseUnique : (ScopedTyping.clauseKeys clauses).Nodup)
    (pending : Segment operations policy contracts tables world stack answer output tailDemand tailRequirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (bodyCheck : Checked (resumes ++ disposals)
      (.ordinary (.handler effect 0 table) :: OwnerPhases.ofStack tables stack)
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow)
    (tailCheck : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand) tailRequirements tailRow)
    (accepted : checkFootprint outside (bodyRow ++ tailRow) = true)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, handler.activation ∉ history ∧
      register tables handler.activation table handler = table ∧
      RawStep ⟨.handle (Instantiation.freezeEffect effect) code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      CheckedState operations policy contracts (register tables handler.activation table) world outside scope
        code (.push (.handler handler) stack) output (bodyDemand ++ tailDemand) (bodyRow ++ tailRow) ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack ∧
      handler.clauses = clauses ∧ handler.effectInst = effect ∧
      SourceTemplates.Frame operations policy contracts world (.handler handler) answer answer [] (.request [] []) := by
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
  let handler : HandlerData := ⟨activation, effect, clauses, scope, ScopedPorts.embedPort answer.port,
    ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
  let next := register tables activation table
  have agree : ∀ actual, actual.activation ∈ stack.erase.activations → tables actual = next actual :=
    register_agrees (fun member => fresh (retained member))
  have sameContext := context_congr agree
  have installed : next handler = table := registered_lookup rfl
  have sameOwners : ownedTickets (.push (.handler handler) stack) = ownedTickets stack := rfl
  have frame : SourceTemplates.Frame operations policy contracts world (.handler handler) answer answer [] (.request [] []) :=
    .handler (.handler (ScopedPorts.effect_scope_has_types scopeTyped |> fun known => ⟨_, known⟩)
      (by simpa only [handler, ScopedPorts.erase_embed_port] using clausesTyped) coverage clauseUnique)
      (by simp only [handler, ScopedPorts.erase_embed_port])
  have source := SourceTemplates.Segment.push frame (segment_congr pending agree)
  have current : Checked (resumes ++ disposals) (OwnerPhases.ofStack next (.push (.handler handler) stack))
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow := by
    have relocated := checked_activation bodyCheck (front := []) (tail := OwnerPhases.ofStack tables stack) (second := activation) rfl
    simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry, installed, handler, sameContext] using relocated
  have afterBody : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand)
      (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack next stack)) tailRequirements) tailRow :=
    .sequence (firstRow := []) (secondRow := tailRow)
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) tailCheck
  have prefixed : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (bodyRequirements.prepend (OwnerPhases.ofStack next (.push (.handler handler) stack))) bodyRow :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using current)
  refine ⟨handler, fresh, installed, .enterHandler handler code stack, ?_, sameOwners, rfl, rfl, frame⟩
  exact .checked (.checked body scopeTyped source) (.push (records_congr closing)) unique
    (.sequence prefixed afterBody) accepted

theorem handler_entry
    (body : SourceTemplates.Expression operations policy contracts world (effect :: residual) scope Environment.empty
      code answer bodyDemand bodyRequirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (clausesTyped : ScopedPorts.ClausesTyped operations.ports world ScopedPorts.TypeEnv.empty effect answer.port residual clauses)
    (coverage : ScopedPorts.Covers operations.ports effect clauses)
    (clauseUnique : (ScopedTyping.clauseKeys clauses).Nodup)
    (pending : Segment operations policy contracts tables world stack answer output tailDemand tailRequirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (bodyCheck : Checked (resumes ++ disposals)
      (.ordinary (.handler effect 0 table) :: OwnerPhases.ofStack tables stack)
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow)
    (tailCheck : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand) tailRequirements tailRow)
    (accepted : checkFootprint outside (bodyRow ++ tailRow) = true)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, handler.activation ∉ history ∧
      register tables handler.activation table handler = table ∧
      RawStep ⟨.handle (Instantiation.freezeEffect effect) code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      CheckedState operations policy contracts (register tables handler.activation table) world outside scope
        code (.push (.handler handler) stack) output (bodyDemand ++ tailDemand) (bodyRow ++ tailRow) ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack ∧
      handler.clauses = clauses := by
  obtain ⟨handler, fresh, installed, step, checked, owners, clausesSame, effectSame, frame⟩ :=
    handler_entry_with_frame body scopeTyped clausesTyped coverage clauseUnique pending closing unique
      bodyCheck tailCheck accepted retained
  exact ⟨handler, fresh, installed, step, checked, owners, clausesSame⟩

/-- A handler expression in the shared source judgment supplies the local
    installation premises. No successor check is an input. -/
theorem handler_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.handle requested code clauses) stack output demand row)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, ∃ table : List (Nat × ClauseContract),
      handler.activation ∉ history ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      CheckedState operations policy contracts (register tables handler.activation table) world outside scope
        code (.push (.handler handler) stack) output demand row ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack ∧
      ClausesUse policy handler.clauses ∧
      SourceTemplates.ClauseModes handler.clauses (register tables handler.activation table handler) := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending => cases current with
      | stable summary => cases summary
      | callable summary => cases summary
      | handler body clausesTyped capabilities coverage clauseUnique admitted table modes =>
          obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
          have bodyCheck := RecursiveRequirements.checked_prepend_iff.mp
            (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
          simp only [List.append_nil, List.cons_append, List.nil_append] at bodyCheck
          obtain ⟨handler, fresh, known, step, successor, owners, sameClauses⟩ := handler_entry
            body scopeTyped clausesTyped coverage clauseUnique pending closing unique bodyCheck tailCheck
            (sameRow ▸ accepted) retained
          exact ⟨handler, table, fresh, step, sameRow.symm ▸ successor, owners,
            sameClauses.symm ▸ capabilities, by simpa only [sameClauses, known] using modes⟩

namespace Examples
open RecursiveClauseOwnership.ResourceClauseExamples (contracts clause stack boundary)
open RecursiveDisposalCapture.Examples (operations tables effect)
open RecursiveRecords.Examples (policy)

theorem registration_retains_dormant_capture : ∃ contract : Owners.Contract,
    CheckedState operations policy (contracts.insert 23 contract) (register tables 74 []) [] [] (.ticket 1 23)
      clause boundary .unit [23] [] := by
  obtain ⟨contract, step, checked⟩ := RecursiveClauseOwnership.ResourceClauseExamples.capture_preserved
  exact ⟨contract, register_preserves checked (by decide)⟩

/-- Active context equality cannot justify changing a dormant handler table.
    Its saved interpretation changes when that capture is restored. -/
theorem dormant_interpretation_changes :
    OwnerPhases.ofStack tables boundary = OwnerPhases.ofStack (register tables 73 []) boundary ∧
    OwnerSource.exportAt (OwnerPhases.ofStack tables stack) OwnerPhaseTransitions.empty [⟨effect, 0, false⟩] = some [] ∧
    OwnerSource.exportAt (OwnerPhases.ofStack (register tables 73 []) stack) OwnerPhaseTransitions.empty
      [⟨effect, 0, false⟩] = none ∧
    73 ∈ boundary.erase.activations := by decide

def initialHandler : Code := .handle (Instantiation.freezeEffect effect)
  (.perform (Instantiation.freezeEffect effect) 0 .unit)
  RecursiveClauseOwnership.ResourceClauseExamples.handler.clauses

def initialHandlerRequirements : Requirements [] :=
  (Requirements.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]).prepend
    [.ordinary (.handler effect 0 [(0, ⟨true, some [], some []⟩)])]

theorem initial_handler_source (world : List Nat) (allowed : List Instance) (scope : Scope) :
    SourceTemplates.Expression operations policy contracts world allowed scope Environment.empty initialHandler .unit []
      initialHandlerRequirements := by
  have body : SourceTemplates.Expression operations policy contracts world [effect] scope Environment.empty
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit []
      (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) :=
    .perform RecursiveDisposalCapture.Examples.operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have coverage : ScopedPorts.Covers operations.ports effect
      RecursiveClauseOwnership.ResourceClauseExamples.handler.clauses := by
    cases RecursiveClauseOwnership.ResourceClauseExamples.handler_typed with
    | handler known clauses coverage unique => exact coverage
  exact .handler body
    (ScopedPorts.clauses_world_weaken RecursiveClauseOwnership.ResourceClauseExamples.clauses_typed (List.nil_subset world))
    RecursiveClauseOwnership.ResourceClauseExamples.clauses_usage coverage (by decide) (List.nil_subset allowed) [(0, ⟨true, some [], some []⟩)]
    (.cons (fun _ => rfl) .nil)

/-- The shared handler rule admits the complete initial expression. -/
theorem initial_handler_checked : CheckedState operations policy contracts tables [] [] .none initialHandler .nil .unit [] [] := by
  have bodyCheck : Checked [] [.ordinary (.handler effect 0 [(0, ⟨true, some [], some []⟩)])]
      (OwnerPhaseTransitions.available []) (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) [] :=
    .emitAfter (bodyRow := []) (requestRow := [])
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) (by decide)
  have source := initial_handler_source [] [] .none
  have current : Checked [] [] (OwnerPhaseTransitions.available [])
      (((Requirements.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]).prepend
        [.ordinary (.handler effect 0 [(0, ⟨true, some [], some []⟩)])]).prepend []) [] := by
    apply RecursiveRequirements.checked_prepend_iff.mpr
    apply RecursiveRequirements.checked_prepend_iff.mpr
    simpa only [List.append_nil] using bodyCheck
  exact .checked (.checked source .none .nil) .nil (by decide)
    (.sequence (firstRow := []) (secondRow := []) current
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))) (by decide)

/-- Shared source admission supplies every local handler-entry premise. -/
theorem install_resource_clause_handler : ∃ handler : HandlerData, ∃ table : List (Nat × ClauseContract),
    RawStep ⟨initialHandler, .none, .nil⟩
      ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, .push (.handler handler) .nil⟩ [] [] ∧
    CheckedState operations policy contracts (register tables handler.activation table) [] [] .none
      (.perform (Instantiation.freezeEffect effect) 0 .unit) (.push (.handler handler) .nil) .unit [] [] := by
  obtain ⟨handler, table, fresh, step, successor, owners, capabilities, modes⟩ :=
    handler_preserves initial_handler_checked (history := []) (List.Subset.refl [])
  exact ⟨handler, table, step, successor⟩

end Examples

end Ash.OneShot.RecursiveHandlerTables

#print axioms Ash.OneShot.RecursiveHandlerTables.frame_entry_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.context_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.segment_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.closing_context_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.template_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.records_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.configuration_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.checked_state_congr
#print axioms Ash.OneShot.RecursiveHandlerTables.registered_lookup
#print axioms Ash.OneShot.RecursiveHandlerTables.register_agrees
#print axioms Ash.OneShot.RecursiveHandlerTables.register_preserves
#print axioms Ash.OneShot.RecursiveHandlerTables.fresh_registration

#print axioms Ash.OneShot.RecursiveHandlerTables.history_support
#print axioms Ash.OneShot.RecursiveHandlerTables.registration_from_history
#print axioms Ash.OneShot.RecursiveHandlerTables.Examples.registration_retains_dormant_capture
#print axioms Ash.OneShot.RecursiveHandlerTables.Examples.dormant_interpretation_changes

#print axioms Ash.OneShot.RecursiveHandlerTables.handler_layer_activation
#print axioms Ash.OneShot.RecursiveHandlerTables.export_activation
#print axioms Ash.OneShot.RecursiveHandlerTables.selection_replace_ordinary
#print axioms Ash.OneShot.RecursiveHandlerTables.checked_activation

#print axioms Ash.OneShot.RecursiveHandlerTables.handler_entry

#print axioms Ash.OneShot.RecursiveHandlerTables.Examples.install_resource_clause_handler

#print axioms Ash.OneShot.RecursiveHandlerTables.handler_preserves

#print axioms Ash.OneShot.RecursiveHandlerTables.Examples.initial_handler_checked

#print axioms Ash.OneShot.RecursiveHandlerTables.Examples.initial_handler_source

#print axioms Ash.OneShot.RecursiveHandlerTables.handler_entry_with_frame

#print axioms Ash.OneShot.RecursiveHandlerTables.annotated_segment_congr
