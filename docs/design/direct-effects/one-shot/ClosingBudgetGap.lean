import NestedClosingBudgets
import ClauseRowAdmission

/-! Check whether structural closing preservation alone bounds closing by
normal resumption. The nested continuation resumes beneath an inner handler;
closing interprets its callback at the surviving outside handler instead. -/
namespace Ash.OneShot.ClosingBudgetGap
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked)
open OwnerPhaseTransitions (available)
open SourceCallableExamples (effect operations policy clauses table operation_known)

def latent : Footprint := [⟨effect, 0, false⟩]
def forwarded : Footprint := [⟨effect, 0, true⟩]
def callback : Code := .lambda 0 (.perform (Instantiation.freezeEffect effect) 0 .unit)

theorem callback_source : Summary operations [] Environment.empty [] callback
    (.function .unit .unit [effect] latent) [] := by
  apply Summary.lambda (input := Value.unit) (latentRequests := [effect])
  · exact .perform operation_known List.mem_cons_self .unit
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, effect, Instance.resources]

def action : ActionData := ⟨7, callback,
  ScopedPorts.typed_value_closed (port_typing callback_source .none) trivial, .none, .unit, [effect]⟩
def shadow : HandlerData := ⟨11, effect, clauses, .none, .unit, rfl⟩
def outer : HandlerData := ⟨12, effect, clauses, .none, .unit, rfl⟩
def tables : CallableProtectionFrames.Tables := fun handler =>
  if handler.activation = 11 then table else [(0, ⟨false, some forwarded, some forwarded⟩)]
def contract : Owners.Contract := ⟨.unit, .unit, false, [], forwarded, [], some forwarded, [effect], [effect]⟩
def contracts : Owners.Contracts := fun owner => if owner = 19 then some contract else none
def saved : Stack := .push (.armed action) .nil
def boundary : Stack := .live 19 .unit .unit saved .none .nil
def receiver : Stack := .push (.handler shadow) boundary
def binding : PlainData := ⟨.bind 99 (.resume 0 .unit), .ticket 0 19, .unit, .unit, [19], rfl⟩
def capture : Stack := .push (.plain binding) receiver
def fixed : Stack := .push (.handler outer) .nil
def plan : List CloseEntry := [.invoke action, .retire 19]
def empty : Requirements [] := .request [] []
def savedRequirements : Requirements [] := .sequence
  ((Requirements.request [] (qualify true latent)).prepend []) empty
def boundaryRequirements : Requirements [] := .sequence (.spent 19) empty
def receiverRequirements : Requirements [] := .sequence
  (empty.prepend (OwnerPhases.ofStack tables boundary)) boundaryRequirements
def resumeRequirements : Requirements [19] := .sequence empty (.invoke ⟨19, .resume⟩ [] [])
def requirements : Requirements [19] := .sequence
  (resumeRequirements.prepend (OwnerPhases.ofStack tables receiver)) receiverRequirements
def records : Store := [(⟨19, .resume⟩, ⟨[], savedRequirements⟩)]
def closingRequirements : Requirements [19] := .sequence
  ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl .none [.retire 19])))
  (.sequence (.retire 19) empty)

theorem owner_known : contracts 19 = some contract := by decide

theorem shadow_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler shadow) := by
  refine .handler (residual := []) ⟨.none, .none⟩
    (.cons (port_lookup operation_known)
      (.resume .unit (List.Subset.refl []) (by simp [shadow, ScopedPorts.InWorld, ScopedPorts.eraseType, ScopedPorts.Port.resources])) .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · simp [same, shadow, clauses, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, shadow] at known

/-- Reuse the literal-resume declaration at the outside handler's actual
residual, retaining its conservative nonempty footprint advertisement. -/
theorem retag_resume_offer (held : Bool) :
    DeclaredSources.Offer operations policy contracts [] Environment.empty [effect]
      1 9 .unit .unit .unit [effect] [] (.resume 9 .unit) held false (some forwarded) := by
  have source := DeclaredSources.Examples.resume_offer contracts Environment.empty [effect] held
  cases source with
  | available resumeInterface closeInterface family =>
      apply DeclaredSources.Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      cases family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance with
      | typed body rows =>
          exact ClauseRowAdmission.resume_value body trivial (by simp [Owners.Contracts.insert])

theorem outer_declaration : DeclaredSources.Declarations operations policy contracts [] Environment.empty
    [effect] effect .unit outer.clauses (tables outer) :=
  .cons operation_known (retag_resume_offer false) (retag_resume_offer true) .nil

theorem outer_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler outer) := by
  refine .handler (residual := [effect]) ⟨.none, .none⟩
    (.cons (port_lookup operation_known)
      (.resume .unit (List.Subset.refl _) (by simp [outer, ScopedPorts.InWorld, ScopedPorts.eraseType, ScopedPorts.Port.resources])) .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · simp [same, outer, clauses, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, outer] at known

theorem outside_source : DeclaredSourceFrames.Segment operations policy contracts tables [] fixed .unit .unit []
    (.sequence (empty.prepend []) empty) [] :=
  DeclaredSourceFrames.push (.handler (tables := tables) outer_typed rfl outer_declaration
    (.cons (.resume rfl .unit) .nil) (.cons (by decide) .nil)) .nil

theorem captured_source : DeclaredSourceFrames.Segment operations policy contracts tables []
    capture .unit .unit [19] requirements records := by
  have nested : DeclaredSourceFrames.Segment operations policy contracts tables [] saved .unit .unit [] savedRequirements [] :=
    DeclaredSourceFrames.push (.armed (action := action) ⟨.none, .none⟩
      (DeclaredSourceValues.from_legacy callback_source) rfl) .nil
  have live : DeclaredSourceFrames.Segment operations policy contracts tables [] boundary .unit .unit [] boundaryRequirements records :=
    .live owner_known rfl rfl ⟨.none, .none⟩ rfl nested .nil
  have interpreted : DeclaredSourceFrames.Segment operations policy contracts tables [] receiver .unit .unit [] receiverRequirements records :=
    DeclaredSourceFrames.push (.handler (tables := tables) shadow_typed rfl
      (DeclaredSources.Examples.declaration contracts Environment.empty)
      (.cons (.resume rfl .unit) .nil) (.cons (by decide) .nil)) live
  have body : DeclaredSources.Expression operations policy contracts [] [effect] binding.scope
      (Environment.empty.extend 99 .unit) (.resume 0 .unit) .unit [19] resumeRequirements :=
    .resume owner_known rfl rfl (.stable .unit) (List.Subset.refl _)
      (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact DeclaredSourceFrames.push
    (.plain (.bind body) (.bound (Owners.ports_lookup owner_known)) rfl rfl) interpreted

theorem normal_checked {disposals : Store} : Checked (records ++ disposals) (OwnerPhases.ofStack tables fixed)
    (available (ownedTickets capture)) requirements [] :=
  RecursiveRequirements.evaluate_sound (by
    simp only [requirements, resumeRequirements, receiverRequirements, boundaryRequirements,
      empty, Requirements.prepend, RecursiveRequirements.evaluate, List.length_cons, List.length_nil,
      RecursiveRequirements.evaluateFuel, records, List.cons_append, List.nil_append,
      RecursiveRequirements.lookup, savedRequirements, if_true]
    decide)

theorem structural_closing : ClosingAdmission.checkedDisposal capture.erase fixed.erase =
    some (plan.map CloseEntry.erase) := by decide

theorem distinct_names : DistinctNames (capture.append fixed).erase := by constructor <;> decide

theorem closing_source : DeclaredSourceClosing.PlanTemplate operations policy contracts tables [] .none
    plan forwarded closingRequirements :=
  .invoke (action := action) (latent := latent)
    (DeclaredSourceValues.from_legacy callback_source) (.retire owner_known .nil)

theorem closing_checked {disposals : Store} : Checked (records ++ disposals) (OwnerPhases.ofStack tables fixed)
    (available (ownedTickets capture)) closingRequirements forwarded :=
  RecursiveRequirements.evaluate_sound (by
    simp only [closingRequirements, empty, Requirements.prepend,
      RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
    decide)

/-- Reuse hereditary record collection: the gap survives an authenticated
complete disposal store, not only the resume-only store used to display it. -/
theorem complete_records : ∃ disposals,
    DeclaredSourceClosing.Records operations policy contracts tables [] capture disposals ∧
    Checked (records ++ disposals) (OwnerPhases.ofStack tables fixed)
      (available (ownedTickets capture)) requirements [] ∧
    Checked (records ++ disposals) (OwnerPhases.ofStack tables fixed)
      (available (ownedTickets capture)) closingRequirements forwarded := by
  obtain ⟨disposals, collected⟩ := DeclaredSourceClosing.collect captured_source
  exact ⟨disposals, collected, normal_checked, closing_checked⟩

theorem closing_exceeds_normal : ¬ EffectBounds.Covers [] forwarded := by
  intro bound
  exact List.not_mem_nil (bound List.mem_cons_self)

/-- The fresh interface keeps the two actual invocation checks separate. -/
def enclosingContract : Owners.Contract :=
  ⟨.unit, .unit, false, [19], [], [19], some forwarded, [effect], [effect]⟩
def enclosingStore : Store :=
  (⟨20, .resume⟩, ⟨[19], requirements⟩) ::
  (⟨20, .dispose⟩, ⟨[19], closingRequirements⟩) :: records

theorem combined_interface : ClauseRowAdmission.Interface 20 enclosingContract true enclosingStore
    (OwnerPhases.ofStack tables fixed) (available [20, 19]) forwarded := by
  refine ⟨?_, ?_, fun _ => ⟨forwarded, rfl⟩, ?_, by decide, by decide⟩
  · apply RecursiveRequirements.evaluate_sound
    simp [enclosingContract, enclosingStore, requirements, resumeRequirements,
      receiverRequirements, boundaryRequirements, empty, Requirements.prepend,
      RecursiveRequirements.evaluate, List.length_cons, List.length_nil,
      RecursiveRequirements.evaluateFuel, records, RecursiveRequirements.lookup,
      savedRequirements] <;> decide
  · intro _ row same
    cases same
    apply RecursiveRequirements.evaluate_sound
    simp [enclosingContract, enclosingStore, closingRequirements, empty,
      Requirements.prepend, RecursiveRequirements.evaluate, List.length_cons, List.length_nil,
      RecursiveRequirements.evaluateFuel, RecursiveRequirements.lookup] <;> decide
  · intro _ row same
    cases same
    exact List.subset_append_left _ _

/-- The same historical closing row need not fit the advertised budget when
disposal is forbidden. Resumption still uses its actual authenticated record. -/
theorem resume_only_unused_closing :
    ClauseRowAdmission.Interface 20 enclosingContract false enclosingStore
      (OwnerPhases.ofStack tables fixed) (available [20, 19]) [] ∧
    ¬ EffectBounds.Covers ([] ++ enclosingContract.resumeRow) forwarded := by
  refine ⟨ClauseRowAdmission.Interface.of_resume combined_interface.resume rfl combined_interface.fresh, ?_⟩
  intro covered
  exact List.not_mem_nil (covered (List.mem_cons_self))

/-- Reuse the disposal schema unchanged apart from its corrected interface
budget. The resulting check admits the closing row through the advertisement;
it does not supply syntax-level disposal permission. -/
theorem discard_with_advertised_budget : ∃ row,
    Checked enclosingStore (.live 20 enclosingContract.held :: OwnerPhases.ofStack tables fixed)
      (available [20, 19]) (.invoke ⟨20, .dispose⟩ enclosingContract.closeDemand []) row ∧
    EffectBounds.Covers forwarded row := by
  have result := ClauseRowAdmission.Rows.instantiate
    (ClauseRowAdmission.discard_rows (templates := fun _ => True) (advertised := forwarded)) combined_interface (by decide)
  simpa only [enclosingContract, List.append_nil] using result

end Ash.OneShot.ClosingBudgetGap

#print axioms Ash.OneShot.ClosingBudgetGap.callback_source
#print axioms Ash.OneShot.ClosingBudgetGap.owner_known
#print axioms Ash.OneShot.ClosingBudgetGap.shadow_typed
#print axioms Ash.OneShot.ClosingBudgetGap.retag_resume_offer
#print axioms Ash.OneShot.ClosingBudgetGap.outer_declaration
#print axioms Ash.OneShot.ClosingBudgetGap.outer_typed
#print axioms Ash.OneShot.ClosingBudgetGap.outside_source
#print axioms Ash.OneShot.ClosingBudgetGap.captured_source
#print axioms Ash.OneShot.ClosingBudgetGap.normal_checked
#print axioms Ash.OneShot.ClosingBudgetGap.structural_closing
#print axioms Ash.OneShot.ClosingBudgetGap.distinct_names
#print axioms Ash.OneShot.ClosingBudgetGap.closing_source
#print axioms Ash.OneShot.ClosingBudgetGap.closing_checked
#print axioms Ash.OneShot.ClosingBudgetGap.complete_records
#print axioms Ash.OneShot.ClosingBudgetGap.closing_exceeds_normal

#print axioms Ash.OneShot.ClosingBudgetGap.combined_interface
#print axioms Ash.OneShot.ClosingBudgetGap.discard_with_advertised_budget

#print axioms Ash.OneShot.ClosingBudgetGap.resume_only_unused_closing
