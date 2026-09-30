import DeclaredExecution

/-! Test the missing disposal certificate against the complete current
invariant. This is a structural machine state, not a claimed execution from
an admitted initial program. The callback is pure; its request annotation is
conservative and has no interpreter in the caller. -/
namespace Ash.OneShot.DeclaredDisposalAdmissionGap
open Instantiation ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)

def operations := RecursiveCells.Examples.writableOperations
def declarations : DeclarationRegistry := fun _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨false, true⟩
def tables : CallableProtectionFrames.Tables := fun _ => []
def action := ResumeOnlyCapture.Examples.action
def capture : Stack := .push (.armed action) .nil
def plan : List CloseEntry := [.invoke action]
def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def record : Owners.Record :=
  ⟨contract, ⟨⟨contract.ports, policy 9⟩, ⟨.storage [], .storage []⟩, [], rfl, rfl⟩, rfl⟩
def registry : Owners.Registry := fun owner => if owner = 0 then some record else none
def stack : Stack := .live 0 .unit .unit capture .none .nil
def state : NamedState := ⟨⟨⟨.discard 9, .ticket 9 0, stack⟩, [.ticket 0, .cleanup 102], []⟩, []⟩
def empty : Requirements [] := .request [] []
def savedRequirements : Requirements [] := .sequence empty empty
def pendingRequirements : Requirements [] := .sequence (.spent 0) empty
def resumes : RecursiveRequirements.Store := [(⟨0, .resume⟩, ⟨[], savedRequirements⟩)]
def disposals : RecursiveRequirements.Store := [(⟨0, .dispose⟩, ⟨[], savedRequirements⟩)]

theorem known : registry.contracts 0 = some contract := rfl

theorem callback_source : DeclaredSourceValues.ValueSummary operations policy registry.contracts []
    Environment.empty [] action.action (.function .unit .unit action.requests []) := by
  apply DeclaredSourceValues.from_legacy
  exact .lambda .unit (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources,
    action, ResumeOnlyCapture.Examples.action, ResumeOnlyCapture.Examples.callbackEffect, Instance.resources])

theorem source : DeclaredSourceStates.CheckedState operations policy registry.contracts tables [] []
    (.ticket 9 0) (.discard 9) stack .unit [0] [] := by
  have saved : DeclaredSourceFrames.Segment operations policy registry.contracts tables []
      capture .unit .unit [] savedRequirements [] :=
    DeclaredSourceFrames.push (.armed ⟨.none, .none⟩ callback_source rfl) .nil
  have pending : DeclaredSourceFrames.Segment operations policy registry.contracts tables []
      stack .unit .unit [] pendingRequirements resumes :=
    .live known rfl rfl ⟨.none, .none⟩ rfl saved .nil
  have template : DeclaredSourceClosing.PlanTemplate operations policy registry.contracts tables []
      .none plan [] savedRequirements :=
    .invoke (latent := []) callback_source .nil
  have closing : DeclaredSourceClosing.Records operations policy registry.contracts tables [] stack disposals :=
    .close rfl .nil template (.push .nil) .nil
  have current : DeclaredSources.Expression operations policy registry.contracts [] [] (.ticket 9 0)
      Environment.empty (.discard 9) .unit [0] (.invoke ⟨0, .dispose⟩ [] []) :=
    .discard known rfl rfl rfl (List.Subset.refl [])
  refine .checked (.checked current (.bound (Owners.ports_lookup known)) pending) closing
    (by decide) ?_ rfl
  apply Checked.sequence (firstRow := []) (secondRow := [])
  · apply Checked.invoke (body := savedRequirements)
    · rfl
    · decide
    · exact .hit
    · apply Checked.sequence (firstRow := []) (secondRow := []) <;> exact .request rfl
  · apply Checked.sequence (firstRow := []) (secondRow := [])
    · exact .spent rfl
    · exact .request rfl

theorem results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results []
    state.execution.configuration (.storage []) := by
  refine ⟨CallableContracts.Environment.empty, _, .storage [], .bound (by rfl), .discard, ?_⟩
  apply CompletionFrames.StackReturns.live (record := ⟨.storage [], .storage []⟩) (by rfl) .none
  · exact .armed (environment := CallableContracts.Environment.empty) (captures := [])
      .none (.lambda (.leaf trivial rfl .nil) .nil) .nil
  · exact .nil

theorem usage : ConfigurationUsage policy registry.runtime.joint.usage state.execution.configuration := by
  refine ⟨[0], [], .consume (by rfl) (.discard rfl), ?_, by decide, .refl _, by decide⟩
  exact .live (by rfl) ⟨.none, .none⟩
    (.push (.armed ⟨.none, .none⟩ (.lambda .unit)) (List.nil_subset _) .nil) .nil

theorem current_invariant : DeclaredExecution.Valid operations declarations policy registry tables [] []
    state .unit [0] [] (.storage []) := by
  constructor
  · rw [show operations.ports = ScopedPorts.withCellSignatures (fun _ _ => none) from
      RecursiveRequestProgress.Examples.writable_signature]
    funext effect operation
    cases effect <;> cases operation with
    | zero => rfl
    | succ operation => cases operation <;> rfl
  · exact source
  · exact results
  · exact ⟨.refl _, by decide⟩
  · refine ⟨?_, ?_, by decide⟩
    · intro ticket
      change ([0] : List Nat).count ticket ≤ ([.ticket 0, .cleanup 102] : List Owner).count (.ticket ticket)
      by_cases same : ticket = 0
      · subst ticket; decide
      · simp [Ne.symm same]
    · intro activation
      simp [state, stack, capture, Stack.erase, Control.activations, ExecFrame.erase,
        ActionData.erase, Frame.activation]
  · refine ⟨.live _ _ _ _ _ _ (.push _ _ _ (.nil _) (by decide)) (.nil _), by decide⟩
  · exact usage
  · intro owner
    by_cases same : owner = 0 <;>
      simp [registry, Owners.Registry.runtime, CallableJoint.Registry.joint, state, same]
  · exact ⟨rfl, ⟨⟨trivial, trivial⟩, trivial⟩⟩

theorem closing_rejected : ClosingAdmission.checkedDisposal capture.erase
    (.spent 0 .unit .nil) = none := by decide

/-- The raw operational rule can run; it is the independent access guarantee
that is missing. The example does not refute raw source progress. -/
theorem raw_step_exists : ∃ after, RawStep state.execution.configuration after [.close 103] [.ticket 0] :=
  ⟨_, .discard 9 0 103 (.ticket 9 0) .none .unit .unit .nil capture .nil plan rfl rfl⟩

theorem no_access_checks : ¬ AccessChecks state.execution.configuration [] := by
  intro checks
  have disposal := checks.discard 9 0 (.ticket 9 0) .none .unit .unit .nil capture .nil plan rfl rfl rfl
  have accepted := ClosingAdmission.checked_disposal_iff.mpr disposal
  change ClosingAdmission.checkedDisposal capture.erase (.spent 0 .unit .nil) = some _ at accepted
  rw [closing_rejected] at accepted
  cases accepted

theorem no_admitted_step : ¬ ∃ after, NamedAccessStep [] state after := by
  rintro ⟨after, step, checks⟩
  exact no_access_checks checks

/-- The missing scoped request judgment rejects this state independently of
the source row. Reuse its existing frame and boundary rules by inversion. -/
theorem declared_interface_missing (incoming : List Instance) :
    ¬ ScopedPorts.EffectStack operations.ports registry.contracts.ports [] stack incoming [] := by
  intro typed
  cases typed with
  | live actual scope saved rest resume close bound =>
      have same := Option.some.inj ((Owners.ports_lookup known).symm.trans actual)
      cases same
      cases saved with
      | push frame rest bound => cases frame with
          | armed scope callable requests => cases rest with
              | nil exported => exact List.not_mem_nil (exported (requests List.mem_cons_self))

theorem current_progress_fails :
    DeclaredExecution.Valid operations declarations policy registry tables [] [] state .unit [0] [] (.storage []) ∧
    ¬ state.execution.configuration.expression.IsValue ∧
    ¬ ∃ after, NamedAccessStep [] state after := by
  refine And.intro current_invariant (And.intro ?_ no_admitted_step)
  intro value
  cases value

end Ash.OneShot.DeclaredDisposalAdmissionGap

#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.known
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.callback_source
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.source
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.results
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.usage
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.current_invariant
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.closing_rejected
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.no_access_checks
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.no_admitted_step
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.declared_interface_missing
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.current_progress_fails
#print axioms Ash.OneShot.DeclaredDisposalAdmissionGap.raw_step_exists
