import DeclaredConnectedAllocation

/-! A small source program tests whether normal cleanup admission suffices
when an outer operation disposes a capture containing its cleanup handler.+This is experimental evidence for the source judgment, not Core semantics. -/
namespace Ash.OneShot.InitialCleanupRouteGap
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open DeclaredSources (Expression Offer Declarations)

def outer : Instance := .user 91 []
def inner : Instance := .user 92 []
def declarations : Instantiation.DeclarationRegistry := fun _ => some ⟨[], [⟨.unit, .unit⟩]⟩
def operations : Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.pair (.reference identity) .integer, .unit)
  | .user _ [], 0 => some (.unit, .unit)
  | _, _ => none
def policy : Syntax.TicketPolicy := fun binder => if binder = 9 then ⟨false, true⟩ else ⟨true, false⟩
def contracts : Owners.Contracts := fun _ => none
def resumeClauses : Clauses := .cons 0 1 8 (.resume 8 .unit) .nil
def discardClauses : Clauses := .cons 0 1 9 (.discard 9) .nil
def resumeTable : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]
def discardTable : List (Nat × ClauseContract) := [(0, ⟨true, some [], none⟩)]
def callback : Code := .lambda 0 (.perform (Instantiation.freezeEffect inner) 0 .unit)
def request : Code := .perform (Instantiation.freezeEffect outer) 0 .unit
def program : Code := .handle (Instantiation.freezeEffect outer)
  (.handle (Instantiation.freezeEffect inner) (.cleanup callback request) resumeClauses) discardClauses
def empty : Requirements [] := .request [] []
def bodyRequirements : Requirements [] :=
  .emitAfter (.sequence empty (.emitAfter empty [] [⟨outer, 0, false⟩])) [] [⟨inner, 0, true⟩]
def requirements : Requirements [] :=
  (bodyRequirements.prepend [.ordinary (.handler inner 0 resumeTable)]).prepend
    [.ordinary (.handler outer 0 discardTable)]

theorem inner_known : operations inner 0 = some (.unit, .unit) := by decide
theorem outer_known : operations outer 0 = some (.unit, .unit) := by decide

theorem resume_offer (held : Bool) :
    Offer operations policy contracts [] Environment.empty [outer] 1 8 .unit .unit .unit [outer] []
      (.resume 8 .unit) held false (some []) := by
  apply Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operand : Expression operations policy (contracts.insert owner contract) [] [outer] (.ticket 8 owner)
      (Environment.empty.extend 1 .unit) .unit contract.input [] empty := inputSame.symm ▸ .stable .unit
  have resumed := Expression.resume (binder := 8) known rfl rfl operand
    (resumeSame.symm ▸ List.Subset.refl [outer])
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows

theorem discard_offer :
    Offer operations policy contracts [] Environment.empty [] 1 9 .unit .unit .unit [] []
      (.discard 9) false true (some []) := by
  apply Offer.available (fun _ => rfl) (fun _ => rfl)
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  exact .typed (.discard known rfl rfl heldSame (closeSame.symm ▸ List.Subset.refl []))
    ClauseRowAdmission.discard_rows

theorem source : Expression operations policy contracts [] [] .none Environment.empty
    program .unit [] requirements := by
  have action : Expression operations policy contracts [] [inner, outer] .none Environment.empty
      callback (.function .unit .unit [inner] [⟨inner, 0, false⟩]) [] empty :=
    .lambda (.perform inner_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
      (.emitAfter (layers := []) (.request (layers := [])))
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, inner, Instance.resources])
  have body : Expression operations policy contracts [] [inner, outer] .none Environment.empty
      (.cleanup callback request) .unit [] bodyRequirements :=
    .cleanup action (.perform outer_known (by simp) (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) (by simp)
  have innerCoverage : ScopedPorts.Covers operations.ports inner resumeClauses := by
    intro operation input output known
    by_cases same : operation = 0
    · simp [same, resumeClauses, ScopedTyping.clauseKeys]
    · cases operation with
      | zero => contradiction
      | succ operation => simp [Operations.ports, operations, inner] at known
  have outerCoverage : ScopedPorts.Covers operations.ports outer discardClauses := by
    intro operation input output known
    by_cases same : operation = 0
    · simp [same, discardClauses, ScopedTyping.clauseKeys]
    · cases operation with
      | zero => contradiction
      | succ operation => simp [Operations.ports, operations, outer] at known
  exact .handler (.handler body
    (.cons (port_lookup inner_known) (.resume .unit (List.Subset.refl _)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) .nil)
    (.cons (.resume rfl .unit) .nil) innerCoverage (by decide) (List.Subset.refl _) resumeTable
    (.cons (by intro impossible; cases impossible) .nil)
    (.cons inner_known (resume_offer false) (resume_offer true) .nil))
    (.cons (port_lookup outer_known) (.discard (List.Subset.refl [])) .nil)
    (.cons (.discard rfl) .nil) outerCoverage (by decide) (List.Subset.refl []) discardTable
    (.cons (by decide) .nil) (.cons outer_known discard_offer .unavailable .nil)

theorem checked : Checked [] [] (OwnerPhaseTransitions.available []) requirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp only [requirements, bodyRequirements, empty, Requirements.prepend,
    RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
  decide

theorem initial_state : DeclaredConnectedSources.State operations policy contracts (fun _ => [])
    (fun _ => none) [] [] .none program .nil .unit [] [] :=
  DeclaredConnectedSources.initial source rfl checked rfl

theorem signature : operations.ports = DeclarationResults.signature declarations := by
  funext effect operation
  cases effect with
  | cell identity => cases operation with
    | zero => rfl
    | succ operation => cases operation <;> rfl
  | user family arguments =>
    cases arguments <;> cases operation <;>
      simp [Operations.ports, operations, DeclarationResults.signature, ScopedPorts.withCellSignatures,
        DeclarationResults.userSignature, declarations, Instantiation.checkFamily,
        Instantiation.OperationTemplate.resources, Instantiation.ValueType.resources,
        Instantiation.parameterEnvironment, Instantiation.ValueType.instantiate,
        DeclarationResults.decodeType, ScopedPorts.eraseType, Value.port]

theorem result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none
    program (.storage []) := by
  have innerPort := port_lookup inner_known
  have outerPort := port_lookup outer_known
  rw [signature] at innerPort outerPort
  exact .handle (.handle (.cleanup (captures := [])
    (.lambda (.perform (.leaf (bound := []) trivial rfl .nil) innerPort rfl) .nil)
    (.perform (.leaf (bound := []) trivial rfl .nil) outerPort rfl))
    (.cons innerPort rfl rfl (.resume (.leaf trivial rfl .nil)) .nil) rfl)
    (.cons outerPort rfl rfl .discard .nil) rfl

theorem initial_run : DeclaredConnectedSources.Run operations declarations policy (fun _ => none) (fun _ => [])
    ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩ .unit [] [] (.storage []) :=
  (DeclaredConnectedSources.initial_run source checked rfl result signature rfl).2

def outerHandler : HandlerData := ⟨100, outer, discardClauses, .none, .unit, rfl⟩
def innerHandler : HandlerData := ⟨101, inner, resumeClauses, .none, .unit, rfl⟩
private theorem callback_closed : ClosedValue callback := by
  refine ⟨trivial, rfl, ?_⟩
  intro dependency member
  cases member

def action : ActionData := ⟨102, callback, callback_closed, .none, .unit, [inner]⟩
def outerStack : Stack := .push (.handler outerHandler) .nil
def innerStack : Stack := .push (.handler innerHandler) outerStack
def capture : Stack := .push (.armed action) innerStack
def plan : List CloseEntry := [.invoke action]

/-- Three entry rules take the admitted source to this particular capture.
The statement is about raw transitions; it does not assume capture admission. -/
theorem entry_trace :
    RawStep ⟨program, .none, .nil⟩
      ⟨.handle (Instantiation.freezeEffect inner) (.cleanup callback request) resumeClauses, .none, outerStack⟩ [] [] ∧
    RawStep ⟨.handle (Instantiation.freezeEffect inner) (.cleanup callback request) resumeClauses, .none, outerStack⟩
      ⟨.cleanup callback request, .none, innerStack⟩ [] [] ∧
    RawStep ⟨.cleanup callback request, .none, innerStack⟩
      ⟨request, .none, capture⟩ [.cleanup 102] [] :=
  ⟨.enterHandler outerHandler _ .nil, .enterHandler innerHandler _ outerStack,
    .enterCleanup action request innerStack⟩

theorem selected_cut : HandlerCut outer capture capture .nil outerHandler :=
  .push _ _ _ _ _ (by decide) (.push _ _ _ _ _ (by decide) (.hit outerHandler .nil rfl))

theorem disposal_selected :
    ProtectionContexts.protectedMode capture.erase = false ∧
    (lookup 0 discardTable).map ClauseContract.dispose = some true ∧
    makePlan capture = some plan := ⟨rfl, rfl, rfl⟩

/-- Giving closing more effect names cannot restore the removed handler. -/
theorem no_open_closing (outward : List Instance) :
    ¬ Admission.OpenCloses capture.erase .nil .nil (Admission.outsideResources capture.erase)
      outward (plan.map CloseEntry.erase) := by
  intro closing
  cases closing with
  | bind frame rest original surviving resources outward suffix kind next => cases kind
  | handler frame effect activation rest original surviving resources outward suffix kind next => cases kind
  | armed frame identity rest original surviving resources outward suffix kind ticketClosed access requests next =>
      cases requests with
      | localTarget request rest target before after next => cases after
      | outside request rest before after declared next => contradiction

theorem no_certificate (record : Owners.Record) :
    ¬ Nonempty (DeclaredClosingInvariant.Certificate operations.ports [] record capture) := by
  rintro ⟨certificate⟩
  have same : certificate.plan = plan := Option.some.inj (certificate.built.symm.trans disposal_selected.2.2)
  exact no_open_closing record.annotation.closeEffects (same ▸ certificate.closing)

end Ash.OneShot.InitialCleanupRouteGap

#print axioms Ash.OneShot.InitialCleanupRouteGap.source
#print axioms Ash.OneShot.InitialCleanupRouteGap.checked
#print axioms Ash.OneShot.InitialCleanupRouteGap.initial_state
#print axioms Ash.OneShot.InitialCleanupRouteGap.signature
#print axioms Ash.OneShot.InitialCleanupRouteGap.result
#print axioms Ash.OneShot.InitialCleanupRouteGap.initial_run
#print axioms Ash.OneShot.InitialCleanupRouteGap.entry_trace
#print axioms Ash.OneShot.InitialCleanupRouteGap.selected_cut
#print axioms Ash.OneShot.InitialCleanupRouteGap.disposal_selected
#print axioms Ash.OneShot.InitialCleanupRouteGap.no_open_closing
#print axioms Ash.OneShot.InitialCleanupRouteGap.no_certificate
