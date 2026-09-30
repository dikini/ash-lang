import SourceDependencySchemes

/-! Test the existing closing-budget obstruction against enriched source
segments. This is a finite source fixture, not a reachable initial execution. -/
namespace Ash.OneShot.SourceDependencyBudgetGap
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open SourceDependencyFrames (Frame Segment)
open SourceDependencySchemes.Examples
open SourceCallableExamples (effect policy clauses)

def operations : Operations := fun actual operation =>
  if actual = effect ∧ operation = 0 then some (.unit, .unit) else none
def contract : Contract := Contract.refine ClosingBudgetGap.contract .unit .unit
def contracts : Contracts := fun owner => if owner = 19 then some contract else none

theorem operations_erased : operations.erase = SourceCallableExamples.operations := by
  funext actual operation
  simp [Operations.erase, operations, SourceCallableExamples.operations]
  split <;> rfl

theorem contracts_erased : contracts.erase = ClosingBudgetGap.contracts := by
  funext owner
  simp [Contracts.erase, contracts, ClosingBudgetGap.contracts]
  split <;> rfl

private theorem resume_offer {environment : Environment} (allowed : List Instance) (held : Bool) (advertised : Footprint) :
    Offer operations policy contracts [] environment allowed 1 9 .unit .unit .unit allowed []
      (.resume 9 .unit) held false (some advertised) (some SourceDependencyCapture.Examples.resumeFamily) := by
  apply Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner offered fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner offered) owner = some offered := by simp [Contracts.insert]
  have operand : Expression operations policy (contracts.insert owner offered) [] allowed (.ticket 9 owner)
      (environment.extend 1 .unit) .unit offered.input [] (.request [] []) .pure := inputSame.symm ▸ .unit
  have resumed := Expression.resume (binder := 9) known rfl rfl operand
    (resumeSame.symm ▸ List.Subset.refl allowed)
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
  exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows

private theorem shadow_frame :
    SourceDependencyFrames.Frame operations policy contracts ClosingBudgetGap.tables ClosingBudget.families [] (.handler ClosingBudgetGap.shadow)
      .unit .unit [] (.request [] [])
      (.handler effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) (ClosingBudget.families ClosingBudgetGap.shadow)) [effect] [] := by
  have typed := ClosingBudgetGap.shadow_typed
  rw [← operations_erased, ← contracts_erased] at typed
  cases typed with
  | handler scope clausePorts coverage unique =>
    exact .handler ⟨.none, .none⟩ rfl
      (.cons (CoherentSourceTypes.port_lookup (SourceDependencyAnnotations.operation_erase
        (show operations effect 0 = some (.unit, .unit) by simp [operations])))
        (.resume .unit (List.Subset.refl []) (by simp [ScopedPorts.InWorld, Value.erase,
          CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])) .nil) coverage unique
      (.cons (by simp [operations, ClosingBudgetGap.shadow]) (resume_offer [] false []) (resume_offer [] true []) .nil)
      (.cons (.resume rfl .unit) .nil) (.cons (by decide) .nil)

theorem callback_source :
    ValueSummary operations policy contracts [] Environment.empty [] ClosingBudgetGap.callback
      (.function .unit .unit [effect] ClosingBudgetGap.latent ClosingBudget.callback) := by
  apply Expression.lambda
  · exact .perform (by simp [operations]) List.mem_cons_self .unit
      (by simp [ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  · exact .emitAfter (layers := []) (.request (layers := []))
  · simp [ScopedPorts.InWorld, CoherentSourceTypes.Value.port, Value.erase,
      ScopedPorts.Port.resources, effect, Instance.resources]
  · intro request member
    cases List.mem_singleton.mp member
    exact List.mem_cons_self

/-- The actual nested capture admits the richer source annotation at the same
owner demand, recursive requirement tree and record store as the old fixture. -/
theorem captured_source :
    Segment operations policy contracts ClosingBudgetGap.tables ClosingBudget.families ClosingBudget.actions []
      ClosingBudgetGap.capture .unit .unit [19] ClosingBudgetGap.requirements ClosingBudgetGap.records ClosingBudget.captured [effect] [effect] := by
  have known : contracts 19 = some contract := rfl
  have callbackPorts := CoherentSourceTypes.port_typing ClosingBudgetGap.callback_source .none
  rw [← operations_erased] at callbackPorts
  have saved : Segment operations policy contracts ClosingBudgetGap.tables ClosingBudget.families ClosingBudget.actions []
      ClosingBudgetGap.saved .unit .unit [] ClosingBudgetGap.savedRequirements [] ClosingBudget.saved [] [effect] :=
    .push (.armed ⟨.none, .none⟩ callback_source rfl
      (.armed ⟨.none, .none⟩ callbackPorts (List.Subset.refl _)))
      (.nil (List.Subset.refl _)) (List.nil_subset _)
  have live : Segment operations policy contracts ClosingBudgetGap.tables ClosingBudget.families ClosingBudget.actions []
      ClosingBudgetGap.boundary .unit .unit [] ClosingBudgetGap.boundaryRequirements ClosingBudgetGap.records
      (.live 19 ClosingBudget.saved .nil) [] [effect] :=
    .live known rfl rfl rfl ⟨.none, .none⟩ rfl saved (fun _ => List.Subset.refl _)
      (.nil (List.Subset.refl _)) (fun _ => List.Subset.refl _) (by intro impossible; cases impossible) (List.nil_subset _)
  have interpreted : Segment operations policy contracts ClosingBudgetGap.tables ClosingBudget.families ClosingBudget.actions []
      ClosingBudgetGap.receiver .unit .unit [] ClosingBudgetGap.receiverRequirements ClosingBudgetGap.records
      (.handler effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) (ClosingBudget.families ClosingBudgetGap.shadow) (.live 19 ClosingBudget.saved .nil)) [effect] [effect] :=
    .push shadow_frame live (List.Subset.refl _)
  have body : Expression operations policy contracts [] [effect] ClosingBudgetGap.binding.scope
      (Environment.empty.extend 99 .unit) (.resume 0 .unit) .unit [19] ClosingBudgetGap.resumeRequirements
      (.sequence .pure (.invoke ⟨19, .resume⟩)) :=
    .resume known rfl rfl .unit (List.Subset.refl _)
      (by simp [contract, Contract.refine, ClosingBudgetGap.contract, Value.erase, ScopedPorts.InWorld,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  exact .push (.plain (.bind body) (.bound (CoherentSourceTypes.Owners.ports_lookup (contract_erase_known known))) rfl rfl)
    interpreted (List.Subset.refl _)

/-- The receiving interpretation has its own enriched declaration, including
the existing conservative nonempty advertised row. -/
theorem outside_source :
    Segment operations policy contracts ClosingBudgetGap.tables ClosingBudget.families
      ClosingBudget.actions [] ClosingBudgetGap.fixed .unit .unit []
      (.sequence (ClosingBudgetGap.empty.prepend []) ClosingBudgetGap.empty) []
      ClosingBudget.outside [effect] [effect] := by
  have typed := ClosingBudgetGap.outer_typed
  rw [← operations_erased, ← contracts_erased] at typed
  cases typed with
  | handler scope clausePorts coverage unique =>
    have frame : SourceDependencyFrames.Frame operations policy contracts ClosingBudgetGap.tables
        ClosingBudget.families [] (.handler ClosingBudgetGap.outer)
        .unit .unit [] (.request [] [])
        (.handler effect (ClosingBudgetGap.tables ClosingBudgetGap.outer)
          (ClosingBudget.families ClosingBudgetGap.outer)) [effect, effect] [effect] :=
      .handler ⟨.none, .none⟩ rfl
        (.cons (CoherentSourceTypes.port_lookup (SourceDependencyAnnotations.operation_erase
          (show operations effect 0 = some (.unit, .unit) by simp [operations])))
          (.resume .unit (List.Subset.refl _) (by simp [ScopedPorts.InWorld, Value.erase,
            CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])) .nil) coverage unique
        (.cons (by simp [operations, ClosingBudgetGap.outer])
          (resume_offer [effect] false ClosingBudgetGap.forwarded)
          (resume_offer [effect] true ClosingBudgetGap.forwarded) .nil)
        (.cons (.resume rfl .unit) .nil) (.cons (by decide) .nil)
    exact .push frame (.nil (List.Subset.refl _)) (List.subset_cons_self _ _)

theorem closing_source :
    SourceDependencySchemes.Closing.Template operations policy contracts ClosingBudgetGap.tables [] .none
      ClosingBudgetGap.plan ClosingBudgetGap.forwarded ClosingBudgetGap.closingRequirements
      ClosingBudget.captured.forClosing :=
  .invoke (action := ClosingBudgetGap.action) (latent := ClosingBudgetGap.latent)
    callback_source (.retire (show contracts 19 = some contract from rfl) .nil)

/-- Even the exact enriched source and closing template can have an empty
normal row and a nonempty closing row. The contextual checks use an outward
effect interface; this does not assert reachability from a closed initial Run. -/
theorem budget_gap :
    RecursiveRequirements.Checked ClosingBudgetGap.records
      (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (OwnerPhaseTransitions.available (ownedTickets ClosingBudgetGap.capture)) ClosingBudgetGap.requirements [] ∧
    RecursiveRequirements.Checked ClosingBudgetGap.records
      (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (OwnerPhaseTransitions.available (ownedTickets ClosingBudgetGap.capture))
      ClosingBudgetGap.closingRequirements ClosingBudgetGap.forwarded ∧
    SourceDependencySchemes.Retained [effect] ClosingBudget.actions
      (OwnerPhaseTransitions.available [19]) [] ClosingBudget.captured
      ClosingBudget.outside ∧
    SourceDependencySchemes.Retained [effect] ClosingBudget.actions
      (OwnerPhaseTransitions.available [19]) [] ClosingBudget.captured.forClosing
      (.running ClosingBudget.outside) ∧
    ¬ EffectBounds.Covers [] ClosingBudgetGap.forwarded := by
  exact ⟨by simpa using (ClosingBudgetGap.normal_checked (disposals := [])),
    by simpa using (ClosingBudgetGap.closing_checked (disposals := [])),
    ClosingBudget.retained_checked,
    ClosingBudget.scheduled_checked, ClosingBudgetGap.closing_exceeds_normal⟩

/-- The same fixture is rejected by the empty outward closing guard used in
the present closed Run. It cannot justify a closed-program impossibility claim. -/
theorem closed_guard_rejects :
    SourceDependencyCapture.checkClosing [] ClosingBudget.captured.shape [] [] = false := by
  decide

namespace LatentInterface

def table : List (Nat × ClauseContract) := [(0, ⟨false, some ClosingBudgetGap.latent, some ClosingBudgetGap.latent⟩)]
def requirements : RecursiveRequirements.Requirements [] :=
  (RecursiveRequirements.Requirements.emitAfter (.request [] []) [] ClosingBudgetGap.latent).prepend
    [.ordinary (.handler effect 0 table)]
def dependencies : Dependencies :=
  .handler effect table SourceDependencyCapture.Examples.resumeDependencies (.sequence .pure (.request effect 0))

/-- A resume-only handler can advertise a conservative nonempty row even
though its ordinary effect interface is empty. -/
theorem body_source (environment : Environment) (allowed : List Instance) :
    Expression operations policy contracts [] allowed .none environment SourceCallableExamples.body
      .unit [] requirements dependencies := by
  have coverage : ScopedPorts.Covers operations.erase.ports effect clauses := by
    cases shadow_frame with
    | handler scope annotation typed coverage unique declarations capabilities modes => exact coverage
  exact .handler (.perform (by simp [operations]) List.mem_cons_self .unit
      (by simp [ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
    (.cons (CoherentSourceTypes.port_lookup (operation_erase
      (show operations effect 0 = some (.unit, .unit) by simp [operations])))
      (.resume .unit (List.Subset.refl []) (by simp [ScopedPorts.InWorld, Value.erase,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])) .nil)
    (.cons (.resume rfl .unit) .nil) coverage (by decide) (List.nil_subset _) table
    (.cons (by decide) .nil)
    (.cons (by simp [operations]) (resume_offer [] false ClosingBudgetGap.latent)
      (resume_offer [] true ClosingBudgetGap.latent) .nil)

theorem body_outward : RecursiveOutward.Outward requirements (some ClosingBudgetGap.latent) := by
  have inside : RecursiveOutward.Outward
      (RecursiveRequirements.Requirements.emitAfter (.request [] []) [] ClosingBudgetGap.latent)
      (some ClosingBudgetGap.latent) := .emitAfter (layers := []) (.request (layers := []))
  have current := RecursiveOutward.prepend inside [.handler effect 0 table]
  have exported : ProtectionResiduals.residualize [.handler effect 0 table] ClosingBudgetGap.latent =
      some ClosingBudgetGap.latent := by decide
  simpa only [Option.bind_some, exported, requirements, List.map_cons, List.map_nil] using current

theorem inconsistent_function_rejected :
    ¬ ValueSummary operations policy contracts [] Environment.empty [] SourceCallableExamples.function
      (.function .unit .unit [] ClosingBudgetGap.latent dependencies) := by
  intro source
  exact List.not_mem_nil (lambda_latent_bound source ⟨effect, 0, false⟩ List.mem_cons_self)

/-- The same body remains accepted when its effect interface includes the
conservatively advertised effect. -/
theorem consistent_function_source :
    ValueSummary operations policy contracts [] Environment.empty [] SourceCallableExamples.function
      (.function .unit .unit [effect] ClosingBudgetGap.latent dependencies) :=
  .lambda (body_source _ [effect]) body_outward
    (by simp [ScopedPorts.InWorld, CoherentSourceTypes.Value.port, Value.erase, ScopedPorts.Port.resources,
      effect, Instance.resources])
    (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self)

end LatentInterface

end Ash.OneShot.SourceDependencyBudgetGap

#print axioms Ash.OneShot.SourceDependencyBudgetGap.operations_erased
#print axioms Ash.OneShot.SourceDependencyBudgetGap.contracts_erased
#print axioms Ash.OneShot.SourceDependencyBudgetGap.callback_source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.captured_source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.outside_source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.closing_source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.budget_gap
#print axioms Ash.OneShot.SourceDependencyBudgetGap.closed_guard_rejects
#print axioms Ash.OneShot.SourceDependencyBudgetGap.LatentInterface.body_source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.LatentInterface.body_outward
#print axioms Ash.OneShot.SourceDependencyBudgetGap.LatentInterface.inconsistent_function_rejected
#print axioms Ash.OneShot.SourceDependencyBudgetGap.LatentInterface.consistent_function_source

namespace Ash.OneShot.SourceDependencyBudgetGap.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available)
open SourceCallableExamples (effect policy)
open SourceDependencySchemes.Examples

def requirements : Requirements [19] :=
  .sequence (ClosingBudgetGap.savedRequirements.prepend
    (OwnerPhases.ofStack ClosingBudgetGap.tables (.push (.retiring 19) .nil)))
    (.sequence (.retire 19) ClosingBudgetGap.empty)

/-- Lexical unwinding drops the plain frame and inner handler before opening
    the dormant continuation. Its callback sees the surviving outer handler. -/
theorem source : UnwindSource operations policy contracts ClosingBudgetGap.tables ClosingBudget.families []
    ClosingBudgetGap.capture [19] requirements ClosingBudget.captured := by
  exact .plain (.handler shadow_frame (.live (.cleanup callback_source .nil) .nil))

theorem checked : Checked ClosingBudgetGap.records
    (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
    (available (ownedTickets ClosingBudgetGap.capture)) requirements ClosingBudgetGap.forwarded := by
  apply RecursiveRequirements.evaluate_sound
  simp only [requirements, ClosingBudgetGap.savedRequirements, ClosingBudgetGap.empty,
    Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
  decide

/-- The effect-budget gap also occurs for the lexical cleanup source. This
    remains a finite typed stack fixture, not a closed initial execution. -/
theorem budget_gap :
    ModeSource operations policy contracts ClosingBudgetGap.tables ClosingBudget.families ClosingBudget.actions []
      ClosingBudgetGap.capture (.value .unit) (.value .unit) [19] ClosingBudgetGap.requirements ClosingBudget.captured ∧
    Checked ClosingBudgetGap.records (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) ClosingBudgetGap.requirements [] ∧
    Checked ClosingBudgetGap.records (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) requirements ClosingBudgetGap.forwarded ∧
    ¬ EffectBounds.Covers [] ClosingBudgetGap.forwarded :=
  ⟨captured_source.mode_source, by simpa using (ClosingBudgetGap.normal_checked (disposals := [])),
    checked, ClosingBudgetGap.closing_exceeds_normal⟩

/-- One finite alternative check admits both return modes for this nonempty
    caller. It reuses the normal and cleanup checks with their joint budget. -/
theorem return_effects : ∀ mode,
    ReturnEffects operations policy contracts ClosingBudgetGap.tables ClosingBudget.families []
      ClosingBudgetGap.capture [19] ClosingBudget.captured
      (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) ClosingBudgetGap.forwarded mode := by
  have normal := ClosingBudgetGap.normal_checked (disposals := [])
  have alternatives : Checked ClosingBudgetGap.records
      (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture))
      (.choice ClosingBudgetGap.requirements requirements (.refl _)) ClosingBudgetGap.forwarded := by
    simpa using (Checked.choice normal checked (same := List.Perm.refl [19]))
  exact (source.choice_return_effects (.refl _) alternatives (List.Subset.refl _)).2

/-- Rechecking the actual lexical cleanup with the normal path's empty row
    fails. This says nothing about a differently annotated source program. -/
theorem empty_budget_rejected :
    ¬ Checked ClosingBudgetGap.records (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) requirements [] := by
  intro empty
  have same := (RecursiveRequirements.checked_complete empty).symm.trans
    (RecursiveRequirements.checked_complete checked)
  cases same

end Ash.OneShot.SourceDependencyBudgetGap.Lexical
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.source
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.checked
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.budget_gap
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.return_effects
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.empty_budget_rejected

namespace Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open CoherentSourceTypes
open RecursiveRequirements (Requirements Checked Store)
open ClauseRowAdmission
open SourceCallableExamples (effect policy)

def enclosing : Owners.Contract := ClosingBudgetGap.enclosingContract
def registry : Owners.Contracts := ClosingBudgetGap.contracts.insert 20 enclosing
def root : Stack := .live 20 .unit .unit ClosingBudgetGap.capture .none .nil
def resumes : Store := (⟨20, .resume⟩, ⟨[19], ClosingBudgetGap.requirements⟩) :: ClosingBudgetGap.records
def disposals : Store := [(⟨20, .dispose⟩, ⟨[19], Lexical.requirements⟩),
  (⟨19, .dispose⟩, ⟨[], ClosingBudgetGap.savedRequirements⟩)]
def store : Store := resumes ++ disposals

private theorem extension : ClosingBudgetGap.contracts.Extends registry :=
  Owners.insert_extends _ rfl

private theorem saved_source : StoreSegment SourceCallableExamples.operations policy registry ClosingBudgetGap.tables []
    ClosingBudgetGap.capture .unit .unit [19] ClosingBudgetGap.requirements ClosingBudgetGap.records :=
  .of_legacy (DeclaredSourceFrames.segment_extension ClosingBudgetGap.captured_source extension).erase

private theorem root_source : StoreSegment SourceCallableExamples.operations policy registry ClosingBudgetGap.tables []
    root .unit .unit [] (.sequence (.spent 20) (.request [] [])) resumes := by
  exact .live (show registry 20 = some enclosing from rfl) rfl rfl ⟨.none, .none⟩ rfl saved_source .nil

private theorem callback_source : SourceTemplates.ValueSummary SourceCallableExamples.operations policy registry []
    Environment.empty [] ClosingBudgetGap.callback (.function .unit .unit [effect] ClosingBudgetGap.latent) :=
  DeclaredSourceValues.erase (DeclaredSourceValues.extension
    (DeclaredSourceValues.from_legacy ClosingBudgetGap.callback_source) extension)

private theorem saved_closing : StoreClosingTemplate SourceCallableExamples.operations policy registry ClosingBudgetGap.tables []
    ClosingBudgetGap.saved [] ClosingBudgetGap.savedRequirements :=
  .cleanup callback_source .nil

private theorem capture_closing : StoreClosingTemplate SourceCallableExamples.operations policy registry ClosingBudgetGap.tables []
    ClosingBudgetGap.capture [19] Lexical.requirements :=
  .plain (.handler (.live saved_closing .nil))

private theorem closing_records : StoreClosingRecords SourceCallableExamples.operations policy registry ClosingBudgetGap.tables [] root disposals :=
  .close rfl capture_closing
    (.push (.push (.close rfl saved_closing (.push .nil) .nil))) .nil

/-- The source-relative quantifier includes this exact lexical record store. -/
theorem authenticated : SourceStore SourceCallableExamples.operations 20 enclosing store := by
  exact ⟨policy, registry, ClosingBudgetGap.tables, [], root, _, _, _, _, resumes, disposals,
    .legacy root_source, fun _ _ member => root_source.records_certified member,
    closing_records, rfl, .refl _⟩

/-- The current enriched source-body constructor accepts the normal-only
    literal resume under this concrete contract. -/
theorem body_admitted : SourceDependencyAnnotations.Body
    SourceDependencyBudgetGap.operations policy
    (SourceDependencyBudgetGap.contracts.insert 20
      (SourceDependencyAnnotations.Contract.refine enclosing .unit .unit))
    [] [effect] (.ticket 9 20) SourceDependencyAnnotations.Environment.empty (.resume 9 .unit) .unit
    ⟨20, enclosing, false, []⟩ (.sequence .pure (.invoke ⟨20, .resume⟩)) := by
  apply SourceDependencyAnnotations.Body.typed
    (SourceDependencyAnnotations.Expression.resume
      (show (SourceDependencyBudgetGap.contracts.insert 20
        (SourceDependencyAnnotations.Contract.refine enclosing .unit .unit)) 20 =
        some (SourceDependencyAnnotations.Contract.refine enclosing .unit .unit) from rfl)
      rfl rfl .unit (List.Subset.refl _) (by
        simp [SourceDependencyAnnotations.Contract.refine, enclosing, ClosingBudgetGap.enclosingContract,
          SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.InWorld,
          ScopedPorts.Port.resources]))
  exact resume_rows

private theorem resume_checked : Checked store
    (.live 20 false :: OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
    (OwnerPhaseTransitions.available [20, 19]) (.invoke ⟨20, .resume⟩ [19] []) [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [store, resumes, disposals, ClosingBudgetGap.records, ClosingBudgetGap.requirements,
    ClosingBudgetGap.resumeRequirements, ClosingBudgetGap.receiverRequirements,
    ClosingBudgetGap.boundaryRequirements, ClosingBudgetGap.empty, ClosingBudgetGap.savedRequirements,
    Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
    RecursiveRequirements.lookup, List.cons_append, List.nil_append, List.length_cons, List.length_nil] <;> decide

private theorem interface : Interface 20 enclosing false store
    (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
    (OwnerPhaseTransitions.available [20, 19]) [] :=
  .of_resume resume_checked rfl (by decide)

/-- Universal source-relative row admission accepts the normal resume, while
    the actual lexical cleanup of its saved body exceeds that empty budget.
    This is not a reachability theorem from a closed source program. -/
theorem admitted_normal_cleanup_gap :
    SourceStore SourceCallableExamples.operations 20 enclosing store ∧
    Checked store (.live 20 false :: OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (OwnerPhaseTransitions.available [20, 19])
      (.sequence (.request [] []) (.invoke ⟨20, .resume⟩ [19] [])) [] ∧
    Checked store (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (OwnerPhaseTransitions.available [19]) Lexical.requirements ClosingBudgetGap.forwarded ∧
    ¬ EffectBounds.Covers [] ClosingBudgetGap.forwarded := by
  have admitted := Rows.instantiate
    (resume_rows (templates := SourceStore SourceCallableExamples.operations 20 enclosing)
      (advertised := [])) interface
    (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]) authenticated
  obtain ⟨row, checked, bounded⟩ := admitted
  have empty : row = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro request member
    exact List.not_mem_nil (bounded member))
  subst row
  refine ⟨authenticated, checked, ?_, ClosingBudgetGap.closing_exceeds_normal⟩
  apply RecursiveRequirements.evaluate_sound
  simp only [Lexical.requirements, ClosingBudgetGap.savedRequirements, ClosingBudgetGap.empty,
    Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
  decide

end Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.authenticated
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.admitted_normal_cleanup_gap
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.body_admitted

namespace Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.CaptureEvidence
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available)
open SourceDependencyFrames (ClosingEffects)

/-- The existing lexical fixture rejects an empty cleanup budget independently
of whether source clause admission retains generated disposal rows. -/
theorem lexical_cleanup_requires_more_than_normal :
    ¬ ClosingEffects [] (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) SourceDependencyBudgetGap.Lexical.requirements := by
  intro effects
  obtain ⟨row, evaluated, bounded⟩ := SourceDependencyBudgetGap.Lexical.source.template.checked_effects
    (entries := ClosingBudgetGap.records) effects (by decide)
    (by intro owner member; exact if_pos member)
  have empty : row = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro request member
    exact List.not_mem_nil (bounded member))
  subst row
  exact SourceDependencyBudgetGap.Lexical.empty_budget_rejected (RecursiveRequirements.evaluate_sound evaluated)

/-- Both existing hereditary row certificates accept a literal-resume body,
including a disposing declaration. They do not construct its invocation
interface and therefore cannot establish the capture's cleanup budget. -/
theorem rows_and_protected_rows_do_not_supply_capture_cleanup (disposes : Bool) :
    ClauseRowAdmission.Rows ⟨20, ClosingBudgetGap.enclosingContract, disposes, []⟩
      (.sequence (.request [] []) (.invoke ⟨20, .resume⟩ [19] []))
      (ClauseRowAdmission.SourceStore SourceCallableExamples.operations 20 ClosingBudgetGap.enclosingContract) ∧
    ClauseRowAdmission.ProtectedRows ⟨20, ClosingBudgetGap.enclosingContract, disposes, []⟩
      (.sequence (.request [] []) (.invoke ⟨20, .resume⟩ [19] []))
      (ClauseRowAdmission.SourceStore SourceCallableExamples.operations 20 ClosingBudgetGap.enclosingContract) ∧
    ClauseRowAdmission.SourceStore SourceCallableExamples.operations 20 ClosingBudgetGap.enclosingContract
      SourceDependencyBudgetGap.Lexical.Admission.store ∧
    Checked ClosingBudgetGap.records (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) ClosingBudgetGap.requirements [] ∧
    ¬ ClosingEffects [] (OwnerPhases.ofStack ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      (available (ownedTickets ClosingBudgetGap.capture)) SourceDependencyBudgetGap.Lexical.requirements := by
  exact ⟨ClauseRowAdmission.resume_rows, ClauseRowAdmission.protected_resume_rows,
    SourceDependencyBudgetGap.Lexical.Admission.authenticated,
    SourceDependencyBudgetGap.Lexical.budget_gap.2.1, lexical_cleanup_requires_more_than_normal⟩
end Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.CaptureEvidence
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.CaptureEvidence.lexical_cleanup_requires_more_than_normal
#print axioms Ash.OneShot.SourceDependencyBudgetGap.Lexical.Admission.CaptureEvidence.rows_and_protected_rows_do_not_supply_capture_cleanup
