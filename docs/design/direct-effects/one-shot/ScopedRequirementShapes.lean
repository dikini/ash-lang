import OwnerOfferContexts

/-! Source grouping for the existing recursive requirements. The index is the
old requirement, so ordinary effect and phase checking uses its established
evaluator. Scope nodes retain information lost by distributed `prepend`.
Sites are analysis obligations, not an execution trace or a source-admission
certificate. In particular, invocation sites still require template expansion.
-/
namespace Ash.OneShot.ScopedRequirementShapes
open RecursiveRequirements (Requirements Key)
open ProtectionContracts (Footprint)
open ScopedExpressions (Code)

inductive Shape : {owners : List Nat} → Requirements owners → Type where
  | request (raw : Footprint) : Shape (.request [] raw)
  | retire (owner : Nat) : Shape (.retire owner)
  | spent (owner : Nat) : Shape (.spent owner)
  | invoke (key : Key) (demand : List Nat) : Shape (.invoke key demand [])
  | sequence {first : Requirements a} {second : Requirements b}
      (left : Shape first) (right : Shape second) : Shape (.sequence first second)
  | emitAfter {body : Requirements owners} (shape : Shape body) (raw : Footprint) :
      Shape (.emitAfter body [] raw)
  | choice {first : Requirements a} {second : Requirements b}
      (left : Shape first) (right : Shape second) (same : a.Perm b) :
      Shape (.choice first second same)
  | scope {body : Requirements owners} (layers : ProtectionContracts.Context)
      (shape : Shape body) : Shape (body.prepend (layers.map OwnerPhases.Entry.ordinary))
  | hide {opened closed : Requirements owners} (identity : Nat) (shape : Shape opened)
      (discharged : ResourceRequirements.Hides identity opened closed) : Shape closed

/-- Newly installed source interpretations own no existing continuation.
The actual caller summary is supplied separately and retains dormant owners. -/
def interpretations (layers : ProtectionContracts.Context) : OwnerOfferContexts.Context :=
  layers.map fun layer => ⟨layer, ⟨[], []⟩⟩

/-- Pending demand is kept at its sequencing boundary. It is not pushed
through every interpretation inside the initializer. This is a demand summary;
the runtime pending-list connection requires the existing usage interface. -/
def pending (owners : List Nat) (receiving : OwnerOfferContexts.Context) : OwnerOfferContexts.Context :=
  ⟨.barrier false, ⟨[], owners⟩⟩ :: receiving

inductive Site where
  | request : ProtectionContracts.Demand → OwnerOfferContexts.Context → Site
  | invoke : Key → List Nat → OwnerOfferContexts.Context → Site
  deriving DecidableEq, Repr

def sites : {owners : List Nat} → {requirements : Requirements owners} →
    Shape requirements → OwnerOfferContexts.Context → List Site
  | _, _, .request raw, receiving => raw.map fun request => .request request receiving
  | _, _, .retire _, _ | _, _, .spent _, _ => []
  | _, _, .invoke key demand, receiving => [.invoke key demand receiving]
  | _, _, @Shape.sequence _ b _ _ left right, receiving =>
      sites left (pending b receiving) ++ sites right receiving
  | _, _, .emitAfter body raw, receiving =>
      sites body receiving ++ raw.map fun request => .request request receiving
  | _, _, .choice left right _, receiving => sites left receiving ++ sites right receiving
  | _, _, .scope layers body, receiving => sites body (interpretations layers ++ receiving)
  | _, _, .hide identity body _, receiving => sites body (interpretations [.builtin identity] ++ receiving)

/-- Structural source provenance for a grouping. Summary leaves keep their
existing typing evidence. Lambda bodies and latent calls still need the
separate callable refinement; this relation does not certify their captures. -/
inductive Describes : Code → {owners : List Nat} → {requirements : Requirements owners} →
    Shape requirements → Prop where
  | stable (source : CoherentSourceTypes.Summary operations world environment allowed code value raw) :
      Describes code (.request raw)
  | callable (source : CallableSources.Summary operations bodyJudgment world environment allowed code value raw) :
      Describes code (.request raw)
  | lambda : Describes (.lambda parameter code) (.request [])
  | purePair {first second : Shape (.request [] [])}
      (left : Describes a first) (right : Describes b second) :
      Describes (.pair a b) (.request [])
  | pair (left : Describes a first) (right : Describes b second) :
      Describes (.pair a b) (.sequence first second)
  | app (left : Describes f first) (right : Describes a second) :
      Describes (.app f a) (.emitAfter (.sequence first second) raw)
  | bind (left : Describes a first) (right : Describes b second) :
      Describes (.bind parameter a b) (.sequence first second)
  | branch (condition : Describes test first) (yes : Describes a second) (no : Describes b third) :
      Describes (.branch test a b) (.sequence first (.choice second third same))
  | perform (operand : Describes code shape) :
      Describes (.perform (Instantiation.freezeEffect effect) operation code)
        (.emitAfter shape [⟨effect, operation, false⟩])
  | handler (body : Describes code shape) :
      Describes (.handle (Instantiation.freezeEffect effect) code clauses)
        (.scope [.handler effect 0 table] shape)
  | resume (operand : Describes code shape) :
      Describes (.resume binder code) (.sequence shape (.invoke ⟨owner, .resume⟩ demand))
  | discard : Describes (.discard binder) (.invoke ⟨owner, .dispose⟩ demand)
  | cleanup (callback : Describes action first) (body : Describes code second) :
      Describes (.cleanup action code) (.emitAfter (.sequence first second) raw)
  | resource (initializer : Describes initial shape) :
      Describes (.resource binder initial code) (.emitAfter shape raw)
  | scopedResource {opened closed : Requirements owners} {second : Shape opened}
      (initializer : Describes initial first)
      (body : Describes (code.instantiate (Instantiation.Environment.empty.bind binder identity)) second)
      (hidden : ResourceRequirements.Hides identity opened closed) :
      Describes (.resource binder initial code) (.sequence first (.hide identity (opened := opened) second hidden))

def startsHandler : Code → Bool
  | .handle _ _ _ => true
  | _ => false

def startsScope : {owners : List Nat} → {requirements : Requirements owners} → Shape requirements → Bool
  | _, _, .scope _ _ => true
  | _, _, _ => false

theorem handler_grouping (described : Describes code shape) : startsHandler code = startsScope shape := by
  cases described with
  | stable source => cases source <;> rfl
  | callable source => cases source <;> rfl
  | _ => rfl

/-- Reuse the old evaluator directly; there is no second effect semantics. -/
def evaluate {requirements : Requirements owners} (_shape : Shape requirements)
    (store : RecursiveRequirements.Store) (receiving : OwnerPhases.Context)
    (before : OwnerPhaseTransitions.Phases) : Option Footprint :=
  RecursiveRequirements.evaluate store receiving before requirements

theorem scope_evaluation {requirements : Requirements owners} (shape : Shape requirements) :
    evaluate (.scope layers shape) store receiving before =
      evaluate shape store (layers.map OwnerPhases.Entry.ordinary ++ receiving) before :=
  RecursiveRequirements.evaluate_prepend requirements

theorem checked_phase_trace {requirements : Requirements owners} (shape : Shape requirements)
    (checked : evaluate shape store receiving before = some row) :
    OwnerPhaseTransitions.Trace before owners (OwnerPhaseTransitions.spendAll before owners) :=
  RecursiveRequirements.checked_trace (RecursiveRequirements.evaluate_sound checked)

/-- Retain grouping at the source constructors instead of reconstructing it
from distributed contexts. Existing summary leaves remain summary leaves;
this does not recover hidden callable bodies from their latent footprints. -/
theorem source_shape
    (source : SourceTemplates.Expression operations policy contracts world allowed scope environment
      code output demand requirements) : ∃ shape : Shape requirements, Describes code shape := by
  induction source using SourceTemplates.Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable summary => exact ⟨_, .stable summary⟩
  | callable summary ih => exact ⟨_, .callable summary⟩
  | lambda body outward formed ih => exact ⟨_, .lambda⟩
  | purePair left right ihLeft ihRight =>
      obtain ⟨first, a⟩ := ihLeft
      obtain ⟨second, b⟩ := ihRight
      exact ⟨_, .purePair a b⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨first, a⟩ := ihLeft
      obtain ⟨second, b⟩ := ihRight
      exact ⟨_, .pair a b⟩
  | bind left right ihLeft ihRight =>
      obtain ⟨first, a⟩ := ihLeft
      obtain ⟨second, b⟩ := ihRight
      exact ⟨_, .bind a b⟩
  | app function argument admitted ihFunction ihArgument =>
      obtain ⟨first, a⟩ := ihFunction
      obtain ⟨second, b⟩ := ihArgument
      exact ⟨_, .app a b⟩
  | cleanup function argument admitted ihFunction ihArgument =>
      obtain ⟨first, a⟩ := ihFunction
      obtain ⟨second, b⟩ := ihArgument
      exact ⟨_, .cleanup a b⟩
  | branch condition yes no same ihCondition ihYes ihNo =>
      obtain ⟨first, a⟩ := ihCondition
      obtain ⟨second, b⟩ := ihYes
      obtain ⟨third, c⟩ := ihNo
      exact ⟨_, .branch (same := same) a b c⟩
  | perform known admitted operand formed ih =>
      obtain ⟨shape, describes⟩ := ih
      exact ⟨_, .perform describes⟩
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      obtain ⟨shape, describes⟩ := ih
      exact ⟨_, .handler describes⟩
  | resume known resolved permission operand admitted formed ih =>
      obtain ⟨shape, describes⟩ := ih
      exact ⟨_, .resume describes⟩
  | discard known resolved permission unprotected admitted => exact ⟨_, .discard⟩
  | resource initializer body formed effectsBound admitted outward ih ihBody =>
      obtain ⟨shape, describes⟩ := ih
      exact ⟨_, .resource describes⟩
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      obtain ⟨first, a⟩ := ihInit
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      obtain ⟨second, b⟩ := ihBody identity fresh
      exact ⟨_, .scopedResource a b (hidden identity fresh)⟩
  | _ => trivial

namespace Examples

def effect : Instance := .user 173 []
def raw : Footprint := [⟨effect, 0, false⟩]
def table : List (Nat × ProtectionContracts.ClauseContract) := [(0, ⟨true, some [], none⟩)]
def layers : ProtectionContracts.Context := [.handler effect 0 table]
def ask : Requirements [] := .emitAfter (.request [] []) [] raw
def resumeOwner : Requirements [9] := .sequence (.request [] []) (.invoke ⟨9, .resume⟩ [] [])
def askShape : Shape ask := .emitAfter (.request []) raw
def resumeShape : Shape resumeOwner := .sequence (.request []) (.invoke ⟨9, .resume⟩ [])

/-- Two separate scopes: bind (handle request H) (handle (resume k) H). -/
def separateRequirements : Requirements [9] :=
  .sequence (ask.prepend (layers.map OwnerPhases.Entry.ordinary))
    (resumeOwner.prepend (layers.map OwnerPhases.Entry.ordinary))
def separate : Shape separateRequirements :=
  .sequence (.scope layers askShape) (.scope layers resumeShape)

/-- One shared scope: handle (bind request (resume k)) H. -/
def sharedRequirements : Requirements [9] :=
  (Requirements.sequence ask resumeOwner).prepend (layers.map OwnerPhases.Entry.ordinary)
def shared : Shape sharedRequirements :=
  .scope layers (.sequence askShape resumeShape)

def clauses : ScopedExpressions.Clauses := .cons 0 1 2 (.discard 2) .nil
def requestCode : Code := .perform (Instantiation.freezeEffect effect) 0 .unit
def separateCode : Code := .bind 7 (.handle (Instantiation.freezeEffect effect) requestCode clauses)
  (.handle (Instantiation.freezeEffect effect) (.resume 3 .unit) clauses)
def sharedCode : Code := .handle (Instantiation.freezeEffect effect)
  (.bind 7 requestCode (.resume 3 .unit)) clauses

private theorem unit_description : Describes .unit (.request []) :=
  .stable (operations := fun _ _ => none) (world := [])
    (environment := CoherentSourceTypes.Environment.empty) (allowed := []) .unit

theorem separate_describes : Describes separateCode separate :=
  .bind (.handler (.perform unit_description)) (.handler (.resume unit_description))

theorem shared_describes : Describes sharedCode shared :=
  .handler (.bind (.perform unit_description) (.resume unit_description))

theorem swapped_grouping_rejected :
    ¬ Describes sharedCode separate ∧ ¬ Describes separateCode shared := by
  constructor <;> intro wrong
  · have impossible := handler_grouping wrong
    cases impossible
  · have impossible := handler_grouping wrong
    cases impossible

theorem same_flat_requirements : separateRequirements = sharedRequirements := rfl

def caller : OwnerOfferContexts.Context := [⟨.barrier false, ⟨[9], []⟩⟩]
def separateRequestContext : OwnerOfferContexts.Context := interpretations layers ++ pending [9] caller
def sharedRequestContext : OwnerOfferContexts.Context := pending [9] (interpretations layers ++ caller)

theorem separate_sites : sites separate caller =
    [.request ⟨effect, 0, false⟩ separateRequestContext,
      .invoke ⟨9, .resume⟩ [] (interpretations layers ++ caller)] := rfl

theorem shared_sites : sites shared caller =
    [.request ⟨effect, 0, false⟩ sharedRequestContext,
      .invoke ⟨9, .resume⟩ [] (interpretations layers ++ caller)] := rfl

theorem different_owner_checks :
    OwnerOfferContexts.checkOwner effect 0 separateRequestContext = true ∧
    OwnerOfferContexts.checkOwner effect 0 sharedRequestContext = false := by decide

def handler : ScopedExecution.HandlerData := ⟨0, effect, clauses, .ticket 3 9, .unit, rfl⟩
def ownerBoundary : ScopedExecution.Stack := .live 9 .unit .unit .nil .none .nil
def separateWaiting : ScopedExecution.PlainData :=
  ⟨.bind 7 (.handle (Instantiation.freezeEffect effect) (.resume 3 .unit) clauses),
    .ticket 3 9, .unit, .unit, [9], rfl⟩
def sharedWaiting : ScopedExecution.PlainData :=
  ⟨.bind 7 (.resume 3 .unit), .ticket 3 9, .unit, .unit, [9], rfl⟩
def separateStack : ScopedExecution.Stack :=
  .push (.handler handler) (.push (.plain separateWaiting) ownerBoundary)
def sharedStack : ScopedExecution.Stack :=
  .push (.plain sharedWaiting) (.push (.handler handler) ownerBoundary)
def separateCapture : ScopedExecution.Stack := .push (.handler handler) .nil
def sharedCapture : ScopedExecution.Stack := .push (.plain sharedWaiting) separateCapture

theorem runtime_contexts :
    OwnerOfferContexts.ofStack (fun _ => table) separateStack = separateRequestContext ∧
    OwnerOfferContexts.ofStack (fun _ => table) sharedStack = sharedRequestContext := ⟨rfl, rfl⟩

theorem separate_cut : ScopedExecution.HandlerCut effect separateStack separateCapture
    (.push (.plain separateWaiting) ownerBoundary) handler := .hit handler _ rfl

theorem shared_cut : ScopedExecution.HandlerCut effect sharedStack sharedCapture ownerBoundary handler :=
  .push _ _ _ _ _ (by decide) (.hit handler _ rfl)

/-- The different source-site decisions equal the checks on actual handler
cuts. Reuse the established summary/cut bridge rather than reprove ownership. -/
theorem actual_capture_checks :
    CaptureOwnerChecks.checkSelected table 0 separateCapture.erase = true ∧
    CaptureOwnerChecks.checkSelected table 0 sharedCapture.erase = false := by
  have first := OwnerOfferContexts.check_cut (tables := fun _ => table) (operation := 0) separate_cut
  have second := OwnerOfferContexts.check_cut (tables := fun _ => table) (operation := 0) shared_cut
  rw [runtime_contexts.1, different_owner_checks.1] at first
  rw [runtime_contexts.2, different_owner_checks.2] at second
  exact ⟨first.symm, second.symm⟩

theorem ordinary_check_accepts_both :
    evaluate separate [(⟨9, .resume⟩, ⟨[], .request [] []⟩)] [.live 9 false]
      (OwnerPhaseTransitions.available [9]) = some [] ∧
    evaluate shared [(⟨9, .resume⟩, ⟨[], .request [] []⟩)] [.live 9 false]
      (OwnerPhaseTransitions.available [9]) = some [] := by
  have checked : RecursiveRequirements.Checked
      [(⟨9, .resume⟩, ⟨[], .request [] []⟩)] [.live 9 false]
      (OwnerPhaseTransitions.available [9]) separateRequirements [] := by
    apply RecursiveRequirements.Checked.sequence
      (a := ask.prepend (layers.map OwnerPhases.Entry.ordinary))
      (b := resumeOwner.prepend (layers.map OwnerPhases.Entry.ordinary))
      (firstRow := []) (secondRow := [])
    · apply RecursiveRequirements.Checked.emitAfter
        (requirements := .request (layers.map OwnerPhases.Entry.ordinary) [])
        (bodyRow := []) (requestRow := [])
      · exact .request (by rfl)
      · decide
    · apply RecursiveRequirements.Checked.sequence
        (a := .request (layers.map OwnerPhases.Entry.ordinary) [])
        (b := .invoke ⟨9, .resume⟩ [] (layers.map OwnerPhases.Entry.ordinary))
        (firstRow := []) (secondRow := [])
      · exact .request (by rfl)
      · exact .invoke (by rfl) (by decide) (.ordinary .hit) (.request (by rfl))
  have evaluated := RecursiveRequirements.checked_complete checked
  exact ⟨evaluated, evaluated⟩

/-- Flattened requirements cannot recover this capture-sensitive decision.
This concerns the analysis index, not a claim of complete source admission. -/
theorem no_flat_owner_classifier :
    ¬ ∃ classify : Requirements [9] → Bool,
      classify separateRequirements = OwnerOfferContexts.checkOwner effect 0 separateRequestContext ∧
      classify sharedRequirements = OwnerOfferContexts.checkOwner effect 0 sharedRequestContext := by
  rintro ⟨classify, first, second⟩
  rw [same_flat_requirements, different_owner_checks.1] at first
  rw [different_owner_checks.2, first] at second
  cases second

end Examples
end Ash.OneShot.ScopedRequirementShapes

#print axioms Ash.OneShot.ScopedRequirementShapes.scope_evaluation
#print axioms Ash.OneShot.ScopedRequirementShapes.checked_phase_trace
#print axioms Ash.OneShot.ScopedRequirementShapes.source_shape
#print axioms Ash.OneShot.ScopedRequirementShapes.handler_grouping
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.separate_describes
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.shared_describes
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.swapped_grouping_rejected
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.same_flat_requirements
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.separate_sites
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.shared_sites
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.different_owner_checks
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.runtime_contexts
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.separate_cut
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.shared_cut
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.actual_capture_checks
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.ordinary_check_accepts_both
#print axioms Ash.OneShot.ScopedRequirementShapes.Examples.no_flat_owner_classifier
