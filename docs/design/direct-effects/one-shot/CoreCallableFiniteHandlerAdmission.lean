import CoreCallableFiniteHandlerSource
import CoreCallableInitialAdmission
import CoreCallableCompositionalAdmissionFacets
namespace Ash.OneShot.CoreCallableFiniteHandlerAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows choiceRows)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature clauseSignatures)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements LocalOwner)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def outerRoot : Template input answer binder bindings code → Requirements []
  | .resume _ => .sequence (.request [] []) (.sequence (.request [] []) (.request [] []))
  | .bind _ body => outerRoot body
  | .branch _ yes no => .choice (outerRoot yes) (outerRoot no) (.refl [])
  | .unsupported _ => .request [] []
def localRoot (owner : Nat) : Template input answer binder bindings code → Requirements [owner]
  | .resume _ => .sequence (.retire owner) (.sequence (.spent owner) (.request [] []))
  | .bind _ body => localRoot owner body
  | .branch _ yes no => .choice (localRoot owner yes) (localRoot owner no) (.refl [owner])
  | .unsupported _ => .retire owner

theorem retire_local (data : Template input answer binder bindings code) (supported : data.supported = true) :
    LocalOwner owner .available (localRoot owner data) (outerRoot data) .consumed := by
  induction data with
  | resume operand => exact .sequence .retireSelf (.sequence .spentSelf .empty)
  | bind operand body ih => exact ih supported
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .choice (ihY y) (ihN n)
  | unsupported reason => cases supported

def terminal {families : SourceDependencyAnnotations.ClauseDependencies}
    {signatures : SourcePlanSignatures.ClauseSignatures families} (effect : Instance) (table : List (Nat × ClauseContract)) (activation : Nat)
    (declarations : ClauseRows signatures) :
    Context (SourceDependencyChecks.Lexical.ReturnHints.handler (effect := effect) (table := table)
      (families := families) SourceDependencyChecks.Lexical.ReturnHints.nil) :=
  Context.handler (effect := effect) (table := table) activation declarations Context.nil

theorem clause_accounting (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) :
    Accounting.Run world installations (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand) (terminal effect table activation declarations) Context.nil)
      (localRoot owner data) := by
  induction data with
  | resume operand =>
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.resume (front := Context.nil) (captured := terminal effect table activation declarations) (tail := Context.nil)
    · exact .hit
    · exact .handler (.spent .nil)
  | bind operand body ih => exact .sequence (.pure (.plain (ih supported)))
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .sequence (.pure (.plain (.choice (ihY y) (ihN n) (.refl _))))
  | unsupported reason => cases supported

structure ClauseFacets {outward : List Instance} {actions : Syntax.UsageTickets} {budget : Footprint}
    {phases : OwnerPhaseTransitions.Phases} {world installations ambient : List Nat} (rows : Rows checking) (context : Context hints)
    (root : Requirements demand) : Prop where
  certificate : SourceAdmission.Code outward actions budget phases world installations rows context
  checked : InstallationSupport.CodeChecked ambient outward certificate
  accounting : Accounting.Run world installations rows context root

theorem clause_facets {rights : Syntax.OneShotRights} {outward : List Instance}
    {actions : Syntax.UsageTickets} {budget : Footprint} {phases : OwnerPhaseTransitions.Phases}
    {world installations ambient : List Nat} {owner : Nat} (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) (permission : rights.resume = true) :
    ClauseFacets (outward := outward) (actions := actions.insert owner rights)
      (phases := OwnerPhaseTransitions.introduce phases owner) (budget := budget) (ambient := ambient)
      (world := world) (installations := installations) (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand) (terminal effect table activation declarations) Context.nil)
      (localRoot owner data) := by
  induction data with
  | resume operand =>
    let restored : SourceAdmission.Pending outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner) world installations
        ((terminal effect table activation declarations).append (.spent (owner := owner) Context.nil)) Context.nil
        .ordinary .ordinary := .handler (.spent .nil)
    let resume : SourceAdmission.Code outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.introduce phases owner) world installations (Rows.invoke (key := ⟨owner,.resume⟩))
        (Context.live (owner := owner) (resumeDemand := resumeDemand) (terminal effect table activation declarations) Context.nil) :=
      .resume (front := Context.nil) .hit (by simp [Syntax.UsageTickets.insert]) permission (by simp [OwnerPhaseTransitions.introduce]) rfl restored
    have checkedRestored : InstallationSupport.PendingChecked ambient outward restored := by
      exact .handler (.spent .nil)
    have checkedResume : InstallationSupport.CodeChecked ambient outward resume := by
      exact InstallationSupport.CodeChecked.resume (front := Context.nil)
        (captured := terminal effect table activation declarations) (tail := Context.nil)
        (resumeDemand := resumeDemand) (rights := rights) (located := .hit)
        (known := by simp [Syntax.UsageTickets.insert]) (permission := permission)
        (available := by simp [OwnerPhaseTransitions.introduce]) (resumeShape := rfl)
        (restored := restored) checkedRestored
    exact ⟨.sequence .pure resume,.sequence .pure checkedResume,clause_accounting (.resume operand) supported declarations⟩
  | bind operand body ih =>
    let b := ih supported
    exact ⟨.sequence .pure b.certificate,.sequence .pure b.checked,clause_accounting (.bind operand body) supported declarations⟩
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    let a := ihY y
    let b := ihN n
    exact ⟨.sequence .pure (.choice a.certificate b.certificate),.sequence .pure (.choice a.checked b.checked),
      clause_accounting (.branch condition yes no) supported declarations⟩
  | unsupported reason => cases supported


/-- Singleton declarations still pass the original whole-registry coverage check. -/
def single (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) :
    Declarations entries effect input bindings (.cons operation parameter binder code .nil) :=
  .cons reference data supportBound ordinary protectedMode resumeEffects closeEffects .nil

theorem request_facets {outward : List Instance} {actions : Syntax.UsageTickets} {budget : Footprint}
    {phases : OwnerPhaseTransitions.Phases} {world installations ambient : List Nat}
    (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : code.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.request (effect := effect) (operation := operation))
      (terminal effect (single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows)
      (outerRoot data) := by
  let declarations := single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let captured := terminal effect declarations.table activation declarations.rows
  have cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation captured captured Context.nil
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := by
    simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut,captured,terminal,select,declarations,single,Declarations.table,Declarations.families,
      ProtectionContracts.lookup,SourceDependencyCapture.lookupDependencies,modeFamily]
  have selected : CapturedClauseRows effect operation false captured data.rows := by
    exact .selected .here .ordinary
  have terminalHere : TerminalHandler effect activation declarations.rows captured := .here
  have requiredRights : SourceAdmission.rightsAt operation (clauseSignatures declarations.plans) = some code.requiredActions := by
    simp [declarations,single,Declarations.plans,clauseSignatures,SourceAdmission.rightsAt]
  have guard : SourceDependencyChecks.Lexical.Capture _ effect operation :=
    .handler cut.select_sound rfl rfl rfl
  have retained : SourceAdmission.Pending outward actions budget phases world installations captured Context.nil
      .ordinary .ordinary := .handler .nil
  have retainedChecked : InstallationSupport.PendingChecked ambient outward retained := .handler .nil
  have callbacks : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceAdmission.Pending outward actions budget phases world installations captured (.closing Context.nil) .unwind .unwind := by
    intro impossible; cases impossible
  have ownerBound : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners (SourceDependencyCapture.Scope.handler effect declarations.table declarations.families .nil))
        (SourceDependencyCapture.Scope.handler effect declarations.table declarations.families .nil) := by
    intro impossible; cases impossible
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ captured.ticketNames) =>
    (clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
      (table := declarations.table) (activation := activation) (outward := outward)
      (actions := actions) (budget := budget) (phases := phases) (world := world)
      (installations := installations) (ambient := ambient) data supported declarations.rows permission).certificate
  let certificate := SourceAdmission.Code.request cut guard callbacks ownerBound
    (RequestBudget.nonconsuming cut rfl) selected terminalHere requiredRights retained body
  have checked : InstallationSupport.CodeChecked ambient outward certificate := by
    apply InstallationSupport.CodeChecked.request (cut := cut) (guarded := guard) (callbacks := callbacks)
      (ownerBound := ownerBound) (cleanupBudget := RequestBudget.nonconsuming cut rfl)
      (selected := selected) (terminal := terminalHere) (requiredRights := requiredRights)
      (retained := retained) (body := body)
    · intro impossible; cases impossible
    · exact retainedChecked
    · intro owner resumeDemand fresh absent
      exact (clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
      (table := declarations.table) (activation := activation) (outward := outward)
      (actions := actions) (budget := budget) (phases := phases) (world := world)
      (installations := installations) (ambient := ambient) data supported declarations.rows permission).checked
  exact ⟨certificate,checked,.request cut selected
    (fun owner resumeDemand _absent => clause_accounting (owner := owner) (resumeDemand := resumeDemand) data supported declarations.rows)
    (fun owner _resumeDemand _absent => retire_local (owner := owner) data supported)⟩


theorem handler_facets {outward : List Instance} {actions : Syntax.UsageTickets} {budget : Footprint}
    {phases : OwnerPhaseTransitions.Phases} {world installations ambient : List Nat}
    (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance)
    (supported : data.supported = true) (permission : code.requiredActions.resume = true)
    (support : (single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows.resourceSupport ⊆ ambient) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.handler (effect := effect)
        (table := (single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table)
        (required := []) (single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows
        (Rows.sequence Rows.pure (Rows.request (effect := effect) (operation := operation))))
      Context.nil (outerRoot data) := by
  let declarations := single reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let inside := fun activation (_fresh : activation ∉ installations) =>
    request_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := activation :: installations) (ambient := ambient)
      reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
  let certificate := SourceAdmission.Code.handler (required := [])
    (fun activation fresh => SourceAdmission.Code.sequence .pure (inside activation fresh).certificate)
  have checked : InstallationSupport.CodeChecked ambient outward certificate := by
    apply InstallationSupport.CodeChecked.handler (supported := by simpa [SourceDependencyCapture.Scope.visibleResources] using support)
    intro activation fresh
    exact .sequence .pure (inside activation fresh).checked
  exact ⟨certificate,checked,Accounting.Run.installHandler
    (fun activation fresh => .sequence (.pure (.plain (inside activation fresh).accounting)))⟩

/-- All desired judgments are outputs on the exact checked original rows. -/
structure Result (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed residual : List Instance)
    (bindings : Bindings) (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint) (resumeEffects closeEffects : List Instance)
    (operand : Annotation entries owners bindings value argument [] (.request [] []) .pure Rows.pure)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat)
    (budget : Footprint) (ambient : List Nat) : Type where
  original : HandlerReceipt entries policy outward owners world allowed residual .none bindings
    (.perform (Instantiation.freezeEffect effect) operation value) input []
    (.emitAfter (.request [] []) [] [⟨effect,operation,false⟩])
    (.sequence .pure (.request (effect := effect) (operation := operation)))
    (sequenceRows Rows.pure Rows.request)
    (single reference data supportBound ordinary protectedMode resumeEffects closeEffects) lexical receiver
  facets : ClauseFacets (outward := outward) (actions := fun _ => none) (budget := budget)
    (phases := OwnerPhaseTransitions.available []) (world := world) (installations := []) (ambient := ambient)
    (Rows.handler (effect := effect)
      (table := (single reference data supportBound ordinary protectedMode resumeEffects closeEffects).table)
      (required := []) (single reference data supportBound ordinary protectedMode resumeEffects closeEffects).rows
      (Rows.sequence Rows.pure (Rows.request (effect := effect) (operation := operation))))
    Context.nil (outerRoot data)

inductive AdmissionError where
  | source : Error → AdmissionError
  | unavailableOrdinary | unsupportedClause | deniedResume | clauseSupport : AdmissionError
  | usage | support | accounting | budget : AdmissionError
  deriving Repr

/-- Executes the original source check; finite declaration/row interpretation
then produces contextual admission and accounting without proof seeds. -/
def check (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed residual : List Instance)
    (bindings : Bindings) (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint) (resumeEffects closeEffects : List Instance)
    (operand : Annotation entries owners bindings value argument [] (.request [] []) .pure Rows.pure)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat)
    (budget : Footprint) (ambient : List Nat) :
    Except AdmissionError (Result entries policy outward owners world allowed residual bindings reference data supportBound
      ordinary protectedMode resumeEffects closeEffects operand lexical receiver budget ambient) :=
  ((CoreCallableFiniteHandlerSource.check (.perform reference operand)
    (single reference data supportBound ordinary protectedMode resumeEffects closeEffects)
    policy outward world allowed residual .none lexical receiver).mapError AdmissionError.source).bind fun original => by
      cases ordinary with
      | none => exact .error .unavailableOrdinary
      | some advertised =>
        exact if supported : data.supported = true then
          if permission : code.requiredActions.resume = true then
            if bounded : CoreCallableGraphAnnotationChecks.subsetB
                (single reference data supportBound (some advertised) protectedMode resumeEffects closeEffects).rows.resourceSupport ambient = true then
              .ok ⟨original,handler_facets reference data supportBound advertised protectedMode resumeEffects closeEffects
                supported permission (CoreCallableGraphAnnotationChecks.subsetB_sound bounded)⟩
            else .error .clauseSupport
          else .error .deniedResume
        else .error .unsupportedClause
/-- Closed initial assembly executes finite usage/support/accounting checks on
that same code and computed root. It does not establish builtin progress ABI. -/
def checkInitial (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (owners : CoreCallableContractRegistries.Owners)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input input binder [(parameter,argument)] code)
    (ordinary protectedMode : Option Footprint)
    (operand : Annotation entries owners [] value argument [] (.request [] []) .pure Rows.pure)
    (budget : Footprint) :
    Except AdmissionError (CoreCallableInitialAdmission.Program
      ⟨operations entries,policy,owners⟩ (fun _ => none) budget
      (.handle (Instantiation.freezeEffect effect) (.perform (Instantiation.freezeEffect effect) operation value)
        (.cons operation parameter binder code .nil))) :=
  (check entries policy [] owners [] [] [] [] reference data [] ordinary protectedMode [] [] operand [] [] budget []).bind fun result => by
    if usage : CoreCallableCompositionalAdmissionFacets.usageCheck value = true then
      if permission : (policy binder).resume = true then
        if supported : data.supported = true then
          let expression := Code.handle (Instantiation.freezeEffect effect)
            (.perform (Instantiation.freezeEffect effect) operation value) (.cons operation parameter binder code .nil)
          if support : CoreCallableGraphAnnotationChecks.subsetB
              (ScopedPorts.Support.evaluate ScopedPorts.Support.empty expression.dependencies) [] = true then
            match evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
                (annotateDisposals (outerRoot data)) with
            | none => exact .error .accounting
            | some row =>
              if bounded : CoreCallableGraphAnnotationChecks.subsetB row budget = true then
                exact .ok {
                  result := input
                  dependencies := _
                  plan := .handler (effect := effect) (table := (single reference data [] ordinary protectedMode [] []).table)
                    [] (single reference data [] ordinary protectedMode [] []).plans
                    (.sequence .pure (.request (effect := effect) (operation := operation)))
                  rows := by simpa only [signature] using
                    (Rows.handler (effect := effect) (table := (single reference data [] ordinary protectedMode [] []).table)
                      (required := []) (single reference data [] ordinary protectedMode [] []).rows
                      (sequenceRows (first := Plan.pure) (second := Plan.request (effect := effect) (operation := operation))
                        Rows.pure Rows.request))
                  demand := []
                  requirements := .prepend [.ordinary (.handler effect 0 (single reference data [] ordinary protectedMode [] []).table)]
                    (.emitAfter (.request [] []) [] [⟨effect,operation,false⟩])
                  source := by with_unfolding_all exact result.original.source
                  authenticated := by with_unfolding_all exact result.original.authenticated
                  support := SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound support)
                  usage := .handle (.perform (CoreCallableCompositionalAdmissionFacets.usage_sound value usage))
                    (.cons (data.use supported permission) .nil)
                  certificate := by with_unfolding_all exact result.facets.certificate
                  certificateChecked := by with_unfolding_all exact result.facets.checked
                  rootDemand := []
                  root := outerRoot data
                  accounting := by with_unfolding_all exact result.facets.accounting
                  annotated := outerRoot data
                  annotation := .original
                  row := row
                  checked := RecursiveRequirements.evaluate_sound evaluated
                  bounded := CoreCallableGraphAnnotationChecks.subsetB_sound bounded }
              else exact .error .budget
          else exact .error .support
        else exact .error .unsupportedClause
      else exact .error .deniedResume
    else exact .error .usage

#print axioms outerRoot
#print axioms localRoot
#print axioms retire_local
#print axioms clause_accounting
#print axioms clause_facets
#print axioms request_facets
#print axioms handler_facets
#print axioms check
#print axioms checkInitial
end Ash.OneShot.CoreCallableFiniteHandlerAdmission
