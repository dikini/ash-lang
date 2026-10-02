import CoreCallableFiniteHandlerBodyRoutes
namespace Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows choiceRows)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableFiniteHandlerAdmission (ClauseFacets terminal)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature clauseSignatures)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements LocalOwner)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableCompositionalAdmissionFacets (annotationRecipe quietCheck usageCheck usage_sound)
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open CoreCallableFiniteHandlerBodyRoutes (Front PendingFacets quietRoot quiet_local quiet_facets wait_reindex annotationRows)

/-- Internal finite spent spine. The public checker constructs it at each resume. -/
inductive Spent : {scope : SourceDependencyCapture.Scope} → {hints : SourceDependencyChecks.Lexical.ReturnHints scope} → Context hints → Type where
  | nil : Spent Context.nil
  | spent (owner : Nat) (rest : Spent tail) : Spent (Context.spent (owner := owner) tail)

def Spent.root : Spent tail → Requirements []
  | .nil => .request [] []
  | .spent owner rest => .sequence (.spent owner) rest.root

theorem Spent.wait (tail : Spent context) : Accounting.Wait world installations context .ordinary tail.root := by
  induction tail with
  | nil => exact .nil
  | spent owner rest ih => exact .spent ih

theorem Spent.pending (tail : Spent context) : PendingFacets outward actions budget phases world installations ambient context := by
  induction tail with
  | nil => exact ⟨.nil,.nil⟩
  | spent owner rest ih => exact ⟨.spent ih.pending,.spent ih.checked⟩

theorem Spent.mode {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} (tail : Spent context) : hints.returnMode .ordinary = .ordinary := by
  induction tail with
  | nil => rfl
  | spent owner rest ih => exact ih

theorem Spent.held {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} (tail : Spent context) : scope.held = false := by
  induction tail with
  | nil => rfl
  | spent owner rest ih => exact ih

theorem Spent.local (tail : Spent context) (absent : owner ∉ context.ticketNames) :
    LocalOwner owner phase tail.root tail.root phase := by
  induction tail with
  | nil => exact .empty
  | spent other rest ih =>
    obtain ⟨different,missing⟩ : owner ≠ other ∧ owner ∉ _ := by simpa [Context.ticketNames] using absent
    exact .sequence (.spentOther (Ne.symm different)) (ih missing)

def clauseLocal (front : Front context) (tail : Requirements []) (owner : Nat) : Template input answer binder bindings code → Requirements [owner]
  | .resume _ => .sequence (.retire owner) (front.root (.sequence (.spent owner) tail))
  | .bind _ body => clauseLocal front tail owner body
  | .branch _ yes no => .choice (clauseLocal front tail owner yes) (clauseLocal front tail owner no) (.refl [owner])
  | .unsupported _ => .retire owner

-- The neutral continuation is kept once; retirement erases only the new owner.
def clauseOuter (front : Front context) (tail : Requirements []) : Template input answer binder bindings code → Requirements []
  | .resume _ => .sequence (.request [] []) (front.root (.sequence (.request [] []) tail))
  | .bind _ body => clauseOuter front tail body
  | .branch _ yes no => .choice (clauseOuter front tail yes) (clauseOuter front tail no) (.refl [])
  | .unsupported _ => tail

theorem clause_retire (front : Front context) (tail : Spent outside)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (absent : owner ∉ outside.ticketNames) :
    LocalOwner owner .available (clauseLocal front tail.root owner data) (clauseOuter front tail.root data) .consumed := by
  induction data with
  | resume operand => exact .sequence .retireSelf (front.local (.sequence .spentSelf (tail.local absent)))
  | bind operand body ih => exact ih supported
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .choice (ihY y) (ihN n)
  | unsupported reason => cases supported

theorem clause_accounting (front : Front context) (valid : front.valid = true)
    (tail : Spent outside)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) :
    Accounting.Run world installations (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand)
        (context.append (terminal effect table activation declarations)) outside)
      (clauseLocal front tail.root owner data) := by
  induction data with
  | resume operand =>
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.resume (front := Context.nil)
    · exact .hit
    · exact wait_reindex (front.wait valid (Accounting.Wait.handler (Accounting.Wait.spent tail.wait)))
        (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) outside)).symm
  | bind operand body ih => exact .sequence (.pure (.plain (ih supported)))
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .sequence (.pure (.plain (.choice (ihY y) (ihN n) (.refl _))))
  | unsupported reason => cases supported

theorem clause_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} {rights : Syntax.OneShotRights} {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (front : Front context) (valid : front.valid = true)
    (tail : Spent outside)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) (permission : rights.resume = true) :
    ClauseFacets (outward := outward) (actions := actions.insert owner rights)
      (phases := OwnerPhaseTransitions.introduce phases owner) (budget := budget) (ambient := ambient)
      (world := world) (installations := installations) (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand)
        (context.append (terminal effect table activation declarations)) outside)
      (clauseLocal front tail.root owner data) := by
  induction data with
  | resume operand =>
    let outsideReady : PendingFacets outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner) world installations ambient
        ((terminal effect table activation declarations).append (.spent (owner := owner) outside)) :=
      ⟨.handler (.spent (tail.pending (ambient := ambient)).pending),.handler (.spent (tail.pending (ambient := ambient)).checked)⟩
    let pending := front.pending valid outsideReady (Accounting.Wait.handler (Accounting.Wait.spent tail.wait))
    let restored := pending.pending.reindex_context
      (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) outside)).symm
    have restoredChecked : InstallationSupport.PendingChecked ambient outward restored :=
      pending.checked.reindex_context (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) outside)).symm
    have mode : (hints.append (terminal effect table activation declarations).pack.hints).returnMode .ordinary = .ordinary :=
      front.hint_mode _
    dsimp only [terminal,Context.pack] at mode
    let resume : SourceAdmission.Code outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.introduce phases owner) world installations (Rows.invoke (key := ⟨owner,.resume⟩))
        (Context.live (owner := owner) (resumeDemand := resumeDemand)
          (context.append (terminal effect table activation declarations)) outside) :=
      .resume (front := Context.nil) .hit (by simp [Syntax.UsageTickets.insert]) permission
        (by simp [OwnerPhaseTransitions.introduce]) (by rw [mode]; rfl)
        (by simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode,tail.mode] using restored)
    have checkedResume : InstallationSupport.CodeChecked ambient outward resume := by
      apply InstallationSupport.CodeChecked.resume (front := Context.nil)
        (captured := context.append (terminal effect table activation declarations)) (tail := outside)
        (resumeDemand := resumeDemand) (rights := rights) (located := .hit)
        (known := by simp [Syntax.UsageTickets.insert]) (permission := permission)
        (available := by simp [OwnerPhaseTransitions.introduce]) (resumeShape := by rw [mode]; rfl)
        (restored := by simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode,tail.mode] using restored)
      simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode,tail.mode] using restoredChecked
    exact ⟨.sequence .pure resume,.sequence .pure checkedResume,
      clause_accounting front valid tail (.resume operand) supported declarations⟩
  | bind operand body ih =>
    let b := ih supported
    exact ⟨.sequence .pure b.certificate,.sequence .pure b.checked,
      clause_accounting front valid tail (.bind operand body) supported declarations⟩
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    let a := ihY y
    let b := ihN n
    exact ⟨.sequence .pure (.choice a.certificate b.certificate),.sequence .pure (.choice a.checked b.checked),
      clause_accounting front valid tail (.branch condition yes no) supported declarations⟩
  | unsupported reason => cases supported



theorem Front.ticketNames (front : Front context) : context.ticketNames = [] := by
  induction front with
  | nil => rfl
  | plain tag rows rest ih => exact ih

theorem request_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (front : Front context) (valid : front.valid = true)
    (tail : Spent outside)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : code.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.request (effect := effect) (operation := operation))
      (context.append ((terminal effect (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows).append outside))
      (clauseOuter front tail.root data) := by
  let declarations := CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let base := terminal effect declarations.table activation declarations.rows
  let captured := context.append base
  let whole := context.append (base.append outside)
  have baseCut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation (base.append outside) base outside
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := by
    simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut,base,terminal,select,declarations,CoreCallableFiniteHandlerBodyRoutes.singleton,Declarations.table,Declarations.families,
      ProtectionContracts.lookup,SourceDependencyCapture.lookupDependencies,modeFamily,Context.append]
    rfl
  have cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation whole captured outside
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := front.selection baseCut
  have held : captured.pack.scope.held = false := by
    exact front.held base
  dsimp only [Context.pack] at held
  have selected : CapturedClauseRows effect operation captured.pack.scope.held captured data.rows := by
    dsimp only [captured,Context.pack]
    rw [held]
    exact .selected front.terminal .ordinary
  have terminalHere : TerminalHandler effect activation declarations.rows captured := front.terminal
  have requiredRights : SourceAdmission.rightsAt operation (clauseSignatures declarations.plans) = some code.requiredActions := by
    simp [declarations,CoreCallableFiniteHandlerBodyRoutes.singleton,Declarations.plans,clauseSignatures,SourceAdmission.rightsAt]
  have guard : SourceDependencyChecks.Lexical.Capture _ effect operation :=
    .handler cut.select_sound (by rw [held]; rfl) (by rw [held]; rfl) (by rw [held]; rfl)
  let retained := front.pending valid (⟨.handler (tail.pending (ambient := ambient)).pending,.handler (tail.pending (ambient := ambient)).checked⟩ :
    PendingFacets outward actions budget phases world installations ambient (base.append outside)) (Accounting.Wait.handler tail.wait)
  have mode : (hints.append (base.append outside).pack.hints).returnMode .ordinary = .ordinary := by
    rw [front.hint_mode]; exact tail.mode
  dsimp only [base,terminal,Context.pack] at mode
  let waiting : SourceAdmission.Pending outward actions budget phases world installations whole Context.nil
      .ordinary ((hints.append (base.append outside).pack.hints).returnMode .ordinary) := by
    simpa only [whole,base,terminal,Context.pack,mode] using retained.pending
  have waitingChecked : InstallationSupport.PendingChecked ambient outward waiting := by
    simpa only [whole,base,terminal,Context.pack,mode] using retained.checked
  have callbacks : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceAdmission.Pending outward actions budget phases world installations captured (.closing outside) .unwind .unwind := by
    intro impossible; cases impossible
  have ownerBound : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope := by
    intro impossible; cases impossible
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ whole.ticketNames) =>
    (clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
      (table := declarations.table) (activation := activation) (outward := outward)
      (actions := actions) (budget := budget) (phases := phases) (world := world)
      (installations := installations) (ambient := ambient) front valid tail data supported declarations.rows permission).certificate
  let certificate := SourceAdmission.Code.request cut guard callbacks ownerBound
    (RequestBudget.nonconsuming cut rfl) selected terminalHere requiredRights waiting body
  have checked : InstallationSupport.CodeChecked ambient outward certificate := by
    apply InstallationSupport.CodeChecked.request (cut := cut) (guarded := guard) (callbacks := callbacks)
      (ownerBound := ownerBound) (cleanupBudget := RequestBudget.nonconsuming cut rfl)
      (selected := selected) (terminal := terminalHere) (requiredRights := requiredRights)
      (retained := waiting) (body := body)
    · intro impossible; cases impossible
    · exact waitingChecked
    · intro owner resumeDemand fresh absent
      exact (clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
        (table := declarations.table) (activation := activation) (outward := outward)
        (actions := actions) (budget := budget) (phases := phases) (world := world)
        (installations := installations) (ambient := ambient) front valid tail data supported declarations.rows permission).checked
  exact ⟨certificate,checked,.request cut selected
    (fun owner resumeDemand _absent => clause_accounting (owner := owner) (resumeDemand := resumeDemand) front valid tail data supported declarations.rows)
    (fun owner _resumeDemand absent => clause_retire front tail data supported (by
      simpa [whole,base,terminal,Context.append_ticketNames,Front.ticketNames front,Context.ticketNames] using absent))⟩



def routeRoot (front : Front context) (tail : Requirements []) (data : Template input answer binder outerBindings clause) :
    CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation → Requirements []
  | .quiet annotation => quietRoot (annotationRecipe annotation) (front.root tail)
  | .request _ operand => quietRoot (annotationRecipe operand) (clauseOuter front tail data)
  | .prefix initial body => quietRoot (annotationRecipe initial) (routeRoot front tail data body)
  | .suffix initial body => routeRoot (.plain (annotationRecipe body) (annotationRows body) front) tail data initial
  | .branch condition yes no _ => quietRoot (annotationRecipe condition)
      (.choice (routeRoot front tail data yes) (routeRoot front tail data no) (.refl []))

theorem route_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (route : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation) (valid : route.valid = true)
    (front : Front context) (frontValid : front.valid = true)
    (tail : Spent outside)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: outerBindings) clause)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : clause.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (annotationRows annotation)
      (context.append ((terminal effect (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows).append outside))
      (routeRoot front tail.root data route) := by
  induction route generalizing scope hints context with
  | quiet annotation =>
    exact quiet_facets (annotationRecipe annotation) (annotationRows annotation) valid
      (front.wait frontValid (Accounting.Wait.handler tail.wait))
  | request selected operand =>
    let requested := request_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient) front frontValid tail reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe operand) (annotationRows operand) valid (Accounting.Wait.plain requested.accounting)
    exact ⟨.sequence evaluated.certificate requested.certificate,.sequence evaluated.checked requested.checked,
      .sequence evaluated.accounting⟩
  | «prefix» initial body ih =>
    obtain ⟨a,b⟩ : quietCheck (annotationRecipe initial) = true ∧ body.valid = true := by simpa [CoreCallableFiniteHandlerBodyRoutes.Route.valid] using valid
    let next := ih b front frontValid
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe initial) (annotationRows initial) a (Accounting.Wait.plain next.accounting)
    exact ⟨.sequence evaluated.certificate next.certificate,.sequence evaluated.checked next.checked,.sequence evaluated.accounting⟩
  | suffix initial body ih =>
    obtain ⟨a,b⟩ : initial.valid = true ∧ quietCheck (annotationRecipe body) = true := by simpa [CoreCallableFiniteHandlerBodyRoutes.Route.valid] using valid
    have v : (Front.plain (annotationRecipe body) (annotationRows body) front).valid = true := by simp [Front.valid,b,frontValid]
    let next := ih a (.plain (annotationRecipe body) (annotationRows body) front) v
    let suffix := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations)
      (context := context.append ((terminal effect
        (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table activation
        (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows).append outside))
      (ambient := ambient) (annotationRecipe body) (annotationRows body) b (front.wait frontValid (Accounting.Wait.handler tail.wait))
    exact ⟨.sequence next.certificate suffix.certificate,.sequence next.checked suffix.checked,.sequence next.accounting⟩
  | branch condition yes no same ihY ihN =>
    obtain ⟨⟨c,y⟩,n⟩ : (quietCheck (annotationRecipe condition) = true ∧ yes.valid = true) ∧ no.valid = true := by simpa [CoreCallableFiniteHandlerBodyRoutes.Route.valid] using valid
    let left := ihY y front frontValid
    let right := ihN n front frontValid
    let choice := Accounting.Run.choice left.accounting right.accounting (.refl [])
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe condition) (annotationRows condition) c (Accounting.Wait.plain choice)
    exact ⟨.sequence evaluated.certificate (.choice left.certificate right.certificate),
      .sequence evaluated.checked (.choice left.checked right.checked),.sequence evaluated.accounting⟩



theorem clauseOuter_local (front : Front context) (data : Template input answer binder bindings code)
    (binding : LocalOwner owner before localTail outerTail after) :
    LocalOwner owner before (clauseOuter front localTail data) (clauseOuter front outerTail data) after := by
  induction data with
  | resume operand => exact .sequence .empty (front.local (.sequence .empty binding))
  | bind operand body ih => exact ih
  | branch condition yes no ihY ihN => exact .choice ihY ihN
  | unsupported reason => exact binding

theorem route_local {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} (route : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation)
    (front : Front context) (data : Template input answer binder bindings code)
    (binding : LocalOwner owner before localTail outerTail after) :
    LocalOwner owner before (routeRoot front localTail data route) (routeRoot front outerTail data route) after := by
  induction route generalizing scope hints context with
  | quiet annotation => exact quiet_local (annotationRecipe annotation) (front.local binding)
  | request reference operand => exact quiet_local (annotationRecipe operand) (clauseOuter_local front data binding)
  | «prefix» initial body ih => exact quiet_local (annotationRecipe initial) (ih front)
  | suffix initial body ih => exact ih (.plain (annotationRecipe body) (annotationRows body) front)
  | branch condition yes no same ihY ihN => exact quiet_local (annotationRecipe condition) (.choice (ihY front) (ihN front))

def firstLocal (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation)
    (chosen : Template input answer binder outerBindings originalClause) (tail : Requirements []) (owner : Nat) : Template input answer binder bindings code → Requirements [owner]
  | .resume _ => .sequence (.retire owner) (routeRoot Front.nil (.sequence (.spent owner) tail) chosen later)
  | .bind _ body => firstLocal later chosen tail owner body
  | .branch _ yes no => .choice (firstLocal later chosen tail owner yes) (firstLocal later chosen tail owner no) (.refl [owner])
  | .unsupported _ => .retire owner

def firstOuter (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation)
    (chosen : Template input answer binder outerBindings originalClause) (tail : Requirements []) : Template input answer binder bindings code → Requirements []
  | .resume _ => .sequence (.request [] []) (routeRoot Front.nil (.sequence (.request [] []) tail) chosen later)
  | .bind _ body => firstOuter later chosen tail body
  | .branch _ yes no => .choice (firstOuter later chosen tail yes) (firstOuter later chosen tail no) (.refl [])
  | .unsupported _ => .request [] []

theorem first_retire (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation)
    (chosen : Template input answer binder outerBindings originalClause)
    (data : Template input answer binder bindings code) (supported : data.supported = true) :
    LocalOwner owner .available (firstLocal later chosen (.request [] []) owner data)
      (firstOuter later chosen (.request [] []) data) .consumed := by
  induction data with
  | resume operand => exact .sequence .retireSelf (route_local later Front.nil chosen (.sequence .spentSelf .empty))
  | bind operand body ih => exact ih supported
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .choice (ihY y) (ihN n)
  | unsupported reason => cases supported


theorem first_clause_facets {rights : Syntax.OneShotRights} {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation) (valid : later.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (chosen : Template input answer binder ((parameter,argument) :: outerBindings) originalClause)
    (chosenSupported : chosen.supported = true) (chosenPermission : originalClause.requiredActions.resume = true)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (permission : rights.resume = true) :
    ClauseFacets (outward := outward) (actions := actions.insert owner rights)
      (phases := OwnerPhaseTransitions.introduce phases owner) (budget := budget) (ambient := ambient)
      (world := world) (installations := installations) (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand)
        (.plain (annotationRows annotation) (terminal effect
          (CoreCallableFiniteHandlerBodyRoutes.singleton reference chosen supportBound (some ordinary) protectedMode resumeEffects closeEffects).table activation
          (CoreCallableFiniteHandlerBodyRoutes.singleton reference chosen supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows)) Context.nil)
      (firstLocal later chosen (.request [] []) owner data) := by
  induction data with
  | resume operand =>
    let declarations := CoreCallableFiniteHandlerBodyRoutes.singleton reference chosen supportBound (some ordinary) protectedMode resumeEffects closeEffects
    let base := terminal effect declarations.table activation declarations.rows
    let next := route_facets (outward := outward) (actions := actions.insert owner rights) (budget := budget)
      (phases := OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner)
      (world := world) (installations := installations) (ambient := ambient)
      later valid Front.nil rfl (Spent.spent owner Spent.nil) reference chosen supportBound ordinary protectedMode resumeEffects closeEffects activation chosenSupported chosenPermission
    let restored : SourceAdmission.Pending outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner) world installations
        ((Context.plain (annotationRows annotation) base).append (.spent (owner := owner) Context.nil)) Context.nil .ordinary .ordinary :=
      .plain (next.certificate.reindex_context (Context.append_nil_pack _).symm) (.handler (.spent .nil))
    have restoredChecked : InstallationSupport.PendingChecked ambient outward restored :=
      .plain (next.checked.reindex_context (Context.append_nil_pack _).symm) (.handler (.spent .nil))
    let resume : SourceAdmission.Code outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.introduce phases owner) world installations (Rows.invoke (key := ⟨owner,.resume⟩))
        (Context.live (owner := owner) (resumeDemand := resumeDemand) (Context.plain (annotationRows annotation) base) Context.nil) :=
      .resume (front := Context.nil) .hit (by simp [Syntax.UsageTickets.insert]) permission
        (by simp [OwnerPhaseTransitions.introduce]) rfl restored
    have checkedResume : InstallationSupport.CodeChecked ambient outward resume := by
      apply InstallationSupport.CodeChecked.resume (front := Context.nil)
        (captured := Context.plain (annotationRows annotation) base) (tail := Context.nil)
        (resumeDemand := resumeDemand) (rights := rights) (located := .hit)
        (known := by simp [Syntax.UsageTickets.insert]) (permission := permission)
        (available := by simp [OwnerPhaseTransitions.introduce]) (resumeShape := rfl)
        (restored := restored)
      exact restoredChecked
    let accounting : Accounting.Run world installations (Rows.invoke (key := ⟨owner,.resume⟩))
        (Context.live (owner := owner) (resumeDemand := resumeDemand) (Context.plain (annotationRows annotation) base) Context.nil)
        (.sequence (.retire owner) (routeRoot Front.nil (.sequence (.spent owner) (.request [] [])) chosen later)) :=
      .resume (front := Context.nil) .hit (.plain next.accounting)
    exact ⟨.sequence .pure resume,.sequence .pure checkedResume,.sequence (.pure (.plain accounting))⟩
  | bind operand body ih =>
    let b := ih supported
    exact ⟨.sequence .pure b.certificate,.sequence .pure b.checked,.sequence (.pure (.plain b.accounting))⟩
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    let a := ihY y
    let b := ihN n
    exact ⟨.sequence .pure (.choice a.certificate b.certificate),.sequence .pure (.choice a.checked b.checked),
      .sequence (.pure (.plain (.choice a.accounting b.accounting (.refl _))))⟩
  | unsupported reason => cases supported


theorem first_request_facets {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input annotation)
    (valid : later.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : code.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.request (effect := effect) (operation := operation))
      (Context.plain (annotationRows annotation) (terminal effect (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows))
      (firstOuter later data (.request [] []) data) := by
  let declarations := CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let base := terminal effect declarations.table activation declarations.rows
  let captured := Context.plain (annotationRows annotation) base
  have baseCut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation base base Context.nil
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := by
    simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut,base,terminal,select,declarations,CoreCallableFiniteHandlerBodyRoutes.singleton,Declarations.table,Declarations.families,
      ProtectionContracts.lookup,SourceDependencyCapture.lookupDependencies,modeFamily]
  have cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation captured captured Context.nil
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := (Front.plain (annotationRecipe annotation) (annotationRows annotation) Front.nil).selection baseCut
  have held : captured.pack.scope.held = false := by
    rfl
  dsimp only [Context.pack] at held
  have selected : CapturedClauseRows effect operation captured.pack.scope.held captured data.rows := by
    dsimp only [captured,Context.pack]
    rw [held]
    exact .selected (TerminalHandler.plain TerminalHandler.here) .ordinary
  have terminalHere : TerminalHandler effect activation declarations.rows captured := (TerminalHandler.plain TerminalHandler.here)
  have requiredRights : SourceAdmission.rightsAt operation (clauseSignatures declarations.plans) = some code.requiredActions := by
    simp [declarations,CoreCallableFiniteHandlerBodyRoutes.singleton,Declarations.plans,clauseSignatures,SourceAdmission.rightsAt]
  have guard : SourceDependencyChecks.Lexical.Capture _ effect operation :=
    .handler cut.select_sound (by rw [held]; rfl) (by rw [held]; rfl) (by rw [held]; rfl)
  let next := route_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
    (world := world) (installations := installations) (ambient := ambient)
    later valid Front.nil rfl Spent.nil reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
  let waiting : SourceAdmission.Pending outward actions budget phases world installations captured Context.nil .ordinary .ordinary :=
    .plain (next.certificate.reindex_context (Context.append_nil_pack _).symm) (.handler .nil)
  have waitingChecked : InstallationSupport.PendingChecked ambient outward waiting :=
    .plain (next.checked.reindex_context (Context.append_nil_pack _).symm) (.handler .nil)
  have callbacks : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceAdmission.Pending outward actions budget phases world installations captured (.closing Context.nil) .unwind .unwind := by
    intro impossible; cases impossible
  have ownerBound : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope := by
    intro impossible; cases impossible
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ captured.ticketNames) =>
    (first_clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
      (outward := outward)
      (actions := actions) (budget := budget) (phases := phases) (world := world)
      (installations := installations) (ambient := ambient) later valid reference data supported permission supportBound ordinary protectedMode resumeEffects closeEffects activation data supported permission).certificate
  let certificate := SourceAdmission.Code.request cut guard callbacks ownerBound
    (RequestBudget.nonconsuming cut rfl) selected terminalHere requiredRights waiting body
  have checked : InstallationSupport.CodeChecked ambient outward certificate := by
    apply InstallationSupport.CodeChecked.request (cut := cut) (guarded := guard) (callbacks := callbacks)
      (ownerBound := ownerBound) (cleanupBudget := RequestBudget.nonconsuming cut rfl)
      (selected := selected) (terminal := terminalHere) (requiredRights := requiredRights)
      (retained := waiting) (body := body)
    · intro impossible; cases impossible
    · exact waitingChecked
    · intro owner resumeDemand fresh absent
      exact (first_clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
        (outward := outward)
        (actions := actions) (budget := budget) (phases := phases) (world := world)
        (installations := installations) (ambient := ambient) later valid reference data supported permission supportBound ordinary protectedMode resumeEffects closeEffects activation data supported permission).checked
  exact ⟨certificate,checked,.request cut selected
    (fun owner resumeDemand _absent => (first_clause_facets (owner := owner) (resumeDemand := resumeDemand)
      (effect := effect) (outward := outward) (actions := fun _ => none) (budget := []) (phases := fun _ => .available)
      (ambient := []) later valid reference data supported permission supportBound ordinary protectedMode resumeEffects closeEffects activation data supported permission).accounting)
    (fun owner _resumeDemand _absent => first_retire later data data supported)⟩



/-- Finite original request followed by an original one-request route. -/
inductive SequentialRoute (entries : OperationEntries) (owners : CoreCallableContractRegistries.Owners)
    (effect : Instance) (operation : Nat) (argument input : Contract) :
    {bindings : Bindings} → {code : Code} → {answer : Contract} → {demand : List Nat} →
    {requirements : Requirements demand} → {dependencies : Dependencies} → {plan : Plan dependencies} →
    {rows : Rows (signature plan)} → Annotation entries owners bindings code answer demand requirements plan rows → Type where
  | sequence {bodyAnnotation : Annotation entries owners ((parameter,input) :: bindings) bodyCode answer bodyDemand bodyReq bodyPlan bodyRows}
      (reference : OperationRef entries effect operation argument input)
      (operand : Annotation entries owners bindings value argument operandDemand operandReq operandPlan operandRows)
      (later : CoreCallableFiniteHandlerBodyRoutes.Route entries owners effect operation argument input bodyAnnotation) :
      SequentialRoute entries owners effect operation argument input (Annotation.bind (parameter := parameter) (.perform reference operand) bodyAnnotation)

def SequentialRoute.valid : SequentialRoute entries owners effect operation argument input annotation → Bool
  | .sequence _ operand later => quietCheck (annotationRecipe operand) && later.valid

def sequentialRoot (route : SequentialRoute entries owners effect operation argument input annotation)
    (data : Template input answer binder outerBindings clause) : Requirements [] :=
  match route with
  | .sequence _ operand later => quietRoot (annotationRecipe operand) (firstOuter later data (.request [] []) data)

theorem sequential_facets (route : SequentialRoute entries owners effect operation argument input annotation) (valid : route.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : clause.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (annotationRows annotation)
      (terminal effect (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows)
      (sequentialRoot route data) := by
  cases route with
  | sequence selected operand later =>
    obtain ⟨a,b⟩ : quietCheck (annotationRecipe operand) = true ∧ later.valid = true := by simpa [SequentialRoute.valid] using valid
    let requested := first_request_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      later b reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient)
      (annotationRecipe operand) (annotationRows operand) a (Accounting.Wait.plain requested.accounting)
    let next := route_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      later b Front.nil rfl Spent.nil reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
    exact ⟨.sequence (.sequence evaluated.certificate requested.certificate) next.certificate,
      .sequence (.sequence evaluated.checked requested.checked) next.checked,.sequence (.sequence evaluated.accounting)⟩

theorem handler_facets (route : SequentialRoute entries owners effect operation argument input annotation) (valid : route.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance)
    (supported : data.supported = true) (permission : clause.requiredActions.resume = true)
    (support : (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows.resourceSupport ⊆ ambient) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.handler (effect := effect)
        (table := (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table)
        (required := []) (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows
        (annotationRows annotation)) Context.nil (sequentialRoot route data) := by
  let declarations := CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let inside := fun activation (_fresh : activation ∉ installations) =>
    sequential_facets route (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := activation :: installations) (ambient := ambient)
      valid reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
  let certificate := SourceAdmission.Code.handler (required := []) (fun activation fresh => (inside activation fresh).certificate)
  have checked : InstallationSupport.CodeChecked ambient outward certificate := by
    apply InstallationSupport.CodeChecked.handler (supported := by simpa [SourceDependencyCapture.Scope.visibleResources] using support)
    intro activation fresh
    exact (inside activation fresh).checked
  exact ⟨certificate,checked,Accounting.Run.installHandler (fun activation fresh => (inside activation fresh).accounting)⟩

structure Result (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed residual : List Instance)
    (bindings : Bindings) (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint) (resumeEffects closeEffects : List Instance)
    (annotation : Annotation entries owners bindings code answer demand requirements plan rows)
    (route : SequentialRoute entries owners effect operation argument input annotation)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat) (budget : Footprint) (ambient : List Nat) : Type where
  original : HandlerReceipt entries policy outward owners world allowed residual .none bindings code answer demand requirements plan rows
    (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects) lexical receiver
  facets : ClauseFacets (outward := outward) (actions := fun _ => none) (budget := budget)
    (phases := OwnerPhaseTransitions.available []) (world := world) (installations := []) (ambient := ambient)
    (Rows.handler (effect := effect)
      (table := (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects).table)
      (required := []) (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects).rows rows)
    Context.nil (sequentialRoot route data)

def check (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed residual : List Instance)
    (bindings : Bindings) (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint) (resumeEffects closeEffects : List Instance)
    (annotation : Annotation entries owners bindings code answer demand requirements plan rows)
    (route : SequentialRoute entries owners effect operation argument input annotation)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat) (budget : Footprint) (ambient : List Nat) :
    Except CoreCallableFiniteHandlerAdmission.AdmissionError (Result entries policy outward owners world allowed residual bindings reference data supportBound
      ordinary protectedMode resumeEffects closeEffects annotation route lexical receiver budget ambient) :=
  ((CoreCallableFiniteHandlerSource.check annotation
    (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects)
    policy outward world allowed residual .none lexical receiver).mapError CoreCallableFiniteHandlerAdmission.AdmissionError.source).bind fun original => by
      if valid : route.valid = true then
       cases ordinary with
       | none => exact .error .unavailableOrdinary
       | some advertised =>
        exact if supported : data.supported = true then
          if permission : clause.requiredActions.resume = true then
            if bounded : CoreCallableGraphAnnotationChecks.subsetB
                (CoreCallableFiniteHandlerBodyRoutes.singleton reference data supportBound (some advertised) protectedMode resumeEffects closeEffects).rows.resourceSupport ambient = true then
              .ok ⟨original,handler_facets route valid reference data supportBound advertised protectedMode resumeEffects closeEffects
                supported permission (CoreCallableGraphAnnotationChecks.subsetB_sound bounded)⟩
            else .error .clauseSupport
          else .error .deniedResume
        else .error .unsupportedClause
      else exact .error (.source (.unsupported "body route"))

/-- Actual syntax usage/support and recursive accounting checks assemble the
same initial Program. Source requirements do not become its accounting root. -/
def checkInitial (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (owners : CoreCallableContractRegistries.Owners)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder [(parameter,argument)] clause)
    (ordinary protectedMode : Option Footprint)
    (annotation : Annotation entries owners [] code answer demand requirements plan rows)
    (route : SequentialRoute entries owners effect operation argument input annotation) (budget : Footprint) :
    Except CoreCallableFiniteHandlerAdmission.AdmissionError (CoreCallableInitialAdmission.Program
      ⟨operations entries,policy,owners⟩ (fun _ => none) budget
      (.handle (Instantiation.freezeEffect effect) code (.cons operation parameter binder clause .nil))) :=
  (check entries policy [] owners [] [] [] [] reference data [] ordinary protectedMode [] [] annotation route [] [] budget []).bind fun result => by
    if usage : usageCheck code = true then
      if permission : (policy binder).resume = true then
        if supported : data.supported = true then
          let expression := Code.handle (Instantiation.freezeEffect effect) code (.cons operation parameter binder clause .nil)
          if support : CoreCallableGraphAnnotationChecks.subsetB
              (ScopedPorts.Support.evaluate ScopedPorts.Support.empty expression.dependencies) [] = true then
            match evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
                (annotateDisposals (sequentialRoot route data)) with
            | none => exact .error .accounting
            | some row =>
              if bounded : CoreCallableGraphAnnotationChecks.subsetB row budget = true then
                exact .ok {
                  result := answer
                  dependencies := _
                  plan := .handler (effect := effect) (table := (CoreCallableFiniteHandlerBodyRoutes.singleton reference data [] ordinary protectedMode [] []).table)
                    [] (CoreCallableFiniteHandlerBodyRoutes.singleton reference data [] ordinary protectedMode [] []).plans plan
                  rows := by simpa only [signature] using
                    (Rows.handler (effect := effect) (table := (CoreCallableFiniteHandlerBodyRoutes.singleton reference data [] ordinary protectedMode [] []).table)
                      (required := []) (CoreCallableFiniteHandlerBodyRoutes.singleton reference data [] ordinary protectedMode [] []).rows rows)
                  demand := demand
                  requirements := requirements.prepend [.ordinary (.handler effect 0 (CoreCallableFiniteHandlerBodyRoutes.singleton reference data [] ordinary protectedMode [] []).table)]
                  source := by with_unfolding_all exact result.original.source
                  authenticated := by with_unfolding_all exact result.original.authenticated
                  support := SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound support)
                  usage := .handle (usage_sound code usage) (.cons (data.use supported permission) .nil)
                  certificate := by with_unfolding_all exact result.facets.certificate
                  certificateChecked := by with_unfolding_all exact result.facets.checked
                  rootDemand := []
                  root := sequentialRoot route data
                  accounting := by with_unfolding_all exact result.facets.accounting
                  annotated := sequentialRoot route data
                  annotation := .original
                  row := row
                  checked := RecursiveRequirements.evaluate_sound evaluated
                  bounded := CoreCallableGraphAnnotationChecks.subsetB_sound bounded }
              else exact .error .budget
          else exact .error .support
        else exact .error .unsupportedClause
      else exact .error .deniedResume
    else exact .error .usage


#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.root
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.wait
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.pending
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.mode
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.held
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Spent.local
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clauseLocal
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clauseOuter
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clause_retire
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clause_accounting
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clause_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Front.ticketNames
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.request_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.routeRoot
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.route_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.clauseOuter_local
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.route_local
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.firstLocal
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.firstOuter
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.first_retire
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.first_clause_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.first_request_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.SequentialRoute
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.SequentialRoute.valid
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.sequentialRoot
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.sequential_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.handler_facets
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.Result
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.check
#print axioms Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix.checkInitial
end Ash.OneShot.CoreCallableFiniteHandlerEffectfulSuffix
