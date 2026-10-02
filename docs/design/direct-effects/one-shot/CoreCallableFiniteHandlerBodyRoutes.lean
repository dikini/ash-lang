import CoreCallableFiniteHandlerAdmission
namespace Ash.OneShot.CoreCallableFiniteHandlerBodyRoutes
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

/-- Quiet instructions transform the actual continuation root, retaining choices. -/
def quietRoot (tag : RecipeTag plan) (tail : Requirements demand) : Requirements demand :=
  match tag with
  | .sequence first second => quietRoot first (quietRoot second tail)
  | .choice first second => .choice (quietRoot first tail) (quietRoot second tail) (.refl demand)
  | _ => tail

 theorem quiet_local (tag : RecipeTag plan)
    (binding : LocalOwner owner before localRoot outerRoot after) :
    LocalOwner owner before (quietRoot tag localRoot) (quietRoot tag outerRoot) after := by
  induction tag generalizing localRoot outerRoot with
  | sequence first second ihF ihS => exact ihF (ihS binding)
  | choice first second ihF ihS => exact .choice (ihF binding) (ihS binding)
  | pure | request | invoke | cleanup | unsupported => exact binding

theorem quiet_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} (tag : RecipeTag plan) (rows : Rows (signature plan))
    (valid : quietCheck tag = true)
    (waiting : Accounting.Wait world installations context .ordinary tail) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      rows context (quietRoot tag tail) := by
  induction tag generalizing scope hints context tail with
  | pure => cases rows; exact ⟨.pure,.pure,.pure waiting⟩
  | sequence first second ihF ihS =>
    cases rows with
    | sequence firstRows secondRows =>
      obtain ⟨a,b⟩ : quietCheck first = true ∧ quietCheck second = true := by simpa [quietCheck] using valid
      let right := ihS secondRows b waiting
      let left := ihF firstRows a (Accounting.Wait.plain right.accounting)
      exact ⟨.sequence left.certificate right.certificate,.sequence left.checked right.checked,.sequence left.accounting⟩
  | choice first second ihF ihS =>
    cases rows with
    | choice firstRows secondRows =>
      obtain ⟨a,b⟩ : quietCheck first = true ∧ quietCheck second = true := by simpa [quietCheck] using valid
      let left := ihF firstRows a waiting
      let right := ihS secondRows b waiting
      exact ⟨.choice left.certificate right.certificate,.choice left.checked right.checked,
        .choice left.accounting right.accounting (.refl _)⟩
  | request | invoke | cleanup | unsupported => cases valid

/-- Internal saved-row instructions are computed by the routing interpreter. -/
inductive Front : {scope : SourceDependencyCapture.Scope} → {hints : SourceDependencyChecks.Lexical.ReturnHints scope} → Context hints → Type where
  | nil : Front Context.nil
  | plain (tag : RecipeTag plan) (rows : Rows (signature plan)) (rest : Front context) : Front (Context.plain rows context)

def Front.valid : Front context → Bool
  | .nil => true
  | .plain tag _ rest => quietCheck tag && rest.valid

def Front.root (front : Front context) (tail : Requirements demand) : Requirements demand :=
  match front with
  | .nil => tail
  | .plain tag _ rest => quietRoot tag (rest.root tail)

theorem Front.local (front : Front context) (binding : LocalOwner owner before localRoot outerRoot after) :
    LocalOwner owner before (front.root localRoot) (front.root outerRoot) after := by
  induction front generalizing localRoot outerRoot with
  | nil => exact binding
  | plain tag rows rest ih => exact quiet_local tag (ih binding)

theorem Front.wait (front : Front context) (valid : front.valid = true)
    (waiting : Accounting.Wait world installations outside .ordinary tail) :
    Accounting.Wait world installations (context.append outside) .ordinary (front.root tail) := by
  induction front with
  | nil => exact waiting
  | plain tag rows rest ih =>
    obtain ⟨a,b⟩ : quietCheck tag = true ∧ rest.valid = true := by simpa [Front.valid] using valid
    exact .plain (quiet_facets (outward := []) (actions := fun _ => none) (budget := []) (phases := fun _ => .available) (ambient := []) tag rows a (ih b)).accounting

structure PendingFacets (outward : List Instance) (actions : Syntax.UsageTickets) (budget : Footprint)
    (phases : OwnerPhaseTransitions.Phases) (world installations ambient : List Nat)
    (context : Context hints) : Prop where
  pending : SourceAdmission.Pending outward actions budget phases world installations context Context.nil .ordinary .ordinary
  checked : InstallationSupport.PendingChecked ambient outward pending

theorem Front.pending (front : Front context) (valid : front.valid = true)
    (outsideReady : PendingFacets outward actions budget phases world installations ambient outside)
    (waiting : Accounting.Wait world installations outside .ordinary tail) :
    PendingFacets outward actions budget phases world installations ambient (context.append outside) := by
  induction front with
  | nil => exact outsideReady
  | plain tag rows rest ih =>
    obtain ⟨a,b⟩ : quietCheck tag = true ∧ rest.valid = true := by simpa [Front.valid] using valid
    let next := ih b
    let code := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (ambient := ambient) tag rows a (rest.wait b waiting)
    exact ⟨.plain (code.certificate.reindex_context (Context.append_nil_pack _).symm) next.pending,
      .plain (code.checked.reindex_context (Context.append_nil_pack _).symm) next.checked⟩

theorem wait_reindex (waiting : Accounting.Wait world installations context mode root)
    (same : context.pack = next.pack) : Accounting.Wait world installations next mode root := by
  change Accounting.Wait world installations context.pack.context mode root at waiting
  rw [same] at waiting
  exact waiting

theorem Front.return_mode (front : Front context) (outside : Context hints) :
    (context.append outside).pack.hints.returnMode mode = outside.pack.hints.returnMode mode := by
  induction front with
  | nil => rfl
  | plain tag rows rest ih => exact ih

theorem Front.hint_mode {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} (front : Front context) (outside : SourceDependencyChecks.Lexical.ReturnHints outsideScope) :
    (hints.append outside).returnMode mode = outside.returnMode mode := by
  induction front with
  | nil => rfl
  | plain tag rows rest ih => exact ih

theorem Front.held (front : Front context) (outside : Context hints) :
    (context.append outside).pack.scope.held = outside.pack.scope.held := by
  induction front with
  | nil => rfl
  | plain tag rows rest ih => exact ih

theorem Front.selection {tailScope : SourceDependencyCapture.Scope} {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope} {tail : Context tailHints} (front : Front context)
    (found : select effect operation outside = some (.handler captured.pack tail.pack contract modes)) :
    select effect operation (context.append outside) = some (.handler (context.append captured).pack tail.pack contract modes) := by
  induction front with
  | nil => exact found
  | plain tag rows rest ih => simpa [Context.append,select,Selection.prepend,Context.pack,SourceDependencyCapture.Scope.append,SourceDependencyChecks.Lexical.ReturnHints.append] using (congrArg
      (Option.map (Selection.prepend (fun p : Packed => (Context.plain rows p.context).pack))) ih)

theorem Front.terminal (front : Front context) :
    TerminalHandler effect activation declarations (context.append (terminal effect table activation declarations)) := by
  induction front with
  | nil => exact .here
  | plain tag rows rest ih => exact .plain ih

def clauseRoot (front : Front context) : Template input answer binder bindings code → Requirements []
  | .resume _ => .sequence (.request [] []) (front.root (.sequence (.request [] []) (.request [] [])))
  | .bind _ body => clauseRoot front body
  | .branch _ yes no => .choice (clauseRoot front yes) (clauseRoot front no) (.refl [])
  | .unsupported _ => .request [] []
def clauseLocal (front : Front context) (owner : Nat) : Template input answer binder bindings code → Requirements [owner]
  | .resume _ => .sequence (.retire owner) (front.root (.sequence (.spent owner) (.request [] [])))
  | .bind _ body => clauseLocal front owner body
  | .branch _ yes no => .choice (clauseLocal front owner yes) (clauseLocal front owner no) (.refl [owner])
  | .unsupported _ => .retire owner

theorem clause_retire (front : Front context) (data : Template input answer binder bindings code)
    (supported : data.supported = true) :
    LocalOwner owner .available (clauseLocal front owner data) (clauseRoot front data) .consumed := by
  induction data with
  | resume operand => exact .sequence .retireSelf (front.local (.sequence .spentSelf .empty))
  | bind operand body ih => exact ih supported
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .choice (ihY y) (ihN n)
  | unsupported reason => cases supported

theorem clause_accounting (front : Front context) (valid : front.valid = true)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) :
    Accounting.Run world installations (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand)
        (context.append (terminal effect table activation declarations)) Context.nil)
      (clauseLocal front owner data) := by
  induction data with
  | resume operand =>
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.resume (front := Context.nil)
    · exact .hit
    · exact wait_reindex (front.wait valid (Accounting.Wait.handler (Accounting.Wait.spent Accounting.Wait.nil)))
        (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) Context.nil)).symm
  | bind operand body ih => exact .sequence (.pure (.plain (ih supported)))
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    exact .sequence (.pure (.plain (.choice (ihY y) (ihN n) (.refl _))))
  | unsupported reason => cases supported

theorem clause_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope} {context : Context hints} {rights : Syntax.OneShotRights} {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (front : Front context) (valid : front.valid = true)
    (data : Template input answer binder bindings code) (supported : data.supported = true)
    (declarations : ClauseRows signatures) (permission : rights.resume = true) :
    ClauseFacets (outward := outward) (actions := actions.insert owner rights)
      (phases := OwnerPhaseTransitions.introduce phases owner) (budget := budget) (ambient := ambient)
      (world := world) (installations := installations) (data.rows owner)
      (Context.live (owner := owner) (resumeDemand := resumeDemand)
        (context.append (terminal effect table activation declarations)) Context.nil)
      (clauseLocal front owner data) := by
  induction data with
  | resume operand =>
    let outsideReady : PendingFacets outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner) world installations ambient
        ((terminal effect table activation declarations).append (.spent (owner := owner) Context.nil)) :=
      ⟨.handler (.spent .nil),.handler (.spent .nil)⟩
    let pending := front.pending valid outsideReady (Accounting.Wait.handler (Accounting.Wait.spent Accounting.Wait.nil))
    let restored := pending.pending.reindex_context
      (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) Context.nil)).symm
    have restoredChecked : InstallationSupport.PendingChecked ambient outward restored :=
      pending.checked.reindex_context (context.append_assoc_pack (terminal effect table activation declarations) (.spent (owner := owner) Context.nil)).symm
    have mode : (hints.append (terminal effect table activation declarations).pack.hints).returnMode .ordinary = .ordinary :=
      front.hint_mode _
    dsimp only [terminal,Context.pack] at mode
    let resume : SourceAdmission.Code outward (actions.insert owner rights) budget
        (OwnerPhaseTransitions.introduce phases owner) world installations (Rows.invoke (key := ⟨owner,.resume⟩))
        (Context.live (owner := owner) (resumeDemand := resumeDemand)
          (context.append (terminal effect table activation declarations)) Context.nil) :=
      .resume (front := Context.nil) .hit (by simp [Syntax.UsageTickets.insert]) permission
        (by simp [OwnerPhaseTransitions.introduce]) (by rw [mode]; rfl)
        (by simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode] using restored)
    have checkedResume : InstallationSupport.CodeChecked ambient outward resume := by
      apply InstallationSupport.CodeChecked.resume (front := Context.nil)
        (captured := context.append (terminal effect table activation declarations)) (tail := Context.nil)
        (resumeDemand := resumeDemand) (rights := rights) (located := .hit)
        (known := by simp [Syntax.UsageTickets.insert]) (permission := permission)
        (available := by simp [OwnerPhaseTransitions.introduce]) (resumeShape := by rw [mode]; rfl)
        (restored := by simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode] using restored)
      simpa only [SourceDependencyChecks.Lexical.ReturnHints.append,SourceDependencyChecks.Lexical.ReturnHints.returnMode,SourceDependencyCapture.Scope.append,Context.append,mode] using restoredChecked
    exact ⟨.sequence .pure resume,.sequence .pure checkedResume,
      clause_accounting front valid (.resume operand) supported declarations⟩
  | bind operand body ih =>
    let b := ih supported
    exact ⟨.sequence .pure b.certificate,.sequence .pure b.checked,
      clause_accounting front valid (.bind operand body) supported declarations⟩
  | branch condition yes no ihY ihN =>
    obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by simpa [Template.supported] using supported
    let a := ihY y
    let b := ihN n
    exact ⟨.sequence .pure (.choice a.certificate b.certificate),.sequence .pure (.choice a.checked b.checked),
      clause_accounting front valid (.branch condition yes no) supported declarations⟩
  | unsupported reason => cases supported

/-- Full operation input and handler answer are separate original contracts. -/
def singleton (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) :
    Declarations entries effect answer bindings (.cons operation parameter binder code .nil) :=
  .cons reference data supportBound ordinary protectedMode resumeEffects closeEffects .nil

theorem request_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (front : Front context) (valid : front.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : code.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.request (effect := effect) (operation := operation))
      (context.append (terminal effect (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows))
      (clauseRoot front data) := by
  let declarations := singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let base := terminal effect declarations.table activation declarations.rows
  let captured := context.append base
  have baseCut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation base base Context.nil
      ⟨false,some ordinary,protectedMode⟩ (some data.dependencies,modeFamily data protectedMode) := by
    simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut,base,terminal,select,declarations,singleton,Declarations.table,Declarations.families,
      ProtectionContracts.lookup,SourceDependencyCapture.lookupDependencies,modeFamily]
  have cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation captured captured Context.nil
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
    simp [declarations,singleton,Declarations.plans,clauseSignatures,SourceAdmission.rightsAt]
  have guard : SourceDependencyChecks.Lexical.Capture _ effect operation :=
    .handler cut.select_sound (by rw [held]; rfl) (by rw [held]; rfl) (by rw [held]; rfl)
  let retained := front.pending valid (⟨.handler .nil,.handler .nil⟩ :
    PendingFacets outward actions budget phases world installations ambient base) (Accounting.Wait.handler Accounting.Wait.nil)
  have mode : (hints.append base.pack.hints).returnMode .ordinary = .ordinary := front.hint_mode _
  dsimp only [base,terminal,Context.pack] at mode
  let waiting : SourceAdmission.Pending outward actions budget phases world installations captured Context.nil
      .ordinary ((hints.append base.pack.hints).returnMode .ordinary) := by
    simpa only [captured,base,terminal,Context.pack,mode] using retained.pending
  have waitingChecked : InstallationSupport.PendingChecked ambient outward waiting := by
    simpa only [captured,base,terminal,Context.pack,mode] using retained.checked
  have callbacks : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceAdmission.Pending outward actions budget phases world installations captured (.closing Context.nil) .unwind .unwind := by
    intro impossible; cases impossible
  have ownerBound : (⟨false,some ordinary,protectedMode⟩ : ClauseContract).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope := by
    intro impossible; cases impossible
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ captured.ticketNames) =>
    (clause_facets (owner := owner) (resumeDemand := resumeDemand) (effect := effect)
      (table := declarations.table) (activation := activation) (outward := outward)
      (actions := actions) (budget := budget) (phases := phases) (world := world)
      (installations := installations) (ambient := ambient) front valid data supported declarations.rows permission).certificate
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
        (installations := installations) (ambient := ambient) front valid data supported declarations.rows permission).checked
  exact ⟨certificate,checked,.request cut selected
    (fun owner resumeDemand _absent => clause_accounting (owner := owner) (resumeDemand := resumeDemand) front valid data supported declarations.rows)
    (fun owner _resumeDemand _absent => clause_retire front data supported)⟩

/-- Instructions select the SAME original Annotation. Quiet checks are executed,
not proof fields. Body-local bindings remain distinct from declaration bindings. -/
inductive Route (entries : OperationEntries) (owners : CoreCallableContractRegistries.Owners)
    (effect : Instance) (operation : Nat) (argument input : Contract) :
    {bindings : Bindings} → {code : Code} → {answer : Contract} → {demand : List Nat} →
    {requirements : Requirements demand} → {dependencies : Dependencies} → {plan : Plan dependencies} →
    {rows : Rows (signature plan)} → Annotation entries owners bindings code answer demand requirements plan rows → Type where
  | quiet (annotation : Annotation entries owners bindings code answer demand requirements plan rows) : Route entries owners effect operation argument input annotation
  | request (reference : OperationRef entries effect operation argument input)
      (operand : Annotation entries owners bindings value argument demand requirements plan rows) :
      Route entries owners effect operation argument input (.perform reference operand)
  | prefix {bodyAnnotation : Annotation entries owners ((parameter,first) :: bindings) bodyCode answer bodyDemand bodyReq bodyPlan bodyRows}
      (initial : Annotation entries owners bindings value first firstDemand firstReq firstPlan firstRows)
      (body : Route entries owners effect operation argument input bodyAnnotation) :
      Route entries owners effect operation argument input (Annotation.bind (parameter := parameter) initial bodyAnnotation)
  | suffix {initialAnnotation : Annotation entries owners bindings initialCode first initialDemand initialReq initialPlan initialRows}
      (initial : Route entries owners effect operation argument input initialAnnotation)
      (body : Annotation entries owners ((parameter,first) :: bindings) code answer demand requirements plan rows) :
      Route entries owners effect operation argument input (Annotation.bind initialAnnotation body)
  | branch {yesAnnotation : Annotation entries owners bindings yesCode answer yesDemand yesReq yesPlan yesRows}
      {noAnnotation : Annotation entries owners bindings noCode answer noDemand noReq noPlan noRows}
      (condition : Annotation entries owners bindings test .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (yes : Route entries owners effect operation argument input yesAnnotation)
      (no : Route entries owners effect operation argument input noAnnotation) (same : DemandPermutation yesDemand noDemand) :
      Route entries owners effect operation argument input (Annotation.branch condition yesAnnotation noAnnotation same)

def Route.valid : Route entries owners effect operation argument input annotation → Bool
  | .quiet annotation => quietCheck (annotationRecipe annotation)
  | .request _ operand => quietCheck (annotationRecipe operand)
  | .prefix initial body => quietCheck (annotationRecipe initial) && body.valid
  | .suffix initial body => initial.valid && quietCheck (annotationRecipe body)
  | .branch condition yes no _ => quietCheck (annotationRecipe condition) && yes.valid && no.valid

def annotationRows (_annotation : Annotation entries owners bindings code contract demand requirements plan rows) :
    Rows (signature plan) := rows

def Route.root (front : Front context) (data : Template input answer binder outerBindings clause) :
    Route entries owners effect operation argument input annotation → Requirements []
  | .quiet annotation => quietRoot (annotationRecipe annotation) (front.root (.request [] []))
  | .request _ operand => quietRoot (annotationRecipe operand) (clauseRoot front data)
  | .prefix initial body => quietRoot (annotationRecipe initial) (body.root front data)
  | .suffix initial body => initial.root (.plain (annotationRecipe body) (annotationRows body) front) data
  | .branch condition yes no _ => quietRoot (annotationRecipe condition)
      (.choice (yes.root front data) (no.root front data) (.refl []))

theorem Route.facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (route : Route entries owners effect operation argument input annotation) (valid : route.valid = true)
    (front : Front context) (frontValid : front.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: outerBindings) clause)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance) (activation : Nat)
    (supported : data.supported = true) (permission : clause.requiredActions.resume = true) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (annotationRows annotation)
      (context.append (terminal effect (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table
        activation (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows))
      (route.root front data) := by
  induction route generalizing scope hints context with
  | quiet annotation =>
    exact quiet_facets (annotationRecipe annotation) (annotationRows annotation) valid
      (front.wait frontValid (Accounting.Wait.handler Accounting.Wait.nil))
  | request selected operand =>
    let requested := request_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient) front frontValid reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe operand) (annotationRows operand) valid (Accounting.Wait.plain requested.accounting)
    exact ⟨.sequence evaluated.certificate requested.certificate,.sequence evaluated.checked requested.checked,
      .sequence evaluated.accounting⟩
  | «prefix» initial body ih =>
    obtain ⟨a,b⟩ : quietCheck (annotationRecipe initial) = true ∧ body.valid = true := by simpa [Route.valid] using valid
    let next := ih b front frontValid
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe initial) (annotationRows initial) a (Accounting.Wait.plain next.accounting)
    exact ⟨.sequence evaluated.certificate next.certificate,.sequence evaluated.checked next.checked,.sequence evaluated.accounting⟩
  | suffix initial body ih =>
    obtain ⟨a,b⟩ : initial.valid = true ∧ quietCheck (annotationRecipe body) = true := by simpa [Route.valid] using valid
    have v : (Front.plain (annotationRecipe body) (annotationRows body) front).valid = true := by simp [Front.valid,b,frontValid]
    let next := ih a (.plain (annotationRecipe body) (annotationRows body) front) v
    let suffix := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations)
      (context := context.append (terminal effect
        (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table activation
        (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows))
      (ambient := ambient) (annotationRecipe body) (annotationRows body) b (front.wait frontValid (Accounting.Wait.handler Accounting.Wait.nil))
    exact ⟨.sequence next.certificate suffix.certificate,.sequence next.checked suffix.checked,.sequence next.accounting⟩
  | branch condition yes no same ihY ihN =>
    obtain ⟨⟨c,y⟩,n⟩ : (quietCheck (annotationRecipe condition) = true ∧ yes.valid = true) ∧ no.valid = true := by simpa [Route.valid] using valid
    let left := ihY y front frontValid
    let right := ihN n front frontValid
    let choice := Accounting.Run.choice left.accounting right.accounting (.refl [])
    let evaluated := quiet_facets (outward := outward) (actions := actions) (budget := budget) (phases := phases) (ambient := ambient) (annotationRecipe condition) (annotationRows condition) c (Accounting.Wait.plain choice)
    exact ⟨.sequence evaluated.certificate (.choice left.certificate right.certificate),
      .sequence evaluated.checked (.choice left.checked right.checked),.sequence evaluated.accounting⟩

theorem handler_facets (route : Route entries owners effect operation argument input annotation) (valid : route.valid = true)
    (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary : Footprint) (protectedMode : Option Footprint)
    (resumeEffects closeEffects : List Instance)
    (supported : data.supported = true) (permission : clause.requiredActions.resume = true)
    (support : (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows.resourceSupport ⊆ ambient) :
    ClauseFacets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (ambient := ambient)
      (Rows.handler (effect := effect)
        (table := (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).table)
        (required := []) (singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects).rows
        (annotationRows annotation)) Context.nil (route.root Front.nil data) := by
  let declarations := singleton reference data supportBound (some ordinary) protectedMode resumeEffects closeEffects
  let inside := fun activation (_fresh : activation ∉ installations) =>
    route.facets (outward := outward) (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := activation :: installations) (ambient := ambient)
      valid Front.nil rfl reference data supportBound ordinary protectedMode resumeEffects closeEffects activation supported permission
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
    (route : Route entries owners effect operation argument input annotation)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat) (budget : Footprint) (ambient : List Nat) : Type where
  original : HandlerReceipt entries policy outward owners world allowed residual .none bindings code answer demand requirements plan rows
    (singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects) lexical receiver
  facets : ClauseFacets (outward := outward) (actions := fun _ => none) (budget := budget)
    (phases := OwnerPhaseTransitions.available []) (world := world) (installations := []) (ambient := ambient)
    (Rows.handler (effect := effect)
      (table := (singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects).table)
      (required := []) (singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects).rows rows)
    Context.nil (route.root Front.nil data)

def check (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed residual : List Instance)
    (bindings : Bindings) (reference : OperationRef entries effect operation argument input)
    (data : Template input answer binder ((parameter,argument) :: bindings) clause)
    (supportBound : List Nat) (ordinary protectedMode : Option Footprint) (resumeEffects closeEffects : List Instance)
    (annotation : Annotation entries owners bindings code answer demand requirements plan rows)
    (route : Route entries owners effect operation argument input annotation)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat) (budget : Footprint) (ambient : List Nat) :
    Except CoreCallableFiniteHandlerAdmission.AdmissionError (Result entries policy outward owners world allowed residual bindings reference data supportBound
      ordinary protectedMode resumeEffects closeEffects annotation route lexical receiver budget ambient) :=
  ((CoreCallableFiniteHandlerSource.check annotation
    (singleton reference data supportBound ordinary protectedMode resumeEffects closeEffects)
    policy outward world allowed residual .none lexical receiver).mapError CoreCallableFiniteHandlerAdmission.AdmissionError.source).bind fun original => by
      if valid : route.valid = true then
       cases ordinary with
       | none => exact .error .unavailableOrdinary
       | some advertised =>
        exact if supported : data.supported = true then
          if permission : clause.requiredActions.resume = true then
            if bounded : CoreCallableGraphAnnotationChecks.subsetB
                (singleton reference data supportBound (some advertised) protectedMode resumeEffects closeEffects).rows.resourceSupport ambient = true then
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
    (route : Route entries owners effect operation argument input annotation) (budget : Footprint) :
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
                (annotateDisposals (route.root Front.nil data)) with
            | none => exact .error .accounting
            | some row =>
              if bounded : CoreCallableGraphAnnotationChecks.subsetB row budget = true then
                exact .ok {
                  result := answer
                  dependencies := _
                  plan := .handler (effect := effect) (table := (singleton reference data [] ordinary protectedMode [] []).table)
                    [] (singleton reference data [] ordinary protectedMode [] []).plans plan
                  rows := by simpa only [signature] using
                    (Rows.handler (effect := effect) (table := (singleton reference data [] ordinary protectedMode [] []).table)
                      (required := []) (singleton reference data [] ordinary protectedMode [] []).rows rows)
                  demand := demand
                  requirements := requirements.prepend [.ordinary (.handler effect 0 (singleton reference data [] ordinary protectedMode [] []).table)]
                  source := by with_unfolding_all exact result.original.source
                  authenticated := by with_unfolding_all exact result.original.authenticated
                  support := SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound support)
                  usage := .handle (usage_sound code usage) (.cons (data.use supported permission) .nil)
                  certificate := by with_unfolding_all exact result.facets.certificate
                  certificateChecked := by with_unfolding_all exact result.facets.checked
                  rootDemand := []
                  root := route.root Front.nil data
                  accounting := by with_unfolding_all exact result.facets.accounting
                  annotated := route.root Front.nil data
                  annotation := .original
                  row := row
                  checked := RecursiveRequirements.evaluate_sound evaluated
                  bounded := CoreCallableGraphAnnotationChecks.subsetB_sound bounded }
              else exact .error .budget
          else exact .error .support
        else exact .error .unsupportedClause
      else exact .error .deniedResume
    else exact .error .usage

#print axioms quietRoot
#print axioms quiet_local
#print axioms quiet_facets
#print axioms Front.local
#print axioms Front.wait
#print axioms Front.pending
#print axioms Front.selection
#print axioms clause_retire
#print axioms clause_accounting
#print axioms clause_facets
#print axioms request_facets
#print axioms Route.valid
#print axioms Route.root
#print axioms Route.facets
#print axioms handler_facets
#print axioms check
#print axioms checkInitial
end Ash.OneShot.CoreCallableFiniteHandlerBodyRoutes
