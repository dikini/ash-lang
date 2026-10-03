import CoreCallableStaticFiniteData
import ClauseRowContracts
namespace Ash.OneShot.CoreCallableFiniteClauseTemplate
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Owners OwnerContract)
open CoreCallableContractAdmission CoreCallableStaticProducer
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- Finite stable operands preserve the whole original slot Contract. No owner
literal or source/checking proof is an operand instruction. -/
inductive Pure : Bindings → Code → Contract → Type where
  | unit : Pure bindings .unit .unit
  | boolean (value : Bool) : Pure bindings (.boolean value) .boolean
  | integer (value : Int) : Pure bindings (.integer value) .integer
  | variable (reference : BindingRef bindings name contract) : Pure bindings (.variable name) contract
  | pair (left : Pure bindings a first) (right : Pure bindings b second) :
      Pure bindings (.pair a b) (.pair first second)

/-- Universal source/authentication is output of the finite structural check.
Changing the current owner does not change a stable operand's full slots. -/
structure PureReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (bindings : Bindings) (code : Code) (contract : Contract)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : ∀ owners scope, IndexedSource (registry entries policy) outward owners world allowed scope
    (environment bindings) code contract [] (.request [] []) .pure Rows.pure
  authenticated : ∀ owners scope, Authenticated (registry entries policy) outward
    (source owners scope) lexical receiver

def finishPure
    (source : ∀ owners scope, IndexedSource (registry entries policy) outward owners world allowed scope
      (environment bindings) code contract [] (.request [] []) .pure Rows.pure)
    (hereditary : ∀ owners scope, Hereditary (registry entries policy) outward (source owners scope) lexical receiver) :
    Except Error (PureReceipt entries policy outward world allowed bindings code contract lexical receiver) :=
  if _issued : CoreCallableGraphAnnotationChecks.subsetB receiver world = true then
    if valid : CoreCallableGraphAnnotationChecks.subsetB
        (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true then
      .ok ⟨source, fun owners scope => .checked
        (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound valid))
        (hereditary owners scope)⟩
    else .error .support
  else .error .unissuedPort

def Pure.check (data : Pure bindings code contract) (entries : OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (PureReceipt entries policy outward world allowed bindings code contract lexical receiver) :=
  match data with
  | .unit => finishPure (fun _ _ => .unit) (fun _ _ => .unit)
  | .boolean _ => finishPure (fun _ _ => .boolean) (fun _ _ => .boolean)
  | .integer _ => finishPure (fun _ _ => .integer) (fun _ _ => .integer)
  | @Pure.variable bindings name contract reference =>
    if located : reference.check = true then
      if formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true then
        if known : CoreCallableGraphAnnotationChecks.knownB lexical [.variable name] = true then
          finishPure (fun _ _ => .variable (reference.sound located)
            (CoreCallableGraphAnnotationChecks.subsetB_sound formed))
            (fun _ _ => .variable (known := reference.sound located)
              (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed)
              (CoreCallableGraphAnnotationChecks.knownB_sound known name (by simp)))
        else .error .missingLexicalSupport
      else .error .unissuedPort
    else .error .lexicalShadowing
  | .pair left right => do
    let a ← left.check entries policy outward world allowed lexical receiver
    let b ← right.check entries policy outward world allowed lexical receiver
    finishPure (fun owners scope => .purePair (a.source owners scope) (b.source owners scope))
      (fun owners scope => .purePair (a.authenticated owners scope) (b.authenticated owners scope))

/-- Exactly one current-owner resume on every path. Prefix and branch are
finite syntax; left-available, double-use and escaping capture instructions
have no constructive case and remain named producer failures. -/
inductive Template (input answer : Contract) (binder : Nat) : Bindings → Code → Type where
  | resume (operand : Pure bindings value input) : Template input answer binder bindings (.resume binder value)
  | bind (initial : Pure bindings value contract)
      (body : Template input answer binder ((parameter,contract) :: bindings) code) :
      Template input answer binder bindings (.bind parameter value code)
  | branch (condition : Pure bindings test .boolean)
      (yes : Template input answer binder bindings a) (no : Template input answer binder bindings b) :
      Template input answer binder bindings (.branch test a b)
  | unsupported (reason : String) : Template input answer binder bindings code

def Template.dependencies (data : Template input answer binder bindings code) (owner : Nat) : Dependencies :=
  match data with
  | .resume _ => .sequence .pure (.invoke ⟨owner,.resume⟩)
  | .bind _ body => .sequence .pure (body.dependencies owner)
  | .branch _ yes no => .sequence .pure (.choice (yes.dependencies owner) (no.dependencies owner))
  | .unsupported _ => .pure

def Template.plan (data : Template input answer binder bindings code) (owner : Nat) : Plan (data.dependencies owner) :=
  match data with
  | .resume _ => .sequence .pure (.invoke (key := ⟨owner,.resume⟩))
  | .bind _ body => .sequence .pure (body.plan owner)
  | .branch _ yes no => .sequence .pure (.choice (yes.plan owner) (no.plan owner))
  | .unsupported _ => .pure

def Template.rows (data : Template input answer binder bindings code) (owner : Nat) : Rows (signature (data.plan owner)) :=
  match data with
  | .resume _ => sequenceRows Rows.pure Rows.invoke
  | .bind _ body => sequenceRows Rows.pure (body.rows owner)
  | .branch _ yes no => sequenceRows Rows.pure (choiceRows (yes.rows owner) (no.rows owner))
  | .unsupported _ => Rows.pure

def Template.demand (_data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract) : List Nat :=
  owner :: contract.resumeDemand

def Template.requirements (data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract) :
    Requirements (data.demand owner contract) :=
  match data with
  | .resume _ => .sequence (.request [] []) (.invoke ⟨owner,.resume⟩ contract.resumeDemand [])
  | .bind _ body => .sequence (.request [] []) (body.requirements owner contract)
  | .branch _ yes no => .sequence (.request [] [])
      (.choice (yes.requirements owner contract) (no.requirements owner contract) (.refl _))
  | .unsupported _ => .invoke ⟨owner,.resume⟩ contract.resumeDemand []

/-- Row derivations are reconstructed pointwise from finite syntax, including
actual protected generation of the SAME requirement tree. -/
theorem Template.normal {operations : CoherentSourceTypes.Operations} (data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract)
    (disposes : Bool) (advertised : Footprint) :
    ClauseRowAdmission.Rows ⟨owner,contract.lower,disposes,advertised⟩ (data.requirements owner contract)
      (ClauseRowAdmission.SourceStore operations owner contract.lower) :=
  match data with
  | .resume _ => ClauseRowAdmission.resume_rows
  | .bind _ body => (body.normal owner contract disposes advertised).pure_prefix
  | .branch _ yes no =>
      ((yes.normal owner contract disposes advertised).alternatives
        (no.normal owner contract disposes advertised) (.refl _)).pure_prefix
  | .unsupported _ => by
      intro store tail before requestRow interface _exported
      have checked := interface.resume
      obtain ⟨calls,derived,supplied⟩ := ContextualClauseChecks.open_checked checked
      exact ⟨contract.lower.resumeRow,calls,derived,supplied,List.subset_append_right _ _⟩

theorem Template.protectedRows {operations : CoherentSourceTypes.Operations} (data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract)
    (disposes : Bool) (advertised : Footprint) :
    ClauseRowAdmission.ProtectedRows ⟨owner,contract.lower,disposes,advertised⟩ (data.requirements owner contract)
      (ClauseRowAdmission.SourceStore operations owner contract.lower) :=
  match data with
  | .resume _ => ClauseRowAdmission.protected_resume_rows
  | .bind _ body => (body.protectedRows owner contract disposes advertised).pure_prefix
  | .branch _ yes no =>
      ((yes.protectedRows owner contract disposes advertised).alternatives
        (no.protectedRows owner contract disposes advertised) (.refl _)).pure_prefix
  | .unsupported _ => by
      intro store tail before requestRow interface _exported
      have checked := interface.toInterface.resume
      obtain ⟨calls,derived,supplied⟩ := ContextualClauseChecks.open_checked checked
      exact ⟨contract.lower.resumeRow,calls,derived,supplied,List.subset_append_right _ _⟩

/-- Finite current-ticket state interpreter on original Code. Unsupported
nested handlers are rejected explicitly; closures recheck under the empty
capability barrier. Its successful supported-template output is paired with
Template.use, never used as a standalone permission theorem. -/
def currentUse (policy : Syntax.TicketPolicy) (scope : Syntax.UseScope) (before : Syntax.UseState) (code : Code) : Option Syntax.UseState :=
  match code with
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ => some before
  | .pair first second | .app first second | .bind _ first second | .resource _ first second | .cleanup first second => do
      let middle ← currentUse policy scope before first
      currentUse policy scope middle second
  | .perform _ _ operand => currentUse policy scope before operand
  | .branch condition yes no => do
      let middle ← currentUse policy scope before condition
      let left ← currentUse policy scope middle yes
      let right ← currentUse policy scope middle no
      if left == right then some left else none
  | .lambda _ body => do
      let after ← currentUse policy .none .available body
      if after == .available then some before else none
  | .resume binder operand =>
      match scope with
      | .none => none
      | .ticket ticket rights =>
          if binder == ticket && rights.resume then do
            let after ← currentUse policy scope before operand
            if after == .available then some .consumed else none
          else none
  | .discard binder =>
      match scope with
      | .none => none
      | .ticket ticket rights =>
          if binder == ticket && rights.dispose && before == .available then some .consumed else none
  | .handle _ _ _ => none
termination_by structural code

theorem Pure.use (data : Pure bindings code contract) : Uses policy scope state code state := by
  induction data with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => exact .variable
  | pair left right ihL ihR => exact .pair ihL ihR

def Template.supported (data : Template input answer binder bindings code) : Bool :=
  match data with
  | .resume _ => true
  | .bind _ body => body.supported
  | .branch _ yes no => yes.supported && no.supported
  | .unsupported _ => false

theorem Template.use (data : Template input answer binder bindings code) (supported : data.supported = true)
    (permission : (policy binder).resume = true) :
    Uses policy (.ticket binder (policy binder)) .available code .consumed := by
  induction data with
  | resume operand => exact .resume permission operand.use
  | bind initial body ih => exact .bind initial.use (ih supported)
  | branch condition yes no ihY ihN =>
      obtain ⟨a,b⟩ : yes.supported = true ∧ no.supported = true := by simpa only [Template.supported, Bool.and_eq_true] using supported
      exact .branch condition.use (ihY a) (ihN b)
  | unsupported reason => cases supported

theorem Template.recipe (data : Template input answer binder bindings code) (supported : data.supported = true)
    (permission : rights.resume = true) : SourcePlannedClauseRecipes.Recipe rights [] data.plan := by
  induction data with
  | resume operand => exact .silent .pure (.resume permission)
  | bind initial body ih => exact .silent .pure (ih supported)
  | branch condition yes no ihY ihN =>
      obtain ⟨a,b⟩ : yes.supported = true ∧ no.supported = true := by simpa only [Template.supported, Bool.and_eq_true] using supported
      exact .silent .pure (.choice (ihY a) (ihN b))
  | unsupported reason => cases supported

structure Specialization (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (registry entries policy) outward (owners.insert owner contract) world allowed
    (.ticket binder owner) (environment bindings) code answer (data.demand owner contract)
    (data.requirements owner contract) (data.plan owner) (data.rows owner)
  authenticated : Authenticated (registry entries policy) outward source lexical receiver

structure Receipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Template input answer binder bindings code) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  specialize : ∀ owner contract, contract.input = input → contract.answer = answer →
    contract.resumeEffects = allowed → Specialization entries policy outward owners world allowed data owner contract lexical receiver

def finishTemplate {entries : OperationEntries} {policy : Syntax.TicketPolicy}
    {outward : List Instance} {owners : Owners} {world : List Nat} {allowed : List Instance}
    {input answer : Contract} {binder : Nat} {bindings : Bindings} {code : Code}
    {data : Template input answer binder bindings code} {lexical : LexicalBounds} {receiver : List Nat}
    (source : ∀ owner contract, contract.input = input → contract.answer = answer → contract.resumeEffects = allowed →
      IndexedSource (registry entries policy) outward (owners.insert owner contract) world allowed (.ticket binder owner)
        (environment bindings) code answer (data.demand owner contract) (data.requirements owner contract) (data.plan owner) (data.rows owner))
    (hereditary : ∀ (owner : Nat) (contract : OwnerContract) (a : contract.input = input)
      (b : contract.answer = answer) (c : contract.resumeEffects = allowed), Hereditary (registry entries policy) outward (source owner contract a b c) lexical receiver) :
    Except Error (Receipt entries policy outward owners world allowed data lexical receiver) :=
  if valid : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true then
    .ok ⟨fun owner contract a b c => ⟨source owner contract a b c,
      .checked (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound valid)) (hereditary owner contract a b c)⟩⟩
  else .error .support

def Template.check (data : Template input answer binder bindings code) (entries : OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (Receipt entries policy outward owners world allowed data lexical receiver) :=
  match data with
  | .unsupported reason => .error (.unsupported reason)
  | .resume operand => do
    let value ← operand.check entries policy outward world allowed lexical receiver
    if permission : (policy binder).resume = true then
      if formed : CoreCallableGraphAnnotationChecks.subsetB answer.port.resources world = true then
        let source := fun owner (contract : OwnerContract) (a : contract.input = input) (b : contract.answer = answer) (c : contract.resumeEffects = allowed) => by
          have argument := value.source (owners.insert owner contract) (.ticket binder owner)
          rw [← a] at argument
          have result := IndexedSource.resume (registry := registry entries policy) (outward := outward)
            Owners.insert_here (by simp [Execution.Scope.resolve]) permission argument
            (by rw [c]; exact List.Subset.refl _) (by rw [b]; exact CoreCallableGraphAnnotationChecks.subsetB_sound formed)
          simpa only [b,Template.demand,Template.requirements,Template.plan,Template.rows,Template.dependencies,List.nil_append] using result
        finishTemplate source (by
          intro owner contract a b c
          cases a; cases b
          exact .resume (known := Owners.insert_here) (resolved := by simp [Execution.Scope.resolve])
            (permission := permission) (admitted := by rw [c]; exact List.Subset.refl _)
            (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed)
            (value.authenticated (owners.insert owner contract) (.ticket binder owner)))
      else .error .unissuedPort
    else .error .capability
  | .bind (parameter := parameter) initial body => do
    let first ← initial.check entries policy outward world allowed lexical receiver
    let rest ← body.check entries policy outward owners world allowed (lexical.extend parameter receiver) receiver
    finishTemplate (fun owner contract a b c =>
      .bind (first.source (owners.insert owner contract) (.ticket binder owner)) (rest.specialize owner contract a b c).source)
      (fun owner contract a b c => .bind (first.authenticated (owners.insert owner contract) (.ticket binder owner))
        (rest.specialize owner contract a b c).authenticated)
  | .branch condition yes no => do
    let test ← condition.check entries policy outward world allowed lexical receiver
    let first ← yes.check entries policy outward owners world allowed lexical receiver
    let second ← no.check entries policy outward owners world allowed lexical receiver
    finishTemplate (fun owner contract a b c =>
      .branch (test.source (owners.insert owner contract) (.ticket binder owner))
        (first.specialize owner contract a b c).source (second.specialize owner contract a b c).source (.refl _))
      (fun owner contract a b c => .branch (test.authenticated (owners.insert owner contract) (.ticket binder owner))
        (first.specialize owner contract a b c).authenticated (second.specialize owner contract a b c).authenticated)

#print axioms Pure.check
#print axioms Template.plan
#print axioms Template.rows
#print axioms Template.normal
#print axioms Template.protectedRows
#print axioms Template.check
#print axioms currentUse
#print axioms Template.use
#print axioms Template.recipe
end Ash.OneShot.CoreCallableFiniteClauseTemplate
