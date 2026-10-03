import CoreCallableSelectedOperandDomainSupport
import CoreCallableClauseActualSupport
namespace Ash.OneShot.CoreCallableSelectedDomainDeclarationTransfer
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners OwnerContract)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableClauseActualSupport CoreCallableSelectedOperandDomainSupport
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- Each original formal keeps its position and can only lose support. -/
inductive FormalNarrower : FormalSupports clauses → FormalSupports clauses → Prop where
  | nil : FormalNarrower .nil .nil
  | cons (included : small ⊆ large) (tail : FormalNarrower before after) :
      FormalNarrower (.cons large before) (.cons small after)

theorem selected_narrower (included : small ⊆ large) :
    FormalNarrower (selected clauses operation large receiver) (selected clauses operation small receiver) := by
  induction measure : sizeOf clauses using Nat.strongRecOn generalizing clauses with
  | ind measure ih =>
    cases clauses with
    | nil => exact .nil
    | cons key parameter binder body rest =>
      have tail := ih (sizeOf rest) (by simp_all; omega) (clauses := rest) rfl
      simp only [selected]
      split
      · exact .cons included tail
      · exact .cons (List.Subset.refl _) tail

/-- Presence is unchanged, including the nearest shadowing binding. -/
structure LexicalNarrower (before after : LexicalBounds) : Prop where
  presence : ∀ name, (after.lookup name).isSome = (before.lookup name).isSome
  support : ∀ name, after.environment name ⊆ before.environment name

theorem LexicalNarrower.refl (lexical : LexicalBounds) : LexicalNarrower lexical lexical :=
  ⟨fun _ => rfl,fun _ => List.Subset.refl _⟩

theorem LexicalNarrower.extend (narrower : LexicalNarrower before after) (included : small ⊆ large) :
    LexicalNarrower (before.extend name large) (after.extend name small) := by
  constructor
  · intro other
    by_cases same : other = name
    · simp [LexicalBounds.extend,LexicalBounds.lookup,same]
    · simpa [LexicalBounds.extend,LexicalBounds.lookup,same] using narrower.presence other
  · intro other
    simp only [LexicalBounds.environment_extend,ScopedPorts.Support.extend]
    split
    · exact included
    · exact narrower.support other

theorem LexicalNarrower.evaluate (narrower : LexicalNarrower before after) (dependencies : List Syntax.Dependency) :
    ScopedPorts.Support.evaluate after.environment dependencies ⊆
      ScopedPorts.Support.evaluate before.environment dependencies := by
  induction dependencies with
  | nil => exact List.Subset.refl _
  | cons dependency rest ih =>
    cases dependency with
    | «variable» name =>
      simp only [ScopedPorts.Support.evaluate,List.flatMap_cons]
      exact List.append_subset.mpr ⟨(narrower.support name).trans (List.subset_append_left _ _), ih.trans (List.subset_append_right _ _)⟩
    | resource identity =>
      simp only [ScopedPorts.Support.evaluate,List.flatMap_cons]
      exact List.append_subset.mpr ⟨List.subset_append_left _ _, ih.trans (List.subset_append_right _ _)⟩
    | ticket owner =>
      simpa only [ScopedPorts.Support.evaluate,List.flatMap_cons,List.nil_append] using ih

theorem subsetB_complete {α : Type} [DecidableEq α] {first second : List α} (included : first ⊆ second) :
    CoreCallableGraphAnnotationChecks.subsetB first second = true := by
  apply List.all_eq_true.mpr
  intro item member
  exact decide_eq_true (included member)

theorem LexicalNarrower.bounded (narrower : LexicalNarrower before after)
    (valid : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate before.environment dependencies) bound = true) :
    CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate after.environment dependencies) bound = true :=
  subsetB_complete ((narrower.evaluate dependencies).trans (CoreCallableGraphAnnotationChecks.subsetB_sound valid))

theorem LexicalNarrower.known (narrower : LexicalNarrower before after) :
    CoreCallableGraphAnnotationChecks.knownB after dependencies =
      CoreCallableGraphAnnotationChecks.knownB before dependencies := by
  unfold CoreCallableGraphAnnotationChecks.knownB
  congr 1
  funext dependency
  cases dependency <;> simp [narrower.presence]

private theorem finishPure_narrow
    {sourceBefore sourceAfter : ∀ owners scope, IndexedSource (registry entries policy) outward owners world allowed scope
      (environment bindings) code contract [] (.request [] []) .pure Rows.pure}
    {hereditaryBefore : ∀ owners scope, Hereditary (registry entries policy) outward (sourceBefore owners scope) before receiver}
    {hereditaryAfter : ∀ owners scope, Hereditary (registry entries policy) outward (sourceAfter owners scope) after receiver}
    (narrower : LexicalNarrower before after)
    (accepted : finishPure sourceBefore hereditaryBefore = .ok initial) :
    ∃ final, finishPure sourceAfter hereditaryAfter = .ok final := by
  unfold finishPure at accepted ⊢
  split at accepted
  · next issued =>
    split at accepted
    · next bounded =>
      have reduced := narrower.bounded bounded
      rw [dif_pos issued,dif_pos reduced]
      exact ⟨_,rfl⟩
    · cases accepted
  · cases accepted

theorem Pure.check_narrow (data : Pure bindings code contract)
    (narrower : LexicalNarrower before after)
    (accepted : data.check entries policy outward world allowed before receiver = .ok initial) :
    ∃ final, data.check entries policy outward world allowed after receiver = .ok final := by
  induction data generalizing before after with
  | unit => exact finishPure_narrow narrower accepted
  | boolean => exact finishPure_narrow narrower accepted
  | integer => exact finishPure_narrow narrower accepted
  | «variable» reference =>
    simp only [Pure.check] at accepted ⊢
    split at accepted
    · next located =>
      split at accepted
      · next formed =>
        split at accepted
        · next known =>
          have nextKnown := (narrower.known (dependencies := [Syntax.Dependency.variable _])).trans known
          simp only [dif_pos located,dif_pos formed,dif_pos nextKnown]
          exact finishPure_narrow narrower accepted
        · cases accepted
      · cases accepted
    · cases accepted
  | pair left right ihL ihR =>
    simp only [Pure.check] at accepted ⊢
    cases first : left.check entries policy outward world allowed before receiver with
    | error error => simp [first,bind,Except.bind] at accepted
    | ok a =>
      cases second : right.check entries policy outward world allowed before receiver with
      | error error => simp [first,second,bind,Except.bind] at accepted
      | ok b =>
        obtain ⟨nextA,afterA⟩ := ihL narrower first
        obtain ⟨nextB,afterB⟩ := ihR narrower second
        simp only [first,second,bind,Except.bind] at accepted
        simp only [afterA,afterB,bind,Except.bind]
        exact finishPure_narrow narrower accepted

private theorem finishTemplate_narrow {owners : Owners}
    {data : Template input answer binder bindings code}
    {sourceBefore sourceAfter : ∀ owner (contract : OwnerContract), contract.input = input → contract.answer = answer → contract.resumeEffects = allowed →
      IndexedSource (registry entries policy) outward (owners.insert owner contract) world allowed (.ticket binder owner)
        (environment bindings) code answer (data.demand owner contract) (data.requirements owner contract) (data.plan owner) (data.rows owner)}
    {hereditaryBefore : ∀ owner contract a b c, Hereditary (registry entries policy) outward (sourceBefore owner contract a b c) before receiver}
    {hereditaryAfter : ∀ owner contract a b c, Hereditary (registry entries policy) outward (sourceAfter owner contract a b c) after receiver}
    (narrower : LexicalNarrower before after)
    {initial : Receipt entries policy outward owners world allowed data before receiver}
    (accepted : finishTemplate sourceBefore hereditaryBefore = .ok initial) :
    ∃ final, finishTemplate sourceAfter hereditaryAfter = .ok final := by
  unfold finishTemplate at accepted ⊢
  split at accepted
  · next bounded =>
    have reduced := narrower.bounded bounded
    rw [dif_pos reduced]
    exact ⟨_,rfl⟩
  · cases accepted

theorem Template.check_narrow {owners : Owners} (data : Template input answer binder bindings code)
    (narrower : LexicalNarrower before after)
    {initialReceipt : Receipt entries policy outward owners world allowed data before receiver}
    (accepted : data.check entries policy outward owners world allowed before receiver = .ok initialReceipt) :
    ∃ final, data.check entries policy outward owners world allowed after receiver = .ok final := by
  induction data generalizing before after with
  | unsupported reason => cases accepted
  | resume operand =>
    simp only [Template.check] at accepted ⊢
    cases operandChecked : operand.check entries policy outward world allowed before receiver with
    | error error => simp [operandChecked,bind,Except.bind] at accepted
    | ok checked =>
      obtain ⟨nextValue,valueChecked⟩ := Pure.check_narrow operand narrower operandChecked
      simp only [operandChecked,bind,Except.bind] at accepted
      split at accepted
      · next permission =>
        split at accepted
        · next formed =>
          simp only [valueChecked,bind,Except.bind,dif_pos permission,dif_pos formed]
          exact finishTemplate_narrow narrower accepted
        · cases accepted
      · cases accepted
  | @bind _ _ _ parameter _ initial body ih =>
    simp only [Template.check] at accepted ⊢
    cases first : initial.check entries policy outward world allowed before receiver with
    | error error => simp [first,bind,Except.bind] at accepted
    | ok checked =>
      cases second : body.check entries policy outward owners world allowed (before.extend parameter receiver) receiver with
      | error error => simp [first,second,bind,Except.bind] at accepted
      | ok rest =>
        obtain ⟨nextFirst,afterFirst⟩ := Pure.check_narrow initial narrower first
        obtain ⟨nextRest,afterRest⟩ := ih (narrower.extend (List.Subset.refl receiver)) second
        simp only [first,second,bind,Except.bind] at accepted
        simp only [afterFirst,afterRest,bind,Except.bind]
        exact finishTemplate_narrow narrower accepted
  | branch condition yes no ihY ihN =>
    simp only [Template.check] at accepted ⊢
    cases test : condition.check entries policy outward world allowed before receiver with
    | error error => simp [test,bind,Except.bind] at accepted
    | ok testResult =>
      cases first : yes.check entries policy outward owners world allowed before receiver with
      | error error => simp [test,first,bind,Except.bind] at accepted
      | ok checkedYes =>
        cases second : no.check entries policy outward owners world allowed before receiver with
        | error error => simp [test,first,second,bind,Except.bind] at accepted
        | ok checkedNo =>
          obtain ⟨nextTest,afterTest⟩ := Pure.check_narrow condition narrower test
          obtain ⟨nextYes,afterYes⟩ := ihY narrower first
          obtain ⟨nextNo,afterNo⟩ := ihN narrower second
          simp only [test,first,second,bind,Except.bind] at accepted
          simp only [afterTest,afterYes,afterNo,bind,Except.bind]
          exact finishTemplate_narrow narrower accepted

theorem checkOffer_narrow {owners : Owners}
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (narrower : LexicalNarrower before after)
    {initialReceipt : OfferReceipt entries policy outward owners world allowed bindings parameter binder argument input answer
      resumeEffects closeEffects code held disposes row data before receiver}
    (accepted : checkOffer data entries policy outward owners world allowed resumeEffects closeEffects
      held disposes row before receiver = .ok initialReceipt) :
    ∃ final, checkOffer data entries policy outward owners world allowed resumeEffects closeEffects
      held disposes row after receiver = .ok final := by
  unfold checkOffer at accepted ⊢
  split at accepted
  · next same =>
    split at accepted
    · next noDispose =>
      cases checked : data.check entries policy outward owners world allowed before receiver with
      | error error => simp [checked,bind,Except.bind] at accepted
      | ok initial =>
        obtain ⟨final,rechecked⟩ := Template.check_narrow data narrower checked
        rw [dif_pos same,dif_pos noDispose]
        rw [rechecked]
        exact ⟨_,rfl⟩
    · cases accepted
  · cases accepted

theorem checkMode_narrow {owners : Owners}
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (narrower : LexicalNarrower before after)
    {initialReceipt : ModeReceipt entries policy outward owners world allowed bindings parameter binder argument input answer
      resumeEffects closeEffects code held disposes offered data before receiver}
    (accepted : checkMode data offered entries policy outward owners world allowed resumeEffects closeEffects
      held disposes before receiver = .ok initialReceipt) :
    ∃ final, checkMode data offered entries policy outward owners world allowed resumeEffects closeEffects
      held disposes after receiver = .ok final := by
  cases offered with
  | none => exact ⟨_,rfl⟩
  | some row =>
    simp only [checkMode] at accepted ⊢
    cases checked : checkOffer data entries policy outward owners world allowed resumeEffects closeEffects
        held disposes row before receiver with
    | error error => simp [checked,bind,Except.bind] at accepted
    | ok initial =>
      obtain ⟨final,rechecked⟩ := checkOffer_narrow data narrower checked
      rw [rechecked]
      exact ⟨_,rfl⟩

theorem checkAssignments_narrow
    (data : Declarations entries requested answer bindings clauses)
    {large small : FormalSupports clauses}
    (narrower : FormalNarrower large small)
    {initialReceipt : ReceiptAt entries policy outward owners world allowed data lexical receiver large}
    (accepted : checkAssignments data policy outward owners world allowed lexical receiver large = .ok initialReceipt) :
    ∃ final, checkAssignments data policy outward owners world allowed lexical receiver small = .ok final := by
  induction data with
  | nil => cases narrower; exact ⟨_,rfl⟩
  | @cons operation argument input binder parameter code clauses reference body supportBound ordinary protectedMode resumeEffects closeEffects rest ih =>
    cases narrower with
    | @cons _ _ _ _ smallSupport largeSupport _ beforeTail afterTail included tail =>
      simp only [checkAssignments] at accepted ⊢
      split at accepted
      · next located =>
        split at accepted
        · next useValid =>
          split at accepted
          · next supported =>
            split at accepted
            · next permission =>
              split at accepted
              · next required =>
                split at accepted
                · next noDispose =>
                  split at accepted
                  · next formalReceived =>
                    split at accepted
                    · next stored =>
                      split at accepted
                      · next bounded =>
                        have lexicalNarrower := (LexicalNarrower.refl lexical).extend (name := parameter) included
                        have nextReceived := subsetB_complete (included.trans (CoreCallableGraphAnnotationChecks.subsetB_sound formalReceived))
                        have nextBounded := lexicalNarrower.bounded bounded
                        cases checkedBody : body.check entries policy outward owners world allowed (lexical.extend parameter largeSupport) receiver with
                        | error error => simp [checkedBody,bind,Except.bind] at accepted
                        | ok bodyReceipt =>
                          cases checkedOrdinary : checkMode body ordinary entries policy outward owners world allowed resumeEffects closeEffects false false (lexical.extend parameter largeSupport) receiver with
                          | error error => simp [checkedBody,checkedOrdinary,bind,Except.bind] at accepted
                          | ok ordinaryReceipt =>
                            cases checkedProtected : checkMode body protectedMode entries policy outward owners world allowed resumeEffects closeEffects true false (lexical.extend parameter largeSupport) receiver with
                            | error error => simp [checkedBody,checkedOrdinary,checkedProtected,bind,Except.bind] at accepted
                            | ok protectedReceipt =>
                              cases checkedTail : checkAssignments rest policy outward owners world allowed lexical receiver beforeTail with
                              | error error => simp [checkedBody,checkedOrdinary,checkedProtected,checkedTail,bind,Except.bind] at accepted
                              | ok tailReceipt =>
                                obtain ⟨nextBody,afterBody⟩ := Template.check_narrow body lexicalNarrower checkedBody
                                obtain ⟨nextOrdinary,afterOrdinary⟩ := checkMode_narrow body lexicalNarrower checkedOrdinary
                                obtain ⟨nextProtected,afterProtected⟩ := checkMode_narrow body lexicalNarrower checkedProtected
                                obtain ⟨nextTail,afterTail⟩ := ih tail checkedTail
                                simp only [dif_pos located,dif_pos useValid,dif_pos supported,dif_pos permission,dif_pos required,dif_pos noDispose,
                                  dif_pos nextReceived,dif_pos stored,dif_pos nextBounded]
                                rw [afterBody]
                                dsimp only [bind,Except.bind]
                                rw [afterOrdinary]
                                dsimp only [bind,Except.bind]
                                rw [afterProtected]
                                dsimp only [bind,Except.bind]
                                rw [afterTail]
                                exact ⟨_,rfl⟩
                      · cases accepted
                    · cases accepted
                  · cases accepted
                · cases accepted
              · cases accepted
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted

/-- The selected wrapper retains complete target coverage and mode availability. -/
theorem checkSelectedDeclarations_narrow
    (data : Declarations entries requested answer bindings clauses) (included : small ⊆ large)
    {initialReceipt : ReceivingReceipt api entries policy outward owners world allowed data lexical receiver
      (selected clauses operation large receiver) operation held}
    (accepted : checkSelectedDeclarations api held data policy outward owners world allowed lexical receiver operation large = .ok initialReceipt) :
    ∃ final, checkSelectedDeclarations api held data policy outward owners world allowed lexical receiver operation small = .ok final := by
  unfold checkSelectedDeclarations at accepted
  cases coverage : CoreCallableFiniteHandlerRegistryCoverage.check api entries policy requested clauses with
  | error error => simp [coverage,bind,Except.bind] at accepted
  | ok receipt =>
    simp only [coverage,bind,Except.bind] at accepted
    split at accepted
    · next covered =>
      split at accepted
      · cases accepted
      · next contract found =>
        split at accepted
        · cases accepted
        · next row available =>
          cases checked : checkAssignments data policy outward owners world allowed lexical receiver (selected clauses operation large receiver) with
          | error error => simp [checked] at accepted
          | ok initial =>
            obtain ⟨final,rechecked⟩ := checkAssignments_narrow data (selected_narrower included) checked
            unfold checkSelectedDeclarations
            simp only [coverage,bind,Except.bind,dif_pos covered]
            split
            · next impossible => rw [found] at impossible; cases impossible
            · next nextContract nextFound =>
              have same : nextContract = contract := Option.some.inj (nextFound.symm.trans found)
              subst nextContract
              split
              · next impossible => rw [available] at impossible; cases impossible
              · next nextRow nextAvailable =>
                have same : nextRow = row := Option.some.inj (nextAvailable.symm.trans available)
                subst nextRow
                rw [rechecked]
                exact ⟨_,rfl⟩
    · cases accepted

structure SelectedDomainReceipt
    (reference : OperationRef entries requested operation argument input)
    (api : CoreCallableFiniteCellRegistry.CellApi) (held : Bool)
    (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat)
    (allowed : List Instance) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  known : operations entries requested operation = some (argument,input)
  receiving : ReceivingReceipt api entries policy outward owners world allowed data lexical receiver
    (selected clauses operation (domainSupport argument receiver) receiver) operation held

def checkSelectedDomainDeclarations
    (reference : OperationRef entries requested operation argument input)
    (api : CoreCallableFiniteCellRegistry.CellApi) (held : Bool)
    (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat)
    (allowed : List Instance) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (SelectedDomainReceipt reference api held data policy outward owners world allowed lexical receiver) := do
  if located : reference.check = true then
    let receiving ← checkSelectedDeclarations api held data policy outward owners world allowed lexical receiver operation
      (domainSupport argument receiver)
    .ok ⟨reference.sound located,receiving⟩
  else .error .operationShadowing

private theorem selected_checked
    {reference : OperationRef entries requested operation argument input}
    {data : Declarations entries requested answer bindings clauses}
    {initial : SelectedDomainReceipt reference api held data policy outward owners world allowed lexical receiver}
    (accepted : checkSelectedDomainDeclarations reference api held data policy outward owners world allowed lexical receiver = .ok initial) :
    checkSelectedDeclarations api held data policy outward owners world allowed lexical receiver operation
      (domainSupport argument receiver) = .ok initial.receiving := by
  unfold checkSelectedDomainDeclarations at accepted
  split at accepted
  · next located =>
    cases checked : checkSelectedDeclarations api held data policy outward owners world allowed lexical receiver operation
        (domainSupport argument receiver) with
    | error error => simp [checked,bind,Except.bind] at accepted
    | ok receipt =>
      simp only [checked,bind,Except.bind,Except.ok.injEq] at accepted
      cases accepted
      rfl
  · cases accepted

/-- Static acceptance and the same current delivery execute the existing checker.
Source proof irrelevance only identifies the same original declaration indices. -/
theorem selected_domain_delivery
    {reference : OperationRef entries requested operation argument input}
    {annotation : Annotation entries owners richBindings deliveredCode argument demand requirements plan rows}
    {data : Declarations entries requested answer bindings clauses}
    {initial : SelectedDomainReceipt reference api held data policy outward owners world allowed lexical receiver}
    (accepted : checkSelectedDomainDeclarations reference api held data policy outward owners world allowed lexical receiver = .ok initial)
    (delivered : CoreCallableDeliveredOperandSupport.DeliveredSupport storageDeclarations reference annotation storageBindings inst recipe
      graph machineOwners heap value policy outward world allowed lexical receiver) :
    ∃ final : ReceivingReceipt api entries policy outward owners world allowed data lexical receiver
      (selected clauses operation (CoreCallableDeliveredOperandSupport.actualSupport deliveredCode delivered.stored) receiver) operation held,
      checkDeliveredDeclarations delivered api held data = .ok final ∧
      DeclarationAuthenticationAt (registry entries policy) outward initial.receiving.checked.source lexical receiver
        (selected clauses operation (CoreCallableDeliveredOperandSupport.actualSupport deliveredCode delivered.stored) receiver) := by
  obtain ⟨final,checked⟩ := checkSelectedDeclarations_narrow data (delivered_support_in_domain delivered) (selected_checked accepted)
  refine ⟨final,checked,?_⟩
  have sameSource : final.checked.source = initial.receiving.checked.source := Subsingleton.elim _ _
  simpa only [sameSource] using final.checked.authenticated

#print axioms checkSelectedDeclarations_narrow
#print axioms checkSelectedDomainDeclarations
#print axioms selected_domain_delivery

#print axioms checkAssignments_narrow

#print axioms checkOffer_narrow
#print axioms checkMode_narrow

#print axioms Template.check_narrow

#print axioms selected_narrower
#print axioms LexicalNarrower.extend
#print axioms LexicalNarrower.evaluate
#print axioms Pure.check_narrow
end Ash.OneShot.CoreCallableSelectedDomainDeclarationTransfer
