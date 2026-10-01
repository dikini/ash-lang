import CoreCallableGeneralHistory
namespace Ash.OneShot.CoreCallableOutsideOrigin
open CoreMachine CoreTranslation ScopedExecution CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport CoreCallableGeneralHistory

def frameMiss (handler owner : Nat) : CoreMachine.Frame → Bool
  | .clauseBoundary candidate selected _ _ _ => !(handler == candidate && owner == selected)
  | _ => true

def prefixMiss (handler owner : Nat) (leading : List CoreMachine.Frame) : Bool :=
  leading.all (frameMiss handler owner)

private theorem lift_cut (frame : CoreMachine.Frame) (result : Except Error OwnerCut) (cut : OwnerCut) :
    (do let c ← result; pure {c with inside := frame :: c.inside}) =
      .ok {cut with inside := frame :: cut.inside} ↔ result = .ok cut := by
  cases result with
  | error e => simp [Bind.bind,Except.bind]
  | ok c => cases c; cases cut; simp [OwnerCut.mk.injEq,Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem prefixMiss_test (leading : List CoreMachine.Frame) :
    findOwner handler owner (leading ++ [.clauseBoundary handler owner 0 0 (some [])]) =
      .ok ⟨leading,handler,owner,0,0,[],[]⟩ ↔ prefixMiss handler owner leading = true := by
  induction leading with
  | nil => simp [findOwner,prefixMiss]
  | cons frame rest ih =>
    cases frame
    case clauseBoundary candidate selected occurrence ticket saved =>
      by_cases same : handler = candidate ∧ owner = selected
      · rcases same with ⟨rfl,rfl⟩
        cases saved <;> simp [findOwner,prefixMiss,frameMiss,OwnerCut.mk.injEq]
      · simp only [List.cons_append,findOwner, Bool.and_eq_true,beq_iff_eq, if_neg same]
        rw [lift_cut (cut := ⟨rest,handler,owner,0,0,[],[]⟩), ih]
        have different : handler ≠ candidate ∨ owner ≠ selected := by
          by_cases h : handler = candidate
          · exact Or.inr (fun o => same ⟨h,o⟩)
          · exact Or.inl h
        simp [prefixMiss,frameMiss,different]
    all_goals
      simp only [List.cons_append,findOwner]
      rw [lift_cut (cut := ⟨rest,handler,owner,0,0,[],[]⟩),ih]
      simp [prefixMiss,frameMiss]

theorem missing_prefixMiss
    (history : GeneralHistory graph heap physical target)
    (missing : ∃ pass, owner_search history handler owner = .missing pass) :
    prefixMiss handler owner physical = true := by
  obtain ⟨pass,_⟩ := missing
  apply (prefixMiss_test physical).mp
  simpa only [List.append_nil] using pass [.clauseBoundary handler owner 0 0 (some [])] ⟨[],handler,owner,0,0,[],[]⟩ (by simp [findOwner])

theorem OwnerPath.prepend_checked
    (path : OwnerPath handler owner occurrence dynamicTicket saved physical front outside)
    (checked : prefixMiss handler owner leading = true) :
    OwnerPath handler owner occurrence dynamicTicket saved
      (leading ++ physical) (leading ++ front) outside := by
  induction leading with
  | nil => exact path
  | cons frame rest ih =>
    have parts : frameMiss handler owner frame = true ∧ prefixMiss handler owner rest = true := by
      simpa only [prefixMiss,List.all_cons,Bool.and_eq_true] using checked
    apply OwnerPath.skip frame _ (ih parts.2)
    intro candidate selected activation ticket capture same
    subst frame
    simpa [frameMiss] using parts.1

theorem OwnerPath.drop_prefix
    (path : OwnerPath handler owner occurrence dynamicTicket saved physical front tail)
    (same : physical = kept ++ outside) (bound : kept.length ≤ front.length) :
    ∃ remaining, OwnerPath handler owner occurrence dynamicTicket saved outside remaining tail ∧
      front = kept ++ remaining ∧ prefixMiss handler owner kept = true := by
  induction path generalizing kept with
  | hit tail =>
    cases kept with
    | nil =>
      simp only [List.nil_append] at same
      subst outside
      exact ⟨[],OwnerPath.hit tail,rfl,rfl⟩
    | cons head rest => simp at bound
  | skip frame miss next ih =>
    cases kept with
    | nil =>
      simp only [List.nil_append] at same
      subst outside
      exact ⟨_,OwnerPath.skip frame miss next,rfl,rfl⟩
    | cons head rest =>
      obtain ⟨rfl,tailSame⟩ := List.cons.inj same
      obtain ⟨remaining,path,frontSame,checked⟩ := ih tailSame (by simpa using bound)
      refine ⟨remaining,path,by simp [frontSame],?_⟩
      have headChecked : frameMiss handler owner frame = true := by
        cases frame <;> simp [frameMiss]
        case clauseBoundary candidate selected activation ticket capture =>
          simpa [frameMiss] using miss candidate selected activation ticket capture rfl
      simpa only [prefixMiss,List.all_cons,Bool.and_eq_true] using And.intro headChecked checked

inductive ScopeOutside {graph : CoreSyntax.Graph} :
    {owners : OwnerMap} → {scope : Execution.Scope} → {physical : List CoreMachine.Frame} →
    CurrentScopeOrigin graph owners scope physical → List CoreMachine.Frame → Prop where
  | inactive (canonical : CanonicalOwnerMap graph owners) :
      ScopeOutside (.inactive (physical := physical) canonical) kept
  | clause (canonical : CanonicalOwnerMap graph owners)
      (path : OwnerPath handler owner occurrence dynamicTicket saved physical front outside)
      (bound : kept.length ≤ front.length) : ScopeOutside (.clause canonical path) kept

/-- The computation examines only the physically inserted prefix, at the old
caller's literal pair. Retained logical and dormant owners are not candidates. -/
noncomputable def outsideCheck (owners : OwnerMap) (scope : Execution.Scope)
    (inserted : GeneralHistory graph heap added addedTarget) : Bool :=
  match scope,owners with
  | .none,_ => true
  | .ticket _ _,entry::_ =>
      match owner_search inserted entry.handler entry.owner with
      | .missing _ => true
      | _ => false
  | .ticket _ _,[] => false

theorem CurrentScopeOrigin.restore_outside_checked
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside) (position : ScopeOutside origin kept)
    (inserted : GeneralHistory graph heap added addedTarget)
    (checked : outsideCheck owners scope inserted = true) :
    CurrentScopeOrigin graph owners scope (kept ++ (added ++ outside)) := by
  cases position with
  | inactive canonical => exact .inactive canonical
  | @clause oldOwners oldHandler oldOwner occurrence dynamicTicket saved originalPhysical front tailOutside originalKept canonical path bound =>
      obtain ⟨remaining,tail,_,keptChecked⟩ := OwnerPath.drop_prefix path same bound
      have addedChecked : prefixMiss oldHandler oldOwner added = true := by
        unfold outsideCheck at checked
        cases selected : owner_search inserted oldHandler oldOwner with
        | found location => simp [selected] at checked
        | blocked => simp [selected] at checked
        | missing pass => exact missing_prefixMiss inserted ⟨pass,selected⟩
      exact .clause canonical (OwnerPath.prepend_checked (OwnerPath.prepend_checked tail addedChecked) keptChecked)

theorem RunningReceipt.restore_outside_checked
    (receipt : RunningReceipt graph owners heap action environment data savedValue savedCode physical)
    (same : physical = kept ++ outside) (position : ScopeOutside receipt.installed.origin kept)
    (inserted : GeneralHistory graph heap added addedTarget)
    (checked : outsideCheck owners data.scope inserted = true) :
    RunningReceipt graph owners heap action environment data savedValue savedCode
      (kept ++ (added ++ outside)) :=
  ⟨⟨receipt.installed.delayed,CurrentScopeOrigin.restore_outside_checked receipt.installed.origin same position inserted checked⟩,
    receipt.value⟩

noncomputable def OwnerLocation.inserted_history
    (location : OwnerLocation graph heap handler owner physical target) :
    GeneralHistory graph heap
      (location.front ++ [.clauseBoundary handler owner location.occurrence location.dynamicTicket none])
      (location.frontTarget.append (.spent location.dynamicTicket location.data.answer location.data.scope .nil)) :=
  location.frontHistory.append (.spent location.installation location.header .nil)

/-- An actual full-prefix resume and the checked restoration of the SAME
running caller receipt. No restored origin or successor history is supplied. -/
theorem resume_outside_checked {base : CoreMachine.State}
    (history : GeneralHistory graph base.heap physical target)
    {location : OwnerLocation graph base.heap handler owner physical target}
    (picked : owner_search history handler owner = .found location)
    (frame : CoreResumeFrames.ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : CoreValueRelation.ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some location.dynamicTicket) (runtimeScope : Execution.Scope)
    (receipt : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode originalPhysical)
    (same : originalPhysical = kept ++ location.outside)
    (position : ScopeOutside receipt.installed.origin kept)
    (captured : location.captured = .cleanupCompletion data.identity savedValue :: kept)
    (checked : outsideCheck cleanupOwners data.scope (OwnerLocation.inserted_history location) = true) :
    CoreGeneralCaptureResume.GeneralStepWitness graph
      ⟨CoreGeneralCaptureResume.resumeBefore base handler owner coreValue physical,
        .eval ⟨.resume binder code,plain.scope,target⟩,owners,[(frameOwners,.resume handler owner)]⟩
      ⟨CoreGeneralCaptureResume.resumeAfter base handler owner location.occurrence location.dynamicTicket coreValue
          location.captured location.front location.outside,
        .eval ⟨code,plain.scope,location.capturedTarget.append (location.frontTarget.append
          (.spent location.dynamicTicket location.data.answer location.data.scope location.tail))⟩,owners,[]⟩
        [] [.ticket location.dynamicTicket] ∧
    RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode
      (kept ++ (location.front ++ .clauseBoundary handler owner location.occurrence location.dynamicTicket none :: location.outside)) ∧
    (CoreGeneralCaptureResume.resumeAfter base handler owner location.occurrence location.dynamicTicket coreValue
      location.captured location.front location.outside).frames =
      .cleanupCompletion data.identity savedValue ::
      (kept ++ (location.front ++ .clauseBoundary handler owner location.occurrence location.dynamicTicket none :: location.outside)) := by
  refine ⟨(resume_history history picked frame context value resolve runtimeScope).1,?_,?_⟩
  · simpa only [List.append_assoc,List.singleton_append] using
      RunningReceipt.restore_outside_checked receipt same position (OwnerLocation.inserted_history location) checked
  · simp [CoreGeneralCaptureResume.resumeAfter,captured,List.append_assoc]

#print axioms prefixMiss_test
#print axioms missing_prefixMiss
#print axioms OwnerPath.prepend_checked
#print axioms OwnerPath.drop_prefix
#print axioms outsideCheck
#print axioms CurrentScopeOrigin.restore_outside_checked
#print axioms RunningReceipt.restore_outside_checked
#print axioms OwnerLocation.inserted_history
#print axioms resume_outside_checked
end Ash.OneShot.CoreCallableOutsideOrigin
