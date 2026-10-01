import CoreCallableRestoredAccounting

namespace Ash.OneShot.CoreCallableContractAdmission
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

/-- Read receiving support from the same declaration authentication at the
current policy instance. -/
theorem DeclarationAuthentication.received_support_current [evidence : SourcePlannedChecks.DeclarationPolicy]
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver) :
    rows.resourceSupport ⊆ receiver := by
  apply DeclarationAuthentication.rec
    (motive_1 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => rows.resourceSupport ⊆ receiver)
    (t := authenticated)
  all_goals intros
  all_goals first | trivial | exact List.append_subset.mpr ⟨by assumption, by assumption⟩ | simp [ClauseRows.resourceSupport]

end Ash.OneShot.CoreCallableContractAdmission

namespace Ash.OneShot.CoreCallableContractExecution
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

theorem HandlerSource.received_support_current [evidence : SourcePlannedChecks.DeclarationPolicy]
    (source : HandlerSource globals outward world residual data answer table plans rows receiver) :
    rows.resourceSupport ⊆ receiver := by
  obtain ⟨lexical, empty, authenticated⟩ := source.authentication
  exact authenticated.received_support_current

end Ash.OneShot.CoreCallableContractExecution

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ProtectionContracts
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

/-- A paired receipt is attached to this actual installed handler. Its new
complete rows are computed from the saved lexical evidence and the current
receiving scope. It retains the same declaration plans and private owner family. -/
structure HandlerRestorationReceipt
    (before : HandlerSource globals outward world residual data answer table plans rows receiver)
    (after : HandlerSource globals outward nextWorld residual data answer table plans nextRows
      (actualReceiver nextWorld receiving ambient)) : Prop where
  worldExtended : world ⊆ nextWorld
  receiverExtended : receiver ⊆ actualReceiver nextWorld receiving ambient
  canonicalRows : ∃ lexical : LexicalBounds,
    lexical.environment = ScopedPorts.Support.empty ∧
    CoreCallableContractAdmission.DeclarationAuthentication globals.registry outward before.source lexical receiver ∧
    nextRows = restoredClauses plans rows lexical (actualReceiver nextWorld receiving ambient)
  completeRows : eraseModeSupportBoundsClauses nextRows = eraseModeSupportBoundsClauses rows
  receiverIssued : actualReceiver nextWorld receiving ambient ⊆ nextWorld
  installationReceived : nextRows.resourceSupport ⊆ receiving.visibleResources ++ ambient

/-- Construct the receipt from the actual saved source and receiving support.
The receiving and issuance checks follow the reconstructed authentication. -/
theorem HandlerSource.restore_receipt
    (before : HandlerSource globals outward world residual data answer table plans rows receiver)
    (larger : world ⊆ nextWorld)
    (receiverLarger : receiver ⊆ actualReceiver nextWorld receiving ambient) :
    ∃ nextRows : ClauseRows (SourcePlanSignatures.clauseSignatures plans),
      ∃ after : HandlerSource globals outward nextWorld residual data answer table plans nextRows
        (actualReceiver nextWorld receiving ambient),
      HandlerRestorationReceipt before after := by
  obtain ⟨lexical, empty, authenticated⟩ := before.authentication
  have domain : CoreCallableContractAdmission.RestoredLexicalDomain lexical lexical :=
    fun name resources found => ⟨resources, found⟩
  have received : ∀ name, lexical.environment name ⊆ actualReceiver nextWorld receiving ambient := by
    intro name
    rw [empty]
    simp [ScopedPorts.Support.empty]
  obtain ⟨nextSource, nextAuthenticated⟩ := authenticated.restore_world_receiver larger receiverLarger domain received
  let after : HandlerSource globals outward nextWorld residual data answer table plans
      (restoredClauses plans rows lexical (actualReceiver nextWorld receiving ambient))
      (actualReceiver nextWorld receiving ambient) :=
    ⟨before.annotation, before.modes, nextSource, lexical, empty, nextAuthenticated⟩
  refine ⟨_, after, larger, receiverLarger, ⟨lexical, empty, authenticated, rfl⟩,
    erase_restoredClauses _ _ _ _, actualReceiver.issued, ?_⟩
  exact after.received_support_current.trans actualReceiver.received

end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.HandlerSource.restore_receipt

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

/-- Source-owned changes carry the original authentication and exact computed
row transformation. Public contract suffixes use the unchanged constructor. -/
inductive RestoredSourceRows (world receiver : List Nat) :
    {dependencies : SourceDependencyAnnotations.Dependencies} →
    {checking : SourcePlanSignatures.Signature dependencies} → Rows checking → Rows checking → Prop where
  | same : RestoredSourceRows world receiver rows rows
  | canonical
      {source : IndexedSource registry outward owners beforeWorld allowed scope environment code contract demand requirements plan rows}
      (authenticated : Authenticated registry outward source lexical beforeReceiver)
      (worldExtended : beforeWorld ⊆ world) (receiverExtended : beforeReceiver ⊆ receiver)
      (domain : RestoredLexicalDomain lexical nextLexical)
      (received : ∀ name, nextLexical.environment name ⊆ receiver) :
      RestoredSourceRows world receiver rows (restoredRows code plan rows nextLexical receiver)
  | sequence (left : RestoredSourceRows world receiver beforeLeft afterLeft)
      (right : RestoredSourceRows world receiver beforeRight afterRight) :
      RestoredSourceRows world receiver (.sequence beforeLeft beforeRight) (.sequence afterLeft afterRight)
  | choice (left : RestoredSourceRows world receiver beforeLeft afterLeft)
      (right : RestoredSourceRows world receiver beforeRight afterRight) :
      RestoredSourceRows world receiver (.choice beforeLeft beforeRight) (.choice afterLeft afterRight)

theorem RestoredSourceRows.complete (receipt : RestoredSourceRows world receiver before after) : SupportOnly before after := by
  induction receipt with
  | same => rfl
  | canonical authenticated worldExtended receiverExtended domain received => exact restoredRows_supportOnly _ _ _ _ _
  | sequence left right ihLeft ihRight =>
    simp only [SupportOnly, eraseSupportBounds] at ihLeft ihRight ⊢
    rw [ihLeft, ihRight]
  | choice left right ihLeft ihRight =>
    simp only [SupportOnly, eraseSupportBounds] at ihLeft ihRight ⊢
    rw [ihLeft, ihRight]

end Ash.OneShot.CoreCallableRestoredChecking

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourcePlanSignatures (clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableContractExecution (actualReceiver)
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

/-- A declaration receipt is taken from the same installed or source-owned
handler, with its exact effect, table, plan and computed complete rows. -/
inductive RestoredDeclarations (world receiver : List Nat) (requested : Instance)
    (table : List (Nat × ClauseContract)) :
    {families : SourceDependencyAnnotations.ClauseDependencies} →
    {checking : SourcePlanSignatures.ClauseSignatures families} → ClauseRows checking → ClauseRows checking → Prop where
  | same : RestoredDeclarations world receiver requested table rows rows
  | canonical
      {source : SourceDeclarations registry outward owners beforeWorld environment allowed requested answer clauses table plans rows}
      (authenticated : DeclarationAuthentication registry outward source lexical beforeReceiver)
      (worldExtended : beforeWorld ⊆ world) (receiverExtended : beforeReceiver ⊆ receiver)
      (domain : RestoredLexicalDomain lexical nextLexical)
      (received : ∀ name, nextLexical.environment name ⊆ receiver) :
      RestoredDeclarations world receiver requested table rows (restoredClauses plans rows nextLexical receiver)

/-- Receipts decorate the existing context delta. They contain no future
admission or execution result and no duplicate runtime stack judgment. -/
inductive RestoredContextReceipts (world : List Nat) : (ambient : List Nat) →
    {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Context hints → Prop where
  | nil : RestoredContextReceipts world ambient .nil .nil
  | plain {rest : ReturnHints restScope} {before after : Context rest}
      {receiver : List Nat} (received : receiver ⊆ restScope.visibleResources ++ ambient)
      (rows : RestoredSourceRows world receiver beforeRows afterRows)
      (tail : RestoredContextReceipts world ambient (before : Context rest) after) :
      RestoredContextReceipts world ambient (.plain beforeRows before) (.plain afterRows after)
  | handler {rest : ReturnHints restScope} {before after : Context rest}
      {receiver : List Nat} (received : receiver ⊆ restScope.visibleResources ++ ambient)
      (rows : RestoredDeclarations world receiver effect table beforeRows afterRows)
      (tail : RestoredContextReceipts world ambient (before : Context rest) after) :
      RestoredContextReceipts world ambient
        (.handler (effect := effect) (table := table) activation beforeRows before)
        (.handler (effect := effect) (table := table) activation afterRows after)
  | cell (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.cell before) (.cell after)
  | cleanup {rest : ReturnHints restScope} {before after : Context rest}
      {receiver : List Nat} (received : receiver ⊆ restScope.visibleResources ++ ambient)
      (rows : RestoredSourceRows world receiver beforeRows afterRows)
      (tail : RestoredContextReceipts world ambient (before : Context rest) after) :
      RestoredContextReceipts world ambient (.cleanup latent beforeRows before) (.cleanup latent afterRows after)
  | normal (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.normal before) (.normal after)
  | unwinding (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.unwinding before) (.unwinding after)
  | closing (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.closing before) (.closing after)
  | retiring (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.retiring owner before) (.retiring owner after)
  | live {rest : ReturnHints restScope} {before after : Context rest}
      (saved : RestoredContextReceipts world (restScope.visibleResources ++ ambient) beforeSaved afterSaved)
      (tail : RestoredContextReceipts world ambient (before : Context rest) after) :
      RestoredContextReceipts world ambient
        (.live (owner := owner) (resumeDemand := demand) beforeSaved before)
        (.live (owner := owner) (resumeDemand := demand) afterSaved after)
  | spent (tail : RestoredContextReceipts world ambient before after) :
      RestoredContextReceipts world ambient (.spent before) (.spent after)

theorem RestoredDeclarations.complete (receipt : RestoredDeclarations world receiver effect table before after) :
    eraseModeSupportBoundsClauses after = eraseModeSupportBoundsClauses before := by
  cases receipt with
  | same => rfl
  | canonical authenticated worldExtended receiverExtended domain received => exact erase_restoredClauses _ _ _ _

theorem RestoredContextReceipts.complete (receipt : RestoredContextReceipts world ambient before after) :
    RestoredContext before after := by
  induction receipt with
  | nil => exact .nil
  | plain received rows tail ih => exact .plain rows.complete ih
  | handler received rows tail ih => exact .handler rows.complete ih
  | cell tail ih => exact .cell ih
  | cleanup received rows tail ih => exact .cleanup rows.complete ih
  | normal tail ih => exact .normal ih
  | unwinding tail ih => exact .unwinding ih
  | closing tail ih => exact .closing ih
  | retiring tail ih => exact .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

end Ash.OneShot.CoreCallableRestoredChecking

namespace Ash.OneShot.CoreCallableContractExecution
open CoreCallableRestoredChecking
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

/-- The actual paired installed source supplies the contextual declaration
receipt. Selection will use this same source family and exact table. -/
theorem HandlerRestorationReceipt.declarations
    {before : HandlerSource globals outward world residual data answer table plans rows receiver}
    {after : HandlerSource globals outward nextWorld residual data answer table plans nextRows
      (actualReceiver nextWorld receiving ambient)}
    (receipt : HandlerRestorationReceipt before after) :
    RestoredDeclarations nextWorld (actualReceiver nextWorld receiving ambient) data.effectInst table rows nextRows := by
  obtain ⟨lexical, empty, authenticated, same⟩ := receipt.canonicalRows
  rw [same]
  apply RestoredDeclarations.canonical authenticated receipt.worldExtended receipt.receiverExtended
    (fun name resources found => ⟨resources, found⟩)
  intro name
  rw [empty]
  simp [ScopedPorts.Support.empty]

end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredSourceRows.complete
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredDeclarations.complete
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.complete
#print axioms Ash.OneShot.CoreCallableContractExecution.HandlerRestorationReceipt.declarations

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission (Authenticated RestoredLexicalDomain)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRestoredSupport (restoredRows)
open CoreCallableRestoredChecking (RestoredSourceRows)
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

/-- Reconstruct the actual saved frame and its source receipt together. The
receipt records this original source, including its exact code and private plan;
it is not inferred from a signature or a bare row comparison. -/
theorem FrameSource.restore_receipt
    (before : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows
      inputBound bodyBound receiver)
    (larger : world ⊆ nextWorld)
    (receiverLarger : receiver ⊆ actualReceiver nextWorld receiving ambient) :
    ∃ nextRows : Rows (signature plan),
      ∃ _after : FrameSource globals outward nextWorld allowed data input output parameter body demand requirements plan nextRows
        (actualReceiver nextWorld receiving ambient)
        (ScopedPorts.Support.evaluate (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter
          (actualReceiver nextWorld receiving ambient)) body.dependencies)
        (actualReceiver nextWorld receiving ambient),
      RestoredSourceRows nextWorld (actualReceiver nextWorld receiving ambient) rows nextRows := by
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := before.bodySource.authentication
  let nextReceiver := actualReceiver nextWorld receiving ambient
  let nextLexical := lexical.extend parameter nextReceiver
  have domain : RestoredLexicalDomain lexical nextLexical := by
    intro name resources found
    by_cases same : name = parameter
    · subst name
      exact ⟨nextReceiver, by simp [nextLexical, LexicalBounds.lookup, LexicalBounds.extend]⟩
    · exact ⟨resources, by simpa [nextLexical, LexicalBounds.lookup, LexicalBounds.extend, same] using found⟩
  have nextEnvironment : nextLexical.environment =
      ScopedPorts.Support.extend ScopedPorts.Support.empty parameter nextReceiver := by
    rw [show nextLexical.environment = ScopedPorts.Support.extend lexical.environment parameter nextReceiver from
      LexicalBounds.environment_extend]
    rw [sameEnvironment]
    funext name
    by_cases same : name = parameter <;> simp [ScopedPorts.Support.extend, same]
  have received : ∀ name, nextLexical.environment name ⊆ nextReceiver := by
    intro name
    rw [nextEnvironment]
    by_cases same : name = parameter
    · subst name; simp [ScopedPorts.Support.extend]
    · simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty, same]
  obtain ⟨nextSource, nextAuthenticated⟩ :=
    authenticated.restore_world_receiver larger receiverLarger domain received
  let nextRows := restoredRows body plan rows nextLexical nextReceiver
  have supported : CoreCallableContractAdmission.Supported globals outward nextWorld allowed data.scope
      (CoreCallableContractSource.Environment.empty.extend parameter input) nextLexical.environment body output
      demand requirements plan nextRows
      (ScopedPorts.Support.evaluate nextLexical.environment body.dependencies) nextReceiver :=
    CoreCallableContractAdmission.Supported.canonical nextSource nextLexical nextReceiver nextAuthenticated
      ((SourceSupport.bounds_iff.mp nextAuthenticated.current_support).trans actualReceiver.issued) actualReceiver.issued
  refine ⟨nextRows, ?_, RestoredSourceRows.canonical authenticated larger receiverLarger domain received⟩
  exact ⟨before.position, before.inputAnnotation, before.outputAnnotation, actualReceiver.issued,
    by simpa only [nextEnvironment] using supported⟩

end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.FrameSource.restore_receipt

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

omit evidence in
theorem scope_visible_append (first second : SourceDependencyCapture.Scope) :
    (first.append second).visibleResources = first.visibleResources ++ second.visibleResources := by
  induction first <;> simp_all [SourceDependencyCapture.Scope.append,
    SourceDependencyCapture.Scope.visibleResources]

theorem RestoredContextReceipts.split
    {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    (head : Context first) (tail : Context second) {after : Context (first.append second)}
    (delta : RestoredContextReceipts world ambient (head.append tail) after) :
    ∃ nextHead : Context first, ∃ nextTail : Context second,
      after = nextHead.append nextTail ∧ RestoredContextReceipts world (secondScope.visibleResources ++ ambient) head nextHead ∧
      RestoredContextReceipts world ambient tail nextTail := by
  induction head with
  | nil => exact ⟨.nil, after, rfl, .nil, delta⟩
  | plain rows rest ih => cases delta with
    | plain received rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.plain _ nextHead, nextTail, rfl, .plain (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rowsSame headDelta, tailDelta⟩
  | handler activation rows rest ih => cases delta with
    | handler received rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.handler activation _ nextHead, nextTail, rfl, .handler (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rowsSame headDelta, tailDelta⟩
  | cell rest ih => cases delta with
    | cell restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.cell nextHead, nextTail, rfl, .cell headDelta, tailDelta⟩
  | cleanup latent rows rest ih => cases delta with
    | cleanup received rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.cleanup latent _ nextHead, nextTail, rfl, .cleanup (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rowsSame headDelta, tailDelta⟩
  | normal rest ih => cases delta with
    | normal restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.normal nextHead, nextTail, rfl, .normal headDelta, tailDelta⟩
  | unwinding rest ih => cases delta with
    | unwinding restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.unwinding nextHead, nextTail, rfl, .unwinding headDelta, tailDelta⟩
  | closing rest ih => cases delta with
    | closing restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.closing nextHead, nextTail, rfl, .closing headDelta, tailDelta⟩
  | retiring owner rest ih => cases delta with
    | retiring restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.retiring owner nextHead, nextTail, rfl, .retiring headDelta, tailDelta⟩
  | live saved rest ihSaved ihRest => cases delta with
    | live savedDelta restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ihRest restDelta
      exact ⟨.live _ nextHead, nextTail, rfl, .live (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedDelta) headDelta, tailDelta⟩
  | spent rest ih => cases delta with
    | spent restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.spent nextHead, nextTail, rfl, .spent headDelta, tailDelta⟩


omit evidence in
private theorem context_append_injective
    {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    (beforeHead afterHead : Context first) (beforeTail afterTail : Context second)
    (same : beforeHead.append beforeTail = afterHead.append afterTail) :
    beforeHead = afterHead ∧ beforeTail = afterTail := by
  induction beforeHead with
  | nil => cases afterHead; exact ⟨rfl, same⟩
  | plain rows rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | handler activation rows rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | cleanup latent rows rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | cell rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | normal rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | unwinding rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | closing rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | retiring owner rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | spent rest ih =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ih _ (by assumption)
    exact ⟨rfl, rfl⟩
  | live saved rest ihSaved ihRest =>
    cases afterHead
    simp only [Context.append] at same
    injection same
    subst_vars
    obtain ⟨rfl, rfl⟩ := ihRest _ (by assumption)
    exact ⟨rfl, rfl⟩

theorem RestoredContextReceipts.cut
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {before after : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    (receipt : RestoredContextReceipts world ambient before after)
    (cut : Contextual.Cut effect operation before captured tail contract modes) :
    ∃ nextCaptured : Context captureHints, ∃ nextTail : Context tailHints,
      Contextual.Cut effect operation after nextCaptured nextTail contract modes ∧
      RestoredContextReceipts world (tailScope.visibleResources ++ ambient) captured nextCaptured ∧
      RestoredContextReceipts world ambient tail nextTail := by
  obtain ⟨nextCaptured, nextTail, nextCut, capturedDelta, tailDelta⟩ := receipt.complete.cut cut
  have oldDecomposition := cut.decomposition
  cases oldDecomposition
  obtain ⟨head, rest, rebuilt, headReceipt, tailReceipt⟩ := receipt.split captured tail
  have packedSame := nextCut.decomposition
  rw [rebuilt] at packedSame
  have same : head.append rest = nextCaptured.append nextTail := by
    injection packedSame with scopeSame hintsSame contextSame
  obtain ⟨rfl, rfl⟩ := context_append_injective head nextCaptured rest nextTail same
  exact ⟨head, rest, nextCut, headReceipt, tailReceipt⟩

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.split

#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.cut

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

def SourceRowView (world receiver : List Nat) (before after : Rows checking) : Prop :=
  match before, after with
  | .sequence beforeLeft beforeRight, .sequence afterLeft afterRight =>
      RestoredSourceRows world receiver beforeLeft afterLeft ∧ RestoredSourceRows world receiver beforeRight afterRight
  | .choice beforeLeft beforeRight, .choice afterLeft afterRight =>
      RestoredSourceRows world receiver beforeLeft afterLeft ∧ RestoredSourceRows world receiver beforeRight afterRight
  | @Rows.handler _ _ _ _ effect table _ beforeDeclarations beforeBody, .handler afterDeclarations afterBody =>
      RestoredDeclarations world receiver effect table beforeDeclarations afterDeclarations ∧
        RestoredSourceRows world receiver beforeBody afterBody
  | .cleanup beforeLatent beforeCallback beforeBody, .cleanup afterLatent afterCallback afterBody =>
      beforeLatent = afterLatent ∧ RestoredSourceRows world receiver beforeCallback afterCallback ∧
        RestoredSourceRows world receiver beforeBody afterBody
  | .resource beforeBodies, .resource afterBodies =>
      ∀ identity, RestoredSourceRows (world ++ [identity]) receiver (beforeBodies identity) (afterBodies identity)
  | _, _ => True

omit evidence in
private theorem receipt_domain_extend
    (domain : RestoredLexicalDomain before after) :
    RestoredLexicalDomain (before.extend parameter oldReceiver) (after.extend parameter receiver) := by
  intro name resources found
  by_cases same : name = parameter
  · subst name; exact ⟨receiver, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩
  · obtain ⟨next, known⟩ := domain name resources
      (by simpa [LexicalBounds.lookup, LexicalBounds.extend, same] using found)
    exact ⟨next, by simpa [LexicalBounds.lookup, LexicalBounds.extend, same] using known⟩

omit evidence in
private theorem receipt_range_extend {lexical : LexicalBounds} {parameter : Nat} {receiver : List Nat}
    (received : ∀ name, lexical.environment name ⊆ receiver) :
    ∀ name, (lexical.extend parameter receiver).environment name ⊆ receiver := by
  intro name
  by_cases same : name = parameter
  · subst name; simp only [LexicalBounds.environment_extend, ScopedPorts.Support.extend]; exact List.Subset.refl _
  · simpa [LexicalBounds.environment_extend, ScopedPorts.Support.extend, same] using received name

theorem Authenticated.restored_row_view
    {source : IndexedSource registry outward owners beforeWorld allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical beforeReceiver)
    (worldExtended : beforeWorld ⊆ world) (receiverExtended : beforeReceiver ⊆ receiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ receiver) :
    SourceRowView world receiver rows (restoredRows code plan rows nextLexical receiver) := by
  cases authenticated with
  | checked current hereditary => cases hereditary with
    | unit | boolean | integer | reference | «variable» | purePair | discard | lambda | receiverLambda => trivial
    | pair left right =>
      exact ⟨.canonical left worldExtended receiverExtended domain received,
        .canonical right worldExtended receiverExtended domain received⟩
    | app function argument =>
      exact ⟨.canonical function worldExtended receiverExtended domain received,
        .sequence (.canonical argument worldExtended receiverExtended domain received) .same⟩
    | bind initial body =>
      exact ⟨.canonical initial worldExtended receiverExtended domain received,
        .canonical body worldExtended receiverExtended (receipt_domain_extend domain) (receipt_range_extend received)⟩
    | branch condition yes no =>
      exact ⟨.canonical condition worldExtended receiverExtended domain received,
        .choice (.canonical yes worldExtended receiverExtended domain received)
          (.canonical no worldExtended receiverExtended domain received)⟩
    | perform operand | resume operand =>
      exact ⟨.canonical operand worldExtended receiverExtended domain received, .same⟩
    | handler clauses capabilities coverage unique admitted modes recipes body declarations =>
      exact ⟨.canonical declarations worldExtended receiverExtended domain received,
        .canonical body worldExtended receiverExtended domain received⟩

theorem RestoredSourceRows.view (receipt : RestoredSourceRows world receiver before after) :
    SourceRowView world receiver before after := by
  cases receipt with
  | same => cases before <;> first | exact ⟨.same, .same⟩ | exact ⟨rfl, .same, .same⟩ | exact fun identity => .same | trivial
  | canonical authenticated worldExtended receiverExtended domain received =>
      exact Authenticated.restored_row_view authenticated worldExtended receiverExtended domain received
  | sequence left right => exact ⟨left, right⟩
  | choice left right => exact ⟨left, right⟩

theorem RestoredSourceRows.handler_parts
    (receipt : RestoredSourceRows world receiver
      (Rows.handler (effect := effect) (table := table) (required := required) beforeDeclarations beforeBody)
      (Rows.handler (effect := effect) (table := table) (required := required) afterDeclarations afterBody)) :
    RestoredDeclarations world receiver effect table beforeDeclarations afterDeclarations ∧
      RestoredSourceRows world receiver beforeBody afterBody := receipt.view

theorem RestoredDeclarations.supported
    (receipt : RestoredDeclarations world receiver effect table before after)
    (supported : before.resourceSupport ⊆ receiving)
    (received : receiver ⊆ receiving) : after.resourceSupport ⊆ receiving := by
  cases receipt with
  | same => exact supported
  | canonical authenticated worldExtended receiverExtended domain lexicalReceived =>
      obtain ⟨nextSource, nextAuthenticated⟩ :=
        authenticated.restore_world_receiver worldExtended receiverExtended domain lexicalReceived
      exact nextAuthenticated.received_support_current.trans received

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.Authenticated.restored_row_view
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredSourceRows.handler_parts
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredDeclarations.supported

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport

/-- The changed handler check is discharged from its actual declaration
receipt. The body premise is the recursive checking induction result. -/
theorem restore_handler_check
    {hints : ReturnHints scope} {before after : Context hints}
    {beforeDeclarations afterDeclarations : ClauseRows declarationSignature}
    {beforeBody : ∀ activation, activation ∉ installations →
      SourceAdmission.Code outward actions budget phases world (activation :: installations) beforeBodyRows
        (.handler (effect := effect) (table := table) activation beforeDeclarations before)}
    {afterBody : ∀ activation, activation ∉ installations →
      SourceAdmission.Code outward actions budget phases world (activation :: installations) afterBodyRows
        (.handler (effect := effect) (table := table) activation afterDeclarations after)}
    (checked : CodeChecked ambient outward (SourceAdmission.Code.handler (required := required) beforeBody))
    (receipt : RestoredDeclarations world receiver effect table beforeDeclarations afterDeclarations)
    (received : receiver ⊆ scope.visibleResources ++ ambient)
    (inside : ∀ activation fresh, CodeChecked ambient outward (afterBody activation fresh)) :
    CodeChecked ambient outward (SourceAdmission.Code.handler (required := required) afterBody) := by
  cases checked with
  | handler supported oldInside => exact .handler (receipt.supported supported received) inside

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.restore_handler_check

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRestoredSupport
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

def ModeRowView (world receiver : List Nat) (before after : ModeRows checking) : Prop :=
  match before, after with
  | .available beforeBodies, .available afterBodies =>
      ∀ owner, RestoredSourceRows world receiver (beforeBodies owner) (afterBodies owner)
  | .unavailable, .unavailable => True

theorem OfferAuthentication.restored_mode_view
    {source : SourceOffer registry outward owners beforeWorld environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans rows}
    (authenticated : OfferAuthentication registry outward source lexical beforeReceiver)
    (worldExtended : beforeWorld ⊆ world) (receiverExtended : beforeReceiver ⊆ receiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ receiver) :
    ModeRowView world receiver rows (restoredModes code plans rows nextLexical receiver) := by
  cases authenticated with
  | unavailable => trivial
  | available resumeInterface closeInterface body =>
      intro owner
      let contract : OwnerContract := ⟨input, answer, held, [], [], [], none, resumeEffects, closeEffects⟩
      have bodyAuth := body owner contract rfl rfl rfl rfl rfl (List.Perm.refl [])
      cases bodyAuth with
      | typed authenticated => exact .canonical authenticated worldExtended receiverExtended domain received

def DeclarationRowView (world receiver : List Nat) (requested : Instance) (table : List (Nat × ClauseContract))
    (before after : ClauseRows checking) : Prop :=
  match before, after with
  | .nil, .nil => True
  | .cons beforeOrdinary beforeProtected beforeRest _, .cons afterOrdinary afterProtected afterRest _ =>
      ModeRowView world receiver beforeOrdinary afterOrdinary ∧
      ModeRowView world receiver beforeProtected afterProtected ∧
      RestoredDeclarations world receiver requested (table.drop 1) beforeRest afterRest

theorem DeclarationAuthentication.restored_declaration_view
    {source : SourceDeclarations registry outward owners beforeWorld environment allowed requested answer clauses table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical beforeReceiver)
    (worldExtended : beforeWorld ⊆ world) (receiverExtended : beforeReceiver ⊆ receiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ receiver) :
    DeclarationRowView world receiver requested table rows (restoredClauses plans rows nextLexical receiver) := by
  cases authenticated with
  | nil => trivial
  | cons known bodyBound storedReceived ordinary protectedMode rest =>
      exact ⟨OfferAuthentication.restored_mode_view ordinary worldExtended receiverExtended
          (receipt_domain_extend domain) (receipt_range_extend received),
        OfferAuthentication.restored_mode_view protectedMode worldExtended receiverExtended
          (receipt_domain_extend domain) (receipt_range_extend received),
        .canonical rest worldExtended receiverExtended domain received⟩

theorem RestoredDeclarations.view
    (receipt : RestoredDeclarations world receiver requested table before after) :
    DeclarationRowView world receiver requested table before after := by
  cases receipt with
  | same => cases before with
    | nil => trivial
    | cons ordinary protectedMode rest bound =>
        refine ⟨?_, ?_, .same⟩
        · cases ordinary <;> first | trivial | exact fun owner => .same
        · cases protectedMode <;> first | trivial | exact fun owner => .same
  | canonical authenticated worldExtended receiverExtended domain received =>
      exact DeclarationAuthentication.restored_declaration_view authenticated worldExtended receiverExtended domain received

theorem RestoredDeclarations.selected
    (receipt : RestoredDeclarations world receiver effect table before after)
    (selected : ClauseRows.Selected operation held before bodyRows) :
    ∃ nextBodyRows,
      ClauseRows.Selected operation held after nextBodyRows ∧
      ∀ owner, RestoredSourceRows world receiver (bodyRows owner) (nextBodyRows owner) := by
  induction selected generalizing table with
  | ordinary =>
      cases after with
      | cons ordinary protectedMode rest bound =>
          cases ordinary with
          | available bodies => exact ⟨bodies, .ordinary, receipt.view.1⟩
  | protectedMode =>
      cases after with
      | cons ordinary protectedMode rest bound =>
          cases protectedMode with
          | available bodies => exact ⟨bodies, .protectedMode, receipt.view.2.1⟩
  | pass different selected ih =>
      cases after with
      | cons ordinary protectedMode rest bound =>
          obtain ⟨nextBodyRows, nextSelected, bodyReceipts⟩ := ih receipt.view.2.2
          exact ⟨nextBodyRows, .pass different nextSelected, bodyReceipts⟩

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.OfferAuthentication.restored_mode_view
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredDeclarations.selected

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

open SourcePlanSignatures (ClauseSignatures)

theorem RestoredContextReceipts.terminal
    {declarations : ClauseSignatures families} {rows : ClauseRows declarations}
    (terminal : TerminalHandler effect activation rows before)
    (delta : RestoredContextReceipts world ambient before after) :
    ∃ table receiver, ∃ nextRows : ClauseRows declarations,
      RestoredDeclarations world receiver effect table rows nextRows ∧ receiver ⊆ ambient ∧
      TerminalHandler effect activation nextRows after := by
  induction terminal with
  | here => cases delta with
    | handler received rows tail => cases tail with
      | nil => exact ⟨_, _, _, rows, received, .here⟩
  | plain terminal ih => cases delta with
    | plain received rows tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .plain found⟩
  | handler terminal ih => cases delta with
    | handler received rows tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .handler found⟩
  | cell terminal ih => cases delta with
    | cell tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .cell found⟩
  | cleanup terminal ih => cases delta with
    | cleanup received rows tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .cleanup found⟩
  | normal terminal ih => cases delta with
    | normal tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .normal found⟩
  | unwinding terminal ih => cases delta with
    | unwinding tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .unwinding found⟩
  | closing terminal ih => cases delta with
    | closing tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .closing found⟩
  | retiring terminal ih => cases delta with
    | retiring tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .retiring found⟩
  | live terminal ih => cases delta with
    | live saved tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .live found⟩
  | spent terminal ih => cases delta with
    | spent tail => obtain ⟨table, receiver, nextRows, same, received, found⟩ := ih tail; exact ⟨table, receiver, nextRows, same, received, .spent found⟩


theorem RestoredContextReceipts.selected
    (receipt : RestoredContextReceipts world ambient before after)
    (selected : CapturedClauseRows effect operation held before bodyRows) :
    ∃ receiver, ∃ nextBodyRows,
      CapturedClauseRows effect operation held after nextBodyRows ∧ receiver ⊆ ambient ∧
      ∀ owner, RestoredSourceRows world receiver (bodyRows owner) (nextBodyRows owner) := by
  cases selected with
  | selected terminal chosen =>
      obtain ⟨table, receiver, nextRows, declarations, received, nextTerminal⟩ := receipt.terminal terminal
      obtain ⟨nextBodyRows, nextChosen, bodies⟩ := declarations.selected chosen
      exact ⟨receiver, nextBodyRows, .selected nextTerminal nextChosen, received, bodies⟩

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.selected

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableRestoredSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]

open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

theorem RestoredSourceRows.world_weaken (receipt : RestoredSourceRows world receiver before after)
    (larger : world ⊆ nextWorld) : RestoredSourceRows nextWorld receiver before after := by
  induction receipt with
  | same => exact .same
  | canonical authenticated extended receiverExtended domain received =>
      exact .canonical authenticated (extended.trans larger) receiverExtended domain received
  | sequence left right ihLeft ihRight => exact .sequence ihLeft ihRight
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight

theorem RestoredDeclarations.world_weaken (receipt : RestoredDeclarations world receiver effect table before after)
    (larger : world ⊆ nextWorld) : RestoredDeclarations nextWorld receiver effect table before after := by
  cases receipt with
  | same => exact .same
  | canonical authenticated extended receiverExtended domain received =>
      exact .canonical authenticated (extended.trans larger) receiverExtended domain received

theorem RestoredContextReceipts.world_weaken (receipt : RestoredContextReceipts world ambient before after)
    (larger : world ⊆ nextWorld) : RestoredContextReceipts nextWorld ambient before after := by
  induction receipt with
  | nil => exact .nil
  | plain received rows tail ih => exact .plain received (rows.world_weaken larger) ih
  | handler received rows tail ih => exact .handler received (rows.world_weaken larger) ih
  | cleanup received rows tail ih => exact .cleanup received (rows.world_weaken larger) ih
  | cell tail ih => exact .cell ih
  | normal tail ih => exact .normal ih
  | unwinding tail ih => exact .unwinding ih
  | closing tail ih => exact .closing ih
  | retiring tail ih => exact .retiring ih
  | spent tail ih => exact .spent ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail

omit evidence in
private theorem append_subset_right {before after front : List Nat} (larger : before ⊆ after) : front ++ before ⊆ front ++ after := by
  intro token member
  rcases List.mem_append.mp member with visible | ambient
  · exact List.mem_append_left _ visible
  · exact List.mem_append_right _ (larger ambient)

theorem RestoredContextReceipts.ambient_mono (receipt : RestoredContextReceipts world ambient before after)
    (larger : ambient ⊆ nextAmbient) : RestoredContextReceipts world nextAmbient before after := by
  induction receipt generalizing nextAmbient with
  | nil => exact .nil
  | plain received rows tail ih => exact .plain (received.trans (append_subset_right larger)) rows (ih larger)
  | handler received rows tail ih => exact .handler (received.trans (append_subset_right larger)) rows (ih larger)
  | cleanup received rows tail ih => exact .cleanup (received.trans (append_subset_right larger)) rows (ih larger)
  | cell tail ih => exact .cell (ih larger)
  | normal tail ih => exact .normal (ih larger)
  | unwinding tail ih => exact .unwinding (ih larger)
  | closing tail ih => exact .closing (ih larger)
  | retiring tail ih => exact .retiring (ih larger)
  | spent tail ih => exact .spent (ih larger)
  | live saved tail ihSaved ihTail => exact .live (ihSaved (append_subset_right larger)) (ihTail larger)

theorem RestoredContextReceipts.append
    {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    {beforeHead afterHead : Context first} {beforeTail afterTail : Context second}
    (head : RestoredContextReceipts world (secondScope.visibleResources ++ ambient) beforeHead afterHead)
    (tail : RestoredContextReceipts world ambient beforeTail afterTail) :
    RestoredContextReceipts world ambient (beforeHead.append beforeTail) (afterHead.append afterTail) := by
  induction beforeHead with
  | nil => cases head; exact tail
  | plain rows rest ih => cases head with
    | plain received rows tailReceipt =>
        exact .plain (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rows (ih tailReceipt)
  | handler activation rows rest ih => cases head with
    | handler received rows tailReceipt =>
        exact .handler (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rows (ih tailReceipt)
  | cleanup latent rows rest ih => cases head with
    | cleanup received rows tailReceipt =>
        exact .cleanup (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received) rows (ih tailReceipt)
  | cell rest ih => cases head with | cell receipt => exact .cell (ih receipt)
  | normal rest ih => cases head with | normal receipt => exact .normal (ih receipt)
  | unwinding rest ih => cases head with | unwinding receipt => exact .unwinding (ih receipt)
  | closing rest ih => cases head with | closing receipt => exact .closing (ih receipt)
  | retiring owner rest ih => cases head with | retiring receipt => exact .retiring (ih receipt)
  | spent rest ih => cases head with | spent receipt => exact .spent (ih receipt)
  | live saved rest ihSaved ihRest => cases head with
    | live savedReceipt tailReceipt =>
        exact .live (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedReceipt) (ihRest tailReceipt)

end Ash.OneShot.CoreCallableRestoredChecking
#print axioms Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.append

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]
open CoreCallableRestoredChecking
open CoreCallableRestoredSupport
open SourceDependencyChecks.Lexical (ReturnHints)
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

theorem _root_.Ash.OneShot.CoreCallableRestoredChecking.RestoredContextReceipts.callback (receipt : RestoredContextReceipts world ambient before after)
    (mode : LexicalUnwind.UseMode) : RestoredContextReceipts world ambient (before.callback mode) (after.callback mode) := by
  cases mode
  · exact .normal receipt
  · exact .unwinding receipt

theorem CodeChecked.restore_receipts
    {checking : SourcePlanSignatures.Signature dependencies} {rows nextRows : Rows checking}
    {hints : ReturnHints scope} {context nextContext : Context hints}
    {admitted : SourceAdmission.Code outward actions budget phases world installations rows context}
    (checked : CodeChecked ambient outward admitted)
    (rowReceipt : RestoredSourceRows world receiver rows nextRows)
    (received : receiver ⊆ scope.visibleResources ++ ambient)
    (contextReceipt : RestoredContextReceipts world ambient context nextContext) :
    CodeChecked ambient outward (admitted.restore_support rowReceipt.complete contextReceipt.complete) := by
  revert receiver nextRows nextContext
  apply CodeChecked.rec
    (motive_1 := fun {actions budget phases world installations dependencies checking rows scope hints context} admitted _ =>
      ∀ receiver (nextRows : Rows checking) (nextContext : Context hints)
        (rowReceipt : RestoredSourceRows world receiver rows nextRows),
        receiver ⊆ scope.visibleResources ++ ambient →
        ∀ (contextReceipt : RestoredContextReceipts world ambient context nextContext),
        CodeChecked ambient outward (admitted.restore_support rowReceipt.complete contextReceipt.complete))
    (motive_2 := fun {actions budget phases world installations scope outsideScope hints external context outside input output} admitted _ =>
      ∀ (nextContext : Context hints) (nextOutside : Context external)
        (contextReceipt : RestoredContextReceipts world (outsideScope.visibleResources ++ ambient) context nextContext)
        (outsideReceipt : RestoredContextReceipts world ambient outside nextOutside),
        PendingChecked ambient outward (admitted.restore_support contextReceipt.complete outsideReceipt.complete))
    (t := checked)
  · intros
    rename_i receiver nextRows nextContext rows received delta
    cases nextRows; exact .pure
  · intros
    rename_i found receiver nextRows nextContext rows received delta
    cases nextRows; exact .builtin (found := delta.complete.builtin found)
  · intros
    rename_i cut callbacks guarded ownerBound cleanupBudget family bodies bodyRows declarations declarationRows terminal requiredRights selected retained body cleanup waiting clauses ihCleanup ihWaiting ihClauses receiver nextRows nextContext rows received delta
    cases nextRows
    obtain ⟨nextCaptured, nextTail, nextCut, capturedReceipt, tailReceipt⟩ := delta.cut cut
    obtain ⟨bodyReceiver, nextBodies, nextSelected, bodyReceived, bodyReceipts⟩ := capturedReceipt.selected selected
    obtain ⟨table, declarationReceiver, nextDeclarations, declarationReceipt, declarationReceived, nextTerminal⟩ := capturedReceipt.terminal terminal
    let nextBody := fun owner demand fresh (absent : owner ∉ nextContext.ticketNames) =>
      (body owner demand fresh (by simpa only [delta.complete.ticketNames] using absent)).restore_support
        (bodyReceipts owner).complete (RestoredContext.live capturedReceipt.complete tailReceipt.complete)
    refine .request (body := nextBody) (cut := nextCut) (guarded := guarded) (ownerBound := ownerBound)
      (cleanupBudget := RequestBudget.restore_support cleanupBudget delta.complete)
      (selected := nextSelected) (terminal := nextTerminal) (requiredRights := requiredRights)
      (fun disposing => ihCleanup disposing _ _ capturedReceipt (.closing tailReceipt))
      (ihWaiting _ _ delta .nil) ?_
    intro owner demand fresh absent
    exact ihClauses owner demand fresh (by simpa only [delta.complete.ticketNames] using absent)
      _ _ _ (bodyReceipts owner) bodyReceived (.live capturedReceipt tailReceipt)
  · intros
    rename_i front captured tail located known available permission shape restored next ih receiver nextRows nextContext rows received delta
    cases nextRows
    obtain ⟨nextFront, nextLive, rfl, frontReceipt, liveReceipt⟩ := delta.split front (.live captured tail)
    cases liveReceipt with
    | live capturedReceipt tailReceipt =>
      refine .resume (located := located) (known := known) (available := available) (permission := permission)
        (resumeShape := by simpa only [ResumeShape, frontReceipt.complete.closing_same] using shape)
        (ih _ _ ?_ .nil)
      apply RestoredContextReceipts.append
      · apply capturedReceipt.ambient_mono
        intro token member
        simp only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.mem_append, List.mem_nil_iff, false_or] at member ⊢
        exact member.elim (fun kept => Or.inl (Or.inr kept)) Or.inr
      · exact frontReceipt.append (second := .spent tail.hints) (.spent tailReceipt)
  · intros
    rename_i front captured tail located known available permission unprotected abandoned waiting cleanup caller ihCleanup ihCaller receiver nextRows nextContext rows received delta
    cases nextRows
    obtain ⟨nextFront, nextLive, rfl, frontReceipt, liveReceipt⟩ := delta.split front (.live captured tail)
    cases liveReceipt with
    | live capturedReceipt tailReceipt =>
      refine .dispose (located := located) (known := known) (available := available) (permission := permission)
        (unprotected := unprotected)
        (ihCleanup _ _ ?_ (.closing (frontReceipt.append (second := .spent tail.hints) (.spent tailReceipt))))
        (ihCaller _ _ (frontReceipt.append (second := .spent tail.hints) (.spent tailReceipt)) .nil)
      apply capturedReceipt.ambient_mono
      intro token member
      simp only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.mem_append] at member ⊢
      exact member.elim (fun kept => Or.inl (Or.inr kept)) Or.inr
  · intros
    rename_i first second left right ihLeft ihRight receiver nextRows nextContext rows received delta
    cases nextRows with
    | choice nextFirst nextSecond =>
      exact .choice (ihLeft _ _ _ rows.view.1 received delta) (ihRight _ _ _ rows.view.2 received delta)
  · intros
    rename_i body callback inside closing ihBody ihCallback receiver nextRows nextContext rows received delta
    cases nextRows with
    | cleanup nextLatent nextCallback nextBody =>
      obtain ⟨latentSame, callbackRows, bodyRows⟩ := rows.view
      subst nextLatent
      exact .cleanup (ihBody _ _ _ bodyRows received (.cleanup received callbackRows delta))
        (ihCallback _ _ _ callbackRows received (.normal delta))
  · intros
    rename_i body inside ih receiver nextRows nextContext rows received delta
    cases nextRows with
    | resource nextBodies =>
      exact .resource (fun identity fresh => ih identity fresh _ _ _ (rows.view identity)
        (by intro token member; exact List.mem_cons_of_mem identity (received member))
        (.cell (delta.world_weaken (by intro token member; exact List.mem_append_left _ member))))
  · intros
    rename_i first second left right ihLeft ihRight receiver nextRows nextContext rows received delta
    cases nextRows with
    | sequence nextFirst nextSecond =>
      exact .sequence (ihLeft _ _ _ rows.view.1 received (.plain received rows.view.2 delta))
        (ihRight _ _ _ rows.view.2 received delta)
  · intros
    rename_i body supported inside ih receiver nextRows nextContext rows received delta
    cases nextRows with
    | handler nextDeclarations nextBody =>
      obtain ⟨declarationRows, bodyRows⟩ := rows.handler_parts
      exact .handler (declarationRows.supported supported received)
        (fun activation fresh => ih activation fresh _ _ _ bodyRows received (.handler received declarationRows delta))
  · intros
    rename_i nextContext nextOutside delta outsideDelta
    cases delta; exact .nil
  · intros
    rename_i code tail body waiting ihBody ihWaiting nextContext nextOutside delta outsideDelta
    cases delta with
    | plain received rows restDelta =>
      exact .plain (ihBody _ _ _ rows (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received)
        (restDelta.append outsideDelta)) (ihWaiting _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with
    | plain received rows restDelta => exact .skipped (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with
    | handler received rows restDelta => exact .handler (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with
    | cell restDelta => exact .cell (ih _ _ restDelta outsideDelta)
  · intros
    rename_i callback tail checked waiting ihCallback ihWaiting nextContext nextOutside delta outsideDelta
    cases delta with
    | cleanup received rows restDelta =>
      exact .cleanup (ihCallback _ _ _ rows (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received)
        ((restDelta.append outsideDelta).callback _))
        (ihWaiting _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with | normal restDelta => exact .normal (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with | unwinding restDelta => exact .unwinding (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with | closing restDelta => exact .closing (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with | retiring restDelta => exact .retiring (ih _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail held waiting ihSaved ihWaiting nextContext nextOutside delta outsideDelta
    cases delta with
    | live savedDelta restDelta =>
      exact .live (ihSaved _ _ (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedDelta)
        (restDelta.append outsideDelta)) (ihWaiting _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail held waiting ihSaved ihWaiting nextContext nextOutside delta outsideDelta
    cases delta with
    | live savedDelta restDelta =>
      exact .opening (ihSaved _ _ (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedDelta)
        (.retiring (restDelta.append outsideDelta))) (ihWaiting _ _ restDelta outsideDelta)
  · intros
    rename_i tail waiting ih nextContext nextOutside delta outsideDelta
    cases delta with | spent restDelta => exact .spent (ih _ _ restDelta outsideDelta)

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked.restore_receipts

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open SourcePlannedChecks (DeclarationPolicy)
variable [evidence : DeclarationPolicy]
open CoreCallableRestoredChecking
open CoreCallableRestoredSupport
open SourceDependencyChecks.Lexical (ReturnHints)

theorem PendingChecked.restore_receipts
    {phases : OwnerPhaseTransitions.Phases}
    {hints : ReturnHints scope} {external : ReturnHints outsideScope}
    {context nextContext : Context hints} {outside nextOutside : Context external}
    {admitted : SourceAdmission.Pending outward actions budget phases world installations context outside input output}
    (checked : PendingChecked ambient outward admitted)
    (contextReceipt : RestoredContextReceipts world (outsideScope.visibleResources ++ ambient) context nextContext)
    (outsideReceipt : RestoredContextReceipts world ambient outside nextOutside) :
    PendingChecked ambient outward (admitted.restore_support contextReceipt.complete outsideReceipt.complete) := by
  revert nextContext nextOutside
  induction context generalizing outsideScope input output with
  | nil =>
      intro nextContext nextOutside delta outsideDelta
      cases delta; cases checked; exact .nil
  | plain rows rest ih => cases checked with
    | plain body waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with
      | plain received rows restDelta =>
        exact .plain (body.restore_receipts rows
          (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received)
          (restDelta.append outsideDelta)) (ih waiting restDelta outsideDelta)
    | skipped waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | plain received rows restDelta => exact .skipped (ih waiting restDelta outsideDelta)
  | handler activation rows rest ih => cases checked with
    | handler waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | handler received rows restDelta => exact .handler (ih waiting restDelta outsideDelta)
  | cell rest ih => cases checked with
    | cell waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | cell restDelta => exact .cell (ih waiting restDelta outsideDelta)
  | cleanup latent rows rest ih => cases checked with
    | cleanup callback waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with
      | cleanup received rows restDelta =>
        exact .cleanup (callback.restore_receipts rows
          (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using received)
          ((restDelta.append outsideDelta).callback _)) (ih waiting restDelta outsideDelta)
  | normal rest ih => cases checked with
    | normal waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | normal restDelta => exact .normal (ih waiting restDelta outsideDelta)
  | unwinding rest ih => cases checked with
    | unwinding waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | unwinding restDelta => exact .unwinding (ih waiting restDelta outsideDelta)
  | closing rest ih => cases checked with
    | closing waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | closing restDelta => exact .closing (ih waiting restDelta outsideDelta)
  | retiring owner rest ih => cases checked with
    | retiring waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | retiring restDelta => exact .retiring (ih waiting restDelta outsideDelta)
  | live saved rest ihSaved ihRest => cases checked with
    | live held waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with
      | live savedDelta restDelta =>
        exact .live (ihSaved held
          (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedDelta)
          (restDelta.append outsideDelta)) (ihRest waiting restDelta outsideDelta)
    | opening held waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with
      | live savedDelta restDelta =>
        exact .opening (ihSaved held
          (by simpa only [SourceDependencyCapture.Scope.visibleResources, scope_visible_append, List.append_assoc] using savedDelta)
          (.retiring (restDelta.append outsideDelta))) (ihRest waiting restDelta outsideDelta)
  | spent rest ih => cases checked with
    | spent waiting =>
      intro nextContext nextOutside delta outsideDelta
      cases delta with | spent restDelta => exact .spent (ih waiting restDelta outsideDelta)

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.PendingChecked.restore_receipts
