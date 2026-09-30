import SourceScheduledSurvivingRequirements
import SourceConsumingCleanupAdmission

/-! Derive handler receiver changes from original operation interfaces. The
structural view covers both compact annotations and expanded retained frames,
including callbacks and dormant captures. No target admission is supplied. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints checkRequirements)
open SourceHandlerRequirements

/-- An exact finite test for insertion at a known boundary, assuming the
original interface checked. Matching providers in the retained source or in
its unchanged receiver prefix discharge requirements before interception. -/
theorem Interfaces.check_handler_insert
    {hints : Hints scope} {forest : SourceRetainedPlans.Forest hints}
    (interfaces : Interfaces world forest)
    (ready : interfaces.check (front.append outside) = true) :
    interfaces.check (front.append (.handler effect table families outside)) = true ↔
      checkRequirements (.handler effect table families .nil)
        (intercepted effect (outwardRequirements front interfaces.exposed)) = true := by
  have original := interfaces.exposed_requirements ready
  rw [interfaces.check_replace_iff ready, requirements_replace_iff original]
  exact requirements_handler_insert (requirements_outward original)

private theorem Interfaces.handler_check
    {hints : Hints scope} {forest : SourceRetainedPlans.Forest hints}
    (interfaces : Interfaces world forest) (ready : interfaces.check outside = true)
    (checked : checkRequirements (.handler effect table families .nil)
      (intercepted effect interfaces.exposed) = true) :
    interfaces.check (.handler effect table families outside) = true := by
  apply (interfaces.check_handler_insert (front := .nil) ready).mpr
  have filtered : interfaces.exposed.filter (fun _ => true) = interfaces.exposed :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [outwardRequirements, reaches, filtered] using checked

private theorem Interfaces.handler_running_check
    {hints : Hints scope} {forest : SourceRetainedPlans.Forest hints}
    (interfaces : Interfaces world forest) (ready : interfaces.check (.running outside) = true)
    (checked : checkRequirements (.handler effect table families .nil)
      (intercepted effect interfaces.exposed) = true) :
    interfaces.check (.running (.handler effect table families outside)) = true := by
  apply (interfaces.check_handler_insert (front := .running .nil) ready).mpr
  have filtered : interfaces.exposed.filter (fun _ => true) = interfaces.exposed :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [outwardRequirements, reaches, filtered] using checked

private theorem Interfaces.provider_check
    {hints : Hints scope} {forest : SourceRetainedPlans.Forest hints}
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : SourceRetainedPlans.Forest beforeHints} {after : SourceRetainedPlans.Forest afterHints}
    (interfaces : Interfaces world forest) (ready : interfaces.check beforeScope = true)
    (changed : SourceScheduledProviders.Insertion identity before after) :
    interfaces.check afterScope = true :=
  interfaces.check_transport ready (changed.erase.requirements (interfaces.exposed_requirements ready))

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledRetainedInterfaces (Interfaces)

/-- A structural view of original source whose code positions carry operation
footprints. This does not replace the source or erase its annotation. Free owner
invocations and selected-request annotations retain their richer rules. -/
inductive OperationSource [DeclarationPolicy] :
    {world : List Nat} → {scope outsideScope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → {outsideHints : Hints outsideScope} →
    {forest : Forest hints} → {outside : Forest outsideHints} →
    Retained world forest outside → Interfaces world forest → Prop where
  | operations : OperationSource (.operations interfaces) interfaces
  | plain {rest : Forest restHints} {tail : Retained world rest outside}
      {interfaces : Interfaces world rest} : OperationSource tail interfaces →
      OperationSource (.plain (.operations required footprint declared) tail)
        (.plain rest required footprint declared interfaces)
  | handler {rest : Forest restHints} {tail : Retained world rest outside}
      {interfaces : Interfaces world rest} : OperationSource tail interfaces →
      OperationSource (.handler (effect := effect) (table := table) (families := families)
        (required := required) tail) (.handler rest interfaces)
  | cell : OperationSource tail interfaces →
      OperationSource (.cell (identity := identity) tail) (.cell interfaces)
  | cleanup {rest : Forest restHints} {tail : Retained world rest outside}
      {interfaces : Interfaces world rest} : OperationSource tail interfaces →
      OperationSource (.cleanup (needs := needs) (.operations required footprint declared) tail)
        (.cleanup rest required footprint declared interfaces)
  | running : OperationSource tail interfaces → OperationSource (.running tail) (.running interfaces)
  | live {rest : Forest restHints} {tail : Retained world rest outside}
      {saved : Retained world captured (rest.append outside)}
      {interfaces : Interfaces world rest} : OperationSource saved inside → OperationSource tail interfaces →
      OperationSource (.live (owner := owner) saved tail) (.live rest inside interfaces)
  | spent : OperationSource tail interfaces → OperationSource (.spent (owner := owner) tail) (.spent interfaces)

variable [DeclarationPolicy]

/-- Read the interface from actual source constructors. Rich selected requests
and free continuation invocations return none; this is a representation test,
not a rejection of those programs by the calculus. -/
def OperationSource.extract {sourceHints : Hints sourceScope} {forest : Forest sourceHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world forest outside) :
    Option { interfaces : Interfaces world forest // OperationSource source interfaces } :=
  match source with
  | .operations interfaces => some ⟨interfaces, .operations⟩
  | .plain (.operations required footprint declared) tail =>
      (extract tail).map (fun result => ⟨.plain _ required footprint declared result.val, .plain result.property⟩)
  | .plain _ _ => none
  | .handler tail => (extract tail).map (fun result => ⟨.handler _ result.val, .handler result.property⟩)
  | .cell tail => (extract tail).map (fun result => ⟨.cell result.val, .cell result.property⟩)
  | .cleanup (.operations required footprint declared) tail =>
      (extract tail).map (fun result => ⟨.cleanup _ required footprint declared result.val, .cleanup result.property⟩)
  | .cleanup _ _ => none
  | .running tail => (extract tail).map (fun result => ⟨.running result.val, .running result.property⟩)
  | .live saved tail =>
      match extract saved, extract tail with
      | some inside, some rest => some ⟨.live _ inside.val rest.val, .live inside.property rest.property⟩
      | _, _ => none
  | .spent tail => (extract tail).map (fun result => ⟨.spent result.val, .spent result.property⟩)

/-- Extraction succeeds on every source represented by this structural view,
with exactly its interface, including duplicate operation requirements. -/
theorem OperationSource.extract_complete
    {source : Retained world forest outside} (view : OperationSource source interfaces) :
    OperationSource.extract source = some ⟨interfaces, view⟩ := by
  induction view <;> simp_all only [OperationSource.extract, Option.map_some]

/-- Failure identifies precisely the absence of this operation-only view;
it says nothing about the richer source judgments. -/
theorem OperationSource.extract_none_iff {source : Retained world forest outside} :
    OperationSource.extract source = none ↔ ¬ ∃ interfaces, OperationSource source interfaces := by
  constructor
  · intro absent ⟨interfaces, view⟩
    rw [view.extract_complete] at absent
    cases absent
  · intro absent
    cases found : OperationSource.extract source with
    | none => rfl
    | some result => exact False.elim (absent ⟨result.val, result.property⟩)

/-- Compaction to the extracted interface preserves the complete retained
snapshot. No handler bounds or recursive owner annotations can be hidden by
this view: each represented code position was already operation-only. -/
theorem OperationSource.bounds
    {source : Retained world forest outside} (view : OperationSource source interfaces) :
    SourceBoundSnapshots.Retained.ofCapability source = SourceBoundSnapshots.Retained.absent forest := by
  induction view <;> simp_all only [SourceBoundSnapshots.Retained.ofCapability,
    SourceBoundSnapshots.Retained.absent, SourcePlanBounds.ofCode]

/-- The source view extends with the resource world by the existing source
and interface maps. Actual plans and their operation requirements are unchanged. -/
theorem OperationSource.world_weaken
    {source : Retained world forest outside} (view : OperationSource source interfaces)
    (larger : world ⊆ nextWorld) :
    OperationSource (source.world_weaken larger) (interfaces.world_weaken larger) := by
  induction view with
  | operations => exact .operations
  | plain tail ih => exact .plain (ih larger)
  | handler tail ih => exact .handler (ih larger)
  | cell tail ih => exact .cell (ih larger)
  | cleanup tail ih => exact .cleanup (ih larger)
  | running tail ih => exact .running (ih larger)
  | live saved tail ihSaved ihTail => exact .live (ihSaved larger) (ihTail larger)
  | spent tail ih => exact .spent (ih larger)

/-- The view has exactly the checks of the actual original annotation.
There is no permission or phase information hidden in operation requirements. -/
theorem OperationSource.valid_iff
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {source : Retained world forest outside} (view : OperationSource source interfaces) :
    source.Valid outward actions phases ↔ interfaces.check outsideScope = true := by
  induction view <;> simp_all only [Retained.Valid, Code.Valid, Interfaces.check, Bool.and_eq_true] <;> rfl

/-- Reuse the original source tree while deriving every retained receiver
rule. Code leaves keep their existing footprints; the compiler retains metadata. -/
theorem OperationSource.receiver
    {source : Retained world forest outside} (view : OperationSource source interfaces)
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (checked : interfaces.check nextScope = true) : ReceiverChange outward actions phases source next := by
  induction view generalizing nextScope with
  | operations => exact .operations _ checked
  | plain tail ih =>
      obtain ⟨code, rest⟩ := Bool.and_eq_true_iff.mp checked
      exact .plain (.operations code) (ih rest)
  | handler tail ih =>
      obtain ⟨requirements, rest⟩ := Bool.and_eq_true_iff.mp checked
      exact .handler requirements (ih rest)
  | cell tail ih => exact .cell (ih checked)
  | cleanup tail ih =>
      obtain ⟨code, rest⟩ := Bool.and_eq_true_iff.mp checked
      exact .cleanup (.operations code) (ih rest)
  | running tail ih => exact .running (ih checked)
  | live saved tail ihSaved ihTail =>
      obtain ⟨inside, rest⟩ := Bool.and_eq_true_iff.mp checked
      exact .live (ihSaved inside) (ihTail rest)
  | spent tail ih => exact .spent (ih checked)

/-- An outside-owner resume authenticates the saved interface against its
actual recursive annotation. A changed caller is checked independently; the
waiting annotation is reused, including any further owner calls it contains.
Only the callee's saved source and the old caller need operation views. -/
theorem Expression.resume_from_bound
    {oldHints : Hints oldScope} {nextHints : Hints nextScope}
    {oldFrontHints : Hints oldFrontScope} {nextFrontHints : Hints nextFrontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {old : Forest oldHints} {next : Forest nextHints}
    {oldFront : Forest oldFrontHints} {nextFront : Forest nextFrontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (oldCut : SourceScheduledNeutral.OwnerCut owner old oldFront saved waiting)
    (nextCut : SourceScheduledNeutral.OwnerCut owner next nextFront saved waiting)
    {inside : Retained world saved (oldFront.append (.spent (owner := owner) waiting))}
    (oldCaller : Interfaces world oldFront) (caller : Interfaces world nextFront)
    (after : Retained world waiting .nil)
    {interfaces : Interfaces world saved}
    (view : OperationSource inside interfaces)
    (original : (Code.resume oldCut inside (.operations oldCaller) after).Valid outward actions phases)
    (bounded : interfaces.exposed ⊆ required)
    (supplied : SourceContextualHints.checkRequirements
      (nextFrontScope.append (.spent owner waitingScope)) required = true)
    (callerChecked : caller.check (.spent owner waitingScope) = true) :
    Expression outward actions phases (Code.resume oldCut inside (.operations oldCaller) after) next := by
  apply Expression.resume nextCut
  · exact (view.receiver (interfaces.check_from_bound
      (view.valid_iff.mp original.2.2.1) bounded supplied)).rechecking
  · exact .operations caller callerChecked
  · exact .same

/-- Disposal uses the independently authenticated closing interface. The
original annotation supplies the owner permission, phase and closing route;
the finite contract supplies callback requirements at the changed receiver. -/
theorem Expression.dispose_from_bound
    {oldHints : Hints oldScope} {nextHints : Hints nextScope}
    {oldFrontHints : Hints oldFrontScope} {nextFrontHints : Hints nextFrontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {old : Forest oldHints} {next : Forest nextHints}
    {oldFront : Forest oldFrontHints} {nextFront : Forest nextFrontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (oldCut : SourceScheduledNeutral.OwnerCut owner old oldFront saved waiting)
    (nextCut : SourceScheduledNeutral.OwnerCut owner next nextFront saved waiting)
    {closing : Retained world saved.forClosing (.running (oldFront.append (.spent (owner := owner) waiting)))}
    (oldCaller : Interfaces world oldFront) (caller : Interfaces world nextFront)
    (after : Retained world waiting .nil)
    {interfaces : Interfaces world saved.forClosing}
    (view : OperationSource closing interfaces)
    (original : (Code.dispose oldCut closing (.operations oldCaller) after).Valid outward actions phases)
    (bounded : interfaces.exposed ⊆ required)
    (supplied : SourceContextualHints.checkRequirements
      (.running (nextFrontScope.append (.spent owner waitingScope))) required = true)
    (callerChecked : caller.check (.spent owner waitingScope) = true) :
    Expression outward actions phases (Code.dispose oldCut closing (.operations oldCaller) after) next := by
  apply Expression.dispose nextCut
  · exact (view.receiver (interfaces.check_from_bound
      (view.valid_iff.mp original.2.2.2.2.1) bounded supplied)).rechecking
  · exact .operations caller callerChecked
  · exact .same

/-- All retained frames use the same exact interception test. Only the
inserted table is checked; unrelated outside operations reuse original validity. -/
theorem OperationSource.handler_receiver
    {leadingHints : Hints leadingScope} {waitingHints : Hints waitingScope}
    (leading : Forest leadingHints) (waiting : Forest waitingHints)
    {source : Retained world forest (leading.append waiting)}
    (view : OperationSource source interfaces) (ready : source.Valid outward actions phases)
    (checked : SourceContextualHints.checkRequirements (.handler effect table families .nil)
      (SourceHandlerRequirements.intercepted effect
        (SourceHandlerRequirements.outwardRequirements leadingScope interfaces.exposed)) = true) :
    ReceiverChange outward actions phases source
      (leading.append (.handler (effect := effect) (table := table) (families := families)
        (required := required) waiting)) :=
  view.receiver ((interfaces.check_handler_insert (view.valid_iff.mp ready)).mpr checked)

/-- Immediate insertion is the resumption receiver used at handler entry. -/
theorem OperationSource.handler_here
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {source : Retained world forest outside}
    (view : OperationSource source interfaces) (ready : source.Valid outward actions phases)
    (checked : SourceContextualHints.checkRequirements (.handler effect table families .nil)
      (SourceHandlerRequirements.intercepted effect interfaces.exposed) = true) :
    ReceiverChange outward actions phases source
      (.handler (effect := effect) (table := table) (families := families) (required := required) outside) := by
  apply view.handler_receiver .nil outside ready
  have filtered : interfaces.exposed.filter (fun _ => true) = interfaces.exposed :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [SourceHandlerRequirements.outwardRequirements, SourceHandlerRequirements.reaches, filtered] using checked

/-- Closing retains its running boundary while inserting the same table. -/
theorem OperationSource.handler_running
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {source : Retained world forest (.running outside)}
    (view : OperationSource source interfaces) (ready : source.Valid outward actions phases)
    (checked : SourceContextualHints.checkRequirements (.handler effect table families .nil)
      (SourceHandlerRequirements.intercepted effect interfaces.exposed) = true) :
    ReceiverChange outward actions phases source
      (.running (.handler (effect := effect) (table := table) (families := families) (required := required) outside)) := by
  apply view.handler_receiver (.running .nil) outside ready
  have filtered : interfaces.exposed.filter (fun _ => true) = interfaces.exposed :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [SourceHandlerRequirements.outwardRequirements, SourceHandlerRequirements.reaches, filtered] using checked

/-- Cleanup insertion does not change uniform operation selection. Its own
callback check remains in clause admission, separate from these retained sites. -/
theorem OperationSource.cleanup_here
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {source : Retained world forest outside}
    (view : OperationSource source interfaces) (ready : source.Valid outward actions phases)
    (callback : SourceDeclarationPlans.Plan dependencies) (needs : List Instance) :
    ReceiverChange outward actions phases source (.cleanup (needs := needs) callback outside) :=
  view.receiver ((SourceScheduledCleanupGeneration.interfaces_receiver interfaces
    (SourceScheduledCleanupInsertion.Insertion.here (needs := needs) (callback := callback)
      (before := outside))).symm.trans (view.valid_iff.mp ready))

theorem OperationSource.cleanup_running
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {source : Retained world forest (.running outside)}
    (view : OperationSource source interfaces) (ready : source.Valid outward actions phases)
    (callback : SourceDeclarationPlans.Plan dependencies) (needs : List Instance) :
    ReceiverChange outward actions phases source (.running (.cleanup (needs := needs) callback outside)) :=
  view.receiver ((SourceScheduledCleanupGeneration.interfaces_receiver interfaces
    (SourceScheduledCleanupInsertion.Insertion.running
      (SourceScheduledCleanupInsertion.Insertion.here (needs := needs) (callback := callback)
        (before := outside)))).symm.trans (view.valid_iff.mp ready))

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_handler_insert
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.valid_iff
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.receiver
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.handler_receiver

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.handler_here
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.handler_running

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledSourceRechecking (OperationSource)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceHandlerRequirements (intercepted)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Handler entry derives both receiver changes from structural views of the
actual saved/closing source and finite intercepted-operation checks. The inner
body retains the existing recursive admission obligation. -/
theorem At.handler_interfaces
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases whole front saved waiting}
    {plans : ClausePlans clauses families} {code : Body world owner plan}
    (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans)
    (declared : declarations.accepts required plans)
    (resumption : ∀ _permission : (actions owner).any (fun rights => rights.resume) = true,
      Interfaces world saved)
    (resumeSource : ∀ permission, OperationSource (context.resumption permission).val (resumption permission))
    (resumeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (resumption permission).exposed) = true)
    (closing : ∀ _permission : (actions owner).any (fun rights => rights.dispose) = true,
      Interfaces world saved.forClosing)
    (closeSource : ∀ permission, OperationSource (context.closing permission).val (closing permission))
    (closeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (closing permission).exposed) = true)
    (inner : At laws (@project) code
      (context.handler laws (@project) effect table families required
        (fun permission => (resumeSource permission).handler_here
          (context.resumption permission).property (resumeChecked permission))
        (fun permission => (closeSource permission).handler_running
          (context.closing permission).property (closeChecked permission)))) :
    At laws (@project) (.handler (effect := effect) (table := table) bounds declared code) context :=
  .handler bounds declared
    (fun permission => (resumeSource permission).handler_here
      (context.resumption permission).property (resumeChecked permission))
    (fun permission => (closeSource permission).handler_running
      (context.closing permission).property (closeChecked permission)) inner

/-- Structural views of both actual saved-source branches. These fields
contain original annotation evidence; operation and continuation checks remain
in the context and its existing source judgments. -/
structure Context.OperationSources
    (context : Context world owner outward actions phases whole front saved waiting) where
  resumption : ∀ _permission : (actions owner).any (fun rights => rights.resume) = true,
    Interfaces world saved
  resumeSource : ∀ permission, OperationSource (context.resumption permission).val (resumption permission)
  closing : ∀ _permission : (actions owner).any (fun rights => rights.dispose) = true,
    Interfaces world saved.forClosing
  closeSource : ∀ permission, OperationSource (context.closing permission).val (closing permission)

section
variable {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {context : Context world owner outward actions phases whole front saved waiting}

/-- Construct the actual successor source explicitly. Compact interfaces
preserve the original snapshots and remain inspectable at the next entry;
there is no choice of an annotation from a validity-only existence proof. -/
def Context.OperationSources.handler (source : context.OperationSources)
    (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (required : List SourceContextualHints.Requirement)
    (resumeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.resumption permission).exposed) = true)
    (closeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.closing permission).exposed) = true) :
    Context world owner outward actions phases
      (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
      (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting where
  cut := .handler context.cut
  before := .handler front context.before
  resumption := fun permission => ⟨.operations (source.resumption permission),
    (source.resumption permission).handler_check
      ((source.resumeSource permission).valid_iff.mp (context.resumption permission).property)
      (resumeChecked permission)⟩
  closing := fun permission => ⟨.operations (source.closing permission),
    (source.closing permission).handler_running_check
      ((source.closeSource permission).valid_iff.mp (context.closing permission).property)
      (closeChecked permission)⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Every permitted branch keeps its original metadata, and the waiting tail
is reused literally. This is stronger than merely constructing a valid context. -/
theorem Context.OperationSources.handler_bounds (source : context.OperationSources)
    (resumeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.resumption permission).exposed) = true)
    (closeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.closing permission).exposed) = true) :
    context.BoundsAgree (source.handler effect table families required resumeChecked closeChecked) :=
  ⟨fun permission => (source.resumeSource permission).bounds.symm,
    fun permission => (source.closeSource permission).bounds.symm, rfl⟩

/-- The same extracted interfaces are available after entry. This is the
source-shape fact needed to compose nested handler derivations. -/
def Context.OperationSources.after_handler (source : context.OperationSources)
    (resumeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.resumption permission).exposed) = true)
    (closeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.closing permission).exposed) = true) :
    (source.handler effect table families required resumeChecked closeChecked).OperationSources where
  resumption := source.resumption
  resumeSource := fun _ => .operations
  closing := source.closing
  closeSource := fun _ => .operations

/-- Admit the same handler through the existing structural rule while allowing
its body to use the explicit, interface-retaining successor. The old rule's
chosen witness is bridged by the established exact-metadata transport rule. -/
theorem At.handler_retaining_interfaces
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {plans : ClausePlans clauses families} {code : Body world owner plan}
    (source : context.OperationSources)
    (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans)
    (declared : declarations.accepts required plans)
    (resumeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.resumption permission).exposed) = true)
    (closeChecked : ∀ permission, checkRequirements (.handler effect table families .nil)
      (intercepted effect (source.closing permission).exposed) = true)
    (inner : At laws (@project) code
      (source.handler effect table families required resumeChecked closeChecked)) :
    At laws (@project) (.handler (effect := effect) (table := table) bounds declared code) context := by
  apply At.handler_interfaces bounds declared source.resumption source.resumeSource resumeChecked
    source.closing source.closeSource closeChecked
  have explicitBounds := source.handler_bounds (required := required) resumeChecked closeChecked
  have oldBounds := context.handler_bounds laws (@project) effect table families required
    (fun permission => (source.resumeSource permission).handler_here
      (context.resumption permission).property (resumeChecked permission))
    (fun permission => (source.closeSource permission).handler_running
      (context.closing permission).property (closeChecked permission))
  exact .sameReceiver
    (original := source.handler effect table families required resumeChecked closeChecked) rfl
    ⟨fun permission => (oldBounds.resumption permission).trans (explicitBounds.resumption permission).symm,
      fun permission => (oldBounds.closing permission).trans (explicitBounds.closing permission).symm, rfl⟩ inner

/-- Cleanup registration retains the extracted interfaces for the next source
entry. The new callback remains the actual caller frame with its own footprint. -/
def Context.OperationSources.cleanup (source : context.OperationSources)
    {callback : SourceDeclarationPlans.Plan dependencies}
    (footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required)
    (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback))
    (needs : List Instance) :
    Context world owner outward actions phases (.cleanup (needs := needs) callback whole)
      (.cleanup (needs := needs) callback front) saved waiting where
  cut := .cleanup context.cut
  before := .cleanup front required footprint declared context.before
  resumption := fun permission => ⟨.operations (source.resumption permission),
    (SourceScheduledCleanupGeneration.interfaces_receiver (source.resumption permission)
      (SourceScheduledCleanupInsertion.Insertion.here (needs := needs) (callback := callback)
        (before := front.append (.spent (owner := owner) waiting)))).symm.trans
      ((source.resumeSource permission).valid_iff.mp (context.resumption permission).property)⟩
  closing := fun permission => ⟨.operations (source.closing permission),
    (SourceScheduledCleanupGeneration.interfaces_receiver (source.closing permission)
      (SourceScheduledCleanupInsertion.Insertion.running
        (SourceScheduledCleanupInsertion.Insertion.here (needs := needs) (callback := callback)
          (before := front.append (.spent (owner := owner) waiting))))).symm.trans
      ((source.closeSource permission).valid_iff.mp (context.closing permission).property)⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem Context.OperationSources.cleanup_bounds (source : context.OperationSources)
    {callback : SourceDeclarationPlans.Plan dependencies}
    (footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required)
    (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback))
    (needs : List Instance) : context.BoundsAgree (source.cleanup footprint declared needs) :=
  ⟨fun permission => (source.resumeSource permission).bounds.symm,
    fun permission => (source.closeSource permission).bounds.symm, rfl⟩

def Context.OperationSources.after_cleanup (source : context.OperationSources)
    {callback : SourceDeclarationPlans.Plan dependencies}
    (footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required)
    (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback))
    (needs : List Instance) : (source.cleanup footprint declared needs).OperationSources where
  resumption := source.resumption
  resumeSource := fun _ => .operations
  closing := source.closing
  closeSource := fun _ => .operations

/-- Derive cleanup entry without losing the source evidence used by subsequent
handler entries. Callback coverage and the recursive body rule are unchanged. -/
theorem At.cleanup_retaining_interfaces
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {code : Body world owner plan} (source : context.OperationSources)
    {callback : SourceDeclarationPlans.Plan dependencies}
    {footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required}
    {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback)}
    (covered : ∀ request ∈ required, request.1 ∈ needs)
    (inner : At laws (@project) code (source.cleanup footprint declared needs)) :
    At laws (@project) (.cleanup (needs := needs) required footprint declared code) context := by
  apply At.cleanupSource covered
    (fun permission => (source.resumeSource permission).cleanup_here
      (context.resumption permission).property callback needs)
    (fun permission => (source.closeSource permission).cleanup_running
      (context.closing permission).property callback needs)
  have explicitBounds := source.cleanup_bounds footprint declared needs
  have oldBounds := context.cleanupSource_bounds laws (@project) footprint declared needs
    (fun permission => (source.resumeSource permission).cleanup_here
      (context.resumption permission).property callback needs)
    (fun permission => (source.closeSource permission).cleanup_running
      (context.closing permission).property callback needs)
  exact .sameReceiver (original := source.cleanup footprint declared needs) rfl
    ⟨fun permission => (oldBounds.resumption permission).trans (explicitBounds.resumption permission).symm,
      fun permission => (oldBounds.closing permission).trans (explicitBounds.closing permission).symm, rfl⟩ inner

/-- Resource entry extends the original interfaces into the larger world
and inserts the actual builtin provider. Saved and closing views remain explicit. -/
def Context.OperationSources.resource (source : context.OperationSources) (identity : Nat) :
    Context (world ++ [identity]) owner outward actions phases (.cell (identity := identity) whole)
      (.cell (identity := identity) front) saved waiting where
  cut := .cell context.cut
  before := .cell (context.before.world_weaken (List.subset_append_left _ _))
  resumption := fun permission => ⟨.operations ((source.resumption permission).world_weaken (List.subset_append_left _ _)), by
    dsimp only [SourceScheduledCapabilityAnnotations.Retained.Valid]
    rw [SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken]
    exact (source.resumption permission).provider_check
      ((source.resumeSource permission).valid_iff.mp (context.resumption permission).property)
      (SourceScheduledProviders.Insertion.here
        (before := front.append (.spent (owner := owner) waiting)))⟩
  closing := fun permission => ⟨.operations ((source.closing permission).world_weaken (List.subset_append_left _ _)), by
    dsimp only [SourceScheduledCapabilityAnnotations.Retained.Valid]
    rw [SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken]
    exact (source.closing permission).provider_check
      ((source.closeSource permission).valid_iff.mp (context.closing permission).property)
      (SourceScheduledProviders.Insertion.running (SourceScheduledProviders.Insertion.here
        (before := front.append (.spent (owner := owner) waiting))))⟩
  disposal := context.disposal
  after := context.after.world_weaken (List.subset_append_left _ _)
  tailReady := context.after.world_weaken_valid (List.subset_append_left _ _) context.tailReady

def Context.OperationSources.after_resource (source : context.OperationSources) (identity : Nat) :
    (source.resource identity).OperationSources where
  resumption := fun permission => (source.resumption permission).world_weaken (List.subset_append_left _ _)
  resumeSource := fun _ => .operations
  closing := fun permission => (source.closing permission).world_weaken (List.subset_append_left _ _)
  closeSource := fun _ => .operations

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- All permitted source projections are exactly the original world extensions. -/
theorem Context.OperationSources.resource_bounds (source : context.OperationSources) (identity : Nat) :
    (source.resource identity).continuationBounds =
      context.continuationBounds.world_weaken (List.subset_append_left world [identity]) := by
  simp only [Context.continuationBounds, SourceConsumingClauseAnnotations.ContinuationBounds.world_weaken,
    SourceConsumingClauseAnnotations.ContinuationBounds.mk.injEq]
  refine ⟨funext (fun permission => ?_), funext (fun permission => ?_), ?_⟩
  · exact ((source.resumeSource permission).world_weaken (List.subset_append_left _ _)).bounds.symm.trans
      ((context.resumption permission).val.ofCapability_world_weaken (List.subset_append_left _ _))
  · exact ((source.closeSource permission).world_weaken (List.subset_append_left _ _)).bounds.symm.trans
      ((context.closing permission).val.ofCapability_world_weaken (List.subset_append_left _ _))
  · exact context.after.ofCapability_world_weaken (List.subset_append_left _ _)

/-- Fresh-resource families use the retained source interfaces at each fresh
identity. Existing resource metadata preservation connects to the same At rule. -/
theorem At.resource_retaining_interfaces
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
    {plans : ∀ identity, SourceDeclarationPlans.Plan (dependencies identity)}
    {code : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
    (source : context.OperationSources)
    (inner : ∀ identity fresh, At laws (@project) (code identity fresh) (source.resource identity)) :
    At laws (@project) (.resource code) context := by
  apply At.resource
  intro identity fresh
  have same := (context.resource_continuationBounds laws (@project) identity).trans
    (source.resource_bounds identity).symm
  have components := congrArg (fun bound =>
    (bound.resumption, bound.closing, bound.after)) same
  simp only [Context.continuationBounds, Prod.mk.injEq] at components
  exact .sameReceiver (original := source.resource identity) rfl
    ⟨fun permission => congrFun components.1 permission,
      fun permission => congrFun components.2.1 permission, components.2.2⟩ (inner identity fresh)

end

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.handler_interfaces

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.extract_complete
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.extract_none_iff

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.resume_from_bound
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.dispose_from_bound
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.handler
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.handler_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.after_handler
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.handler_retaining_interfaces

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.cleanup_here
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.cleanup_running
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.cleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.cleanup_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.after_cleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.cleanup_retaining_interfaces

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.OperationSource.world_weaken
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.resource
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.after_resource
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.OperationSources.resource_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.resource_retaining_interfaces
