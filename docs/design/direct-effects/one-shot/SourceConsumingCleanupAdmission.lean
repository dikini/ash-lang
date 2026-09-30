import SourceConsumingGeneratedSource
import SourceScheduledRetainedReceiver
import SourceScheduledProviderRetention
import SourceScheduledCleanupGeneration
import SourceScheduledReceiverRechecking
import SourceConsumingBoundGeneration
import SourceScheduledNeutralBoundRetention
import SourceScheduledNeutralComposition
import SourceScheduledNeutralRetained

/-! Contextual source admission for consuming clauses with cleanup and handlers.
Explicit structural rechecking derives saved/closing annotations from original
source evidence and is the cleanup admission rule. The earlier conditional
cleanup generator remains separate sound evidence; its existential check choice
is not a completeness or inference guarantee.
The sameReceiver rule requires equal caller interfaces and retained bounds.
Neutral transport retains the original derivation and structural receiver
expansions. Saved and closing bounds stay exact; waiting-tail changes retain
structural metadata provenance. Target finite checks remain independent.
No target Valid judgment is an admission premise. This remains actual-capture
admission. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Admitted ContinuationBounds Generated)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws neutral_receiver_laws)
open SourceScheduledCleanupGeneration (Checks RetainedResult)
open SourceScheduledCleanupInsertion (Insertion)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open OwnerPhaseTransitions (spend)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceScheduledNeutral (Expansion OwnerCut)

/-- Structural rules for precisely the existing primitive check language. -/
inductive Checked (outward : List Instance) : Checks → Prop where
  | done : Checked outward .done
  | operations (supplied : ∀ request ∈ required,
      SourceContextualClauses.RequestCapability request.1 request.2 scope) :
      Checked outward (.operations scope required)
  | closing (routes : SourceRecursiveRoutes.Closing outward scope.shape [] []) :
      Checked outward (.closing scope)
  | both : Checked outward first → Checked outward second → Checked outward (.both first second)
  | resource {checks : ∀ identity, identity ∉ world → Checks}
      (body : ∀ identity fresh, Checked outward (checks identity fresh)) :
      Checked outward (.resource world checks)

theorem checked_iff : Checked outward checks ↔ checks.Holds outward := by
  constructor
  · intro checked
    induction checked with
    | done => trivial
    | operations supplied => exact SourceContextualRequirements.check_requirements_iff.mpr supplied
    | closing routes => exact SourceDependencyCapture.check_closing_iff.mpr routes
    | both first second ihFirst ihSecond => exact ⟨ihFirst, ihSecond⟩
    | resource body ih => exact ih
  · intro supplied
    induction checks with
    | done => exact .done
    | operations scope required => exact .operations (SourceContextualRequirements.check_requirements_iff.mp supplied)
    | closing scope => exact .closing (SourceDependencyCapture.check_closing_iff.mp supplied)
    | both first second ihFirst ihSecond => exact .both (ihFirst supplied.1) (ihSecond supplied.2)
    | resource world body ih => exact .resource (fun identity fresh => ih identity fresh (supplied identity fresh))

section
variable [declarations : DeclarationPolicy]

/-- Fix the compiler before defining admission; callers cannot supply an
arbitrary result with its own soundness proof. The operation-interface branch
has an explicit empty check tree because outside cleanup does not change lookup.
Other constructors reuse the proved general generator. Its existential choice
is deliberately not advertised as executable or complete inference. -/
noncomputable def outsideCleanup
    {hints : Hints scope} {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {forest : Forest hints} {outside : Forest outsideHints} {next : Forest nextHints}
    (source : Retained world forest outside) (footprint : RequestFootprint callback required)
    (declared : Declared world (signature callback))
    (changed : Insertion needs callback outside next) : RetainedResult source forest next :=
  match source with
  | .operations interfaces => ⟨.operations interfaces, .done, by
      intro outward actions phases ready _
      exact (SourceScheduledCleanupGeneration.interfaces_receiver interfaces changed).symm.trans ready,
      fun _ _ _ ready _ => .operations interfaces
        ((SourceScheduledCleanupGeneration.interfaces_receiver interfaces changed).symm.trans ready)⟩
  | source => Classical.choice (SourceScheduledCleanupGeneration.retained_generate footprint source declared (.outside changed))

/-- An empty saved forest introduces no cleanup obligations, including when
its annotation was chosen by an earlier handler compiler. -/
theorem outsideCleanup_empty
    {outside : Forest outsideHints} {next : Forest nextHints}
    (source : Retained world .nil outside)
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    (changed : Insertion needs callback outside next) :
    (outsideCleanup source footprint declared changed).checks = .done := by
  rw [SourceScheduledSourceRechecking.retained_nil_eq source]
  rfl

/-- Original retained capability evidence at an actual owner cut. Validity here
belongs to the current source, before the clause constructor being admitted. -/
structure Context (world : List Nat) (owner : Nat) (outward : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    {wholeScope frontScope savedScope waitingScope : Scope}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    (whole : Forest wholeHints) (front : Forest frontHints)
    (saved : Forest savedHints) (waiting : Forest waitingHints) where
  cut : SourceScheduledNeutral.OwnerCut owner whole front saved waiting
  before : Interfaces world front
  resumption : (actions owner).any (fun rights => rights.resume) = true →
    {inside : Retained world saved (front.append (.spent (owner := owner) waiting)) //
      inside.Valid outward actions (spend phases owner)}
  closing : (actions owner).any (fun rights => rights.dispose) = true →
    {inside : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) waiting))) //
      inside.Valid outward actions (spend phases owner)}
  disposal : (actions owner).any (fun rights => rights.dispose) = true →
    savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true
  after : Retained world waiting .nil
  tailReady : after.Valid outward actions (spend phases owner)

/-- Project immutable metadata for the bound continuation, independently of
its caller's receiver shape and the capability proofs carried by this context. -/
def Context.continuationBounds (context : Context world owner outward actions phases whole front saved waiting) :
    ContinuationBounds world owner actions saved waiting where
  resumption := fun permission => ofCapability (context.resumption permission).val
  closing := fun permission => ofCapability (context.closing permission).val
  after := ofCapability context.after

/-- Saved and waiting metadata are stable even when the caller's physical
receiver changes. Each permitted action retains its own original projection. -/
structure Context.BoundsAgree
    (original : Context world owner outward actions phases whole front saved waiting)
    (current : Context world owner outward actions phases nextWhole nextFront saved waiting) : Prop where
  resumption : ∀ permission, ofCapability (current.resumption permission).val = ofCapability (original.resumption permission).val
  closing : ∀ permission, ofCapability (current.closing permission).val = ofCapability (original.closing permission).val
  tail : ofCapability current.after = ofCapability original.after

theorem Context.BoundsAgree.refl (context : Context world owner outward actions phases whole front saved waiting) :
    context.BoundsAgree context := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem Context.BoundsAgree.trans
    {first : Context world owner outward actions phases whole front saved waiting}
    {second : Context world owner outward actions phases middleWhole middleFront saved waiting}
    {third : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (left : first.BoundsAgree second) (right : second.BoundsAgree third) : first.BoundsAgree third :=
  ⟨fun permission => (right.resumption permission).trans (left.resumption permission),
    fun permission => (right.closing permission).trans (left.closing permission), right.tail.trans left.tail⟩

theorem Context.BoundsAgree.continuationBounds_eq
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (agreement : original.BoundsAgree current) : current.continuationBounds = original.continuationBounds := by
  simp only [Context.continuationBounds, ContinuationBounds.mk.injEq]
  exact ⟨funext agreement.resumption, funext agreement.closing, agreement.tail⟩

/-- The existing persistent plan registry fixes the saved forest at every
actual owner cut. Source transport need not permit arbitrary saved replacements
when both contexts agree with that registry and its proved extension. -/
theorem Context.saved_registry_identity
    (original : Context world owner outward actions phases whole front saved waiting)
    (current : Context nextWorld owner outward nextActions nextPhases nextWhole nextFront nextSaved nextWaiting)
    (before : SourceScheduledSavedPlans.Matches annotations whole)
    (after : SourceScheduledSavedPlans.Matches nextAnnotations nextWhole)
    (extension : ∀ name entry, annotations name = some entry → nextAnnotations name = some entry) :
    (⟨_, _, saved⟩ : SourceScheduledSavedPlans.Saved) = ⟨_, _, nextSaved⟩ :=
  Option.some.inj ((extension _ _ (before.selected original.cut)).symm.trans (after.selected current.cut))

/-- A waiting-tail change cannot replace the owner's saved or closing bounds. -/
structure Context.SavedAgree
    (original : Context world owner outward actions phases whole front saved waiting)
    (current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting) : Prop where
  resumption : ∀ permission, ofCapability (current.resumption permission).val = ofCapability (original.resumption permission).val
  closing : ∀ permission, ofCapability (current.closing permission).val = ofCapability (original.closing permission).val

theorem Context.SavedAgree.refl (context : Context world owner outward actions phases whole front saved waiting) :
    context.SavedAgree context := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Context.SavedAgree.symm
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    (same : original.SavedAgree current) : current.SavedAgree original :=
  ⟨fun permission => (same.resumption permission).symm, fun permission => (same.closing permission).symm⟩

theorem Context.SavedAgree.trans
    {first : Context world owner outward actions phases whole front saved waiting}
    {second : Context world owner outward actions phases middleWhole middleFront saved middleWaiting}
    {third : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    (left : first.SavedAgree second) (right : second.SavedAgree third) : first.SavedAgree third :=
  ⟨fun permission => (right.resumption permission).trans (left.resumption permission),
    fun permission => (right.closing permission).trans (left.closing permission)⟩

theorem Context.BoundsAgree.saved_agreement
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (same : original.BoundsAgree current) : original.SavedAgree current := ⟨same.resumption, same.closing⟩

theorem Context.SavedAgree.with_tail
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (same : original.SavedAgree current) (tail : ofCapability current.after = ofCapability original.after) :
    original.BoundsAgree current := ⟨same.resumption, same.closing, tail⟩

variable {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Move an original retained context along a neutral caller expansion. The
actual target cut and caller interface are supplied structurally; saved and
closing code come from the existing neutral source transport. -/
noncomputable def Context.neutral
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner nextWhole nextFront saved waiting)
    (before : SourceScheduledRetainedInterfaces.Interfaces world nextFront)
    (caller : SourceScheduledNeutral.Expansion front nextFront) :
    Context world owner outward actions phases nextWhole nextFront saved waiting where
  cut := cut
  before := before
  resumption := fun permission =>
    let result := (context.resumption permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.resumption permission).property (caller.append .refl)
    ⟨Classical.choose result, (Classical.choose_spec result).1⟩
  closing := fun permission =>
    let result := (context.closing permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.closing permission).property (.running (caller.append .refl))
    ⟨Classical.choose result, (Classical.choose_spec result).1⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

theorem Context.neutral_bounds
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner nextWhole nextFront saved waiting)
    (before : SourceScheduledRetainedInterfaces.Interfaces world nextFront)
    (caller : SourceScheduledNeutral.Expansion front nextFront) :
    context.BoundsAgree (context.neutral laws project cut before caller) := by
  refine ⟨?_, ?_, rfl⟩
  · intro permission
    exact (Classical.choose_spec ((context.resumption permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.resumption permission).property (caller.append .refl))).2
  · intro permission
    exact (Classical.choose_spec ((context.closing permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.closing permission).property (.running (caller.append .refl)))).2

noncomputable def Context.cleanupChecks (context : Context world owner outward actions phases whole front saved waiting)
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    (needs : List Instance) : Checks :=
  .both (Checks.when _ (fun permission =>
    (outsideCleanup (context.resumption permission).val footprint declared (Insertion.here (needs := needs))).checks))
    (Checks.when _ (fun permission =>
      (outsideCleanup (context.closing permission).val footprint declared (.running (Insertion.here (needs := needs)))).checks))

/-- No retained work exists to recheck when the selected owner saved nothing. -/
theorem Context.empty_cleanupChecks
    (context : Context world owner outward actions phases whole front .nil waiting)
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    (needs : List Instance) : Checked outward (context.cleanupChecks footprint declared needs) := by
  apply checked_iff.mpr
  constructor
  · apply (Checks.when_holds _).mpr
    intro permission
    have empty := outsideCleanup_empty (context.resumption permission).val footprint declared
      (Insertion.here (needs := needs))
    exact empty.symm ▸ (show Checks.Holds outward .done from True.intro)
  · apply (Checks.when_holds _).mpr
    intro permission
    have empty := outsideCleanup_empty (context.closing permission).val footprint declared
      (.running (Insertion.here (needs := needs)))
    exact empty.symm ▸ (show Checks.Holds outward .done from True.intro)

noncomputable def Context.cleanup (context : Context world owner outward actions phases whole front saved waiting)
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    (needs : List Instance) (checked : Checked outward (context.cleanupChecks footprint declared needs)) :
    Context world owner outward actions phases (.cleanup (needs := needs) callback whole)
      (.cleanup (needs := needs) callback front) saved waiting where
  cut := .cleanup context.cut
  before := .cleanup front required footprint declared context.before
  resumption := fun permission =>
    let result := outsideCleanup (context.resumption permission).val footprint declared (Insertion.here (needs := needs))
    ⟨result.annotation, result.sound outward actions (spend phases owner) (context.resumption permission).property
      ((Checks.when_holds _).mp ((checked_iff.mp checked).1) permission)⟩
  closing := fun permission =>
    let result := outsideCleanup (context.closing permission).val footprint declared (.running (Insertion.here (needs := needs)))
    ⟨result.annotation, result.sound outward actions (spend phases owner) (context.closing permission).property
      ((Checks.when_holds _).mp ((checked_iff.mp checked).2) permission)⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Reuse an already derived target tail while transporting the original
saved/closing sources. Nested source generation uses its parent's checked tail. -/
noncomputable def Context.neutral_tail
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting)
    (after : Retained world nextWaiting .nil)
    (ready : after.Valid outward actions (OwnerPhaseTransitions.spend phases owner)) :
    Context world owner outward actions phases nextWhole nextFront saved nextWaiting where
  cut := cut
  before := before
  resumption := fun permission =>
    let result := (context.resumption permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.resumption permission).property
      (caller.append (.spent waitingChange))
    ⟨Classical.choose result, (Classical.choose_spec result).1⟩
  closing := fun permission =>
    let result := (context.closing permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.closing permission).property
      (.running (caller.append (.spent waitingChange)))
    ⟨Classical.choose result, (Classical.choose_spec result).1⟩
  disposal := context.disposal
  after := after
  tailReady := ready

theorem Context.neutral_tail_saved
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting)
    (after : Retained world nextWaiting .nil)
    (ready : after.Valid outward actions (OwnerPhaseTransitions.spend phases owner)) :
    context.SavedAgree (context.neutral_tail laws project cut before caller waitingChange after ready) := by
  constructor
  · intro permission
    exact (Classical.choose_spec ((context.resumption permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.resumption permission).property
      (caller.append (.spent waitingChange)))).2
  · intro permission
    exact (Classical.choose_spec ((context.closing permission).val.receiver_retaining
      (neutral_receiver_laws laws project) (context.closing permission).property
      (.running (caller.append (.spent waitingChange))))).2

/-- Construct the target waiting source from the original one. There is no
target validity premise in this outer context construction. -/
noncomputable def Context.expand_waiting
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting) :
    Context world owner outward actions phases nextWhole nextFront saved nextWaiting :=
  let result := Retained.expand_neutral laws project waitingChange .refl context.after context.tailReady
  context.neutral_tail laws project cut before caller waitingChange
    (Classical.choose result) (Classical.choose_spec result).1

theorem Context.expand_waiting_saved
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting) :
    context.SavedAgree (context.expand_waiting laws project cut before caller waitingChange) :=
  context.neutral_tail_saved laws project cut before caller waitingChange _ _

theorem Context.expand_waiting_tail
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting) :
    SourceBoundSnapshots.Retained.Neutral world (ofCapability context.after)
      (ofCapability (context.expand_waiting laws project cut before caller waitingChange).after) :=
  (Classical.choose_spec (Retained.expand_neutral laws project waitingChange .refl context.after context.tailReady)).2


/-- Explicit source derivations admit cleanup without choosing an arbitrary
conditional check tree. Receiver-only derivations retain the saved and closing code positions; the
compiler returns validity together with exact original metadata. -/
noncomputable def Context.cleanupSource
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    (needs : List Instance)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.resumption permission).val
      (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.closing permission).val
      (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))) :
    Context world owner outward actions phases (.cleanup (needs := needs) callback whole)
      (.cleanup (needs := needs) callback front) saved waiting where
  cut := .cleanup context.cut
  before := .cleanup front required footprint declared context.before
  resumption := fun permission =>
    let generated := (resumption permission).compile_retaining laws project (context.resumption permission).property
    ⟨Classical.choose generated, (Classical.choose_spec generated).1⟩
  closing := fun permission =>
    let generated := (closing permission).compile_retaining laws project (context.closing permission).property
    ⟨Classical.choose generated, (Classical.choose_spec generated).1⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

/-- Install an interpretation around the caller. Saved and closing code are
rechecked structurally from the original context; owner identity, saved forest,
disposal protection and the waiting tail are preserved. -/
noncomputable def Context.handler
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (required : List Requirement)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.resumption permission).val
      (.handler (effect := effect) (table := table) (families := families) (required := required)
        (front.append (.spent (owner := owner) waiting))))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.closing permission).val
      (.running (.handler (effect := effect) (table := table) (families := families) (required := required)
        (front.append (.spent (owner := owner) waiting))))) :
    Context world owner outward actions phases
      (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
      (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting where
  cut := .handler context.cut
  before := .handler front context.before
  resumption := fun permission =>
    let generated := (resumption permission).compile_retaining laws project (context.resumption permission).property
    ⟨Classical.choose generated, (Classical.choose_spec generated).1⟩
  closing := fun permission =>
    let generated := (closing permission).compile_retaining laws project (context.closing permission).property
    ⟨Classical.choose generated, (Classical.choose_spec generated).1⟩
  disposal := context.disposal
  after := context.after
  tailReady := context.tailReady

noncomputable def Context.resource
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) (identity : Nat) :
    Context (world ++ [identity]) owner outward actions phases (.cell (identity := identity) whole)
      (.cell (identity := identity) front) saved waiting where
  cut := .cell context.cut
  before := .cell (context.before.world_weaken (List.subset_append_left _ _))
  resumption := fun permission => ⟨Classical.choose
    ((context.resumption permission).val.provide_world_retaining laws project
      (context.resumption permission).property (List.subset_append_left _ _) .here),
    (Classical.choose_spec ((context.resumption permission).val.provide_world_retaining laws project
      (context.resumption permission).property (List.subset_append_left _ _) .here)).1⟩
  closing := fun permission => ⟨Classical.choose
    ((context.closing permission).val.provide_world_retaining laws project
      (context.closing permission).property (List.subset_append_left _ _) (.running .here)),
    (Classical.choose_spec ((context.closing permission).val.provide_world_retaining laws project
      (context.closing permission).property (List.subset_append_left _ _) (.running .here))).1⟩
  disposal := context.disposal
  after := context.after.world_weaken (List.subset_append_left _ _)
  tailReady := context.after.world_weaken_valid (List.subset_append_left _ _) context.tailReady

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Resource entry keeps the original resumption snapshot in the extended world. -/
theorem Context.resource_resumption_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) (identity : Nat)
    (permission : (actions owner).any (fun rights => rights.resume) = true) :
    SourceBoundSnapshots.Retained.ofCapability ((context.resource laws project identity).resumption permission).val =
      (SourceBoundSnapshots.Retained.ofCapability (context.resumption permission).val).world_weaken
        (List.subset_append_left world [identity]) := by
  exact (Classical.choose_spec ((context.resumption permission).val.provide_world_retaining laws project
    (context.resumption permission).property (List.subset_append_left world [identity]) (identity := identity) .here)).2

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Resource entry keeps the original closing snapshot in the extended world. -/
theorem Context.resource_closing_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) (identity : Nat)
    (permission : (actions owner).any (fun rights => rights.dispose) = true) :
    SourceBoundSnapshots.Retained.ofCapability ((context.resource laws project identity).closing permission).val =
      (SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val).world_weaken
        (List.subset_append_left world [identity]) := by
  exact (Classical.choose_spec ((context.closing permission).val.provide_world_retaining laws project
    (context.closing permission).property (List.subset_append_left world [identity]) (identity := identity) (.running .here))).2

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- The waiting source is weakened structurally; no annotation is reconstructed. -/
theorem Context.resource_tail_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) (identity : Nat) :
    SourceBoundSnapshots.Retained.ofCapability (context.resource laws project identity).after =
      (SourceBoundSnapshots.Retained.ofCapability context.after).world_weaken
        (List.subset_append_left world [identity]) :=
  context.after.ofCapability_world_weaken (List.subset_append_left world [identity])

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- The complete bound-continuation metadata is mapped into the new resource world. -/
theorem Context.resource_continuationBounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) (identity : Nat) :
    (context.resource laws project identity).continuationBounds =
      context.continuationBounds.world_weaken (List.subset_append_left world [identity]) := by
  simp only [Context.continuationBounds, ContinuationBounds.world_weaken, ContinuationBounds.mk.injEq]
  exact ⟨funext (Context.resource_resumption_bounds laws project context identity),
    funext (Context.resource_closing_bounds laws project context identity),
    Context.resource_tail_bounds laws project context identity⟩

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- The actual admission constructor preserves every permitted saved and
closing projection, together with the waiting tail. -/
theorem Context.handler_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (required : List SourceContextualHints.Requirement)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.resumption permission).val
      (.handler (effect := effect) (table := table) (families := families) (required := required)
        (front.append (.spent (owner := owner) waiting))))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.closing permission).val
      (.running (.handler (effect := effect) (table := table) (families := families) (required := required)
        (front.append (.spent (owner := owner) waiting))))) :
    context.BoundsAgree (context.handler laws (@project) effect table families required resumption closing) := by
  refine ⟨?_, ?_, rfl⟩
  · intro permission
    exact (Classical.choose_spec ((resumption permission).compile_retaining laws project
      (context.resumption permission).property)).2
  · intro permission
    exact (Classical.choose_spec ((closing permission).compile_retaining laws project
      (context.closing permission).property)).2

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- The actual admission constructor preserves every permitted saved and
closing projection, together with the waiting tail. -/
theorem Context.cleanupSource_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting)
    (footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required) (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback))
    (needs : List Instance)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.resumption permission).val
      (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (context.closing permission).val
      (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))) :
    context.BoundsAgree (context.cleanupSource laws (@project) footprint declared needs resumption closing) := by
  refine ⟨?_, ?_, rfl⟩
  · intro permission
    exact (Classical.choose_spec ((resumption permission).compile_retaining laws project
      (context.resumption permission).property)).2
  · intro permission
    exact (Classical.choose_spec ((closing permission).compile_retaining laws project
      (context.closing permission).property)).2

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Saved agreement follows resource-world extension even when waiting tails differ. -/
theorem Context.SavedAgree.resource
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (metadata : original.SavedAgree current) (identity : Nat) :
    (original.resource laws project identity).SavedAgree (current.resource laws project identity) := by
  constructor
  · intro permission
    simp only [Context.resource_resumption_bounds]
    exact congrArg (fun bounds => bounds.world_weaken (List.subset_append_left _ [identity])) (metadata.resumption permission)
  · intro permission
    simp only [Context.resource_closing_bounds]
    exact congrArg (fun bounds => bounds.world_weaken (List.subset_append_left _ [identity])) (metadata.closing permission)

/-- Contextual rules follow the clause syntax. Cleanup and handler installation
use explicit recursive rechecking of the original saved and closing source.
The conditional generator is not an admission constructor: its existential
check choice carries no structural transport law. -/
inductive At [declarations : DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    {world : List Nat} → {owner : Nat} → {dependencies : SourceDependencyAnnotations.Dependencies} →
    {plan : Plan dependencies} → Body world owner plan →
    {wholeScope frontScope savedScope waitingScope : Scope} →
    {wholeHints : Hints wholeScope} → {frontHints : Hints frontScope} →
    {savedHints : Hints savedScope} → {waitingHints : Hints waitingScope} →
    {whole : Forest wholeHints} → {front : Forest frontHints} →
    {saved : Forest savedHints} → {waiting : Forest waitingHints} →
    Context world owner outward actions phases whole front saved waiting → Prop where
  | resume : At (actions := actions) (phases := phases) laws (@project) .resume context
  | dispose : At (actions := actions) (phases := phases) laws (@project) .dispose context
  | sequence : At (actions := actions) (phases := phases) laws (@project) body context → At (actions := actions) (phases := phases) laws (@project) (.sequence required footprint declared body) context
  | choice : At (actions := actions) (phases := phases) laws (@project) first context → At (actions := actions) (phases := phases) laws (@project) second context → At (actions := actions) (phases := phases) laws (@project) (.choice first second) context
  | handler {world : List Nat} {owner : Nat}
      {plans : ClausePlans clauses families}
      {code : Body world owner plan}
      {wholeScope frontScope savedScope waitingScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans)
      (declared : declarations.accepts required plans)
      (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.resumption permission).val
        (.handler (effect := effect) (table := table) (families := families) (required := required)
          (front.append (.spent (owner := owner) waiting))))
      (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.closing permission).val
        (.running (.handler (effect := effect) (table := table) (families := families) (required := required)
          (front.append (.spent (owner := owner) waiting)))))
      (body : At (actions := actions) (phases := phases) laws (@project) code
        (context.handler laws (@project) effect table families required resumption closing)) :
      At (actions := actions) (phases := phases) laws (@project)
        (.handler (effect := effect) (table := table) bounds declared code) context
  | cleanupSource {world : List Nat} {owner : Nat}
      {code : Body world owner plan}
      {wholeScope frontScope savedScope waitingScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      {footprint : RequestFootprint callback required} {declared : Declared world (signature callback)}
      (covered : ∀ request ∈ required, request.1 ∈ needs)
      (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.resumption permission).val
        (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))
      (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.closing permission).val
        (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting)))))
      (body : At (actions := actions) (phases := phases) laws (@project) code
        (context.cleanupSource laws (@project) footprint declared needs resumption closing)) :
      At (actions := actions) (phases := phases) laws (@project)
        (.cleanup (needs := needs) required footprint declared code) context
  | sameReceiver {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeScope frontScope savedScope waitingScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {original current : Context world owner outward actions phases whole front saved waiting}
      (caller : original.before = current.before)
      (metadata : original.BoundsAgree current)
      (source : At (actions := actions) (phases := phases) laws (@project) body original) :
      At (actions := actions) (phases := phases) laws (@project) body current
  | neutral {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeScope frontScope savedScope waitingScope nextWholeScope nextFrontScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
      {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
      {original : Context world owner outward actions phases whole front saved waiting}
      {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
      (receiver : Expansion whole nextWhole)
      (caller : Expansion front nextFront)
      (metadata : original.BoundsAgree current)
      (source : At (actions := actions) (phases := phases) laws (@project) body original) :
      At (actions := actions) (phases := phases) laws (@project) body current
  | waitingNeutral {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeScope frontScope savedScope waitingScope nextWholeScope nextFrontScope nextWaitingScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {nextWaitingHints : Hints nextWaitingScope}
      {nextWaiting : Forest nextWaitingHints}
      {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
      {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
      {original : Context world owner outward actions phases whole front saved waiting}
      {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
      (receiver : Expansion whole nextWhole)
      (caller : Expansion front nextFront)
      (waitingChange : Expansion waiting nextWaiting)
      (metadata : original.SavedAgree current)
      (tail : SourceBoundSnapshots.Retained.Neutral world (ofCapability original.after) (ofCapability current.after))
      (source : At (actions := actions) (phases := phases) laws (@project) body original) :
      At (actions := actions) (phases := phases) laws (@project) body current
  | resource {world : List Nat} {owner : Nat}
      {families : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ identity, Plan (families identity)}
      {code : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
      {wholeScope frontScope savedScope waitingScope : Scope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      (body : ∀ identity fresh, At (actions := actions) (phases := phases) laws (@project) (code identity fresh) (context.resource laws (@project) identity)) :
      At (actions := actions) (phases := phases) laws (@project) (.resource code) context

private def cleanupInterface {plan : Plan dependencies} (body : Body world owner plan) :
    Option (List Instance × List Requirement) :=
  match body with
  | .cleanup (needs := needs) required _ _ _ => some (needs, required)
  | _ => none

private theorem At.cleanup_coverage
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context) :
    match cleanupInterface body with
    | some (needs, required) => ∀ request ∈ required, request.1 ∈ needs
    | none => True := by
  induction admitted with
  | cleanupSource covered resumption closing body ih => exact covered
  | sameReceiver caller metadata source ih => exact ih
  | neutral receiver caller metadata source ih => exact ih
  | waitingNeutral receiver caller waitingChange metadata tail source ih => exact ih
  | resume | dispose | sequence | choice | handler | resource => trivial

/-- Annotation changes at the same receiver cannot erase a cleanup's declared
dependency coverage. Structural cleanup retains the same source check. -/
theorem At.cleanup_dependencies
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {plan : Plan dependencies} {body : Body world owner plan}
    {footprint : RequestFootprint callback required} {declared : Declared world (signature callback)}
    {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project (.cleanup (needs := needs) required footprint declared body) context) :
    ∀ request ∈ required, request.1 ∈ needs := admitted.cleanup_coverage

/-- The original source derivation generates at an actual new waiting tail.
There is no target At premise. Independent target finite checks remain explicit
here; the outer context theorem below derives them from the original checks. -/
theorem At.generate_waiting_source
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan}
    {original : Context world owner outward actions phases whole front saved waiting}
    (source : At laws project body original)
    {nextWholeScope nextFrontScope nextWaitingScope : Scope}
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting)
    (metadata : original.SavedAgree current)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope nextWaitingScope current.before) :
    ∃ annotation : Code world plan nextWhole, annotation.Valid outward actions phases ∧
      Generated actions current.continuationBounds body annotation := by
  induction source generalizing nextWholeScope nextFrontScope nextWaitingScope with
  | resume =>
      exact ⟨.resume current.cut (current.resumption checked.1).val (.operations current.before) current.after,
        ⟨checked.1, checked.2.1, (current.resumption checked.1).property, checked.2.2.2, current.tailReady⟩,
        .resume checked.1 rfl rfl⟩
  | dispose =>
      exact ⟨.dispose current.cut (current.closing checked.1).val (.operations current.before) current.after,
        ⟨checked.1, checked.2.1, (current.disposal checked.1).1, (current.disposal checked.1).2,
          (current.closing checked.1).property, checked.2.2.2, current.tailReady⟩, .dispose checked.1 rfl rfl⟩
  | sequence body ih =>
      rename_i required prefixDependencies prefixPlan footprint declared
      obtain ⟨annotation, ready, generated⟩ := ih current caller waitingChange metadata checked.2
      exact ⟨.sequence (.operations required footprint declared) annotation, ⟨checked.1, ready⟩, .sequence generated⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨first, firstReady, firstGenerated⟩ := ihFirst current caller waitingChange metadata checked.1
      obtain ⟨second, secondReady, secondGenerated⟩ := ihSecond current caller waitingChange metadata checked.2
      exact ⟨.choice first second, ⟨firstReady, secondReady⟩, .choice firstGenerated secondGenerated⟩
  | handler bounds declared resumption closing body ih =>
      rename_i parent
      let child := parent.handler laws project _ _ _ _ resumption closing
      let moved := child.neutral_tail laws project (.handler current.cut) (.handler _ current.before)
        (.handler caller) waitingChange current.after current.tailReady
      have childKept : child.SavedAgree moved := child.neutral_tail_saved laws project _ _ _ _ _ _
      obtain ⟨annotation, ready, generated⟩ := ih moved (.handler caller) waitingChange childKept checked.2
      have aligned : current.BoundsAgree moved :=
        (metadata.symm.trans ((Context.handler_bounds laws project parent _ _ _ _ resumption closing).saved_agreement.trans childKept)).with_tail rfl
      refine ⟨.handler declared annotation (some bounds), ⟨checked.1, ready⟩, .handler ?_⟩
      simpa only [aligned.continuationBounds_eq] using generated
  | cleanupSource covered resumption closing body ih =>
      rename_i parent footprint declared
      let child := parent.cleanupSource laws project footprint declared _ resumption closing
      let moved := child.neutral_tail laws project (.cleanup current.cut)
        (.cleanup _ _ footprint declared current.before) (.cleanup caller) waitingChange current.after current.tailReady
      have childKept : child.SavedAgree moved := child.neutral_tail_saved laws project _ _ _ _ _ _
      obtain ⟨annotation, ready, generated⟩ := ih moved (.cleanup caller) waitingChange childKept checked.1
      have aligned : current.BoundsAgree moved :=
        (metadata.symm.trans ((Context.cleanupSource_bounds laws project parent footprint declared _ resumption closing).saved_agreement.trans childKept)).with_tail rfl
      refine ⟨.cleanup annotation (.operations _ footprint declared), ⟨ready, checked.2⟩, .cleanup ?_⟩
      simpa only [aligned.continuationBounds_eq] using generated
  | sameReceiver same previous source ih =>
      exact ih current caller waitingChange (previous.saved_agreement.trans metadata) checked
  | neutral receiver prior previous source ih =>
      exact ih current (prior.trans caller) waitingChange (previous.saved_agreement.trans metadata) checked
  | waitingNeutral receiver prior priorWaiting previous tail source ih =>
      exact ih current (prior.trans caller) (priorWaiting.trans waitingChange) (previous.trans metadata) checked
  | resource body ih =>
      rename_i parent
      have kept := fun identity => metadata.resource laws project identity
      have generated := fun identity fresh => ih identity fresh (current.resource laws project identity)
        (.cell caller) waitingChange (kept identity) (checked identity fresh)
      refine ⟨.resource (fun identity fresh => Classical.choose (generated identity fresh)),
        (fun identity fresh => (Classical.choose_spec (generated identity fresh)).1), .resource ?_⟩
      intro identity fresh
      simpa only [Context.resource_continuationBounds] using (Classical.choose_spec (generated identity fresh)).2

/-- Source induction covers arbitrary saved code, callbacks and handler
requirements. The target finite check is independent of source admission; no
target contextual derivation or future code-validity premise is used. -/
theorem At.generate_neutral_source
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan}
    {original : Context world owner outward actions phases whole front saved waiting}
    (source : At laws project body original)
    {nextWholeScope nextFrontScope : Scope}
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    (current : Context world owner outward actions phases nextWhole nextFront saved waiting)
    (caller : Expansion front nextFront)
    (metadata : original.BoundsAgree current)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope waitingScope current.before) :
    ∃ annotation : Code world plan nextWhole, annotation.Valid outward actions phases ∧
      Generated actions original.continuationBounds body annotation := by
  obtain ⟨annotation, ready, generated⟩ := source.generate_waiting_source current caller .refl metadata.saved_agreement checked
  exact ⟨annotation, ready, by simpa only [metadata.continuationBounds_eq] using generated⟩

/-- Source induction generates valid code with exact correspondence at every
bound-owner consumption, through ordered handlers, cleanup and fresh resources. -/
theorem At.generate_source
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      Generated actions context.continuationBounds body annotation := by
  exact admitted.generate_neutral_source context .refl (Context.BoundsAgree.refl context) checked

/-- Preserve the established current-bound API as a projection of the stronger
source correspondence theorem, rather than a second generation induction. -/
theorem At.generate_retaining
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation := by
  obtain ⟨annotation, ready, generated⟩ := admitted.generate_source checked
  exact ⟨annotation, ready, generated.current_bounds⟩

/-- Scheduling is the first projection of generation with exact source bounds. -/
theorem At.generate
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases := by
  obtain ⟨annotation, ready, _⟩ := admitted.generate_retaining checked
  exact ⟨annotation, ready⟩

/-- Nested source admission certifies the same bounds the compiler emits. -/
theorem At.generate_admitted
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context) (nested : body.Nested)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation ∧ (SourcePlanBounds.ofCode annotation).Admitted := by
  obtain ⟨annotation, ready, kept⟩ := admitted.generate_retaining checked
  exact ⟨annotation, ready, kept, kept.symm ▸ nested.boundAnnotation_admitted⟩

/-- Build the initial contextual evidence from the original saved and waiting
annotations. Freshness and the spent marker reuse the existing phase and
neutral-transport lemmas; no selected clause body is checked here. -/
noncomputable def Context.capture
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (resumeReady : rights.resume = true → inside.Valid outward actions phases)
    (closing : rights.dispose = true → ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases)
    (disposal : rights.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none)
    (absent : owner ∉ SourceDependencyOwners.owners (savedScope.append waitingScope)) :
    Context world owner outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      (.live (owner := owner) saved waiting) .nil saved waiting := by
  have known : (actions.insert owner rights) owner = some rights := by simp [Syntax.UsageTickets.insert]
  have tailAbsent : owner ∉ SourceDependencyOwners.owners (waitingScope.append .nil) := by
    simp only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners, List.append_nil] at absent ⊢
    exact fun member => absent (List.mem_append_right _ member)
  have generateResume (permission : ((actions.insert owner rights) owner).any (fun rights => rights.resume) = true) :
      ∃ next : Retained world saved (.spent (owner := owner) waiting),
        next.Valid outward (actions.insert owner rights) (spend (OwnerPhaseTransitions.introduce phases owner) owner) ∧
        SourceBoundSnapshots.Retained.ofCapability next = SourceBoundSnapshots.Retained.ofCapability inside := by
    have allowed : rights.resume = true := by simpa only [known, Option.any_some] using permission
    exact inside.expand_receiver_retaining laws project
      (inside.valid_spent_fresh_owner (resumeReady allowed) fresh absent) (.history .refl)
  have generateClosing (permission : ((actions.insert owner rights) owner).any (fun rights => rights.dispose) = true) :
      ∃ next : Retained world saved.forClosing (.running (.spent (owner := owner) waiting)),
        next.Valid outward (actions.insert owner rights) (spend (OwnerPhaseTransitions.introduce phases owner) owner) ∧
        ∃ original : Retained world saved.forClosing (.running waiting), original.Valid outward actions phases ∧
          SourceBoundSnapshots.Retained.ofCapability next = SourceBoundSnapshots.Retained.ofCapability original := by
    have allowed : rights.dispose = true := by simpa only [known, Option.any_some] using permission
    obtain ⟨annotation, ready⟩ := closing allowed
    have closingAbsent : owner ∉ SourceDependencyOwners.owners (savedScope.forClosing.append (.running waitingScope)) := by
      intro member
      apply absent
      simp only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners] at member ⊢
      exact (ScopedExpressions.append_subset (SourceScheduledPhaseRestriction.owners_closing savedScope)
        (List.Subset.refl (SourceDependencyOwners.owners waitingScope))) member
    obtain ⟨next, valid, kept⟩ := annotation.expand_receiver_retaining laws project
      (annotation.valid_spent_fresh_owner ready fresh closingAbsent) (.running (.history .refl))
    exact ⟨next, valid, annotation, ready, kept⟩
  exact {
    cut := .hit
    before := .nil
    resumption := fun permission => ⟨Classical.choose (generateResume permission), (Classical.choose_spec (generateResume permission)).1⟩
    closing := fun permission => ⟨Classical.choose (generateClosing permission), (Classical.choose_spec (generateClosing permission)).1⟩
    disposal := fun permission => disposal (by simpa only [known, Option.any_some] using permission)
    after := after
    tailReady := after.valid_spent_fresh_owner tailReady fresh tailAbsent }

/-- Fresh capture preserves the saved source's exact persistent metadata
while adding the spent-owner marker to its resumption receiver. -/
theorem Context.capture_resumption_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (resumeReady : rights.resume = true → inside.Valid outward actions phases)
    (closing : rights.dispose = true → ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases)
    (disposal : rights.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none)
    (absent : owner ∉ SourceDependencyOwners.owners (savedScope.append waitingScope))
    (permission : ((actions.insert owner rights) owner).any (fun rights => rights.resume) = true) :
    SourceBoundSnapshots.Retained.ofCapability ((Context.capture laws project inside after resumeReady closing disposal tailReady fresh absent).resumption permission).val =
      SourceBoundSnapshots.Retained.ofCapability inside := by
  dsimp only [Context.capture]
  exact (Classical.choose_spec (p := fun next : Retained world saved (.spent (owner := owner) waiting) =>
    next.Valid outward (actions.insert owner rights) (spend (OwnerPhaseTransitions.introduce phases owner) owner) ∧
      SourceBoundSnapshots.Retained.ofCapability next = SourceBoundSnapshots.Retained.ofCapability inside) _).2

/-- Closing keeps the metadata of an original closing annotation supplied by
the request evidence; changing the receiver cannot replace those bound fields. -/
theorem Context.capture_closing_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (resumeReady : rights.resume = true → inside.Valid outward actions phases)
    (closing : rights.dispose = true → ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases)
    (disposal : rights.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (fresh : actions owner = none)
    (absent : owner ∉ SourceDependencyOwners.owners (savedScope.append waitingScope))
    (permission : ((actions.insert owner rights) owner).any (fun rights => rights.dispose) = true) :
    ∃ original : Retained world saved.forClosing (.running waiting), original.Valid outward actions phases ∧
      SourceBoundSnapshots.Retained.ofCapability ((Context.capture laws project inside after resumeReady closing disposal tailReady fresh absent).closing permission).val =
        SourceBoundSnapshots.Retained.ofCapability original := by
  dsimp only [Context.capture]
  exact (Classical.choose_spec (p := fun next : Retained world saved.forClosing (.running (.spent (owner := owner) waiting)) =>
    next.Valid outward (actions.insert owner rights) (spend (OwnerPhaseTransitions.introduce phases owner) owner) ∧
      ∃ original : Retained world saved.forClosing (.running waiting), original.Valid outward actions phases ∧
        SourceBoundSnapshots.Retained.ofCapability next = SourceBoundSnapshots.Retained.ofCapability original) _).2

/-- Existing finite source admission supplies permissions, phase and caller
checks. Contextual admission supplies the additional cleanup route conditions.
Together they generate the actual fresh selected body. -/
theorem At.capture_body
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {body : Body world owner plan} (source : Admitted rights resumeRequired closeRequired body required)
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (resumeReady : rights.resume = true → inside.Valid outward actions phases)
    (closing : rights.dispose = true → ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases)
    (disposal : rights.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none)
    (absent : owner ∉ SourceDependencyOwners.owners (savedScope.append waitingScope))
    (contextual : At laws project body
      (Context.capture laws project inside after resumeReady closing disposal tailReady fresh absent)) :
    ∃ annotation : Code world plan (.live (owner := owner) saved waiting),
      annotation.Valid outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner) := by
  apply contextual.generate (resumeRequired := resumeRequired) (closeRequired := closeRequired)
  exact source.at_capture (by simp [Syntax.UsageTickets.insert]) (by simp [OwnerPhaseTransitions.introduce]) supplied

/-- Compilation reaches the existing scheduling judgment. It does not add a
new transition relation or alter continuation ownership. -/
theorem At.scheduled
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {body : Body world owner plan} {context : Context world owner outward actions phases whole front saved waiting}
    (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    SourceScheduledChecks.Local outward actions phases world plan whole := by
  obtain ⟨annotation, ready⟩ := admitted.generate checked
  exact annotation.compile_with laws ready

end
end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.checked_iff
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.capture_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.scheduled

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.outsideCleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.resource
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.handler

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.outsideCleanup_empty

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.empty_cleanupChecks

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_retaining
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_admitted

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanupSource

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.cleanup_dependencies

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture_resumption_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.capture_closing_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.resource_resumption_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.resource_closing_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.resource_tail_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.refl

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.trans

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.handler_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanupSource_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.continuationBounds_eq

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.resource_continuationBounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.neutral_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_neutral_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.SavedAgree.refl

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.SavedAgree.symm

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.SavedAgree.trans

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.saved_agreement

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.SavedAgree.with_tail

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.neutral_tail_saved

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.expand_waiting_saved

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.expand_waiting_tail

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.saved_registry_identity

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.SavedAgree.resource

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_waiting_source
