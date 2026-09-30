import SourceConsumingCaptureBounds
import SourceConsumingDeclarationEntry
import SourceAnnotatedRuntimeCuts

/-! Explicit declaration bounds and proof routes attached to runtime frames.
Selection reads this retained data. Admission checks either the recorded bounds
or an existing structural recipe valid for arbitrary retained continuations.
No accepted future capture or successor state occurs in these annotations. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingClauseAnnotations (ClauseBounds Declarations Bounded)
open SourceAnnotatedRuntime (Handler Stack HandlerCut)

/-- The proof route is retained data, so an explicit bound cannot later be
reclassified as an inherited contract to bypass its capture check. -/
inductive DeclarationRoute where
  | bounded
  | inherited
  deriving DecidableEq

structure HandlerBounds (families : SourceDependencyCapture.Families) (handler : Handler) where
  plans : ClausePlans handler.clauses.erase (families handler.erase)
  bounds : ClauseBounds plans
  admission : DeclarationRoute := .bounded

inductive FrameBounds (families : SourceDependencyCapture.Families) : SourceAnnotatedRuntime.Frame → Type where
  | plain : FrameBounds families (.plain data)
  | handler : HandlerBounds families data → FrameBounds families (.handler data)
  | cell : FrameBounds families (.cell identity payload caller answer)
  | armed : FrameBounds families (.armed action)
  | running : FrameBounds families (.running action saved closed)
  | closing : FrameBounds families (.closing identity caller)
  | retiring : FrameBounds families (.retiring owner)

inductive StackBounds (families : SourceDependencyCapture.Families) : Stack → Type where
  | nil : StackBounds families .nil
  | push : FrameBounds families frame → StackBounds families rest → StackBounds families (.push frame rest)
  | live : StackBounds families saved → StackBounds families rest →
      StackBounds families (.live owner input answer saved caller rest)
  | spent : StackBounds families rest → StackBounds families (.spent owner answer caller rest)

def StackBounds.append {front tail : Stack}
    (first : StackBounds families front) (second : StackBounds families tail) :
    StackBounds families (front.append tail) :=
  match first with
  | .nil => second
  | .push frame rest => .push frame (rest.append second)
  | .live saved rest => .live saved (rest.append second)
  | .spent rest => .spent (rest.append second)

def StackBounds.splitAt (front tail : Stack) (source : StackBounds families (front.append tail)) :
    StackBounds families front × StackBounds families tail :=
  match front with
  | .nil => (.nil, source)
  | .push _ rest => match source with
    | .push frame next =>
        let pieces := next.splitAt rest tail
        (.push frame pieces.1, pieces.2)
  | .live _ _ _ _ _ rest => match source with
    | .live saved next =>
        let pieces := next.splitAt rest tail
        (.live saved pieces.1, pieces.2)
  | .spent _ _ _ rest => match source with
    | .spent next =>
        let pieces := next.splitAt rest tail
        (.spent pieces.1, pieces.2)

theorem StackBounds.splitAt_append (front tail : Stack) (source : StackBounds families (front.append tail)) :
    (source.splitAt front tail).1.append (source.splitAt front tail).2 = source := by
  induction front with
  | nil => rfl
  | push frame rest ih => cases source with
    | push annotation next =>
        simpa only [StackBounds.splitAt, StackBounds.append, Stack.append] using
          congrArg (StackBounds.push annotation) (ih next)
  | live owner input answer saved caller rest ihSaved ih => cases source with
    | live dormant next =>
        simpa only [StackBounds.splitAt, StackBounds.append, Stack.append] using
          congrArg (StackBounds.live dormant) (ih next)
  | spent owner answer caller rest ih => cases source with
    | spent next =>
        simpa only [StackBounds.splitAt, StackBounds.append, Stack.append] using
          congrArg StackBounds.spent (ih next)

/-- Capture retains exactly the original prefix and suffix annotations. -/
def StackBounds.atCut {whole capture tail : Stack} (source : StackBounds families whole)
    (cut : HandlerCut requested whole capture tail handler) :
    StackBounds families capture × StackBounds families tail := by
  cases cut.reconstructs
  exact source.splitAt capture tail

def StackBounds.capture {whole captured tail : Stack} (source : StackBounds families whole)
    (cut : HandlerCut requested whole captured tail handler) (owner : Nat) (input answer : Ty)
    (caller : ScopedExecution.Scope) :
    StackBounds families (.live owner input answer captured caller tail) :=
  .live (source.atCut cut).1 (source.atCut cut).2

/-- Dormant branches retain their own handler annotations, but active lookup
does not search them. A builtin provider blocks lower handler lookup. -/
def StackBounds.handlerAt {stack : Stack} (source : StackBounds families stack) (requested : Instance) :
    Option (Σ handler, HandlerBounds families handler) :=
  match source with
  | .nil => none
  | .push (.handler (data := handler) packet) rest =>
      if handler.effectInst = requested then some ⟨handler, packet⟩ else rest.handlerAt requested
  | .push (.cell (identity := identity)) rest =>
      if Instance.cell identity = requested then none else rest.handlerAt requested
  | .push .plain rest | .push .armed rest | .push .running rest |
      .push .closing rest | .push .retiring rest => rest.handlerAt requested
  | .live _ rest | .spent rest => rest.handlerAt requested

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- A structural source derivation for the recorded proof route. The bounded
case validates its exact bounds; the inherited case reuses a structural recipe
whose capture theorem handles arbitrary retained continuation syntax. -/
inductive HandlerBounds.Admitted (world : List Nat) (required : SourceContextualRechecking.Required)
    {handler : Handler} (packet : HandlerBounds families handler) : Prop where
  | bounded (route : packet.admission = .bounded) (annotated : Declarations world packet.plans)
      (checked : Bounded packet.bounds annotated (required handler.erase)) : Admitted world required packet
  | inherited (route : packet.admission = .inherited)
      (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler.erase) packet.plans) :
      Admitted world required packet

inductive FrameBounds.Admitted (world : List Nat) (required : SourceContextualRechecking.Required) :
    {frame : SourceAnnotatedRuntime.Frame} → FrameBounds families frame → Prop where
  | plain : Admitted world required .plain
  | handler : HandlerBounds.Admitted world required packet → Admitted world required (.handler packet)
  | cell : Admitted world required .cell
  | armed : Admitted world required .armed
  | running : Admitted world required .running
  | closing : Admitted world required .closing
  | retiring : Admitted world required .retiring

inductive StackBounds.Admitted (world : List Nat) (required : SourceContextualRechecking.Required) :
    {stack : Stack} → StackBounds families stack → Prop where
  | nil : Admitted world required .nil
  | push : FrameBounds.Admitted world required head → Admitted world required tail →
      Admitted world required (.push head tail)
  | live : Admitted world required saved → Admitted world required tail →
      Admitted world required (.live saved tail)
  | spent : Admitted world required tail → Admitted world required (.spent tail)

theorem HandlerBounds.Admitted.world_weaken
    (admitted : HandlerBounds.Admitted world required packet) (larger : world ⊆ nextWorld) :
    HandlerBounds.Admitted nextWorld required packet := by
  cases admitted with
  | bounded route annotated checked =>
      exact .bounded route (annotated.world_weaken larger) (checked.world_weaken larger)
  | inherited route recipes => exact .inherited route recipes

theorem FrameBounds.Admitted.world_weaken
    (admitted : FrameBounds.Admitted world required source) (larger : world ⊆ nextWorld) :
    FrameBounds.Admitted nextWorld required source := by
  cases admitted with
  | plain => exact .plain
  | handler checked => exact .handler (checked.world_weaken larger)
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

theorem StackBounds.Admitted.world_weaken
    (admitted : StackBounds.Admitted world required source) (larger : world ⊆ nextWorld) :
    StackBounds.Admitted nextWorld required source := by
  induction admitted with
  | nil => exact .nil
  | push head tail ih => exact .push (head.world_weaken larger) ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem StackBounds.Admitted.append {first : StackBounds families front} {second : StackBounds families tail}
    (before : first.Admitted world required) (after : second.Admitted world required) :
    (first.append second).Admitted world required := by
  induction before with
  | nil => exact after
  | push head tail ih => exact .push head (ih after)
  | live saved tail ihSaved ihTail => exact .live saved (ihTail after)
  | spent tail ih => exact .spent (ih after)

theorem StackBounds.Admitted.splitAt (front tail : Stack)
    {source : StackBounds families (front.append tail)} (admitted : source.Admitted world required) :
    (source.splitAt front tail).1.Admitted world required ∧
      (source.splitAt front tail).2.Admitted world required := by
  induction front with
  | nil => exact ⟨.nil, admitted⟩
  | push frame rest ih => cases source with
    | push annotation next => cases admitted with
      | push head checked =>
          obtain ⟨before, after⟩ := ih checked
          exact ⟨.push head before, after⟩
  | live owner input answer saved caller rest ihSaved ih => cases source with
    | live dormant next => cases admitted with
      | live saved checked =>
          obtain ⟨before, after⟩ := ih checked
          exact ⟨.live saved before, after⟩
  | spent owner answer caller rest ih => cases source with
    | spent next => cases admitted with
      | spent checked =>
          obtain ⟨before, after⟩ := ih checked
          exact ⟨.spent before, after⟩

theorem StackBounds.Admitted.atCut {whole capture tail : Stack} {source : StackBounds families whole}
    (admitted : source.Admitted world required) (cut : HandlerCut requested whole capture tail handler) :
    (source.atCut cut).1.Admitted world required ∧ (source.atCut cut).2.Admitted world required := by
  cases cut.reconstructs
  exact admitted.splitAt capture tail

theorem StackBounds.Admitted.capture {whole captured tail : Stack} {source : StackBounds families whole}
    (admitted : source.Admitted world required) (cut : HandlerCut requested whole captured tail handler) :
    (source.capture cut owner input answer caller).Admitted world required :=
  .live (admitted.atCut cut).1 (admitted.atCut cut).2

end

/-- Existing physical dispatch identifies exactly one stored annotation.
The theorem follows the existing cut, including builtin shadowing and dormant
branches; it does not introduce a different operational selection rule. -/
theorem StackBounds.handlerAt_cut {whole capture tail : Stack} {handler : Handler}
    (source : StackBounds families whole) (cut : HandlerCut requested whole capture tail handler) :
    ∃ packet : HandlerBounds families handler, source.handlerAt requested = some ⟨handler, packet⟩ := by
  induction cut with
  | hit handler tail same => cases source with
    | push head rest => cases head with
      | handler packet => exact ⟨packet, by simp only [StackBounds.handlerAt, same, if_true]⟩
  | push frame rest capture tail handler miss cut ih => cases source with
    | push head rest =>
      obtain ⟨packet, found⟩ := ih rest
      refine ⟨packet, ?_⟩
      cases head <;>
        simp_all [StackBounds.handlerAt, SourceAnnotatedRuntime.Frame.erase,
          ScopedExecution.ExecFrame.erase, Ash.OneShot.Frame.target, SourceAnnotatedRuntime.Handler.erase,
          ScopedExecution.HandlerData.erase]
  | live owner input answer saved caller rest capture tail handler cut ih => cases source with
    | live dormant rest => exact ih rest
  | spent owner answer caller rest capture tail handler cut ih => cases source with
    | spent rest => exact ih rest

/-- The finite lookup fixes the packet, including its bounds, uniquely. -/
theorem StackBounds.handlerAt_unique {source : StackBounds families stack}
    (first : source.handlerAt requested = some ⟨handler, before⟩)
    (second : source.handlerAt requested = some ⟨handler, after⟩) : before = after :=
  eq_of_heq (Sigma.mk.inj (Option.some.inj (first.symm.trans second))).2

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem StackBounds.Admitted.handlerAt {source : StackBounds families stack}
    (admitted : StackBounds.Admitted world required source)
    (found : source.handlerAt requested = some ⟨handler, packet⟩) :
    HandlerBounds.Admitted world required packet := by
  induction admitted with
  | nil => cases found
  | push head tail ih =>
      cases head with
      | handler checked =>
          simp only [StackBounds.handlerAt] at found
          split at found
          · cases Option.some.inj found
            exact checked
          · exact ih found
      | cell =>
          simp only [StackBounds.handlerAt] at found
          split at found
          · cases found
          · exact ih found
      | plain | armed | running | closing | retiring => exact ih found
  | live saved tail ihSaved ihTail => exact ihTail found
  | spent tail ih => exact ih found

/-- Existing typed structural handler admission supplies annotations at entry.
The handler case uses the very plans and bounds in that source derivation. -/
theorem frame_annotations {hints : SourceContextualHints.Hints receivingScope}
    {receiving : SourceRetainedPlans.Forest hints}
    (frame : SourceAnnotatedRuntimeTyping.Frame (evidence := SourceConsumingDeclarationEntry.evidence world)
      operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing) :
    ∃ source : FrameBounds families entry, source.Admitted world required := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation checked => exact ⟨.plain, .plain⟩
  | handler scope annotation clauses coverage unique declarations stored supplied capabilities modes =>
      obtain ⟨bounds, annotated, checked⟩ := stored
      exact ⟨.handler ⟨_, bounds, .bounded⟩, .handler (.bounded rfl annotated checked)⟩
  | cell scopeKnown noEscape annotation interface => exact ⟨.cell, .cell⟩
  | armed scopeKnown callback annotation interface checked => exact ⟨.armed, .armed⟩
  | running scopeKnown callback saved annotation interface => exact ⟨.running, .running⟩
  | closing scopeKnown interface => exact ⟨.closing, .closing⟩
  | retiring known interface => exact ⟨.retiring, .retiring⟩

/-- Initial extraction from an admitted segment covers recursively dormant
captures. Later capture/recomposition transports this data instead of invoking
this existential extraction to choose new bounds at each request. -/
theorem segment_annotations
    (segment : SourceAnnotatedRuntimeTyping.Segment (evidence := SourceConsumingDeclarationEntry.evidence world)
      operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing) :
    ∃ source : StackBounds families stack, source.Admitted world required := by
  generalize sameEvidence : SourceConsumingDeclarationEntry.evidence world = sourceEvidence at segment
  induction segment with
  | nil bound => exact ⟨.nil, .nil⟩
  | push head tail bound ih =>
      cases sameEvidence
      obtain ⟨entry, entryChecked⟩ := frame_annotations head
      obtain ⟨rest, restChecked⟩ := ih rfl
      exact ⟨.push entry rest, .push entryChecked restChecked⟩
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases sameEvidence
      obtain ⟨inside, insideChecked⟩ := ihSaved rfl
      obtain ⟨rest, restChecked⟩ := ihTail rfl
      exact ⟨.live inside rest, .live insideChecked restChecked⟩
  | spent known annotation scope tail bound ih =>
      cases sameEvidence
      obtain ⟨rest, restChecked⟩ := ih rfl
      exact ⟨.spent rest, .spent restChecked⟩

end
end Ash.OneShot.SourceConsumingStoredBounds

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.Admitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingStoredBounds.FrameBounds.Admitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.world_weaken
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.handlerAt_cut
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.handlerAt_unique
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.handlerAt
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.splitAt_append
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.append
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.splitAt
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.atCut
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.capture
#print axioms Ash.OneShot.SourceConsumingStoredBounds.frame_annotations
#print axioms Ash.OneShot.SourceConsumingStoredBounds.segment_annotations
