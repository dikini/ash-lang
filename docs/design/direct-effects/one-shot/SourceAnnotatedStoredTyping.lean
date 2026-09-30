import SourceAnnotatedRuntimeTransport
import SourceConsumingStoredBounds

/-! Runtime source and stored declaration packets share each intermediate rich
interface in one structural judgment. A handler checks its packet's exact plan;
no equality is inferred between independent existential source derivations. -/
namespace Ash.OneShot.SourceAnnotatedStoredTyping
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Operations Contracts)
open SourceAnnotatedSources (Declarations)
open SourcePlannedFrames (DependencyScope Families Decoration DeclarationEvidence recipeEvidence)
open SourceAnnotatedRuntimeTyping (PlanDecoration)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (FrameBounds StackBounds)
open RecursiveRequirements (Requirements Store)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The source at an installed handler packet has the same rich answer and
residual interfaces as its runtime frame. Other frames carry no handler packet. -/
inductive PacketSource (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families)
    (required : SourceContextualRechecking.Required) (world : List Nat) (evidence : DeclarationEvidence) :
    {entry : SourceAnnotatedRuntime.Frame} → FrameBounds families entry →
      Value → Value → List Instance → List Instance → Prop where
  | plain : PacketSource operations policy contracts tables families required world evidence .plain input output incoming outgoing
  | handler {packet : SourceConsumingStoredBounds.HandlerBounds families handler}
      (source : Declarations operations policy contracts world (fun _ => none) residual handler.effectInst answer
        handler.clauses (tables handler.erase) packet.plans)
      (checked : evidence (required handler.erase) packet.plans) :
      PacketSource operations policy contracts tables families required world evidence (.handler packet)
        answer answer (handler.effectInst :: residual) residual
  | cell : PacketSource operations policy contracts tables families required world evidence .cell input output incoming outgoing
  | armed : PacketSource operations policy contracts tables families required world evidence .armed input output incoming outgoing
  | running : PacketSource operations policy contracts tables families required world evidence .running input output incoming outgoing
  | closing : PacketSource operations policy contracts tables families required world evidence .closing input output incoming outgoing
  | retiring : PacketSource operations policy contracts tables families required world evidence .retiring input output incoming outgoing

structure Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required)
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (world : List Nat) {receivingScope : DependencyScope} {receivingHints : Hints receivingScope}
    (receiving : Forest receivingHints) (entry : SourceAnnotatedRuntime.Frame) (input output : Value)
    (demand : List Nat) (requirements : Requirements demand) (layer : DependencyScope → DependencyScope)
    (decorate : Decoration layer) (decoratePlans : PlanDecoration @decorate) (incoming outgoing : List Instance)
    (packet : FrameBounds families entry) (evidence : DeclarationEvidence := recipeEvidence) : Prop where
  forget : SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts tables families required
    outward actions phases world receiving entry input output demand requirements layer @decorate @decoratePlans incoming outgoing
  packetSource : PacketSource operations policy contracts tables families required world evidence packet input output incoming outgoing

inductive Segment [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (phases : OwnerPhaseTransitions.Phases) (world : List Nat) :
    (stack : SourceAnnotatedRuntime.Stack) → Value → Value → (demand : List Nat) → Requirements demand → Store → {dependencyScope : DependencyScope} → {hints : Hints dependencyScope} → Forest hints → {outsideScope : DependencyScope} → {outsideHints : Hints outsideScope} → Forest outsideHints →
      List Instance → List Instance → StackBounds families stack → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world .nil result result [] (.request [] []) [] .nil outside incoming outgoing .nil
  | push (head : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world (restHints.append outside) entry input middle headDemand first layer decorate decoratePlans inner outer headStored)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest middle output tailDemand second records restHints outside outer outgoing restStored)
      (bound : incoming ⊆ inner) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest.erase)) second) records (decoratePlans restHints) outside incoming outgoing (.push headStored restStored)
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase.erase)
      (saved : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        capture contract.input contract.answer contract.resumeDemand body nested savedHints (restHints.append outside) [] savedBoundary captureStored)
      (savedBound : rights.resume = true → savedBoundary ⊆ contract.resumeEffects)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest contract.answer output
        demand requirements remaining restHints outside boundary outgoing restStored)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) (.live (owner := owner) savedHints restHints) outside incoming outgoing (.live captureStored restStored)
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest contract.answer output
        demand requirements records restHints outside boundary outgoing restStored)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records (.spent (owner := owner) restHints) outside incoming outgoing (.spent restStored)

/-- The packet data are an index of the judgment, not extracted from a proof. -/
def Segment.packets
    (_source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing stored) :
    StackBounds families stack := stored

theorem Segment.forget {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing stored) :
    SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.forget ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

omit admission certification in
theorem PacketSource.transport
    (source : PacketSource operations policy contracts tables families required world evidence packet input output incoming outgoing)
    (extension : contracts.Extends nextContracts) :
    PacketSource operations policy nextContracts tables families required world evidence packet input output incoming outgoing := by
  cases source with
  | handler source checked => exact .handler (SourceAnnotatedSources.declarations_extension source extension) checked
  | plain => exact .plain
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

omit admission certification in
theorem PacketSource.world_weaken
    (source : PacketSource operations policy contracts tables families required world evidence packet input output incoming outgoing)
    (larger : world ⊆ nextWorld) :
    PacketSource operations policy contracts tables families required nextWorld evidence packet input output incoming outgoing := by
  cases source with
  | handler source checked => exact .handler (SourceAnnotatedSources.declarations_world_weaken source larger) checked
  | plain => exact .plain
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

theorem Frame.transport
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Frame (evidence := evidence) operations policy nextContracts tables families required outward nextActions after world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet :=
  ⟨frame.forget.transport extension phases permissions, frame.packetSource.transport extension⟩

theorem Frame.world_weaken
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (larger : world ⊆ nextWorld) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions phases nextWorld
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet :=
  ⟨frame.forget.world_weaken larger, frame.packetSource.world_weaken larger⟩

theorem Segment.transport
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records hints outside incoming outgoing stored)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Segment (evidence := evidence) operations policy nextContracts tables families required nextActions outward after world
      stack input output demand requirements records hints outside incoming outgoing stored := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension
    (SourceDependencyFrames.erased_contract_extension (SourcePlannedCheckedFrames.erased_extension extension))
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.transport extension phases permissions) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ actionKnown) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension scope ports) held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports) ih bound

theorem Segment.world_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing stored)
    (larger : world ⊆ nextWorld) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases nextWorld
      stack input output demand requirements records forest outside incoming outgoing stored := by
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.world_weaken larger) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

theorem Frame.receiving_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      first entry input output demand requirements layer decorate decoratePlans incoming outgoing packet) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      second entry input output demand requirements layer decorate decoratePlans incoming outgoing packet := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

theorem Segment.receiving_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints first incoming outgoing stored) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints second incoming outgoing stored := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

theorem Segment.forest_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records first outside incoming outgoing stored) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records second outside incoming outgoing stored := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

/-- Read the exact recorded declaration at the frame's rich answer/residual. -/
theorem Frame.handler_source
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving (.handler handler) answer answer demand requirements layer decorate decoratePlans incoming residual (.handler packet)) :
    SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) residual handler.effectInst answer
      handler.clauses (tables handler.erase) packet.plans ∧ evidence (required handler.erase) packet.plans := by
  cases frame.packetSource with
  | handler source checked => exact ⟨source, checked⟩

theorem Segment.input_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside incoming outgoing stored)
    (smaller : nextIncoming ⊆ incoming) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside nextIncoming outgoing stored := by
  cases source with
  | nil bound => exact .nil (List.Subset.trans smaller bound)
  | push head tail bound => exact .push head tail (List.Subset.trans smaller bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close
        (List.Subset.trans smaller bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (List.Subset.trans smaller bound)


theorem Frame.recheck {oldHints : Hints oldScope} {receiving : Forest oldHints}
    {restHints : Hints restScope} {rest : Forest restHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (checked : SourceScheduledChecks.Pending nextOutward actions after world (decoratePlans rest) outside) :
    Frame (evidence := evidence) operations policy contracts tables families required nextOutward actions after world
      (rest.append outside) entry input output demand requirements layer decorate decoratePlans incoming outgoing packet ∧
    SourceScheduledChecks.Pending nextOutward actions after world rest outside := by
  obtain ⟨next, pending⟩ := frame.forget.recheck checked
  exact ⟨⟨next, frame.packetSource⟩, pending⟩

theorem Segment.recheck {hints : Hints scope} {forest : Forest hints}
    {oldHints : Hints oldScope} {oldOutside : Forest oldHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records forest oldOutside incoming outgoing stored)
    (checked : SourceScheduledChecks.Pending nextOutward actions after world forest outside) :
    Segment (evidence := evidence) operations policy contracts tables families required actions nextOutward after world
      stack input output demand requirements records forest outside incoming outgoing stored := by
  induction source generalizing outsideScope with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      obtain ⟨headNext, tailCheck⟩ := head.recheck checked
      exact .push headNext (ih tailCheck) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases checked with
      | live inside outside =>
        exact .live known actionKnown inputAnnotation answerAnnotation scope held (ihSaved inside) savedBound
          (ihTail outside) resume close bound
  | spent known annotation scope tail bound ih => cases checked with
    | spent outside => exact .spent known annotation scope (ih outside) bound

/-- Widen the external effect interface without changing retained plans. -/
theorem Segment.output_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing stored)
    (larger : outgoing ⊆ nextOutgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming nextOutgoing stored := by
  induction source with
  | nil bound => exact .nil (List.Subset.trans bound larger)
  | push head tail bound ih => exact .push head (ih larger) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ihTail larger) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih larger) bound


end Ash.OneShot.SourceAnnotatedStoredTyping

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.forget
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.PacketSource.transport
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.PacketSource.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.transport
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.transport
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.receiving_congr
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.receiving_congr
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.forest_congr

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.handler_source
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.input_weaken

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.recheck

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.recheck

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.output_weaken
