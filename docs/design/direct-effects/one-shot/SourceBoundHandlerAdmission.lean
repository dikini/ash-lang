import SourceBoundHandlerEntry
import SourceConsumingBoundInstallation

/-! The admitted source annotation determines the installed packet and its
proof route. Explicit bounds cannot switch to inherited admission. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (ModePlans ClausePlans)

/-- Inherited packets use their recipe proof rather than these empty fields.
The constructor retains the actual offer shape, including unavailable modes. -/
def ModeBounds.inherited (plans : ModePlans family) : ModeBounds plans :=
  match plans with
  | .unavailable => .unavailable
  | .available _ => .available ⟨[], []⟩

def ClauseBounds.inherited (plans : ClausePlans clauses families) : ClauseBounds plans :=
  match plans with
  | .nil => .nil
  | .cons ordinary protectedMode rest =>
      .cons (ModeBounds.inherited ordinary) (ModeBounds.inherited protectedMode) (ClauseBounds.inherited rest)

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (ClauseBounds)
open SourceConsumingStoredBounds (HandlerBounds)
open SourceAnnotatedRuntime (Handler)
open SourceScheduledHandlers (register)

def Annotation.handlerPacket (handler : Handler)
    {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
    (actual : ClausePlans handler.clauses.erase clauseFamilies) :
    HandlerBounds (register families handler.activation clauseFamilies) handler :=
  match bounds.handlerBounds with
  | none => HandlerBounds.installed handler actual (ClauseBounds.inherited actual) .inherited
  | some recorded => HandlerBounds.installed handler actual (recorded.reindex actual) .bounded

/-- Both admission routes retain the same actual typed declaration witness. -/
theorem Annotation.handlerPacket_source (handler : Handler)
    {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
    (actual : ClausePlans handler.clauses.erase clauseFamilies)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table actual) :
    SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table (bounds.handlerPacket (families := families) handler actual).plans := by
  unfold Annotation.handlerPacket
  cases bounds.handlerBounds <;> exact HandlerBounds.installed_source handler actual _ _ source

theorem Annotation.handlerPacket_recorded (handler : Handler)
    {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
    (actual : ClausePlans handler.clauses.erase clauseFamilies)
    {original : ClauseBounds checking}
    (recorded : bounds.handlerBounds = some original) :
    (bounds.handlerPacket (families := families) handler actual).admission = .bounded ∧
    ∀ operation held, (bounds.handlerPacket (families := families) handler actual).bounds.lookup operation held =
      original.lookup operation held := by
  constructor
  · simp only [Annotation.handlerPacket, recorded, HandlerBounds.installed_admission]
  · intro operation held
    rw [Annotation.handlerPacket, recorded]
    exact (HandlerBounds.installed_lookup _ _ _ _).trans (ClauseBounds.lookup_reindex _ _)

theorem Annotation.handlerPacket_inherited (handler : Handler)
    {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
    (actual : ClausePlans handler.clauses.erase clauseFamilies)
    (missing : bounds.handlerBounds = none) :
    (bounds.handlerPacket (families := families) handler actual).admission = .inherited := by
  simp only [Annotation.handlerPacket, missing, HandlerBounds.installed_admission]

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Annotation.Admitted.handler_packet
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (handler : Handler) {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) declarationRequired checking body)}
    (admitted : bounds.Admitted) (actual : ClausePlans handler.clauses.erase clauseFamilies)
    (same : SourcePlanSignatures.clauseSignatures checking = SourcePlanSignatures.clauseSignatures actual) :
    (bounds.handlerPacket (families := families) handler actual).Admitted
      world (register required handler.activation declarationRequired) := by
  have original := admitted.handler_declaration
  cases recorded : bounds.handlerBounds with
  | none =>
      simp only [recorded] at original
      simpa only [Annotation.handlerPacket, recorded] using
        (HandlerBounds.installed_inherited (families := families) (required := required) (world := world)
          handler actual (ClauseBounds.inherited actual) (original.signature_congr same))
  | some packet =>
      simp only [recorded] at original
      obtain ⟨source, checked⟩ := original
      simpa only [Annotation.handlerPacket, recorded] using
        (HandlerBounds.installed_from_signature transport handler actual packet source checked same).1

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanBounds (Annotation)
open SourcePlanSignatures (clauseSignatures)
open SourceConsumingStoredBounds (HandlerBounds StackBounds)
open SourceAnnotatedRuntime (Handler)
open SourceScheduledHandlers (register register_agrees)

/-- The installed packet comes from the original root annotation and the
same actual clause plans exposed by runtime entry. -/
inductive HandlerPacketFrom (handler : Handler) (table : List (Nat × ProtectionContracts.ClauseContract))
    (required : List SourceContextualHints.Requirement)
    {clauseFamilies} (actual : ClausePlans handler.clauses.erase clauseFamilies) :
    Snapshot world → HandlerBounds (register families handler.activation clauseFamilies) handler → Prop where
  | step {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
      {hints : SourceContextualHints.Hints scope} {forest : SourceRetainedPlans.Forest hints}
      (bounds : Annotation world (.handler (effect := handler.effectInst) (table := table) required checking body))
      (remaining : Retained world forest) (same : clauseSignatures checking = clauseSignatures actual) :
      HandlerPacketFrom handler table required actual ⟨_, _, bounds, _, hints, forest, remaining⟩
        (bounds.handlerPacket handler actual)

theorem HandlerPacketFrom.lookup {before : Snapshot world}
    {families : SourceDependencyCapture.Families}
    {actual : ClausePlans handler.clauses.erase clauseFamilies}
    {packet : HandlerBounds (register families handler.activation clauseFamilies) handler}
    (source : HandlerPacketFrom handler table required actual before packet) :
    before.current.lookup .here operation held =
      if packet.admission = .bounded then some (packet.bounds.lookup operation held) else none := by
  cases source with
  | step bounds remaining same =>
      rw [← Annotation.handlerBounds_lookup]
      cases recorded : bounds.handlerBounds with
      | none =>
          have route := bounds.handlerPacket_inherited (families := families) handler actual recorded
          simp only [Option.map_none, route, reduceCtorEq, if_false]
      | some original =>
          obtain ⟨route, lookup⟩ := bounds.handlerPacket_recorded (families := families) handler actual recorded
          simp only [Option.map_some, route, if_true]
          exact congrArg some (lookup operation held).symm

/-- Source typing follows the packet origin, rather than an independently
chosen plan with the same dependency family. -/
theorem HandlerPacketFrom.source {before : Snapshot world}
    {families : SourceDependencyCapture.Families}
    {actual : ClausePlans handler.clauses.erase clauseFamilies}
    {packet : HandlerBounds (register families handler.activation clauseFamilies) handler}
    (origin : HandlerPacketFrom handler table required actual before packet)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table actual) :
    SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table packet.plans := by
  cases origin with
  | step bounds remaining same => exact bounds.handlerPacket_source handler actual source

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem EnteredHandler.install_admitted
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → clauseSignatures first = clauseSignatures second →
        nested.accepts required second)
    {handler : Handler} {actual : ClausePlans handler.clauses.erase clauseFamilies}
    {before after : Snapshot world}
    (step : EnteredHandler handler.effectInst table declarationRequired actual before after)
    (admitted : before.Admitted)
    (stored : StackBounds families stack) (checked : stored.Admitted world requirements)
    (fresh : handler.activation ∉ stack.erase.erase.activations) :
    ∃ packet : HandlerBounds (register families handler.activation clauseFamilies) handler,
    ∃ next : StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack),
      next = .push (.handler packet) (stored.registries_congr (register_agrees fresh)) ∧
      next.Admitted world (register requirements handler.activation declarationRequired) ∧
      after.Admitted ∧ HandlerPacketFrom handler table declarationRequired actual before packet := by
  cases step with
  | step bounds remaining same =>
      let packet := bounds.handlerPacket (families := families) handler actual
      have packetChecked := admitted.1.handler_packet (families := families) (required := requirements)
        transport handler actual same
      exact ⟨packet, .push (.handler packet) (stored.registries_congr (register_agrees fresh)), rfl,
        .push (.handler packetChecked) (checked.registries_congr (register_agrees fresh) (register_agrees fresh)),
        ⟨admitted.1.handler_body, .handler admitted.2⟩, .step bounds remaining same⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerPacket_recorded
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerPacket_inherited
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.handler_packet

#print axioms Ash.OneShot.SourceBoundSnapshots.HandlerPacketFrom.lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredHandler.install_admitted

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerPacket_source
#print axioms Ash.OneShot.SourceBoundSnapshots.HandlerPacketFrom.source
