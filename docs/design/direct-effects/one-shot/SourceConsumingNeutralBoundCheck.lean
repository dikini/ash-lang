import SourceConsumingBoundTransport
import SourceNeutralScopes

/-! Neutral receiver changes preserve the existing finite clause checks.
The proof reuses neutral operation lookup and interface weakening. It does not
transport saved-source admission or grant a continuation action. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourcePlannedNeutralFrames (Expansion)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Changes preserve the receiving and caller interpretation observations.
The caller interface equality is checked at the actual waiting suffix; nested
source constructors and resource weakening preserve that equality. -/
theorem Body.boundCheck_neutral_waiting {plan : Plan dependencies} (body : Body world owner plan)
    {receivingHints : Hints receiving} {nextReceivingHints : Hints nextReceiving}
    {frontHints : Hints frontScope} {nextFrontHints : Hints nextFrontScope}
    {front : Forest frontHints} {nextFront : Forest nextFrontHints}
    {before : Interfaces world front} {after : Interfaces world nextFront}
    {waitingHints : Hints waiting} {nextWaitingHints : Hints nextWaiting}
    (waitingChange : Expansion waitingHints nextWaitingHints)
    (receiver : Expansion receivingHints nextReceivingHints)
    (caller : Expansion frontHints nextFrontHints)
    (sameCheck : before.check (.spent owner waiting) = after.check (.spent owner nextWaiting))
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before) :
    body.BoundCheck resumeRequired closeRequired actions phases nextReceiving nextWaiting after := by
  induction body generalizing receiving nextReceiving frontScope nextFrontScope with
  | resume =>
      exact ⟨checked.1, checked.2.1,
        (caller.append (.spent waitingChange)).requirements ▸ checked.2.2.1,
        sameCheck ▸ checked.2.2.2⟩
  | dispose =>
      exact ⟨checked.1, checked.2.1,
        (Expansion.running (caller.append (.spent waitingChange))).requirements ▸ checked.2.2.1,
        sameCheck ▸ checked.2.2.2⟩
  | sequence required footprint declared rest ih =>
      exact ⟨(Expansion.plain receiver).requirements ▸ checked.1,
        ih receiver caller sameCheck checked.2⟩
  | choice first second ihFirst ihSecond =>
      exact ⟨ihFirst receiver caller sameCheck checked.1,
        ihSecond receiver caller sameCheck checked.2⟩
  | handler bounds declared inner ih =>
      refine ⟨receiver.requirements ▸ checked.1,
        ih (.handler (required := []) receiver) (.handler caller) ?_ checked.2⟩
      simp only [Interfaces.check, sameCheck]
      congr 1
      exact (caller.append (.spent waitingChange)).requirements
  | cleanup required footprint declared inner ih =>
      refine ⟨ih (.cleanup receiver) (.cleanup caller) ?_ checked.1,
        (Expansion.running receiver).requirements ▸ checked.2⟩
      simp only [Interfaces.check, sameCheck]
      congr 1
      exact (Expansion.running (caller.append (.spent waitingChange))).requirements
  | resource inner ih =>
      intro identity fresh
      apply ih identity fresh (.cell receiver) (.cell caller) ?_ (checked identity fresh)
      simpa only [Interfaces.check, Interfaces.check_world_weaken] using sameCheck

/-- The original fixed-waiting API is the reflexive case. -/
theorem Body.boundCheck_neutral {plan : Plan dependencies} (body : Body world owner plan)
    {receivingHints : Hints receiving} {nextReceivingHints : Hints nextReceiving}
    {frontHints : Hints frontScope} {nextFrontHints : Hints nextFrontScope}
    {front : Forest frontHints} {nextFront : Forest nextFrontHints}
    {before : Interfaces world front} {after : Interfaces world nextFront}
    (waitingHints : Hints waiting)
    (receiver : Expansion receivingHints nextReceivingHints)
    (caller : Expansion frontHints nextFrontHints)
    (sameCheck : before.check (.spent owner waiting) = after.check (.spent owner waiting))
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before) :
    body.BoundCheck resumeRequired closeRequired actions phases nextReceiving waiting after :=
  body.boundCheck_neutral_waiting (Expansion.refl (hints := waitingHints)) receiver caller sameCheck checked

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_neutral

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_neutral_waiting
