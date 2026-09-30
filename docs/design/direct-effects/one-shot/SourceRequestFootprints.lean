import SourcePlanSignatures
import SourceHandlerRequirements

/-! Finite request interfaces belong to stable source signatures. They do not
depend on literal clause witnesses, runtime forests, or a source-success
judgment. Actual plans and callable annotations share this representation. -/
namespace Ash.OneShot.SourceRequestFootprints
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (Signature)
open SourceContextualHints (Requirement checkRequirements)

/-- Handler declarations remain independently authenticated by source typing.
The interface records the operation requirements of the computation signature;
explicit continuation uses require their separate capability judgment. -/
inductive Footprint : {dependencies : Dependencies} → Signature dependencies → List Requirement → Prop where
  | pure : Footprint .pure []
  | request : Footprint (.request (effect := effect) (operation := operation)) [(effect, operation)]
  | handledRequest : Footprint
      (SourcePlanSignatures.signature (SourceDeclarationPlans.HandledRequest.plan effect operation)) []
  | sequence : Footprint first firstRequired → Footprint second secondRequired →
      Footprint (.sequence first second) (firstRequired ++ secondRequired)
  | choice : Footprint first firstRequired → Footprint second secondRequired →
      Footprint (.choice first second) (firstRequired ++ secondRequired)
  | handler {declarations : SourcePlanSignatures.ClauseSignatures families}
      (body : Footprint code bodyRequired)
      (internal : checkRequirements (.handler effect table families .nil)
        (SourceHandlerRequirements.intercepted effect bodyRequired) = true) :
      Footprint (.handler (effect := effect) (table := table) required declarations code)
        (required ++ SourceHandlerRequirements.outwardRequirements (.handler effect table families .nil) bodyRequired)
  | cleanup : Footprint callback callbackRequired → Footprint body bodyRequired →
      Footprint (.cleanup (needs := needs) callback body) (callbackRequired ++ bodyRequired)
  | resource (body : ∀ identity, Footprint (code identity)
      ([(Instance.cell identity, 0), (.cell identity, 1)] ++ required)) :
      Footprint (.resource code) required
  | weaken : Footprint code first → first ⊆ second → Footprint code second

/-- Signature equality transports the same finite interface. No complete
body checker or successful future instantiation is an annotation field. -/
theorem Footprint.congr (source : Footprint first required) (same : first = second) :
    Footprint second required := same ▸ source

/-- Operation requirements cannot stand in for continuation permissions. -/
theorem Footprint.no_invocation {checking : Signature dependencies}
    (footprint : Footprint checking required) (same : dependencies = .invoke key) : False := by
  induction footprint with
  | pure | request | handledRequest | sequence | choice | handler | cleanup | resource => cases same
  | weaken body included ih => exact ih same

end Ash.OneShot.SourceRequestFootprints

#print axioms Ash.OneShot.SourceRequestFootprints.Footprint.congr
#print axioms Ash.OneShot.SourceRequestFootprints.Footprint.no_invocation
