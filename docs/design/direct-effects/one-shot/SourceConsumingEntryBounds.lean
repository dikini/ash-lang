import SourceConsumingCleanupAdmission

/-! Observation equations for actual handler and cleanup admission constructors.
These are projections of their exact metadata-agreement proofs. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints Requirement)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceBoundSnapshots.Retained (ofCapability)
open OwnerPhaseTransitions (spend)
variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

theorem Context.handler_resumption_bounds
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
        (front.append (.spent (owner := owner) waiting)))))
    (permission : (actions owner).any (fun rights => rights.resume) = true) :
    ofCapability ((context.handler laws (@project) effect table families required resumption closing).resumption permission).val = ofCapability (context.resumption permission).val :=
  (Context.handler_bounds laws (@project) context effect table families required resumption closing).resumption permission

theorem Context.handler_closing_bounds
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
        (front.append (.spent (owner := owner) waiting)))))
    (permission : (actions owner).any (fun rights => rights.dispose) = true) :
    ofCapability ((context.handler laws (@project) effect table families required resumption closing).closing permission).val = ofCapability (context.closing permission).val :=
  (Context.handler_bounds laws (@project) context effect table families required resumption closing).closing permission

theorem Context.handler_tail_bounds
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
    ofCapability (context.handler laws (@project) effect table families required resumption closing).after = ofCapability context.after :=
  (Context.handler_bounds laws (@project) context effect table families required resumption closing).tail

theorem Context.cleanupSource_resumption_bounds
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
      (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting)))))
    (permission : (actions owner).any (fun rights => rights.resume) = true) :
    ofCapability ((context.cleanupSource laws (@project) footprint declared needs resumption closing).resumption permission).val = ofCapability (context.resumption permission).val :=
  (Context.cleanupSource_bounds laws (@project) context footprint declared needs resumption closing).resumption permission

theorem Context.cleanupSource_closing_bounds
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
      (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting)))))
    (permission : (actions owner).any (fun rights => rights.dispose) = true) :
    ofCapability ((context.cleanupSource laws (@project) footprint declared needs resumption closing).closing permission).val = ofCapability (context.closing permission).val :=
  (Context.cleanupSource_bounds laws (@project) context footprint declared needs resumption closing).closing permission

theorem Context.cleanupSource_tail_bounds
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
    ofCapability (context.cleanupSource laws (@project) footprint declared needs resumption closing).after = ofCapability context.after :=
  (Context.cleanupSource_bounds laws (@project) context footprint declared needs resumption closing).tail

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.handler_resumption_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.handler_closing_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.handler_tail_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanupSource_resumption_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanupSource_closing_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.cleanupSource_tail_bounds
