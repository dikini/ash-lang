import SourceConsumingBoundAnnotations

/-! Stable signatures transport structural consuming declarations while keeping
their recorded bounds. Nested declaration policies must supply their own source
transport law; the established recipe judgment supplies one. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

theorem ModeBounds.acceptsResume_reindex {first : ModePlans family} (bounds : ModeBounds first)
    (second : ModePlans family) :
    (bounds.reindex second).acceptsResume required = bounds.acceptsResume required := by
  cases bounds <;> cases second <;> rfl

theorem ClauseBounds.acceptsResume_reindex {first : ClausePlans before families} (bounds : ClauseBounds first)
    (second : ClausePlans after families) :
    (bounds.reindex second).acceptsResume required = bounds.acceptsResume required := by
  induction bounds generalizing after with
  | nil => cases second; rfl
  | cons ordinary protectedMode rest ih => cases second with
    | cons nextOrdinary nextProtected nextRest =>
      simp only [ClauseBounds.reindex, ClauseBounds.acceptsResume, ModeBounds.acceptsResume_reindex, ih]

section
variable [nested : DeclarationPolicy]
variable (transport : ∀ {before after families required}
    {first : ClausePlans before families} {second : ClausePlans after families},
    nested.accepts required first → clauseSignatures first = clauseSignatures second →
      nested.accepts required second)

include transport

/-- Reindex the original source data deterministically. This lets independent
structural judgments follow the same transported body and recorded bounds. -/
noncomputable def Body.reindex {first : Plan dependencies} (body : Body world owner first) :
    (second : Plan dependencies) → signature first = signature second → Body world owner second :=
  match world, owner, dependencies, first, body with
  | _, _, _, _, .resume => fun second _ => match second with | .invoke => .resume
  | _, _, _, _, .dispose => fun second _ => match second with | .invoke => .dispose
  | _, _, _, _, .sequence required footprint declared rest => fun second same => match second with
    | .sequence _before after =>
      .sequence required
        (SourceScheduledAdaptationCompilation.RequestFootprint.signature_congr footprint (Signature.sequence.inj same).1)
        (SourceScheduledSourceInterfaces.Declared.congr declared (Signature.sequence.inj same).1)
        (rest.reindex after (Signature.sequence.inj same).2)
  | _, _, _, _, .choice first last => fun second same => match second with
    | .choice nextFirst nextLast =>
      .choice (first.reindex nextFirst (Signature.choice.inj same).1)
        (last.reindex nextLast (Signature.choice.inj same).2)
  | _, _, _, _, .handler bounds declared code => fun second same => match second with
    | .handler _nextRequired nextPlans nextCode =>
      (Signature.handler.inj same).1 ▸
        Body.handler (bounds.reindex nextPlans) (transport declared (Signature.handler.inj same).2.1)
          (code.reindex nextCode (Signature.handler.inj same).2.2)
  | _, _, _, _, .cleanup required footprint declared code => fun second same => match second with
    | .cleanup _nextCallback nextCode =>
      .cleanup required
        (SourceScheduledAdaptationCompilation.RequestFootprint.signature_congr footprint (Signature.cleanup.inj same).1)
        (SourceScheduledSourceInterfaces.Declared.congr declared (Signature.cleanup.inj same).1)
        (code.reindex nextCode (Signature.cleanup.inj same).2)
  | _, _, _, _, .resource code => fun second same => match second with
    | .resource nextCode =>
      .resource (fun identity fresh => (code identity fresh).reindex (nextCode identity) (congrFun (Signature.resource.inj same) identity))
termination_by structural body

/-- Continuation-use admission follows the deterministic transport of source
annotations, independently of recursive nested-declaration validation. -/
theorem Admitted.reindex {first second : Plan dependencies} {body : Body world owner first}
    (admitted : Admitted rights resumeRequired closeRequired body required)
    (same : signature first = signature second) :
    Admitted rights resumeRequired closeRequired (body.reindex transport second same) required := by
  induction admitted with
  | resume permission => cases second; exact .resume permission
  | dispose permission => cases second; exact .dispose permission
  | sequence rest ih => cases second with
    | sequence first next =>
      obtain ⟨firstSame, nextSame⟩ := Signature.sequence.inj same
      exact .sequence (ih nextSame)
  | choice first last ihFirst ihLast => cases second with
    | choice nextFirst nextLast =>
      obtain ⟨firstSame, lastSame⟩ := Signature.choice.inj same
      exact .choice (ihFirst firstSame) (ihLast lastSame)
  | handler body internal coverage ih => cases second with
    | handler nextRequired nextPlans nextCode =>
      obtain ⟨rfl, clausesSame, bodySame⟩ := Signature.handler.inj same
      simp only [Body.reindex]
      refine .handler (ih bodySame) internal ?_
      simpa only [ClauseBounds.acceptsResume_reindex] using coverage
  | cleanup body ih => cases second with
    | cleanup nextCallback nextCode =>
      obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
      exact .cleanup (ih bodySame)
  | resource body ih => cases second with
    | resource nextCode =>
      simp only [Body.reindex]
      exact .resource (fun identity fresh => ih identity fresh (congrFun (Signature.resource.inj same) identity))
  | weaken body included ih => exact .weaken (ih same) included

/-- Existing callers retain the existential interface, with its witness now
fixed by the deterministic source-data transport. -/
theorem Admitted.signature_congr {first second : Plan dependencies} {body : Body world owner first}
    (admitted : Admitted rights resumeRequired closeRequired body required)
    (same : signature first = signature second) :
    ∃ next : Body world owner second, Admitted rights resumeRequired closeRequired next required :=
  ⟨body.reindex transport second same, admitted.reindex transport same⟩

/-- The same rebuilt body retains its recursively checked nested bounds. -/
theorem Body.Nested.reindex {first second : Plan dependencies} {body : Body world owner first}
    (checked : body.Nested) (same : signature first = signature second) :
    (body.reindex transport second same).Nested := by
  induction checked using Body.Nested.rec
      (motive_2 := fun rights {world} {family} {first} bounds annotation required _ =>
        ∀ second : ModePlans family, modeSignatures first = modeSignatures second →
          ∃ next : Modes world second, BoundedMode rights (bounds.reindex second) next required)
      (motive_3 := fun {world} {before} {families} {first} bounds annotation required _ =>
        ∀ {after} (second : ClausePlans after families), clauseSignatures first = clauseSignatures second →
          ∃ next : Declarations world second, Bounded (bounds.reindex second) next required)
      with
  | resume => cases second; exact .resume
  | dispose => cases second; exact .dispose
  | sequence body ih => cases second with
    | sequence first next => exact .sequence (ih (Signature.sequence.inj same).2)
  | choice first last ihFirst ihLast => cases second with
    | choice nextFirst nextLast =>
      exact .choice (ihFirst (Signature.choice.inj same).1) (ihLast (Signature.choice.inj same).2)
  | handler source admitted body ihSource ihBody => cases second with
    | handler nextRequired nextPlans nextCode =>
      obtain ⟨rfl, clausesSame, bodySame⟩ := Signature.handler.inj same
      obtain ⟨nextSource, nextChecked⟩ := ihSource nextPlans clausesSame
      simp only [Body.reindex]
      exact .handler nextSource nextChecked (ihBody bodySame)
  | cleanup body ih => cases second with
    | cleanup nextCallback nextCode => exact .cleanup (ih (Signature.cleanup.inj same).2)
  | resource body ih => cases second with
    | resource nextCode =>
      simp only [Body.reindex]
      exact .resource (fun identity fresh => ih identity fresh (congrFun (Signature.resource.inj same) identity))
  | unavailable =>
      rename_i second same
      cases second
      exact ⟨.unavailable, .unavailable⟩
  | available source nested ih =>
      rename_i second same
      cases second with
      | available nextPlans =>
        exact ⟨_, .available
          (.available (fun owner => (available_body (owner := owner) source).reindex transport
            (congrFun (ModeSignatures.available.inj same) owner)))
          (fun owner => ih owner (congrFun (ModeSignatures.available.inj same) owner))⟩
  | nil =>
      rename_i after second same
      cases second
      exact ⟨.nil, .nil⟩
  | cons ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i after second same
      cases second with
      | cons nextOrdinary nextProtected nextRest =>
        obtain ⟨actions, ordinarySame, protectedSame, tail⟩ := ClauseSignatures.cons.inj same
        obtain ⟨ordinarySource, ordinaryChecked⟩ := ihOrdinary nextOrdinary ordinarySame
        obtain ⟨protectedSource, protectedChecked⟩ := ihProtected nextProtected protectedSame
        obtain ⟨restSource, restChecked⟩ := ihRest nextRest tail
        exact ⟨.cons ordinarySource protectedSource restSource,
          .cons (actions ▸ ordinaryChecked) (actions ▸ protectedChecked) restChecked⟩

theorem BoundedMode.signature_congr {first second : ModePlans family}
    {bounds : ModeBounds first} {annotation : Modes world first}
    (admitted : BoundedMode rights bounds annotation required)
    (same : modeSignatures first = modeSignatures second) :
    ∃ next : Modes world second, BoundedMode rights (bounds.reindex second) next required := by
  cases admitted with
  | unavailable => cases second; exact ⟨.unavailable, .unavailable⟩
  | available source nested => cases second with
    | available nextPlans =>
      exact ⟨_, .available
        (.available (fun owner => (available_body (owner := owner) source).reindex transport
          (congrFun (ModeSignatures.available.inj same) owner)))
        (fun owner => (nested owner).reindex transport (congrFun (ModeSignatures.available.inj same) owner))⟩

/-- Both modes and every clause retain their exact bounds. The signature
equality also authenticates the actual clause's required continuation rights. -/
theorem Bounded.signature_congr {first : ClausePlans before families} {second : ClausePlans after families}
    {bounds : ClauseBounds first} {annotation : Declarations world first}
    (admitted : Bounded bounds annotation required)
    (same : clauseSignatures first = clauseSignatures second) :
    ∃ next : Declarations world second, Bounded (bounds.reindex second) next required := by
  induction bounds generalizing after required with
  | nil => cases admitted; cases second; exact ⟨.nil, .nil⟩
  | cons ordinaryBounds protectedBounds restBounds ih =>
    cases admitted with
    | cons ordinary protectedMode rest => cases second with
      | cons nextOrdinary nextProtected nextRest =>
        obtain ⟨actions, ordinarySame, protectedSame, tail⟩ := ClauseSignatures.cons.inj same
        obtain ⟨ordinarySource, ordinaryChecked⟩ := ordinary.signature_congr transport ordinarySame
        obtain ⟨protectedSource, protectedChecked⟩ := protectedMode.signature_congr transport protectedSame
        obtain ⟨restSource, restChecked⟩ := ih rest tail
        exact ⟨.cons ordinarySource protectedSource restSource,
          .cons (actions ▸ ordinaryChecked) (actions ▸ protectedChecked) restChecked⟩

end

namespace CongruenceExamples
open SourcePlanSignatures.Examples (plans clauses families)

def bounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) .unavailable .nil

def annotation : Declarations [] plans := .cons (.available (fun _ => .resume)) .unavailable .nil

theorem admitted : Bounded bounds annotation [] :=
  .cons (.available (.available (fun _ => .resume rfl)) (fun _ => .resume)) .unavailable .nil

/-- Actual clause syntax changes, while the structural derivation and exact
recorded bounds transfer through the established substitution signature. -/
theorem substituted_admission :
    ∃ actual : Declarations [] (substituteClauses plans 2 .unit),
      Bounded (bounds.reindex (substituteClauses plans 2 .unit)) actual [] :=
  admitted.signature_congr (nested := SourceScheduledCapabilityAnnotations.recipePolicy)
    (fun source same => SourcePlannedRecipeDeclarations.Declarations.signature_congr source same)
    (substitution_signature plans (value := .unit) trivial).symm

def first (owner : Nat) : Plan (.handler (.user 92 []) [] families (.invoke ⟨owner, .resume⟩)) :=
  .handler [] plans .invoke

def second (owner : Nat) : Plan (.handler (.user 92 []) [] families (.invoke ⟨owner, .resume⟩)) :=
  .handler [] (substituteClauses plans 2 .unit) .invoke

def body (owner : Nat) : Body [] owner (first owner) :=
  .handler bounds (.cons (.available (.resume rfl)) .unavailable .nil) .resume

theorem nested_admitted (owner : Nat) :
    Admitted ⟨true, false⟩ [] [] (body owner) [] :=
  .handler (.resume rfl) rfl rfl

theorem nested_actual_admission (owner : Nat) :
    ∃ actual : Body [] owner (second owner), Admitted ⟨true, false⟩ [] [] actual [] := by
  apply (nested_admitted owner).signature_congr (nested := SourceScheduledCapabilityAnnotations.recipePolicy)
    (fun source same => SourcePlannedRecipeDeclarations.Declarations.signature_congr source same)
  simp only [first, second, signature, substitution_signature plans (value := .unit) trivial]

end CongruenceExamples
end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ModeBounds.acceptsResume_reindex
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ClauseBounds.acceptsResume_reindex
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.signature_congr
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundedMode.signature_congr
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.signature_congr

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.CongruenceExamples.admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.CongruenceExamples.substituted_admission
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.CongruenceExamples.nested_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.CongruenceExamples.nested_actual_admission

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.reindex

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.reindex

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.reindex
