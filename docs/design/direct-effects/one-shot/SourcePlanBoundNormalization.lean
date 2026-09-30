import SourceBoundAdmission

/-! Canonical current-plan bound spines separate annotation representation
from recorded declaration data. Expanding an absent subtree exposes its actual
syntax without inventing a bound at any handler or changing lookup results. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourceScheduledSourceInterfaces (Declared)

def Annotation.empty (world : List Nat) {dependencies : SourceDependencyAnnotations.Dependencies}
    (plan : Plan dependencies) : Annotation world plan :=
  match plan with
  | .pure | .request | .invoke => .absent
  | .sequence first second => .sequence (.empty world first) (.empty world second)
  | .choice first second => .choice (.empty world first) (.empty world second)
  | .handler _ _ body => .handler none (.empty world body)
  | .cleanup callback body => .cleanup (.empty world body) (.empty world callback)
  | .resource body => .resource (fun identity _ => .empty (world ++ [identity]) (body identity))

def Annotation.normalize {world dependencies} {plan : Plan dependencies}
    (bounds : Annotation world plan) : Annotation world plan :=
  match bounds with
  | .absent => .empty world plan
  | .sequence first second => .sequence first.normalize second.normalize
  | .choice first second => .choice first.normalize second.normalize
  | .handler recorded body => .handler recorded body.normalize
  | .cleanup body callback => .cleanup body.normalize callback.normalize
  | .resource body => .resource (fun identity fresh => (body identity fresh).normalize)

/-- Every expanded empty subtree still has no recorded handler-bound entry. -/
theorem Annotation.empty_lookup {world dependencies} (plan : Plan dependencies) (path : Path) :
    (Annotation.empty world plan).lookup path operation held = none := by
  induction path generalizing world dependencies with
  | here => cases plan <;> rfl
  | first path ih | second path ih | body path ih | callback path ih =>
      cases plan <;> first | rfl | exact ih _
  | resource identity path ih =>
      cases plan <;> first
      | rfl
      | (simp only [Annotation.empty, Annotation.lookup]
         split <;> first | exact ih _ | rfl)

/-- Normalization keeps each exact bound observation, including the distinction
between absent metadata and a present declaration with an unavailable mode. -/
theorem Annotation.normalize_lookup {world dependencies} {plan : Plan dependencies}
    (bounds : Annotation world plan) (path : Path) :
    bounds.normalize.lookup path operation held = bounds.lookup path operation held := by
  induction bounds generalizing path with
  | absent => exact Annotation.empty_lookup _ _
  | sequence first second ihFirst ihSecond | choice first second ihFirst ihSecond =>
      cases path <;> first | rfl | exact ihFirst _ | exact ihSecond _
  | handler recorded body ih => cases path <;> first | rfl | exact ih _
  | cleanup body callback ihBody ihCallback =>
      cases path <;> first | rfl | exact ihBody _ | exact ihCallback _
  | resource body ih =>
      cases path <;> first
      | rfl
      | (simp only [Annotation.normalize, Annotation.lookup]
         split <;> first | exact ih _ _ _ | rfl)

/-- Canonical empty trees are fixed points, including fresh-resource families. -/
theorem Annotation.empty_normalize {world : List Nat} {dependencies : SourceDependencyAnnotations.Dependencies}
    (plan : Plan dependencies) : (Annotation.empty world plan).normalize = Annotation.empty world plan := by
  fun_induction Annotation.empty world plan <;> simp_all only [Annotation.empty, Annotation.normalize]

/-- Rechecking may normalize again without changing canonical runtime indices. -/
theorem Annotation.normalize_idempotent {world dependencies} {plan : Plan dependencies}
    (bounds : Annotation world plan) : bounds.normalize.normalize = bounds.normalize := by
  induction bounds <;> simp_all only [Annotation.normalize, Annotation.empty_normalize]

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Missing bounds remain on the existing recipe route. Source declaration
evidence, rather than lookup equality alone, admits the expanded structure. -/
theorem Annotation.empty_admitted_signature
    {world dependencies} {checking : Signature dependencies} {plan : Plan dependencies}
    (declared : Declared world checking) (same : signature plan = checking) :
    (Annotation.empty world plan).Admitted := by
  induction declared with
  | pure => cases plan; exact .absent .pure
  | request => cases plan; exact .absent .request
  | invoke => cases plan; exact .absent .invoke
  | sequence first second ihFirst ihSecond => cases plan with
    | sequence firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
      exact .sequence (ihFirst firstSame) (ihSecond secondSame)
  | choice first second ihFirst ihSecond => cases plan with
    | choice firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.choice.inj same
      exact .choice (ihFirst firstSame) (ihSecond secondSame)
  | handler declarations body ih => cases plan with
    | handler required plans code =>
      obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
      exact .inherited (declarations.signature_congr declarationsSame.symm) (ih bodySame)
  | cleanup callback body ihCallback ihBody => cases plan with
    | cleanup callbackPlan bodyPlan =>
      obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
      exact .cleanup (ihBody bodySame) (ihCallback callbackSame)
  | resource body ih => cases plan with
    | resource plans =>
      exact .resource (fun identity fresh => ih identity fresh (congrFun (Signature.resource.inj same) identity))

theorem Annotation.Admitted.normalize {world dependencies} {plan : Plan dependencies}
    {bounds : Annotation world plan} (admitted : bounds.Admitted) : bounds.normalize.Admitted := by
  induction admitted with
  | absent source => exact Annotation.empty_admitted_signature source rfl
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | inherited declarations body ih => exact .inherited declarations ih
  | bounded source checked body ih => exact .bounded source checked ih
  | cleanup body callback ihBody ihCallback => exact .cleanup ihBody ihCallback
  | resource body ih => exact .resource ih

end Ash.OneShot.SourcePlanBounds

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.empty_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.normalize_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.empty_admitted_signature
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.normalize

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.empty_normalize
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.normalize_idempotent
