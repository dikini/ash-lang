import SourceConsumingBoundAnnotations

/-! Change only the declaration evidence in existing consuming annotations.
Clause plans, bounds, modes, permissions and operation requirements are retained.
The induction follows the existing world-weakening proofs. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

variable {source target : DeclarationPolicy}

abbrev PolicyTranslation (source target : DeclarationPolicy) :=
  ∀ {clauses families required} {plans : ClausePlans clauses families},
    source.accepts required plans → target.accepts required plans

def Body.map_policy {plan : Plan dependencies}
    (body : Body (declarations := source) world owner plan) (translate : PolicyTranslation source target) :
    Body (declarations := target) world owner plan :=
  letI := source
  match body with
  | .resume => Body.resume (declarations := target)
  | .dispose => Body.dispose (declarations := target)
  | .sequence required footprint declared rest =>
      Body.sequence (declarations := target) required footprint declared (rest.map_policy translate)
  | .choice first second => Body.choice (declarations := target) (first.map_policy translate) (second.map_policy translate)
  | .handler bounds admitted body => Body.handler (declarations := target) bounds (translate admitted) (body.map_policy translate)
  | .cleanup required footprint declared body =>
      Body.cleanup (declarations := target) required footprint declared (body.map_policy translate)
  | .resource body => Body.resource (declarations := target) (fun identity fresh => (body identity fresh).map_policy translate)

def Modes.map_policy {plans : ModePlans family}
    (modes : Modes (declarations := source) world plans) (translate : PolicyTranslation source target) :
    Modes (declarations := target) world plans :=
  letI := source
  match modes with
  | .unavailable => Modes.unavailable (declarations := target)
  | .available bodies => Modes.available (declarations := target) (fun owner => (bodies owner).map_policy translate)

def Declarations.map_policy {plans : ClausePlans clauses families}
    (declarations : Declarations (declarations := source) world plans) (translate : PolicyTranslation source target) :
    Declarations (declarations := target) world plans :=
  letI := source
  match declarations with
  | .nil => Declarations.nil (declarations := target)
  | .cons ordinary protectedMode rest =>
      Declarations.cons (declarations := target) (ordinary.map_policy translate) (protectedMode.map_policy translate)
        (rest.map_policy translate)

theorem Admitted.map_policy {body : Body (declarations := source) world owner plan}
    (checked : Admitted (declarations := source) rights resumeRequired closeRequired body required)
    (translate : PolicyTranslation source target) :
    Admitted (declarations := target) rights resumeRequired closeRequired (body.map_policy translate) required := by
  induction checked using Admitted.rec (declarations := source) with
  | resume permission => exact .resume permission
  | dispose permission => exact .dispose permission
  | sequence rest ih => exact .sequence ih
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | handler body internal coverage ih => exact .handler ih internal coverage
  | cleanup body ih => exact .cleanup ih
  | resource body ih => exact .resource ih
  | weaken body included ih => exact .weaken ih included

theorem ModeAdmitted.map_policy {modes : Modes (declarations := source) world plans}
    (checked : ModeAdmitted (declarations := source) rights resumeRequired closeRequired required modes)
    (translate : PolicyTranslation source target) :
    ModeAdmitted (declarations := target) rights resumeRequired closeRequired required (modes.map_policy translate) := by
  cases checked with
  | unavailable => exact .unavailable
  | available body => exact .available (fun owner => (body owner).map_policy translate)

/-- Recursive nested-bound admission survives the same evidence translation.
The actual bounds are unchanged, including bounds beneath resource binders. -/
theorem Body.Nested.map_policy {body : Body (declarations := source) world owner plan}
    (checked : Body.Nested (declarations := source) body) (translate : PolicyTranslation source target) :
    Body.Nested (declarations := target) (body.map_policy translate) := by
  induction checked using Body.Nested.rec (declarations := source)
    (motive_2 := fun rights {world} {_} {_} bounds annotations required _ =>
      BoundedMode (declarations := target) rights bounds (annotations.map_policy translate) required)
    (motive_3 := fun {world} {_} {_} {_} bounds annotations required _ =>
      Bounded (declarations := target) bounds (annotations.map_policy translate) required) with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence ih
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | handler declarations admitted body ihDeclarations ihBody =>
      exact .handler (declarations.map_policy translate) ihDeclarations ihBody
  | cleanup body ih => exact .cleanup ih
  | resource body ih => exact .resource ih
  | unavailable => exact .unavailable
  | available admitted nested ih => exact .available (admitted.map_policy translate) ih
  | nil => exact .nil
  | cons ordinary protectedMode rest ihOrdinary ihProtected ihRest => exact .cons ihOrdinary ihProtected ihRest

theorem BoundedMode.map_policy {bounds : ModeBounds plans}
    {annotations : Modes (declarations := source) world plans}
    (checked : BoundedMode (declarations := source) rights bounds annotations required) (translate : PolicyTranslation source target) :
    BoundedMode (declarations := target) rights bounds (annotations.map_policy translate) required := by
  cases checked with
  | unavailable => exact .unavailable
  | available admitted nested =>
      exact .available (admitted.map_policy translate) (fun owner => (nested owner).map_policy translate)

theorem Bounded.map_policy {bounds : ClauseBounds plans}
    {annotations : Declarations (declarations := source) world plans}
    (checked : Bounded (declarations := source) bounds annotations required) (translate : PolicyTranslation source target) :
    Bounded (declarations := target) bounds (annotations.map_policy translate) required := by
  induction bounds generalizing required with
  | nil => cases checked; exact .nil
  | cons ordinaryBounds protectedBounds restBounds ih => cases checked with
    | cons ordinary protectedMode rest =>
        exact .cons (ordinary.map_policy translate) (protectedMode.map_policy translate) (ih rest)

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.map_policy
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ModeAdmitted.map_policy
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.map_policy
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.BoundedMode.map_policy
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.map_policy
