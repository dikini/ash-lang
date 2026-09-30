import SourceScheduledBoundRetention

/-! Immutable bounds for the current plan, independent of its receiving
continuation. This is a projection of source annotations, not a computation
grammar or an admission judgment. Captured segments retain their own source
annotations; they are not part of this current-plan projection. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (ClauseBounds Bounds)
open SourceScheduledCapabilityAnnotations (Code BoundEdge)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

inductive Annotation : List Nat → {dependencies : SourceDependencyAnnotations.Dependencies} →
    Plan dependencies → Type where
  | absent : Annotation world plan
  | sequence : Annotation world first → Annotation world second → Annotation world (.sequence first second)
  | choice : Annotation world first → Annotation world second → Annotation world (.choice first second)
  | handler {plans : ClausePlans clauses families} (bounds : Option (ClauseBounds plans))
      (body : Annotation world code) :
      Annotation world (.handler (effect := effect) (table := table) required plans code)
  | cleanup : Annotation world body → Annotation world callback → Annotation world (.cleanup callback body)
  | resource : (∀ identity, identity ∉ world → Annotation (world ++ [identity]) (body identity)) →
      Annotation world (.resource body)

def ofCode [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) : Annotation world plan :=
  match annotation with
  | .operations _ _ _ | .selected _ _ _ | .resume _ _ _ _ | .dispose _ _ _ _ => .absent
  | .sequence first second => .sequence (ofCode first) (ofCode second)
  | .choice first second => .choice (ofCode first) (ofCode second)
  | .handler _ body bounds => .handler bounds (ofCode body)
  | .cleanup body callback => .cleanup (ofCode body) (ofCode callback)
  | .resource body => .resource (fun identity fresh => ofCode (body identity fresh))

/-- These paths select current syntax only. Saved/caller continuation paths
belong to the existing retained annotation, not to this projection. -/
inductive Path where
  | here
  | first (rest : Path)
  | second (rest : Path)
  | body (rest : Path)
  | callback (rest : Path)
  | resource (identity : Nat) (rest : Path)

def Path.edges : Path → List BoundEdge
  | .here => []
  | .first rest => .first :: rest.edges
  | .second rest => .second :: rest.edges
  | .body rest => .body :: rest.edges
  | .callback rest => .callback :: rest.edges
  | .resource identity rest => .resource identity :: rest.edges

def Annotation.lookup {world dependencies} {plan : Plan dependencies}
    (annotation : Annotation world plan) (path : Path) (operation : Nat) (held : Bool) : Option (Option Bounds) :=
  match annotation, path with
  | .handler bounds _, .here => bounds.map (fun recorded => recorded.lookup operation held)
  | .sequence first _, .first rest | .choice first _, .first rest => first.lookup rest operation held
  | .sequence _ second, .second rest | .choice _ second, .second rest => second.lookup rest operation held
  | .handler _ body, .body rest | .cleanup body _, .body rest => body.lookup rest operation held
  | .cleanup _ callback, .callback rest => callback.lookup rest operation held
  | .resource body, .resource identity rest =>
      if fresh : identity ∉ world then (body identity fresh).lookup rest operation held else none
  | _, _ => none

/-- Projection preserves every source-code bound observation exactly,
including absent metadata and ordinary/protected mode differences. -/
theorem ofCode_lookup [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies} {forest : Forest hints}
    (annotation : Code world plan forest) (path : Path) :
    (ofCode annotation).lookup path operation held = annotation.boundAt path.edges operation held := by
  induction path generalizing world dependencies scope with
  | here => cases annotation <;> rfl
  | first path ih | second path ih | body path ih | callback path ih =>
      cases annotation <;> first
        | rfl
        | exact ih _
  | resource identity path ih =>
      cases annotation <;> first
        | rfl
        | (dsimp only [ofCode, Annotation.lookup, Path.edges, Code.boundAt]
           split <;> first | exact ih _ | rfl)

def Annotation.first {first : Plan firstDependencies} {second : Plan secondDependencies} :
    Annotation world (.sequence first second) → Annotation world first
  | .absent => .absent
  | .sequence first _ => first

def Annotation.second {first : Plan firstDependencies} {second : Plan secondDependencies} :
    Annotation world (.sequence first second) → Annotation world second
  | .absent => .absent
  | .sequence _ second => second

def Annotation.handlerBounds {plans : ClausePlans clauses families} {code : Plan dependencies} :
    Annotation world (.handler (effect := effect) (table := table) required plans code) → Option (ClauseBounds plans)
  | .absent => none
  | .handler bounds _ => bounds

theorem ofCode_handlerBounds [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {hints : Hints scope} {forest : Forest hints} {plans : ClausePlans clauses families} {body : Plan dependencies}
    (annotation : Code world (.handler (effect := effect) (table := table) required plans body) forest) :
    (ofCode annotation).handlerBounds = annotation.handlerBounds := by
  cases annotation <;> rfl

def Annotation.rewrite (change : SourcePlanRewriting.ClauseMap)
    {world dependencies} {plan : Plan dependencies} (annotation : Annotation world plan) :
    Annotation world (change.plan plan) :=
  match annotation with
  | .absent => .absent
  | .sequence first second => .sequence (first.rewrite change) (second.rewrite change)
  | .choice first second => .choice (first.rewrite change) (second.rewrite change)
  | .handler (plans := plans) bounds body =>
      .handler (bounds.map (fun recorded => recorded.reindex (change.apply plans).2)) (body.rewrite change)
  | .cleanup body callback => .cleanup (body.rewrite change) (callback.rewrite change)
  | .resource body => .resource (fun identity fresh => (body identity fresh).rewrite change)

/-- Queued code keeps its bound observations when its literal clause
witnesses change. Closed substitution is the existing ClauseMap instance. -/
theorem Annotation.lookup_rewrite (change : SourcePlanRewriting.ClauseMap)
    {world dependencies} {plan : Plan dependencies} (annotation : Annotation world plan) (path : Path) :
    (annotation.rewrite change).lookup path operation held = annotation.lookup path operation held := by
  induction path generalizing world dependencies with
  | here =>
      cases annotation <;> first
        | rfl
        | (dsimp only [Annotation.rewrite, Annotation.lookup]
           simp only [Option.map_map, Function.comp_def, ClauseBounds.lookup_reindex])
  | first path ih | second path ih | body path ih | callback path ih =>
      cases annotation <;> first | rfl | exact ih _
  | resource identity path ih =>
      cases annotation <;> first
        | rfl
        | (dsimp only [Annotation.rewrite, Annotation.lookup]
           split <;> first | exact ih _ | rfl)

theorem ofCode_rewrite_lookup {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (change : SourcePlanRewriting.ClauseMap) (path : Path) :
    (ofCode (annotation.rewrite change)).lookup path operation held =
      ((ofCode annotation).rewrite change).lookup path operation held := by
  rw [ofCode_lookup, Code.boundAt_rewrite, Annotation.lookup_rewrite, ofCode_lookup]

theorem Annotation.first_lookup {first : Plan firstDependencies} {second : Plan secondDependencies}
    (annotation : Annotation world (.sequence first second)) :
    annotation.first.lookup path operation held = annotation.lookup (.first path) operation held := by
  cases annotation <;> rfl

theorem Annotation.second_lookup {first : Plan firstDependencies} {second : Plan secondDependencies}
    (annotation : Annotation world (.sequence first second)) :
    annotation.second.lookup path operation held = annotation.lookup (.second path) operation held := by
  cases annotation <;> rfl

end Ash.OneShot.SourcePlanBounds

#print axioms Ash.OneShot.SourcePlanBounds.ofCode_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.first_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.second_lookup
#print axioms Ash.OneShot.SourcePlanBounds.ofCode_handlerBounds
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.lookup_rewrite
#print axioms Ash.OneShot.SourcePlanBounds.ofCode_rewrite_lookup
