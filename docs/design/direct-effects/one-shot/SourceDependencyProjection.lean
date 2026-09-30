import SourceDependencyInvocations

/-! Remove spent markers only from dependency-checking scopes. Runtime stacks,
owner phases and owner accounting are unchanged. The projection retains every
pending expression, handler, provider, callback and dormant live branch. -/
namespace Ash.OneShot.SourceDependencyProjection
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyCapture
abbrev Receiving := SourceDependencyCapture.Scope

/-- Spent markers carry runtime ownership history, but introduce no source
code, interpretation or live invocation capability. -/
def project : Receiving → Receiving
  | .nil => .nil
  | .plain dependencies rest => .plain dependencies (project rest)
  | .handler effect table families rest => .handler effect table families (project rest)
  | .cell identity rest => .cell identity (project rest)
  | .cleanup needs callback rest => .cleanup needs callback (project rest)
  | .running rest => .running (project rest)
  | .live owner captured rest => .live owner (project captured) (project rest)
  | .spent _ rest => project rest

theorem project_idempotent (scope : Receiving) : project (project scope) = project scope := by
  induction scope <;> simp_all [project]

theorem scope_append_nil (scope : Receiving) : scope.append .nil = scope := by
  induction scope <;> simp_all [SourceDependencyCapture.Scope.append]

theorem project_append (first second : Receiving) :
    project (first.append second) = (project first).append (project second) := by
  induction first <;> simp_all [SourceDependencyCapture.Scope.append, project]

theorem project_held (scope : Receiving) : (project scope).held = scope.held := by
  induction scope <;> simp_all [project, SourceDependencyCapture.Scope.held]

theorem project_normal (scope : Receiving) : (project scope).shape.normal = scope.shape.normal := by
  induction scope <;> simp_all [project, SourceDependencyCapture.Scope.shape, SourceRecursiveRoutes.Shape.normal]

theorem project_closing (scope : Receiving) : (project scope).shape.closing = scope.shape.closing := by
  induction scope <;> simp_all [project, SourceDependencyCapture.Scope.shape, SourceRecursiveRoutes.Shape.closing]

theorem project_checkClosing (scope : Receiving) :
    checkClosing outward (project scope).shape original surviving = checkClosing outward scope.shape original surviving := by
  induction scope generalizing original surviving <;>
    simp_all [project, SourceDependencyCapture.Scope.shape, checkClosing, project_normal, project_closing]

def selection : Selection → Selection
  | .builtin identity => .builtin identity
  | .handler captured tail contract modes => .handler (project captured) (project tail) contract modes

theorem project_select (scope : Receiving) :
    select effect operation (project scope) = (select effect operation scope).map selection := by
  induction scope with
  | nil => rfl
  | handler requested table families rest ih =>
      by_cases same : effect = requested
      · simp only [project, select, if_pos same]
        cases lookup operation table <;> cases lookupDependencies operation families <;> rfl
      · simp only [project, select, if_neg same, ih, Option.map_map]
        congr 1
        funext selected
        cases selected <;> rfl
  | cell identity rest ih =>
      by_cases same : effect = .cell identity
      · simp [project, select, same, selection]
      · simp only [project, select, if_neg same, ih, Option.map_map]
        congr 1
        funext selected
        cases selected <;> rfl
  | spent owner rest ih =>
      simp only [project, select, ih, Option.map_map]
      congr 1
      funext selected
      cases selected <;> rfl
  | plain dependencies rest ih | cleanup needs callback rest ih | running rest ih =>
      simp only [project, select, ih, Option.map_map]
      congr 1
      funext selected
      cases selected <;> rfl
  | live owner captured rest ihCaptured ihRest =>
      simp only [project, select, ihRest, Option.map_map]
      congr 1
      funext selected
      cases selected <;> rfl

theorem project_checkCapture (scope : Receiving) :
    checkCapture outward (project scope) effect operation = checkCapture outward scope effect operation := by
  simp only [checkCapture, project_select]
  cases select effect operation scope with
  | none => rfl
  | some selected => cases selected <;>
      simp [selection, project_held, project_checkClosing]

def ownerSelection (selected : OwnerSelection) : OwnerSelection :=
  ⟨project selected.front, project selected.captured, project selected.tail⟩

theorem project_findOwner (scope : Receiving) :
    findOwner owner (project scope) = (findOwner owner scope).map ownerSelection := by
  induction scope with
  | nil => rfl
  | live other captured rest ihCaptured ihRest =>
      by_cases same : owner = other
      · simp [project, findOwner, same, ownerSelection]
      · simp only [project, findOwner, if_neg same, ihRest, Option.map_map]
        congr 1

  | spent other rest ih =>
      simp only [project, findOwner, ih, Option.map_map]
      congr 1

  | plain dependencies rest ih | handler effect table families rest ih | cell identity rest ih
      | cleanup needs callback rest ih | running rest ih =>
      simp only [project, findOwner, ih, Option.map_map]
      congr 1


theorem project_forClosing (scope : Receiving) :
    project scope.forClosing = (project scope).forClosing := by
  induction scope <;> simp_all [project, SourceDependencyCapture.Scope.forClosing, project_append]

theorem project_resumed (selected : OwnerSelection) :
    project (selected.resumed owner) = project ((ownerSelection selected).resumed owner) := by
  simp [OwnerSelection.resumed, ownerSelection, project_append, project, project_idempotent]

theorem project_disposed (selected : OwnerSelection) :
    project (selected.disposed owner) = project ((ownerSelection selected).disposed owner) := by
  simp [OwnerSelection.disposed, ownerSelection, project_append, project, project_idempotent, project_forClosing]

/-- The result still carries the runtime spent marker; only the comparison
of resulting source scopes uses the projection. Permissions and phases are the
same on both sides. -/
theorem project_checkResume (scope : Receiving) :
    (checkResume actions phases owner (project scope)).map project =
      (checkResume actions phases owner scope).map project := by
  simp only [checkResume, project_findOwner]
  cases actions owner with
  | none => rfl
  | some rights => cases findOwner owner scope with
      | none => rfl
      | some selected =>
          simp only [Option.map_some]
          split
          · exact congrArg some (project_resumed selected).symm
          · rfl

theorem project_checkDispose (scope : Receiving) :
    (checkDispose outward actions phases owner (project scope)).map project =
      (checkDispose outward actions phases owner scope).map project := by
  simp only [checkDispose, project_findOwner]
  cases actions owner with
  | none => rfl
  | some rights => cases findOwner owner scope with
      | none => rfl
      | some selected =>
          simp only [Option.map_some, ownerSelection, project_held, project_checkClosing]
          split
          · exact congrArg some (project_disposed selected).symm
          · rfl

end Ash.OneShot.SourceDependencyProjection

#print axioms Ash.OneShot.SourceDependencyProjection.project_idempotent
#print axioms Ash.OneShot.SourceDependencyProjection.project_append
#print axioms Ash.OneShot.SourceDependencyProjection.project_held
#print axioms Ash.OneShot.SourceDependencyProjection.project_normal
#print axioms Ash.OneShot.SourceDependencyProjection.project_closing
#print axioms Ash.OneShot.SourceDependencyProjection.project_checkClosing
#print axioms Ash.OneShot.SourceDependencyProjection.project_select
#print axioms Ash.OneShot.SourceDependencyProjection.project_checkCapture
#print axioms Ash.OneShot.SourceDependencyProjection.project_findOwner
#print axioms Ash.OneShot.SourceDependencyProjection.project_forClosing
#print axioms Ash.OneShot.SourceDependencyProjection.project_resumed
#print axioms Ash.OneShot.SourceDependencyProjection.project_disposed
#print axioms Ash.OneShot.SourceDependencyProjection.project_checkResume
#print axioms Ash.OneShot.SourceDependencyProjection.project_checkDispose

#print axioms Ash.OneShot.SourceDependencyProjection.scope_append_nil
