import SourceScheduledCleanupInterfaces
import SourceScheduledSourceRechecking

/-! Generate annotations for arbitrary source after cleanup insertion. Extra
obligations are structural trees of primitive operation and closing-route checks;
no target Local, Pending or Valid judgment can be placed in an obligation.
The same induction now derives structural source rechecking from those primitive
conditions, so receiver clients can reuse the exact source-directed compiler. -/
namespace Ash.OneShot.SourceScheduledCleanupGeneration
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCleanupInsertion (Insertion Split)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourceScheduledSourceRechecking (Expression RetainedChange)

/-- Only new operation requirements and closing routes are rechecked.
Generative resources retain their existing fresh-name quantification. -/
inductive Checks where
  | done
  | operations : Scope → List Requirement → Checks
  | closing : Scope → Checks
  | both : Checks → Checks → Checks
  | resource (world : List Nat) (body : ∀ identity, identity ∉ world → Checks)

def Checks.Holds (outward : List Instance) : Checks → Prop
  | .done => True
  | .operations scope required => checkRequirements scope required = true
  | .closing scope => SourceDependencyCapture.checkClosing outward scope.shape [] [] = true
  | .both first second => first.Holds outward ∧ second.Holds outward
  | .resource _ body => ∀ identity fresh, (body identity fresh).Holds outward

def Checks.when (condition : Bool) (body : condition = true → Checks) : Checks :=
  if accepted : condition = true then body accepted else .done

theorem Checks.when_holds (body : condition = true → Checks) :
    (Checks.when condition body).Holds outward ↔ ∀ accepted, (body accepted).Holds outward := by
  unfold Checks.when
  split
  · rename_i accepted
    exact ⟨fun ready _ => ready, fun ready => ready accepted⟩
  · rename_i rejected
    exact ⟨fun _ accepted => False.elim (rejected accepted), fun _ => True.intro⟩

section
variable [declarations : DeclarationPolicy]

structure CodeResult {world dependencies first second} {beforeHints : Hints first} {afterHints : Hints second}
    {plan : Plan dependencies} {before : Forest beforeHints} (source : Code world plan before) (after : Forest afterHints) where
  annotation : Code world plan after
  checks : Checks
  sound : ∀ outward actions phases, source.Valid outward actions phases → checks.Holds outward →
    annotation.Valid outward actions phases
  rechecking : ∀ outward actions phases, source.Valid outward actions phases → checks.Holds outward →
    Expression outward actions phases source after

structure RetainedResult {world first second outside nextOutside}
    {beforeHints : Hints first} {afterHints : Hints second}
    {outsideHints : Hints outside} {nextOutsideHints : Hints nextOutside}
    {before : Forest beforeHints} {receiver : Forest outsideHints}
    (source : Retained world before receiver) (after : Forest afterHints) (next : Forest nextOutsideHints) where
  annotation : Retained world after next
  checks : Checks
  sound : ∀ outward actions phases, source.Valid outward actions phases → checks.Holds outward →
    annotation.Valid outward actions phases
  rechecking : ∀ outward actions phases, source.Valid outward actions phases → checks.Holds outward →
    RetainedChange outward actions phases source after next

def RetainedResult.unchanged (source : Retained world forest outside) : RetainedResult source forest outside :=
  ⟨source, .done, fun _ _ _ ready _ => ready, fun _ _ _ _ _ => .same⟩

end

theorem interfaces_receiver {hints : Hints scope} {forest : Forest hints}
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest)
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion needs callback before after) :
    interfaces.check first = interfaces.check second := by
  induction interfaces generalizing first second with
  | nil => rfl
  | plain rest required footprint declared next ih | handler rest next ih =>
      dsimp only [SourceScheduledRetainedInterfaces.Interfaces.check]
      exact congr (congrArg Bool.and (changed.prefix rest).requirements) (ih changed)
  | cell next ih | running next ih | spent next ih => exact ih changed
  | cleanup rest required footprint declared next ih =>
      dsimp only [SourceScheduledRetainedInterfaces.Interfaces.check]
      exact congr (congrArg Bool.and (Insertion.running (changed.prefix rest)).requirements) (ih changed)
  | live rest saved next ihSaved ihRest =>
      dsimp only [SourceScheduledRetainedInterfaces.Interfaces.check]
      exact congr (congrArg Bool.and (ihSaved (changed.prefix rest))) (ihRest changed)

/-- Operation-only retained annotations are generated structurally. The new
callback contributes its registration check; every old requirement is reused. -/
theorem interfaces_generate {callback : Plan callbackDependencies}
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints)
    (changed : Insertion needs callback before after)
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world before) :
    ∃ next : SourceScheduledRetainedInterfaces.Interfaces world after, ∃ checks : Checks,
      ∀ outward, interfaces.check outsideScope = true → checks.Holds outward → next.check outsideScope = true := by
  induction changed with
  | here =>
      exact ⟨.cleanup _ required footprint declared interfaces,
        .operations (.running (Scope.append _ outsideScope)) required,
        fun _ ready supplied => Bool.and_eq_true_iff.mpr ⟨supplied, ready⟩⟩
  | plain changed ih => cases interfaces with
    | plain rest oldRequired oldFootprint oldDeclared next =>
      obtain ⟨next, checks, sound⟩ := ih next
      refine ⟨.plain _ oldRequired oldFootprint oldDeclared next, checks, ?_⟩
      intro outward ready supplied
      obtain ⟨code, tail⟩ := Bool.and_eq_true_iff.mp ready
      refine Bool.and_eq_true_iff.mpr ⟨?_, sound outward tail supplied⟩
      exact (changed.suffix outside).requirements.symm.trans code
  | handler changed ih => cases interfaces with
    | handler rest next =>
      obtain ⟨next, checks, sound⟩ := ih next
      refine ⟨.handler _ next, checks, ?_⟩
      intro outward ready supplied
      obtain ⟨code, tail⟩ := Bool.and_eq_true_iff.mp ready
      refine Bool.and_eq_true_iff.mpr ⟨?_, sound outward tail supplied⟩
      exact (changed.suffix outside).requirements.symm.trans code
  | cell changed ih => cases interfaces with | cell next =>
      obtain ⟨next, checks, sound⟩ := ih next
      exact ⟨.cell next, checks, sound⟩
  | cleanup changed ih => cases interfaces with
    | cleanup rest oldRequired oldFootprint oldDeclared next =>
      obtain ⟨next, checks, sound⟩ := ih next
      refine ⟨.cleanup _ oldRequired oldFootprint oldDeclared next, checks, ?_⟩
      intro outward ready supplied
      obtain ⟨code, tail⟩ := Bool.and_eq_true_iff.mp ready
      refine Bool.and_eq_true_iff.mpr ⟨?_, sound outward tail supplied⟩
      exact (Insertion.running (changed.suffix outside)).requirements.symm.trans code
  | running changed ih => cases interfaces with | running next =>
      obtain ⟨next, checks, sound⟩ := ih next
      exact ⟨.running next, checks, sound⟩
  | live changed ih => cases interfaces with
    | live rest saved next =>
      obtain ⟨next, checks, sound⟩ := ih next
      refine ⟨.live _ saved next, checks, ?_⟩
      intro outward ready supplied
      obtain ⟨inside, tail⟩ := Bool.and_eq_true_iff.mp ready
      refine Bool.and_eq_true_iff.mpr ⟨?_, sound outward tail supplied⟩
      exact (interfaces_receiver saved (changed.suffix outside)).symm.trans inside
  | spent changed ih => cases interfaces with | spent next =>
      obtain ⟨next, checks, sound⟩ := ih next
      exact ⟨.spent next, checks, sound⟩

private theorem split_bounds {savedHints : Hints savedScope} {nextSavedHints : Hints nextSavedScope}
    {saved : Forest savedHints} {nextSaved : Forest nextSavedHints}
    (pieces : Split needs callback saved waiting nextSaved nextWaiting)
    (bounded : SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners savedScope) savedScope) :
    SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners nextSavedScope) nextSavedScope := by
  cases pieces with
  | inside inserted =>
      rw [← inserted.owners]
      exact SourceScheduledCleanupInterfaces.Insertion.pending_within inserted bounded
  | outside inserted => exact bounded

private theorem split_guard {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {savedHints : Hints savedScope} {nextSavedHints : Hints nextSavedScope}
    {saved : Forest savedHints} {nextSaved : Forest nextSavedHints}
    (oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
    (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting)
    (pieces : Split needs callback saved waiting nextSaved nextWaiting)
    (guarded : SourceDependencyCapture.checkCapture outward first effect operation = true)
    (closing : contract.dispose = true → SourceDependencyCapture.checkClosing outward nextSavedScope.shape [] [] = true) :
    SourceDependencyCapture.checkCapture outward second effect operation = true := by
  have held : savedScope.held = nextSavedScope.held := by
    cases pieces with
    | inside inserted => exact SourceScheduledCleanupInterfaces.Insertion.held inserted
    | outside inserted => rfl
  apply SourceDependencyCapture.check_capture_iff.mpr
  cases SourceDependencyCapture.check_capture_iff.mp guarded with
  | builtin found => cases Option.some.inj (oldCut.erase.lookup.symm.trans found)
  | handler found permission row body oldClosing =>
      cases Option.some.inj (oldCut.erase.lookup.symm.trans found)
      exact .handler nextCut.erase.lookup (held ▸ permission) (held ▸ row) (held ▸ body)
        (fun disposes => SourceDependencyCapture.check_closing_iff.mp (closing disposes))

private theorem split_caller (pieces : Split needs callback front tail nextFront nextTail) :
    Split needs callback front (.spent (owner := owner) tail) nextFront (.spent (owner := owner) nextTail) := by
  cases pieces with
  | inside inserted => exact .inside inserted
  | outside inserted => exact .outside (.spent inserted)

private def scopeOf {hints : Hints scope} (_ : Forest hints) : Scope := scope

section
variable [declarations : DeclarationPolicy]
variable {callback : Plan callbackDependencies} (footprint : RequestFootprint callback required)

private def retainedForest {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (_ : Retained world forest outside) : Forest hints := forest

private def retainedOutside {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (_ : Retained world forest outside) : Forest outsideHints := outside

private def install {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (declared : Declared world (signature callback)) (source : Retained world forest outside) :
    RetainedResult source (.cleanup (needs := needs) callback forest) outside :=
  ⟨.cleanup (.operations required footprint declared) source,
    .operations (.running (scope.append outsideScope)) required,
    fun _ _ _ ready supplied => ⟨supplied, ready⟩,
    fun _ _ _ _ supplied => .installCleanup required footprint declared supplied⟩

/-- Mutual source induction generates every expression and retained-frame case.
The returned checks contain only additional primitive obligations and never
continuation permissions, phases, source admission or target validity predicates.
Both target validity and structural rechecking are produced by this induction;
existence alone still does not establish success of a chosen check tree. -/
theorem generate_all (footprint : RequestFootprint callback required) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (source : Code world plan forest), Declared world (signature callback) →
      ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
        Insertion needs callback forest next → Nonempty (CodeResult source next)) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (source : Retained world forest outside),
      Declared world (signature callback) → ∀ {nextScope nextOutsideScope}
      {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutsideScope}
      (next : Forest nextHints) (nextOutside : Forest nextOutsideHints),
        Split needs callback forest outside next nextOutside → Nonempty (RetainedResult source next nextOutside)) := by
  classical
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest source
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source =>
           Declared world (signature callback) → ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
             Insertion needs callback forest next → Nonempty (CodeResult source next))
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source =>
           Declared world (signature callback) → ∀ {nextScope nextOutsideScope}
             {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutsideScope}
             (next : Forest nextHints) (nextOutside : Forest nextOutsideHints),
             Split needs callback forest outside next nextOutside → Nonempty (RetainedResult source next nextOutside))
         (t := source))
    | (intro world scope outsideScope hints outsideHints forest outside source
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest source =>
           Declared world (signature callback) → ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
             Insertion needs callback forest next → Nonempty (CodeResult source next))
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source =>
           Declared world (signature callback) → ∀ {nextScope nextOutsideScope}
             {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutsideScope}
             (next : Forest nextHints) (nextOutside : Forest nextOutsideHints),
             Split needs callback forest outside next nextOutside → Nonempty (RetainedResult source next nextOutside))
         (t := source))
  all_goals intros
  all_goals first
    | (rename_i oldRequired oldFootprint oldDeclared declared nextScope nextHints next changed
       exact ⟨.operations oldRequired oldFootprint oldDeclared, .done,
         (fun _ _ _ ready _ => changed.requirements.symm.trans ready),
         fun _ _ _ ready _ => .operations (changed.requirements.symm.trans ready)⟩)
    | (rename_i cut bounded closing ih declared nextScope nextHints next changed
       obtain ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩ := changed.cut cut
       let generated := fun disposes => Classical.choice (ih disposes declared _ _ pieces.forClosing)
       refine ⟨.selected nextCut (fun disposes => split_bounds pieces (bounded disposes))
         (fun disposes => (generated disposes).annotation),
         Checks.when _ (fun disposes => .both (.closing (scopeOf nextSaved)) (generated disposes).checks), ?_, ?_⟩
       · intro outward actions phases ready checked
         have conditions := (Checks.when_holds _).mp checked
         exact ⟨split_guard cut nextCut pieces ready.1 (fun disposes => (conditions disposes).1),
           fun disposes => (generated disposes).sound outward actions phases (ready.2 disposes) (conditions disposes).2⟩
       · intro outward actions phases ready checked
         have conditions := (Checks.when_holds _).mp checked
         exact .selected nextCut
           (split_guard cut nextCut pieces ready.1 (fun disposes => (conditions disposes).1))
           (fun disposes => split_bounds pieces (bounded disposes))
           (fun disposes => (generated disposes).rechecking outward actions phases
             (ready.2 disposes) (conditions disposes).2))
    | (rename_i cut inside before after ihInside ihBefore ihAfter declared nextScope nextHints next changed
       obtain ⟨_, _, _, _, front, tail, nextCut, pieces⟩ := changed.owner_cut cut
       obtain ⟨insideNext⟩ := ihInside declared _ _ (.outside pieces.spent_append)
       obtain ⟨beforeNext⟩ := ihBefore declared _ _ (split_caller pieces)
       have afterExists : Nonempty (RetainedResult after tail .nil) := by
         cases pieces with
         | inside inserted => exact ⟨RetainedResult.unchanged after⟩
         | outside inserted => exact ihAfter declared _ _ (.inside inserted)
       obtain ⟨afterNext⟩ := afterExists
       refine ⟨.resume nextCut insideNext.annotation beforeNext.annotation afterNext.annotation,
         .both insideNext.checks (.both beforeNext.checks afterNext.checks), ?_, ?_⟩
       · intro outward actions phases ready checked
         exact ⟨ready.1, ready.2.1,
           insideNext.sound _ _ _ ready.2.2.1 checked.1,
           beforeNext.sound _ _ _ ready.2.2.2.1 checked.2.1,
           afterNext.sound _ _ _ ready.2.2.2.2 checked.2.2⟩
       · intro outward actions phases ready checked
         exact .resume nextCut
           (insideNext.rechecking _ _ _ ready.2.2.1 checked.1)
           (beforeNext.rechecking _ _ _ ready.2.2.2.1 checked.2.1)
           (afterNext.rechecking _ _ _ ready.2.2.2.2 checked.2.2))
    | (rename_i cut closing before after ihClosing ihBefore ihAfter declared nextScope nextHints next changed
       obtain ⟨_, _, _, _, front, tail, nextCut, pieces⟩ := changed.owner_cut cut
       obtain ⟨closingNext⟩ := ihClosing declared _ _ (.outside (.running pieces.spent_append))
       obtain ⟨beforeNext⟩ := ihBefore declared _ _ (split_caller pieces)
       have afterExists : Nonempty (RetainedResult after tail .nil) := by
         cases pieces with
         | inside inserted => exact ⟨RetainedResult.unchanged after⟩
         | outside inserted => exact ihAfter declared _ _ (.inside inserted)
       obtain ⟨afterNext⟩ := afterExists
       refine ⟨.dispose nextCut closingNext.annotation beforeNext.annotation afterNext.annotation,
         .both closingNext.checks (.both beforeNext.checks afterNext.checks), ?_, ?_⟩
       · intro outward actions phases ready checked
         exact ⟨ready.1, ready.2.1, ready.2.2.1, ready.2.2.2.1,
           closingNext.sound _ _ _ ready.2.2.2.2.1 checked.1,
           beforeNext.sound _ _ _ ready.2.2.2.2.2.1 checked.2.1,
           afterNext.sound _ _ _ ready.2.2.2.2.2.2 checked.2.2⟩
       · intro outward actions phases ready checked
         exact .dispose nextCut
           (closingNext.rechecking _ _ _ ready.2.2.2.2.1 checked.1)
           (beforeNext.rechecking _ _ _ ready.2.2.2.2.2.1 checked.2.1)
           (afterNext.rechecking _ _ _ ready.2.2.2.2.2.2 checked.2.2))
    | (rename_i first second ihFirst ihSecond declared nextScope nextHints next changed
       obtain ⟨firstNext⟩ := ihFirst declared _ (.plain changed)
       obtain ⟨secondNext⟩ := ihSecond declared _ changed
       exact ⟨.sequence firstNext.annotation secondNext.annotation, .both firstNext.checks secondNext.checks,
         (fun _ _ _ ready checked => ⟨firstNext.sound _ _ _ ready.1 checked.1, secondNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .sequence (firstNext.rechecking _ _ _ ready.1 checked.1)
               (secondNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i first second ihFirst ihSecond declared nextScope nextHints next changed
       obtain ⟨firstNext⟩ := ihFirst declared _ changed
       obtain ⟨secondNext⟩ := ihSecond declared _ changed
       exact ⟨.choice firstNext.annotation secondNext.annotation, .both firstNext.checks secondNext.checks,
         (fun _ _ _ ready checked => ⟨firstNext.sound _ _ _ ready.1 checked.1, secondNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .choice (firstNext.rechecking _ _ _ ready.1 checked.1)
               (secondNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i source body bounds ih declared nextScope nextHints next changed
       obtain ⟨bodyNext⟩ := ih declared _ (.handler changed)
       exact ⟨.handler source bodyNext.annotation bounds, bodyNext.checks,
         (fun _ _ _ ready checked => ⟨changed.requirements.symm.trans ready.1, bodyNext.sound _ _ _ ready.2 checked⟩),
         fun _ _ _ ready checked => .handler (changed.requirements.symm.trans ready.1)
           (bodyNext.rechecking _ _ _ ready.2 checked)⟩)
    | (rename_i body completion ihBody ihCompletion declared nextScope nextHints next changed
       obtain ⟨bodyNext⟩ := ihBody declared _ (.cleanup changed)
       obtain ⟨completionNext⟩ := ihCompletion declared _ (.running changed)
       exact ⟨.cleanup bodyNext.annotation completionNext.annotation, .both bodyNext.checks completionNext.checks,
         (fun _ _ _ ready checked => ⟨bodyNext.sound _ _ _ ready.1 checked.1, completionNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .cleanup (bodyNext.rechecking _ _ _ ready.1 checked.1)
               (completionNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i body ih declared nextScope nextHints next changed
       let generated := fun identity fresh => Classical.choice
         (ih identity fresh (declared.world_weaken (List.subset_append_left _ _)) _ (.cell changed))
       exact ⟨.resource (fun identity fresh => (generated identity fresh).annotation),
         .resource _ (fun identity fresh => (generated identity fresh).checks),
         (fun _ _ _ ready checked identity fresh => (generated identity fresh).sound _ _ _ (ready identity fresh) (checked identity fresh)),
         fun _ _ _ ready checked => .resource (fun identity fresh =>
           (generated identity fresh).rechecking _ _ _ (ready identity fresh) (checked identity fresh))⟩)
    | (rename_i originalOutside interfaces declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | inside inserted =>
           obtain ⟨nextInterface, checks, sound⟩ := interfaces_generate footprint declared originalOutside inserted interfaces
           exact ⟨.operations nextInterface, checks, (fun outward _ _ ready checked => sound outward ready checked),
             fun outward _ _ ready checked => .operations nextInterface (sound outward ready checked)⟩
       | outside inserted =>
           exact ⟨.operations interfaces, .done, (fun _ _ _ ready _ => (interfaces_receiver interfaces inserted).symm.trans ready),
             fun _ _ _ ready _ => .operations interfaces ((interfaces_receiver interfaces inserted).symm.trans ready)⟩)
    | (rename_i code tail ihCode ihTail declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨codeNext⟩ := ihCode declared _ (inserted.prefix _)
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.outside inserted)
           exact ⟨.plain codeNext.annotation tailNext.annotation, .both codeNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨codeNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .plain (codeNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.plain code tail)⟩
         | plain inserted =>
           obtain ⟨codeNext⟩ := ihCode declared _ (inserted.suffix _)
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.inside inserted)
           exact ⟨.plain codeNext.annotation tailNext.annotation, .both codeNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨codeNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .plain (codeNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i tail ih declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.outside inserted)
           exact ⟨.cell tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .cell (tailNext.rechecking _ _ _ ready checked)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.cell tail)⟩
         | cell inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.inside inserted)
           exact ⟨.cell tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .cell (tailNext.rechecking _ _ _ ready checked)⟩)
    | (rename_i completion tail ihCompletion ihTail declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨completionNext⟩ := ihCompletion declared _ (.running (inserted.prefix _))
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.outside inserted)
           exact ⟨.cleanup completionNext.annotation tailNext.annotation, .both completionNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨completionNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .cleanup (completionNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.cleanup completion tail)⟩
         | cleanup inserted =>
           obtain ⟨completionNext⟩ := ihCompletion declared _ (.running (inserted.suffix _))
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.inside inserted)
           exact ⟨.cleanup completionNext.annotation tailNext.annotation, .both completionNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨completionNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .cleanup (completionNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i tail ih declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.outside inserted)
           exact ⟨.running tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .running (tailNext.rechecking _ _ _ ready checked)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.running tail)⟩
         | running inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.inside inserted)
           exact ⟨.running tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .running (tailNext.rechecking _ _ _ ready checked)⟩)
    | (rename_i saved tail ihSaved ihTail declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨savedNext⟩ := ihSaved declared _ _ (.outside (inserted.prefix _))
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.outside inserted)
           exact ⟨.live savedNext.annotation tailNext.annotation, .both savedNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨savedNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .live (savedNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.live saved tail)⟩
         | live inserted =>
           obtain ⟨savedNext⟩ := ihSaved declared _ _ (.outside (inserted.suffix _))
           obtain ⟨tailNext⟩ := ihTail declared _ _ (.inside inserted)
           exact ⟨.live savedNext.annotation tailNext.annotation, .both savedNext.checks tailNext.checks,
             (fun _ _ _ ready checked => ⟨savedNext.sound _ _ _ ready.1 checked.1, tailNext.sound _ _ _ ready.2 checked.2⟩),
             fun _ _ _ ready checked => .live (savedNext.rechecking _ _ _ ready.1 checked.1)
               (tailNext.rechecking _ _ _ ready.2 checked.2)⟩)
    | (rename_i tail ih declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.outside inserted)
           exact ⟨.spent tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .spent (tailNext.rechecking _ _ _ ready checked)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.spent tail)⟩
         | spent inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.inside inserted)
           exact ⟨.spent tailNext.annotation, tailNext.checks, (fun _ _ _ ready checked => tailNext.sound _ _ _ ready checked),
             fun _ _ _ ready checked => .spent (tailNext.rechecking _ _ _ ready checked)⟩)
    | (rename_i tail ih declared nextScope nextOutside nextHints nextOutsideHints next receiver changed
       cases changed with
       | outside inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.outside inserted)
           exact ⟨.handler tailNext.annotation, tailNext.checks,
             (fun _ _ _ ready checked => ⟨(inserted.prefix (retainedForest tail)).requirements.symm.trans ready.1, tailNext.sound _ _ _ ready.2 checked⟩),
             fun _ _ _ ready checked => .handler ((inserted.prefix (retainedForest tail)).requirements.symm.trans ready.1)
               (tailNext.rechecking _ _ _ ready.2 checked)⟩
       | inside inserted => cases inserted with
         | here => exact ⟨install footprint declared (.handler tail)⟩
         | handler inserted =>
           obtain ⟨tailNext⟩ := ih declared _ _ (.inside inserted)
           exact ⟨.handler tailNext.annotation, tailNext.checks,
             (fun _ _ _ ready checked => ⟨(inserted.suffix (retainedOutside tail)).requirements.symm.trans ready.1, tailNext.sound _ _ _ ready.2 checked⟩),
             fun _ _ _ ready checked => .handler ((inserted.suffix (retainedOutside tail)).requirements.symm.trans ready.1)
               (tailNext.rechecking _ _ _ ready.2 checked)⟩)

/-- Public expression entry point. The generator derives the annotation and
its primitive check tree without an adaptation or target-validity premise. -/
theorem code_generate (footprint : RequestFootprint callback required) {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (source : Code world plan forest) (declared : Declared world (signature callback))
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (changed : Insertion needs callback forest next) : Nonempty (CodeResult source next) :=
  (generate_all footprint).1 _ _ _ source declared _ changed

theorem retained_generate (footprint : RequestFootprint callback required) {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (source : Retained world forest outside)
    (declared : Declared world (signature callback))
    {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutsideScope}
    {next : Forest nextHints} {nextOutside : Forest nextOutsideHints}
    (changed : Split needs callback forest outside next nextOutside) : Nonempty (RetainedResult source next nextOutside) :=
  (generate_all footprint).2 _ _ _ source declared _ _ changed

end

section
variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Existing compilation connects generated annotations to scheduling. The
additional premise checks only the explicitly generated primitive obligations. -/
theorem CodeResult.scheduled {hints : Hints scope} {forest : Forest hints}
    {plan : Plan dependencies} {source : Code world plan forest}
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    (generated : CodeResult source next) (ready : source.Valid outward actions phases)
    (checked : generated.checks.Holds outward) :
    SourceScheduledChecks.Local outward actions phases world plan next :=
  generated.annotation.compile_with laws (generated.sound outward actions phases ready checked)

theorem RetainedResult.scheduled {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {source : Retained world forest outside}
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    (generated : RetainedResult source next nextOutside) (ready : source.Valid outward actions phases)
    (checked : generated.checks.Holds outward) :
    SourceScheduledChecks.Pending outward actions phases world next nextOutside :=
  generated.annotation.compile_with laws (generated.sound outward actions phases ready checked)

end

namespace Examples
open SourceCleanupClosingInsertion.Examples

/-- Every sound result rejects the earlier removed-handler counterexample.
The requirement tree cannot turn its normal callback availability into a valid
disposing request, regardless of which annotation the generator constructs. -/
theorem removed_handler_checks_rejected
    (generated : CodeResult originalRequest
      (.cleanup (needs := [callbackEffect])
        (.request (effect := callbackEffect) (operation := 0)) removedForest)) :
    ¬ generated.checks.Holds [] := by
  intro checked
  have ready := generated.sound [] (fun _ => none) OwnerPhaseTransitions.empty original_pieces_valid.1 checked
  exact request_annotation_rejected (SourceScheduledCapabilityAnnotations.recipeLaws []) generated.annotation ready

def cellHints : Hints (.cell 4 .nil) := .cell .nil
def cellForest : Forest cellHints := .cell .nil
def ownerHints : Hints (.live 37 .nil (.cell 4 .nil)) := .live .nil (.cell .nil)
def ownerForest : Forest ownerHints := .live .nil cellForest

def resumeSource : Code [4] (.invoke (key := ⟨37, .resume⟩)) ownerForest :=
  .resume .hit (.operations .nil) (.operations .nil) (.cell (.operations .nil))

/-- A concrete generated result for effectful cleanup around an outside owner
invocation. Its sole extra operation check refers to the actual cell receiver. -/
def resumeResult : CodeResult resumeSource
    (.cleanup (needs := [callbackEffect])
      (.request (effect := callbackEffect) (operation := 0)) ownerForest) :=
  ⟨.resume (.cleanup .hit) (.operations .nil)
    (.cleanup (.operations [(callbackEffect, 0)] .request .request) (.operations .nil))
    (.cell (.operations .nil)),
    .operations (.running (.spent 37 (.cell 4 .nil))) [(callbackEffect, 0)],
    (fun _ _ _ ready checked => ⟨ready.1, ready.2.1, rfl, ⟨checked, rfl⟩, ready.2.2.2.2⟩),
    fun _ _ _ _ checked => .resume (.cleanup .hit) (.operations .nil rfl)
      (.installCleanup [(callbackEffect, 0)] .request .request checked) .same⟩

theorem resume_checks_supplied : resumeResult.checks.Holds outward := rfl

theorem effectful_resume_preserved (ready : resumeSource.Valid outward actions phases) :
    resumeResult.annotation.Valid outward actions phases :=
  resumeResult.sound outward actions phases ready resume_checks_supplied

/-- Passing the new callback check never revives a consumed continuation. -/
theorem consumed_resume_rejected :
    resumeResult.checks.Holds outward ∧
      ¬ resumeResult.annotation.Valid outward actions (OwnerPhaseTransitions.spend phases 37) := by
  refine ⟨resume_checks_supplied, ?_⟩
  intro ready
  have available := ready.2.1
  simp [OwnerPhaseTransitions.spend] at available

end Examples

end Ash.OneShot.SourceScheduledCleanupGeneration

#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.Checks.when_holds
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.interfaces_generate
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.generate_all
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.code_generate
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.retained_generate
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.CodeResult.scheduled
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.RetainedResult.scheduled
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.Examples.removed_handler_checks_rejected
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.Examples.resume_checks_supplied
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.Examples.effectful_resume_preserved
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.Examples.consumed_resume_rejected

#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.interfaces_receiver
