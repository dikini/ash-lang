import SourceContextualRechecking
import SourceHandlerRequirements

/-! Structural checking of source handler requirements, and authentication
against the existing runtime realization. Successful checks reconstruct the
existing contextual certificates; they are not whole-state safety premises. -/
namespace Ash.OneShot.SourceContextualHintChecking
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints checkRequirements checkResume checkDispose)
open SourceContextualRequirements (DeclarationRecipes check_requirements_iff)
open SourceContextualRechecking (Required checkForest checkFrame handlers)
open SourceContextualClauses (RequestCapability)
abbrev Receiving := SourceDependencyCapture.Scope

/-- Each rule checks one source scope constructor. A saved continuation is
checked at its full receiving scope, including the waiting suffix. -/
inductive Compatible : {scope : Receiving} → Hints scope → Receiving → Prop where
  | nil : Compatible .nil outside
  | plain : Compatible rest outside → Compatible (.plain rest) outside
  | handler {rest : Hints restScope} (supplied : ∀ request ∈ required,
      RequestCapability request.1 request.2 (restScope.append outside))
      (tail : Compatible rest outside) :
      Compatible (.handler (effect := effect) (table := table) (families := families)
        (rest := restScope) required rest) outside
  | cell : Compatible rest outside → Compatible (.cell rest) outside
  | cleanup : Compatible rest outside → Compatible (.cleanup rest) outside
  | running : Compatible rest outside → Compatible (.running rest) outside
  | live {rest : Hints restScope} : Compatible saved (restScope.append outside) → Compatible rest outside →
      Compatible (.live (rest := restScope) saved rest) outside
  | spent : Compatible rest outside → Compatible (.spent rest) outside

theorem check_iff (hints : Hints scope) : hints.check outside = true ↔ Compatible hints outside := by
  induction hints generalizing outside with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | plain rest ih => exact ⟨fun checked => .plain (ih.mp checked), fun accepted => by cases accepted; exact ih.mpr ‹_›⟩
  | handler required rest ih =>
      simp only [Hints.check, Bool.and_eq_true, check_requirements_iff, ih]
      exact ⟨fun ⟨supplied, tail⟩ => .handler supplied tail,
        fun accepted => by cases accepted with | handler supplied tail => exact ⟨supplied, tail⟩⟩
  | cell rest ih => exact ⟨fun checked => .cell (ih.mp checked), fun accepted => by cases accepted; exact ih.mpr ‹_›⟩
  | cleanup rest ih => exact ⟨fun checked => .cleanup (ih.mp checked), fun accepted => by cases accepted; exact ih.mpr ‹_›⟩
  | running rest ih => exact ⟨fun checked => .running (ih.mp checked), fun accepted => by cases accepted; exact ih.mpr ‹_›⟩
  | live saved rest ihSaved ihRest =>
      simp only [Hints.check, Bool.and_eq_true, ihSaved, ihRest]
      exact ⟨fun ⟨inside, tail⟩ => .live inside tail,
        fun accepted => by cases accepted with | live inside tail => exact ⟨inside, tail⟩⟩
  | spent rest ih => exact ⟨fun checked => .spent (ih.mp checked), fun accepted => by cases accepted; exact ih.mpr ‹_›⟩

/-- Existing structural compatibility supplies the internal obligations.
The finite exposed operation list exactly characterizes a replacement
receiving scope, using the established independent RequestCapability. -/
theorem compatible_replace_iff (checked : Compatible hints before) :
    Compatible hints after ↔ ∀ request ∈ SourceHandlerRequirements.exposed hints,
      RequestCapability request.1 request.2 after :=
  (check_iff hints).symm.trans
    ((SourceHandlerRequirements.check_replace_iff hints ((check_iff hints).mpr checked)).trans
      check_requirements_iff)

/-- Reuse structural compatibility at the actual retained hints. Requests
intercepted at the inserted handler must have its operation capability;
requirements shielded by the preceding scope keep their old derivation. -/
theorem compatible_handler_insert_iff (checked : Compatible hints (front.append outside)) :
    Compatible hints (front.append (.handler effect table families outside)) ↔
      ∀ request ∈ SourceHandlerRequirements.intercepted effect
        (SourceHandlerRequirements.outwardRequirements front (SourceHandlerRequirements.exposed hints)),
        RequestCapability request.1 request.2 (.handler effect table families .nil) :=
  (check_iff hints).symm.trans
    ((SourceHandlerRequirements.check_handler_insert hints ((check_iff hints).mpr checked)).trans
      check_requirements_iff)

theorem check_append (first : Hints firstScope) (second : Hints secondScope) :
    (first.append second).check outside =
      (first.check (secondScope.append outside) && second.check outside) := by
  induction first generalizing outside <;>
    simp_all [Hints.append, Hints.check, SourceDependencyChecks.scope_append_assoc, Bool.and_assoc] <;> rfl

theorem compatible_append_iff (first : Hints firstScope) (second : Hints secondScope) :
    Compatible (first.append second) outside ↔
      Compatible first (secondScope.append outside) ∧ Compatible second outside := by
  simp only [← check_iff, check_append, Bool.and_eq_true]

/-- Authentication fixes each requirement list to the same actual handler as
its table and dependency family. It adds no execution-safety assumption. -/
inductive Matches (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyCapture.Families) (required : Required) :
    {scope : Receiving} → Hints scope → Stack → Prop where
  | nil : Matches tables families required .nil .nil
  | plain : Matches tables families required rest stack →
      Matches tables families required (.plain rest) (.push (.plain data) stack)
  | handler : Matches tables families required rest stack →
      Matches tables families required
        (.handler (effect := data.effectInst) (table := tables data)
          (families := families data) (required data) rest) (.push (.handler data) stack)
  | cell : Matches tables families required rest stack →
      Matches tables families required (.cell (identity := identity) rest)
        (.push (.cell identity payload caller answer) stack)
  | cleanup : Matches tables families required rest stack →
      Matches tables families required (.cleanup (needs := action.requests) rest) (.push (.armed action) stack)
  | running : Matches tables families required rest stack →
      Matches tables families required (.running rest) (.push (.running action value closed) stack)
  | unwinding : Matches tables families required rest stack →
      Matches tables families required (.running rest) (.push (.unwinding action) stack)
  | closing : Matches tables families required rest stack →
      Matches tables families required (.running rest) (.push (.closing identity caller) stack)
  | retiring : Matches tables families required rest stack →
      Matches tables families required (.running rest) (.push (.retiring owner) stack)
  | live : Matches tables families required saved capture → Matches tables families required rest stack →
      Matches tables families required (.live (owner := owner) saved rest)
        (.live owner input answer capture caller stack)
  | spent : Matches tables families required rest stack →
      Matches tables families required (.spent (owner := owner) rest) (.spent owner answer caller stack)

theorem Matches.realizes {hints : Hints scope} (matched : Matches tables families required hints stack) :
    SourceDependencyCapture.Realizes tables families scope stack := by
  induction matched with
  | nil => exact .nil
  | plain tail ih => exact .push .plain ih
  | handler tail ih => exact .push .handler ih
  | cell tail ih => exact .push .cell ih
  | cleanup tail ih => exact .push .cleanup ih
  | running tail ih => exact .push .running ih
  | unwinding tail ih => exact .push .unwinding ih
  | closing tail ih => exact .push .closing ih
  | retiring tail ih => exact .push .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem Matches.check_eq {hints : Hints scope} (matched : Matches tables families required hints stack) :
    hints.check outside = checkForest required stack scope outside := by
  induction matched generalizing outside <;> simp_all [Hints.check, checkForest, checkFrame]

theorem Matches.handler_required
    (matched : Matches tables families required
      (.handler (effect := effect) (table := table) (families := dependencies) needs rest)
      (.push (.handler data) stack)) : needs = required data := by
  cases matched
  rfl

theorem Matches.append {first second : Stack} (matchedFirst : Matches tables families required firstHints first)
    (matchedSecond : Matches tables families required secondHints second) :
    Matches tables families required (firstHints.append secondHints) (first.append second) := by
  induction matchedFirst with
  | nil => exact matchedSecond
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup tail ih => exact .cleanup ih
  | running tail ih => exact .running ih
  | unwinding tail ih => exact .unwinding ih
  | closing tail ih => exact .closing ih
  | retiring tail ih => exact .retiring ih
  | live saved tail ihSaved ihTail => exact .live saved ihTail
  | spent tail ih => exact .spent ih

/-- Every existing realization admits the extra data. This construction
does not claim that the resulting requirements are compatible. -/
theorem annotate (realized : SourceDependencyCapture.Realizes tables families scope stack)
    (required : Required) : ∃ hints : Hints scope, Matches tables families required hints stack := by
  induction realized with
  | nil => exact ⟨.nil, .nil⟩
  | push frame tail ih =>
      obtain ⟨rest, matched⟩ := ih
      cases frame with
      | plain => exact ⟨.plain rest, .plain matched⟩
      | handler => exact ⟨.handler _ rest, .handler matched⟩
      | cell => exact ⟨.cell rest, .cell matched⟩
      | cleanup => exact ⟨.cleanup rest, .cleanup matched⟩
      | running => exact ⟨.running rest, .running matched⟩
      | unwinding => exact ⟨.running rest, .unwinding matched⟩
      | closing => exact ⟨.running rest, .closing matched⟩
      | retiring => exact ⟨.running rest, .retiring matched⟩
  | live saved tail ihSaved ihTail =>
      obtain ⟨inside, matchedSaved⟩ := ihSaved
      obtain ⟨rest, matchedTail⟩ := ihTail
      exact ⟨.live inside rest, .live matchedSaved matchedTail⟩
  | spent tail ih =>
      obtain ⟨rest, matched⟩ := ih
      exact ⟨.spent rest, .spent matched⟩

theorem Matches.recheck {hints : Hints scope} (matched : Matches tables families required hints stack)
    (recipes : ∀ handler ∈ handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : hints.check outside = true) :
    SourceContextualForest.Forest outward tables families stack scope outside :=
  SourceContextualRechecking.recheck_forest matched.realizes recipes (matched.check_eq ▸ checked)

/-- Invocation rechecking now takes source annotations only. Authentication
and retained recipes connect that source test to the actual runtime step. -/
theorem resume_rechecked
    {savedHints : Hints capturedScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (saved : Matches tables families required savedHints capture)
    (waiting : Matches tables families required frontHints front)
    (outside : Matches tables families required tailHints tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkResume savedHints frontHints tailHints owner outer = true) :
    SourceContextualForest.Forest outward tables families
      (capture.append (front.append (.spent owner answer caller tail)))
      (capturedScope.append (frontScope.append (.spent owner tailScope))) outer :=
  (saved.append (waiting.append (.spent outside))).recheck
    (fun handler member => recipes handler ((SourceContextualRechecking.resume_handlers handler).mp member)) checked

theorem dispose_rechecked
    {closingHints : Hints closingScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (scheduled : Matches tables families required closingHints (closeControl caller plan))
    (waiting : Matches tables families required frontHints front)
    (outside : Matches tables families required tailHints tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer captured savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkDispose closingHints frontHints tailHints owner outer = true) :
    SourceContextualForest.Forest outward tables families
      ((closeControl caller plan).append (.push (.closing closeId caller) (front.append (.spent owner answer caller tail))))
      (closingScope.append (.running (frontScope.append (.spent owner tailScope)))) outer :=
  (scheduled.append (.closing (waiting.append (.spent outside)))).recheck
    (fun handler member => recipes handler (SourceContextualRechecking.dispose_handlers plan member)) checked

namespace Examples
open SourceContextualRechecking.Examples (tables families required captured front tail capturedScope frontScope)

def savedHints : Hints capturedScope := .handler [(SourceDependencyHandlerGap.effect, 0)] .nil
def frontHints : Hints frontScope := .handler [] .nil
def tailHints : Hints SourceDependencyHandlerGap.outside := .handler [] .nil

theorem source_resume_checked : checkResume savedHints frontHints tailHints 19 .nil = true := by decide

/-- The same positive example now reconstructs runtime certificates using a
source-only check, authenticated against the actual three handlers. -/
theorem source_resume_rechecked : SourceContextualForest.Forest outward tables families
    (captured.append (front.append (.spent 19 .unit .none tail)))
    (capturedScope.append (frontScope.append (.spent 19 SourceDependencyHandlerGap.outside))) .nil :=
  resume_rechecked (required := required)
    (.handler (data := SourceContextualForest.Examples.inner) .nil)
    (.handler (data := SourceContextualRechecking.Examples.callerHandler) .nil)
    (.handler (data := SourceContextualForest.Examples.outer) .nil)
    SourceContextualRechecking.Examples.retained_recipes source_resume_checked

def maskingScope : Receiving := .handler SourceDependencyHandlerGap.effect [] [] .nil
def maskingHints : Hints maskingScope := .handler [] .nil

/-- Before invocation the saved handler still receives the original outer
interpretation. Resumption inserts the masking caller into that path. -/
theorem current_check_does_not_imply_resume_check :
    (maskingHints.append (.live (owner := 19) savedHints tailHints)).check .nil = true ∧
      checkResume savedHints maskingHints tailHints 19 .nil = false := by decide

theorem incompatible_resume_rejected :
    ¬ Compatible (savedHints.append (maskingHints.append (.spent (owner := 19) tailHints))) .nil := by
  intro compatible
  have accepted := (check_iff _).mpr compatible
  have rejected := current_check_does_not_imply_resume_check.2
  change checkResume savedHints maskingHints tailHints 19 .nil = true at accepted
  rw [rejected] at accepted
  cases accepted

/-- An empty fabricated requirement list cannot authenticate as the saved
handler whose retained recipe requires F. -/
theorem missing_hint_rejected : ¬ Matches tables families required
    (.handler (effect := SourceDependencyHandlerGap.effect)
      (table := SourceDependencyHandlerGap.table) (families := SourceDependencyHandlerGap.dependencies) [] .nil)
    captured := by
  intro matched
  have impossible := matched.handler_required
  change [] = [(SourceDependencyHandlerGap.effect, 0)] at impossible
  cases impossible

end Examples

end Ash.OneShot.SourceContextualHintChecking

#print axioms Ash.OneShot.SourceContextualHintChecking.check_iff
#print axioms Ash.OneShot.SourceContextualHintChecking.check_append
#print axioms Ash.OneShot.SourceContextualHintChecking.compatible_append_iff
#print axioms Ash.OneShot.SourceContextualHintChecking.Matches.realizes
#print axioms Ash.OneShot.SourceContextualHintChecking.Matches.check_eq
#print axioms Ash.OneShot.SourceContextualHintChecking.Matches.handler_required
#print axioms Ash.OneShot.SourceContextualHintChecking.Matches.append
#print axioms Ash.OneShot.SourceContextualHintChecking.annotate
#print axioms Ash.OneShot.SourceContextualHintChecking.Matches.recheck
#print axioms Ash.OneShot.SourceContextualHintChecking.resume_rechecked
#print axioms Ash.OneShot.SourceContextualHintChecking.dispose_rechecked
#print axioms Ash.OneShot.SourceContextualHintChecking.Examples.source_resume_checked
#print axioms Ash.OneShot.SourceContextualHintChecking.Examples.source_resume_rechecked
#print axioms Ash.OneShot.SourceContextualHintChecking.Examples.current_check_does_not_imply_resume_check
#print axioms Ash.OneShot.SourceContextualHintChecking.Examples.incompatible_resume_rejected
#print axioms Ash.OneShot.SourceContextualHintChecking.Examples.missing_hint_rejected

#print axioms Ash.OneShot.SourceContextualHintChecking.compatible_replace_iff
#print axioms Ash.OneShot.SourceContextualHintChecking.compatible_handler_insert_iff
