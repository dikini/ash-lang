import SourceDeclarationPlans
import SourceContextualInvocations

/-! Source checks retain recursive declaration plans and independently check
invocation capabilities at their actual receiving scopes. Erasure reuses the
existing contextual source checks. Connecting plans to the full hereditary
expression/value judgment and strengthening clause instantiation remain open. -/
namespace Ash.OneShot.SourcePlannedChecks
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceContextualHints (Hints checkRequirements)
open SourceContextualRequirements (DeclarationRecipes)
open SourceContextualInvocations (Resume Dispose)
open SourceDependencySchemes (Checked Retained)
open SourceDependencyProjection (project project_append project_idempotent)
abbrev Receiving := SourceDependencyCapture.Scope

/-- Declaration admission is independent of scheduling. The parameter names
its judgment on actual clause plans; it does not supply future execution proofs. -/
class DeclarationPolicy where
  accepts : ∀ (_outward : List Instance) (_required : List SourceContextualHints.Requirement)
    {clauses : Clauses} {families : SourceDependencyAnnotations.ClauseDependencies}, ClausePlans clauses families → Prop

/-- Compatibility discipline for existing clients. Alternative structural
judgments use an explicit policy instance in the same source calculus. -/
instance contextualPolicy : DeclarationPolicy where
  accepts := fun outward required {clauses families} _ =>
    DeclarationRecipes outward clauses families required

section
variable [evidence : DeclarationPolicy]

mutual
/-- Every future handler retains declaration evidence for its actual clauses,
including handlers inside either offered mode. Scope compatibility and execution
checking are separate. The default policy retains the earlier recipes. -/
inductive Certified (outward : List Instance) [evidence : DeclarationPolicy] : List Nat → {dependencies : Dependencies} → Plan dependencies → Prop where
  | pure : Certified outward world .pure
  | request : Certified outward world .request
  | invoke : Certified outward world .invoke
  | sequence : Certified outward world first → Certified outward world second → Certified outward world (.sequence first second)
  | choice : Certified outward world first → Certified outward world second → Certified outward world (.choice first second)
  | handler {plans : ClausePlans clauses families} (recipes : evidence.accepts outward required plans)
      (declarations : CertifiedClauses outward world plans) (body : Certified outward world code) :
      Certified outward world (.handler (clauses := clauses) (families := families) required plans code)
  | cleanup : Certified outward world callback → Certified outward world body → Certified outward world (.cleanup callback body)
  | resource : (∀ identity, identity ∉ world → Certified outward (world ++ [identity]) (body identity)) →
      Certified outward world (.resource body)

inductive CertifiedModes (outward : List Instance) [evidence : DeclarationPolicy] : List Nat → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : CertifiedModes outward world .unavailable
  | available : (∀ owner, Certified outward world (body owner)) → CertifiedModes outward world (.available body)

inductive CertifiedClauses (outward : List Instance) [evidence : DeclarationPolicy] : List Nat →
    {clauses : Clauses} → {families : SourceDependencyAnnotations.ClauseDependencies} → ClausePlans clauses families → Prop where
  | nil : CertifiedClauses outward world .nil
  | cons : CertifiedModes outward world ordinary → CertifiedModes outward world protectedMode → CertifiedClauses outward world rest →
      CertifiedClauses outward world (.cons ordinary protectedMode rest)
end

mutual
inductive Local (outward : List Instance) (actions : Syntax.UsageTickets) [evidence : DeclarationPolicy] :
    OwnerPhaseTransitions.Phases → List Nat → {dependencies : Dependencies} → {scope : Receiving} →
      Plan dependencies → Hints scope → Prop where
  | pure : Local outward actions phases world .pure hints
  | request {hints : Hints scope} (checked : Checked outward actions phases world (.request effect operation) scope)
      (scheduled : ∀ captured tail (saved : Hints captured) (waiting : Hints tail) contract modes,
        HEq hints (saved.append waiting) →
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → Pending outward actions phases world
          (SourceContextualInvocationHints.forClosing saved) (.running waiting)) :
      Local outward actions phases world (.request (effect := effect) (operation := operation)) hints
  | resume (access : Resume actions phases owner hints after)
      (restored : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world after.hints .nil) :
      Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) hints
  | dispose (access : Dispose outward actions phases owner hints after)
      (scheduled : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world after.hints .nil) :
      Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) hints
  | sequence {after : Plan afterDep} (first : Local outward actions phases world before (.plain (dependencies := afterDep) hints))
      (second : Local outward actions phases world after hints) :
      Local outward actions phases world (.sequence before after) hints
  | choice : Local outward actions phases world first hints → Local outward actions phases world second hints →
      Local outward actions phases world (.choice first second) hints
  | handler {plans : ClausePlans clauses families} {hints : Hints scope}
      (recipes : evidence.accepts outward required plans)
      (declarations : CertifiedClauses outward world plans)
      (supplied : checkRequirements scope required = true)
      (body : Local outward actions phases world code
        (.handler (effect := effect) (table := table) (families := families) required hints)) :
      Local outward actions phases world (.handler (effect := effect) (table := table) (clauses := clauses) required plans code) hints
  | cleanup {callback : Plan callbackDep}
      (body : Local outward actions phases world code (.cleanup (needs := needs) (callback := callbackDep) hints))
      (completion : Local outward actions phases world callback (.running hints)) :
      Local outward actions phases world (.cleanup (needs := needs) callback code) hints
  | resource (body : ∀ identity, identity ∉ world →
      Local outward actions phases (world ++ [identity]) (code identity) (.cell (identity := identity) hints)) :
      Local outward actions phases world (.resource code) hints

inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets) [evidence : DeclarationPolicy] :
    OwnerPhaseTransitions.Phases → List Nat → {scope outside : Receiving} → Hints scope → Hints outside → Prop where
  | nil : Pending outward actions phases world .nil outside
  | plain {plan : Plan dependencies} (code : Local outward actions phases world plan (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.plain (dependencies := dependencies) rest) outside
  | handler : Pending outward actions phases world rest outside → Pending outward actions phases world (.handler required rest) outside
  | cell : Pending outward actions phases world rest outside → Pending outward actions phases world (.cell rest) outside
  | cleanup {plan : Plan dependencies} (completion : Local outward actions phases world plan (.running (rest.append outside)))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cleanup (callback := dependencies) rest) outside
  | running : Pending outward actions phases world rest outside → Pending outward actions phases world (.running rest) outside
  | live : Pending outward actions phases world saved (rest.append outside) → Pending outward actions phases world rest outside →
      Pending outward actions phases world (.live saved rest) outside
  | spent : Pending outward actions phases world rest outside → Pending outward actions phases world (.spent rest) outside
end

omit evidence in
theorem resume_projected {hints : Hints scope} (access : Resume actions phases owner hints after) :
    ∃ projectedAfter, SourceDependencyCapture.ResumeChecked actions phases owner (project scope) projectedAfter ∧
      project projectedAfter = project after.scope := by
  cases access with
  | checked found checked compatible =>
      rename_i selected
      have mapped : (SourceDependencyCapture.checkResume actions phases owner (project scope)).map project =
          some (project (SourceContextualInvocationHints.Selection.resumed owner selected).scope) := by
        rw [SourceDependencyProjection.project_checkResume, SourceDependencyCapture.check_resume_iff.mpr checked]
        rfl
      obtain ⟨actual, found, same⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨actual, SourceDependencyCapture.check_resume_iff.mp found, same⟩

omit evidence in
theorem dispose_projected {hints : Hints scope} (access : Dispose outward actions phases owner hints after) :
    ∃ projectedAfter, SourceDependencyCapture.DisposeChecked outward actions phases owner (project scope) projectedAfter ∧
      project projectedAfter = project after.scope := by
  cases access with
  | checked found checked compatible =>
      rename_i selected
      have mapped : (SourceDependencyCapture.checkDispose outward actions phases owner (project scope)).map project =
          some (project (SourceContextualInvocationHints.Selection.disposed owner selected).scope) := by
        rw [SourceDependencyProjection.project_checkDispose, SourceDependencyCapture.check_dispose_iff.mpr checked]
        rfl
      obtain ⟨actual, found, same⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨actual, SourceDependencyCapture.check_dispose_iff.mp found, same⟩

/-- Use one erasure algebra for both mutually recursive source judgments. -/
theorem erase_all (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ phases world {dependencies scope} (plan : Plan dependencies) (hints : Hints scope),
      Local outward actions phases world plan hints → Checked outward actions phases world dependencies scope) ∧
    (∀ phases world {scope outside} (hints : Hints scope) (outsideHints : Hints outside),
      Pending outward actions phases world hints outsideHints → Retained outward actions phases world scope outside) := by
  constructor <;> intro phases world
  all_goals first
    | (intro dependencies scope plan hints checked
       apply Local.rec
         (motive_1 := fun phases world {dependencies scope} _ _ _ => Checked outward actions phases world dependencies scope)
         (motive_2 := fun phases world {scope outside} _ _ _ => Retained outward actions phases world scope outside)
         (t := checked))
    | (intro scope outside hints outsideHints checked
       apply Pending.rec
         (motive_1 := fun phases world {dependencies scope} _ _ _ => Checked outward actions phases world dependencies scope)
         (motive_2 := fun phases world {scope outside} _ _ _ => Retained outward actions phases world scope outside)
         (t := checked))
  all_goals intros
  all_goals simp only [Checked, Retained, project_append, project] at *
  all_goals first
    | assumption
    | exact .pure
    | exact .nil
    | exact .sequence ‹_› ‹_›
    | exact .choice ‹_› ‹_›
    | exact .handler ‹_›
    | exact .cleanup ‹_› ‹_›
    | exact .resource ‹_›
    | exact .plain ‹_› ‹_›
    | exact .cell ‹_›
    | exact .running ‹_›
    | exact .live ‹_› ‹_›
    | (obtain ⟨actual, access, same⟩ := resume_projected ‹Resume _ _ _ _ _›
       exact .resume access (by rw [same]; assumption))
    | (obtain ⟨actual, access, same⟩ := dispose_projected ‹Dispose _ _ _ _ _ _›
       exact .dispose access (by rw [same]; assumption))

theorem Local.erase {plan : Plan dependencies} {hints : Hints scope}
    (checked : Local outward actions phases world plan hints) : Checked outward actions phases world dependencies scope :=
  (erase_all outward actions).1 phases world plan hints checked

theorem Pending.erase {hints : Hints scope} {outsideHints : Hints outside}
    (checked : Pending outward actions phases world hints outsideHints) : Retained outward actions phases world scope outside :=
  (erase_all outward actions).2 phases world hints outsideHints checked

theorem Local.certified {plan : Plan dependencies} {hints : Hints scope}
    (checked : Local outward actions phases world plan hints) : Certified outward world plan := by
  apply Local.rec
    (motive_1 := fun _ world {dependencies scope} plan _ _ => Certified outward world plan)
    (motive_2 := fun _ _ {scope outside} _ _ _ => True) (t := checked)
  all_goals intros
  all_goals first
    | trivial
    | exact .pure
    | exact .request
    | exact .invoke
    | exact .sequence ‹_› ‹_›
    | exact .choice ‹_› ‹_›
    | exact .handler ‹_› ‹_› ‹_›
    | exact .cleanup ‹_› ‹_›
    | exact .resource ‹_›

theorem CertifiedModes.selected {plans : ModePlans offered}
    (checked : CertifiedModes outward world plans) (found : offered = some family) :
    ∃ bodies : ∀ owner, Plan (family owner), ∀ owner, Certified outward world (bodies owner) := by
  subst offered
  cases checked with
  | available bodies => exact ⟨_, bodies⟩

/-- Selecting a clause retains the recursive annotations for the same mode
and dependency family, including recipes for handlers in its future body. -/
theorem CertifiedClauses.selected {plans : ClausePlans clauses families}
    (checked : CertifiedClauses outward world plans)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (SourceDependencyCapture.lookupDependencies operation families).bind
      (SourceDependencyCapture.modeDependencies held) = some family) :
    ∃ bodies : ∀ owner, Plan (family owner), ∀ owner, Certified outward world (bodies owner) := by
  induction selected generalizing families with
  | hit => cases checked with
    | cons ordinary protectedMode rest =>
        simp only [SourceDependencyCapture.lookupDependencies, if_true, Option.bind_some] at found
        cases held with
        | false => exact ordinary.selected found
        | true => exact protectedMode.selected found
  | pass different next ih => cases checked with
    | cons ordinary protectedMode rest =>
        exact ih rest (by simpa only [SourceDependencyCapture.lookupDependencies, if_neg different] using found)

/-- A planned request's closing premise applies to the exact retained hints
at its actual split; it cannot discharge the check with fabricated requirements. -/
theorem Local.request_schedule {hints : Hints (captured.append tail)}
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) hints)
    (found : SourceDependencyCapture.select effect operation (captured.append tail) =
      some (.handler captured tail contract modes)) (disposes : contract.dispose = true) :
    ∃ saved : Hints captured, ∃ waiting : Hints tail,
      hints = saved.append waiting ∧ Pending outward actions phases world
        (SourceContextualInvocationHints.forClosing saved) (.running waiting) := by
  obtain ⟨saved, waiting, same⟩ := SourceDeclarationPlans.splitHints hints
  cases checked with
  | request legacy scheduled => exact ⟨saved, waiting, same, scheduled _ _ saved waiting _ _ (heq_of_eq same) found disposes⟩

end

/-- The handler-entry source rule supplies the recipe for the same actual
handler being installed and retains the checked body under its new hints. -/
theorem Local.handler_entry {hints : Hints scope}
    {plans : ClausePlans data.clauses (families data)} {body : Plan dependencies}
    (checked : Local outward actions phases world
      (.handler (effect := data.effectInst) (table := tables data) (required data) plans body) hints)
    (matched : SourceContextualHintChecking.Matches tables families required hints stack)
    (recipes : ∀ handler ∈ SourceContextualRechecking.handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (compatible : SourceContextualHintChecking.Compatible hints .nil) :
    Local outward actions phases world body
      (.handler (effect := data.effectInst) (table := tables data) (families := families data) (required data) hints) ∧
    SourceContextualHintChecking.Matches tables families required
      (.handler (effect := data.effectInst) (table := tables data) (families := families data)
        (required data) hints) (.push (.handler data) stack) ∧
    (∀ handler ∈ SourceContextualRechecking.handlers (.push (.handler data) stack),
      DeclarationRecipes outward handler.clauses (families handler) (required handler)) ∧
    SourceContextualForest.Forest outward tables families (.push (.handler data) stack)
      (.handler data.effectInst (tables data) (families data) scope) .nil := by
  cases checked with
  | handler introduced declarations supplied body =>
      have next := SourceContextualHintChecking.Matches.handler (data := data) matched
      have retained : ∀ handler ∈ SourceContextualRechecking.handlers (.push (.handler data) stack),
          DeclarationRecipes outward handler.clauses (families handler) (required handler) := by
        intro handler member
        change handler ∈ data :: SourceContextualRechecking.handlers stack at member
        rcases List.mem_cons.mp member with rfl | existing
        · exact introduced
        · exact recipes handler existing
      refine ⟨body, next, retained, next.recheck retained ?_⟩
      simp only [Hints.check, SourceDependencyProjection.scope_append_nil, Bool.and_eq_true]
      exact ⟨supplied, (SourceContextualHintChecking.check_iff _).mpr compatible⟩

/-- A source-admitted resume carries the reconstructed pending source check
as well as the independent invocation judgment. Reuse the actual-step and
ownership proof rather than assuming invocation success separately. -/
theorem Local.resume_step {hints : Hints scope}
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) hints)
    (matched : SourceContextualHintChecking.Matches tables families required hints stack)
    (recipes : ∀ handler ∈ SourceContextualRechecking.handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (unique : (ownedTickets stack).Nodup)
    (resolved : caller.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ after : SourceContextualInvocationHints.Annotated, ∃ afterStack,
      Pending outward actions (OwnerPhaseTransitions.spend phases owner) world after.hints .nil ∧
      RawStep ⟨.resume binder value, caller, stack⟩ ⟨value, caller, afterStack⟩ [] [.ticket owner] ∧
      SourceContextualHintChecking.Matches tables families required after.hints afterStack ∧
      SourceContextualForest.Forest outward tables families afterStack after.scope .nil ∧
      (ownedTickets stack).Perm (owner :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) := by
  cases checked with
  | resume access restored =>
      obtain ⟨afterStack, facts⟩ := access.step matched recipes unique resolved closed
      exact ⟨_, afterStack, restored, facts⟩

theorem Local.dispose_step {hints : Hints scope}
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) hints)
    (matched : SourceContextualHintChecking.Matches tables families required hints stack)
    (recipes : ∀ handler ∈ SourceContextualRechecking.handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (unique : (ownedTickets stack).Nodup) (resolved : caller.resolve binder = some owner) :
    ∃ after : SourceContextualInvocationHints.Annotated, ∃ afterStack captured plan,
      Pending outward actions (OwnerPhaseTransitions.spend phases owner) world after.hints .nil ∧
      RawStep ⟨.discard binder, caller, stack⟩ ⟨.unit, caller, afterStack⟩ [.close closeId] [.ticket owner] ∧
      SourceContextualHintChecking.Matches tables families required after.hints afterStack ∧
      SourceContextualForest.Forest outward tables families afterStack after.scope .nil ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners ∧
      (ownedTickets stack).Perm (owner :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) := by
  cases checked with
  | dispose access scheduled =>
      obtain ⟨afterStack, captured, plan, facts⟩ := access.step matched recipes unique resolved
      exact ⟨_, afterStack, captured, plan, scheduled, facts⟩

namespace Examples
open SourceDependencyHandlerGap (effect family clauses dependencies table outside)
open SourceContextualHintChecking.Examples (tailHints)

def clausePlan (owner : Nat) : Plan (family owner) :=
  .sequence (.sequence .pure .request) (.sequence .pure .invoke)

def clausePlans : ClausePlans clauses dependencies :=
  .cons (.available clausePlan) .unavailable .nil

theorem certified_clauses : CertifiedClauses outward world clausePlans :=
  .cons (.available (fun _ => .sequence (.sequence .pure .request) (.sequence .pure .invoke))) .unavailable .nil

def installPlan : Plan (.handler effect table dependencies .pure) :=
  .handler [(effect, 0)] clausePlans .pure

theorem handler_admitted : Local outward actions phases world installPlan tailHints :=
  .handler SourceContextualRequirements.Examples.declaration_recipes certified_clauses (by decide) .pure

/-- Cleanup retains the plan for a handler installed by its callback, with
that handler checked under running protection at the actual outside scope. -/
theorem callback_handler_admitted : Local outward actions phases world
    (.cleanup (needs := [effect]) installPlan .pure) tailHints :=
  .cleanup .pure (.handler SourceContextualRequirements.Examples.declaration_recipes certified_clauses (by decide) .pure)

theorem callback_recipes_retained : Certified outward world (.cleanup (needs := [effect]) installPlan .pure) :=
  (callback_handler_admitted (actions := fun _ => none) (phases := fun _ => .consumed)).certified

theorem missing_outer_rejected : ¬ Local outward actions phases world installPlan .nil := by
  intro checked
  cases checked with
  | handler recipes declarations supplied body => cases supplied

/-- The nonuniform forwarding handler now obtains its installed contextual
certificate from the new source handler rule. Full expression typing remains
the separate hereditary source integration. -/
theorem source_handler_entered : SourceContextualForest.Forest outward
    SourceContextualRechecking.Examples.tables SourceContextualRechecking.Examples.families
    (.push (.handler SourceContextualForest.Examples.inner) SourceContextualRechecking.Examples.tail)
    (.handler effect table dependencies outside) .nil := by
  have entered := Local.handler_entry
    (outward := outward)
    (data := SourceContextualForest.Examples.inner)
    (tables := SourceContextualRechecking.Examples.tables)
    (families := SourceContextualRechecking.Examples.families)
    (required := SourceContextualRechecking.Examples.required)
    (handler_admitted (actions := fun _ => none) (phases := fun _ => .consumed) (world := []))
    (SourceContextualHintChecking.Matches.handler (data := SourceContextualForest.Examples.outer) .nil)
    (fun handler member => by
      change handler ∈ [SourceContextualForest.Examples.outer] at member
      cases List.mem_singleton.mp member
      exact SourceContextualRequirements.Examples.resume_declarations)
    ((SourceContextualHintChecking.check_iff _).mp (by decide))
  exact entered.2.2.2

end Examples

end Ash.OneShot.SourcePlannedChecks

#print axioms Ash.OneShot.SourcePlannedChecks.resume_projected
#print axioms Ash.OneShot.SourcePlannedChecks.dispose_projected
#print axioms Ash.OneShot.SourcePlannedChecks.erase_all
#print axioms Ash.OneShot.SourcePlannedChecks.Local.erase
#print axioms Ash.OneShot.SourcePlannedChecks.Pending.erase
#print axioms Ash.OneShot.SourcePlannedChecks.Local.certified
#print axioms Ash.OneShot.SourcePlannedChecks.CertifiedModes.selected
#print axioms Ash.OneShot.SourcePlannedChecks.CertifiedClauses.selected
#print axioms Ash.OneShot.SourcePlannedChecks.Local.request_schedule
#print axioms Ash.OneShot.SourcePlannedChecks.Local.handler_entry
#print axioms Ash.OneShot.SourcePlannedChecks.Local.resume_step
#print axioms Ash.OneShot.SourcePlannedChecks.Local.dispose_step
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.certified_clauses
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.handler_admitted
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.callback_handler_admitted
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.callback_recipes_retained
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.missing_outer_rejected
#print axioms Ash.OneShot.SourcePlannedChecks.Examples.source_handler_entered
