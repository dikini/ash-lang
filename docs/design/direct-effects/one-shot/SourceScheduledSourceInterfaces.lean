import SourceScheduledAdaptationCompilation
import SourceScheduledClauses

/-! Syntax-directed declaration annotations and finite operation interfaces
construct source scheduling without a previously checked whole computation.
Annotations live on stable signatures; actual clause syntax is authenticated
through the existing declaration-signature transport theorem. -/
namespace Ash.OneShot.SourceScheduledSourceInterfaces
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (Signature signature clauseSignatures)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceRequestFootprints (Footprint)
open SourceScheduledChecks (Local)
open SourceScheduledAdaptationCompilation (requirements_prefix requirements_handler requirements_cell)

/-- This judgment retains declarations at each source constructor. It has no
receiving forest, scheduling judgment, or successful future-body field.
Continuation invocations retain a separate capability obligation. -/
inductive Declared : List Nat → {dependencies : Dependencies} → Signature dependencies → Prop where
  | pure : Declared world .pure
  | request : Declared world .request
  | invoke : Declared world .invoke
  | sequence : Declared world first → Declared world second → Declared world (.sequence first second)
  | choice : Declared world first → Declared world second → Declared world (.choice first second)
  | handler {plans : ClausePlans clauses families}
      (declarations : SourcePlannedRecipeDeclarations.Declarations required plans)
      (body : Declared world code) :
      Declared world (.handler (effect := effect) (table := table) required (clauseSignatures plans) code)
  | cleanup : Declared world callback → Declared world body → Declared world (.cleanup callback body)
  | resource (body : ∀ identity, identity ∉ world → Declared (world ++ [identity]) (code identity)) :
      Declared world (.resource code)

/-- Existing checked code already supplies this source-only declaration
annotation. Extract it once; reinterpretation needs only the finite interface. -/
theorem declared_of_local {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) : Declared world (signature plan) := by
  apply Local.rec
    (motive_1 := fun phases world {dependencies scope hints} plan forest checked =>
      Declared world (signature plan))
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (t := checked)
  all_goals intros
  all_goals first
    | exact True.intro
    | exact Declared.pure
    | exact Declared.request
    | exact Declared.invoke
    | exact Declared.sequence ‹_› ‹_›
    | exact Declared.choice ‹_› ‹_›
    | exact Declared.handler ‹_› ‹_›
    | exact Declared.cleanup ‹_› ‹_›
    | exact Declared.resource ‹_›

/-- Source substitution retains the stable signature, so it also retains this
annotation without another induction over literal clause bodies. -/
theorem Declared.congr (declared : Declared world first) (same : first = second) :
    Declared world second := same ▸ declared

/-- Compile directly from two independent structural source annotations and
one finite receiving-scope check. No old or future Local/Pending premise is
accepted. The rule for internally handled disposal uses its existing proof. -/
theorem compile_signature {plan : Plan dependencies} {checking : Signature dependencies}
    {hints : Hints scope} {forest : Forest hints}
    (interface : Footprint checking required)
    (same : signature plan = checking)
    (declared : Declared world checking)
    (supplied : checkRequirements scope required = true) :
    Local outward actions phases world plan forest := by
  induction interface generalizing scope world with
  | pure => cases plan; exact .pure
  | request =>
      cases plan
      exact SourceScheduledScopedInvocations.request_from_capability
        (SourceContextualRequirements.check_requirements_iff.mp supplied _ List.mem_cons_self)
  | handledRequest => exact SourceScheduledClauses.handled_request_local same
  | sequence left right ihLeft ihRight => cases plan with
    | sequence firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
      cases declared with
      | sequence firstDeclared secondDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        exact .sequence
          (ihLeft firstSame firstDeclared (requirements_prefix (front := .plain _ .nil) (fun _ => rfl) supplied.1))
          (ihRight secondSame secondDeclared supplied.2)
  | choice left right ihLeft ihRight => cases plan with
    | choice firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.choice.inj same
      cases declared with
      | choice firstDeclared secondDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        exact .choice (ihLeft firstSame firstDeclared supplied.1) (ihRight secondSame secondDeclared supplied.2)
  | handler body internal ih => cases plan with
    | handler required declarations bodyPlan =>
      cases declared with
      | handler sourceDeclarations bodyDeclared =>
        obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
        have recipes := sourceDeclarations.signature_congr declarationsSame.symm
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        exact .handler recipes recipes.certified supplied.1
          (ih bodySame bodyDeclared (requirements_handler internal supplied.2))
  | cleanup callback body ihCallback ihBody => cases plan with
    | cleanup callbackPlan bodyPlan =>
      obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
      cases declared with
      | cleanup callbackDeclared bodyDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        exact .cleanup
          (ihBody bodySame bodyDeclared (requirements_prefix (front := .cleanup _ _ .nil) (fun _ => rfl) supplied.2))
          (ihCallback callbackSame callbackDeclared (requirements_prefix (front := .running .nil) (fun _ => rfl) supplied.1))
  | resource body ih => cases plan with
    | resource plans => cases declared with
      | resource declarations =>
        exact .resource (fun identity fresh => ih identity
          (congrFun (Signature.resource.inj same) identity) (declarations identity fresh)
          (requirements_cell identity supplied))
  | weaken body included ih =>
      exact ih same declared (SourceContextualRequirements.check_requirements_subset included supplied)

theorem compile {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (interface : Footprint (signature plan) required)
    (declared : Declared world (signature plan))
    (supplied : checkRequirements scope required = true) :
    Local outward actions phases world plan forest :=
  compile_signature interface rfl declared supplied

/-- At program entry the receiving stack is empty. A closed finite interface
therefore derives the formerly separate scheduling premise for this source
class; completion, source typing and resource support are still independent. -/
theorem initial_contextual {plan : Plan dependencies}
    (interface : Footprint (signature plan) [])
    (declared : Declared [] (signature plan)) :
    Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil :=
  compile interface declared rfl

end Ash.OneShot.SourceScheduledSourceInterfaces

#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.declared_of_local
#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.Declared.congr
#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.compile_signature
#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.compile
#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.initial_contextual
