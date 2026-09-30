import SourcePlanBoundNormalization

/-! Expand operation-only source annotations along actual computation syntax.
The proof reuses source footprints, declaration transport and finite capability
checks. Recorded bounds use the canonical empty spine, not a compact absent
node around a compound computation. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (Signature signature)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledSourceInterfaces (Declared)
open SourceRequestFootprints (Footprint)
open SourceScheduledAdaptationCompilation (requirements_prefix requirements_handler requirements_cell)
open SourcePlanBounds (ofCode)

variable [declarations : DeclarationPolicy]

mutual
/-- Expanded annotations expose every computation constructor. This is only
an annotation-shape judgment; permissions and validity remain independent. -/
def Code.Expanded {world dependencies scope} {hints : Hints scope}
    {plan : Plan dependencies} {forest : Forest hints} (source : Code world plan forest) : Prop :=
  match source with
  | .operations (plan := plan) _ _ _ => match plan with
      | .pure | .request => True
      | _ => False
  | .selected _ _ closing => ∀ disposes, (closing disposes).Expanded
  | .resume _ inside before after => inside.Expanded ∧ before.Expanded ∧ after.Expanded
  | .dispose _ closing before after => closing.Expanded ∧ before.Expanded ∧ after.Expanded
  | .sequence first second | .choice first second => first.Expanded ∧ second.Expanded
  | .handler _ body _ => body.Expanded
  | .cleanup body completion => body.Expanded ∧ completion.Expanded
  | .resource body => ∀ identity fresh, (body identity fresh).Expanded

def Retained.Expanded {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (source : Retained world forest outside) : Prop :=
  match source with
  | .operations interfaces => match interfaces with
      | .nil => True
      | _ => False
  | .plain code tail | .cleanup code tail => code.Expanded ∧ tail.Expanded
  | .handler tail | .cell tail | .running tail | .spent tail => tail.Expanded
  | .live saved tail => saved.Expanded ∧ tail.Expanded
end

/-- Source declaration evidence is kept through literal-plan signature
transport. The finite operation interface is expanded, not weakened into a
successful-target premise. -/
theorem expand_operations_signature
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {plan : Plan dependencies} {checking : Signature dependencies}
    {hints : Hints scope} {forest : Forest hints}
    (interface : Footprint checking required) (same : signature plan = checking)
    (declared : Declared world checking) (supplied : checkRequirements scope required = true) :
    ∃ annotation : Code world plan forest,
      annotation.Valid outward actions phases ∧
      ofCode annotation = SourcePlanBounds.Annotation.empty world plan ∧ annotation.Expanded := by
  induction interface generalizing scope world with
  | pure => cases plan; exact ⟨.operations [] .pure .pure, rfl, rfl, True.intro⟩
  | request => cases plan; exact ⟨.operations _ .request .request, supplied, rfl, True.intro⟩
  | handledRequest =>
      rename_i effect operation
      cases plan with
      | handler required plans body =>
          obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
          have recipes := SourcePlannedRecipeDeclarations.handled_request_declarations.signature_congr declarationsSame.symm
          cases body with
          | sequence initial request =>
              cases initial
              cases request
              refine ⟨.handler (plans := plans) (bounds := none) (legacy recipes)
                (.sequence (.operations [] .pure .pure)
                  (.selected (contract := ⟨true, some [], none⟩)
                    (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
                    (.hit ?_ ?_) (fun _ => .handler .nil) (fun _ => .operations .nil))),
                ?_, ?_, ?_⟩
              · simp [SourceDeclarationPlans.HandledRequest.table, ProtectionContracts.lookup]
              · simp [SourceDeclarationPlans.HandledRequest.families, SourceDependencyCapture.lookupDependencies]
              · dsimp only [Code.Valid, Retained.Valid]
                refine ⟨rfl, rfl, ?_, fun _ => rfl⟩
                apply SourceDependencyCapture.check_capture_iff.mpr
                exact .handler
                  (capture := .handler effect (SourceDeclarationPlans.HandledRequest.table operation)
                    (SourceDeclarationPlans.HandledRequest.families operation) .nil)
                  (tail := scope) (contract := ⟨true, some [], none⟩)
                  (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
                  (by simp [SourceDependencyCapture.select, SourceDeclarationPlans.HandledRequest.table,
                    SourceDeclarationPlans.HandledRequest.families, ProtectionContracts.lookup,
                    SourceDependencyCapture.lookupDependencies])
                  rfl rfl rfl (fun _ => .handler .nil)
              · rfl
              · exact ⟨True.intro, fun _ => True.intro⟩
  | sequence left right ihLeft ihRight => cases plan with
    | sequence firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
      cases declared with
      | sequence firstDeclared secondDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        obtain ⟨first, firstReady, firstBounds, firstExpanded⟩ := ihLeft firstSame firstDeclared
          (requirements_prefix (front := .plain _ .nil) (fun _ => rfl) supplied.1)
        obtain ⟨second, secondReady, secondBounds, secondExpanded⟩ := ihRight secondSame secondDeclared supplied.2
        exact ⟨.sequence first second, ⟨firstReady, secondReady⟩,
          (congrArg (fun bound => SourcePlanBounds.Annotation.sequence bound (ofCode second)) firstBounds).trans
            (congrArg (SourcePlanBounds.Annotation.sequence _) secondBounds), ⟨firstExpanded, secondExpanded⟩⟩
  | choice left right ihLeft ihRight => cases plan with
    | choice firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := Signature.choice.inj same
      cases declared with
      | choice firstDeclared secondDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        obtain ⟨first, firstReady, firstBounds, firstExpanded⟩ := ihLeft firstSame firstDeclared supplied.1
        obtain ⟨second, secondReady, secondBounds, secondExpanded⟩ := ihRight secondSame secondDeclared supplied.2
        exact ⟨.choice first second, ⟨firstReady, secondReady⟩,
          (congrArg (fun bound => SourcePlanBounds.Annotation.choice bound (ofCode second)) firstBounds).trans
            (congrArg (SourcePlanBounds.Annotation.choice _) secondBounds), ⟨firstExpanded, secondExpanded⟩⟩
  | handler body internal ih => cases plan with
    | handler required plans bodyPlan =>
      cases declared with
      | handler sourceDeclarations bodyDeclared =>
        obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
        have recipes := sourceDeclarations.signature_congr declarationsSame.symm
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        obtain ⟨body, ready, bounds, expanded⟩ := ih bodySame bodyDeclared (requirements_handler internal supplied.2)
        exact ⟨.handler (legacy recipes) body, ⟨supplied.1, ready⟩,
          congrArg (SourcePlanBounds.Annotation.handler none) bounds, expanded⟩
  | cleanup callback body ihCallback ihBody => cases plan with
    | cleanup callbackPlan bodyPlan =>
      obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
      cases declared with
      | cleanup callbackDeclared bodyDeclared =>
        simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
        obtain ⟨body, bodyReady, bodyBounds, bodyExpanded⟩ := ihBody bodySame bodyDeclared
          (requirements_prefix (front := .cleanup _ _ .nil) (fun _ => rfl) supplied.2)
        obtain ⟨callback, callbackReady, callbackBounds, callbackExpanded⟩ := ihCallback callbackSame callbackDeclared
          (requirements_prefix (front := .running .nil) (fun _ => rfl) supplied.1)
        exact ⟨.cleanup body callback, ⟨bodyReady, callbackReady⟩,
          (congrArg (fun bound => SourcePlanBounds.Annotation.cleanup bound (ofCode callback)) bodyBounds).trans
            (congrArg (SourcePlanBounds.Annotation.cleanup _) callbackBounds), ⟨bodyExpanded, callbackExpanded⟩⟩
  | resource body ih => cases plan with
    | resource plans => cases declared with
      | resource declarations =>
        have generated := fun identity fresh => ih identity
          (forest := Forest.cell (identity := identity) forest)
          (congrFun (Signature.resource.inj same) identity) (declarations identity fresh)
          (requirements_cell identity supplied)
        refine ⟨.resource (fun identity fresh => Classical.choose (generated identity fresh)),
          (fun identity fresh => (Classical.choose_spec (generated identity fresh)).1), ?_,
          (fun identity fresh => (Classical.choose_spec (generated identity fresh)).2.2)⟩
        simp only [ofCode, SourcePlanBounds.Annotation.empty]
        congr 1
        funext identity fresh
        exact (Classical.choose_spec (generated identity fresh)).2.1
  | weaken body included ih =>
      exact ih same declared (SourceContextualRequirements.check_requirements_subset included supplied)

/-- Expansion happens at the original receiver, before contextual rechecking.
The result has the exact normalized original bound spine and identical lookups. -/
theorem expand_operations
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (interface : SourceScheduledAdaptationCompilation.RequestFootprint plan required)
    (declared : Declared world (signature plan))
    (ready : (Code.operations (forest := forest) required interface declared).Valid outward actions phases) :
    ∃ annotation : Code world plan forest,
      annotation.Valid outward actions phases ∧
      ofCode annotation = (ofCode (Code.operations (forest := forest) required interface declared)).normalize := by
  obtain ⟨annotation, valid, bounds, _⟩ := expand_operations_signature legacy interface rfl declared ready
  exact ⟨annotation, valid, bounds⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.expand_operations_signature
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.expand_operations
