import SourceScheduledCapturePrep
import SourceScheduledRequirements
import SourceScheduledProviderChecks
import SourceScheduledFreshRequests

/-! Structural consuming recipes compile against actual retained plans,
including local resource operations, pure cleanup and internally handled request
prefixes before continuation use. General handler and effectful-cleanup recipe
rules remain a separate obligation. -/
namespace Ash.OneShot.SourceScheduledClauses
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourcePlannedRecipeDeclarations (Selected)
open SourcePlannedTyping (Contract)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceContextualHints (Hints checkRequirements)
open SourceContextualHintChecking (Compatible)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourcePlannedClauseRecipes (Recipe)
open SourceContextualClauses (RequestCapability)
open OwnerPhaseTransitions (introduce spend)
open SourceScheduledProviders (providerForest)
open SourceScheduledProviderChecks (provider_local)
open SourceContextualRequirements (provider_capability provider_member capability_plain capability_live)

section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem silent {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (empty : dependencies.Silent) : Local outward actions phases world plan forest := by
  induction empty generalizing scope with
  | pure => cases plan; exact .pure
  | sequence first second ihFirst ihSecond => cases plan with
    | sequence left right => exact .sequence ihFirst ihSecond

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem request_prefix {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints} {plan : Plan dependencies}
    (capability : RequestCapability effect operation tailScope)
    (next : Local outward actions phases world plan (.live (owner := owner) saved tail)) :
    Local outward actions phases world (.sequence (.sequence .pure (.request (effect := effect) (operation := operation))) plan)
      (.live (owner := owner) saved tail) := by
  refine .sequence (.sequence .pure (.request capability.request ?_)) next
  intro captured outside capturedHints outsideHints contract modes cut capturedForest outsideForest same disposes
  have selected := cut.lookup
  cases capability with
  | builtin found =>
      simp only [SourceDependencyCapture.select, found, Option.map_some, SourceDependencyCapture.Selection.prepend] at selected
      cases selected
  | handler found resumesOnly rows bodies =>
      simp only [SourceDependencyCapture.select, found, Option.map_some, SourceDependencyCapture.Selection.prepend, Option.some.injEq] at selected
      cases selected
      simp [resumesOnly] at disposes

/-- Actual source witnesses may differ from the canonical internally handled
request while retaining its signature. Reuse declaration transport and exact
request capture checking instead of assuming a complete body check. -/
theorem handled_request_local_with {hints : Hints scope} {forest : Forest hints}
    (admitRecipe : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {plan : Plan (SourceDeclarationPlans.HandledRequest.dependencies effect operation)}
    (same : signature plan = signature (SourceDeclarationPlans.HandledRequest.plan effect operation)) :
    Local outward actions phases world plan forest := by
  cases plan with
  | handler required declarations body =>
      obtain ⟨rfl, declarationsSame, bodySame⟩ := SourcePlanSignatures.Signature.handler.inj same
      have recipes := SourcePlannedRecipeDeclarations.handled_request_declarations.signature_congr declarationsSame.symm
      refine .handler (admitRecipe recipes) (certifyRecipe recipes) rfl ?_
      cases body with
      | sequence initial request =>
          cases initial
          cases request
          refine .sequence .pure ?_
          apply SourceScheduledFreshRequests.request_from_schedule (fun checked => SourceScheduledChecks.DeclarationProjection.project checked)
            (contract := ⟨true, some [], none⟩) (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
            (.hit (by simp [SourceDeclarationPlans.HandledRequest.table, lookup])
              (by simp [SourceDeclarationPlans.HandledRequest.families, lookupDependencies]))
          · exact .handler
              (capture := .handler effect (SourceDeclarationPlans.HandledRequest.table operation)
                (SourceDeclarationPlans.HandledRequest.families operation) .nil)
              (tail := scope) (contract := ⟨true, some [], none⟩)
              (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
              (by simp [SourceDependencyCapture.select,
              SourceDeclarationPlans.HandledRequest.table, SourceDeclarationPlans.HandledRequest.families,
              lookup, lookupDependencies]) rfl rfl rfl (fun _ => .handler .nil)
          · intro permission; exact .handler .nil
          · intro permission; exact .nil

/-- Recomposition checks each constructor against the retained pieces. These
premises are derived from pre-capture checks by `Recipe.capture` below. -/
theorem compile_providers_with {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (admitRecipe : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans provided)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        saved.forClosing (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) savedHints waitingHints) .nil)
    (tailCompatible : Compatible waitingHints .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (providerForest provided (.live (owner := owner) saved waiting)) := by
  induction recipe generalizing world with
  | resume permission =>
      exact provider_local _ (SourceScheduledScopedInvocations.resume_from_parts .hit known permission available inside .nil outside
        (SourcePlannedRecomposition.resume_compatible compatible))
  | dispose permission =>
      obtain ⟨unprotected, route, closing⟩ := disposal permission
      exact provider_local _ (SourceScheduledScopedInvocations.dispose_from_parts .hit known permission available unprotected route closing .nil outside
        (SourcePlannedRecomposition.dispose_compatible tailCompatible))
  | silent empty rest ih => exact .sequence (silent empty) (ih inside outside disposal supplied)
  | request rest ih =>
      exact .sequence (.sequence .pure (SourceScheduledScopedInvocations.request_from_capability (capability_plain
        (provider_capability _ (capability_live (supplied _ List.mem_cons_self))))))
        (ih inside outside disposal (fun request member => supplied request (List.mem_cons_of_mem _ member)))
  | localRequest member rest ih =>
      exact .sequence (.sequence .pure (SourceScheduledScopedInvocations.request_from_capability (capability_plain (provider_member member))))
        (ih inside outside disposal supplied)
  | handledRequest shape rest ih =>
      exact .sequence (handled_request_local_with admitRecipe certifyRecipe (shape owner)) (ih inside outside disposal supplied)
  | resource body ih =>
      apply Local.resource
      intro identity fresh
      apply ih identity
      · exact SourceScheduledTransport.pending_transport_world inside
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)
      · exact SourceScheduledTransport.pending_transport_world outside
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)
      · intro permitted
        obtain ⟨held, route, closing⟩ := disposal permitted
        exact ⟨held, route, SourceScheduledTransport.pending_transport_world closing
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _)⟩
      · exact supplied
  | cleanup rest ih => exact SourceScheduledNeutralChecks.pure_cleanup (ih inside outside disposal supplied)
  | choice left right ihLeft ihRight =>
      exact .choice (ihLeft inside outside disposal (fun request member => supplied request (List.mem_append_left _ member)))
        (ihRight inside outside disposal (fun request member => supplied request (List.mem_append_right _ member)))

theorem compile_with {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (admitRecipe : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        saved.forClosing (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) savedHints waitingHints) .nil)
    (tailCompatible : Compatible waitingHints .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (.live (owner := owner) saved waiting) :=
  compile_providers_with admitRecipe certifyRecipe recipe known available inside outside disposal compatible tailCompatible supplied

/-- The actual clause plan is checked using only judgments before capture,
fresh-owner facts and the declaration's finite operation requirements. -/
theorem capture_with {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (admitRecipe : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans)
    {forest : Forest hints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : rights.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    Local outward (actions.insert owner rights) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner rights) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  obtain ⟨live, inside, outside, disposal⟩ := SourceScheduledCapturePrep.captured_checks cut request retained fresh consumed
  obtain ⟨liveCompatible, tailCompatible⟩ := SourcePlannedCapturePrep.cut_compatible (owner := owner) cut.erase compatible
  exact ⟨compile_with admitRecipe certifyRecipe recipe (by simp [Syntax.UsageTickets.insert]) (by simp [introduce]) inside outside
    (fun permitted => disposal (permission permitted)) liveCompatible tailCompatible
    (SourceContextualRequirements.check_requirements_iff.mp supplied), live⟩

/-- Declaration selection and pre-capture checks suffice for the selected
actual clause plan. Both offered modes use the same independent rights. -/
theorem declaration_capture_with {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (admitRecipe : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {declarations : ClausePlans clauses families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (selected : Selected operation captured.held declarations parameter binder body plans)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : body.requiredActions.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    SourceDependencyCapture.modeDependencies captured.held modes = some family ∧
    Local outward (actions.insert owner body.requiredActions) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner body.requiredActions) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  obtain ⟨needed, recipe, included⟩ := recipes.selected selected
  refine ⟨?_, capture_with admitRecipe certifyRecipe recipe cut request retained compatible fresh consumed permission
    (SourceContextualRequirements.check_requirements_subset included supplied)⟩
  simpa only [declared, Option.bind_some] using selected.lookup


end

/-- Specialize the policy-parametric proof to the original recipe policy. -/
theorem handled_request_local {hints : Hints scope} {forest : Forest hints}
    {plan : Plan (SourceDeclarationPlans.HandledRequest.dependencies effect operation)}
    (same : signature plan = signature (SourceDeclarationPlans.HandledRequest.plan effect operation)) :
    Local outward actions phases world plan forest :=
  handled_request_local_with (fun checked => checked) (fun checked => checked.certified) same

/-- Specialize the policy-parametric proof to the original recipe policy. -/
theorem compile_providers {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans provided)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        saved.forClosing (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) savedHints waitingHints) .nil)
    (tailCompatible : Compatible waitingHints .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (providerForest provided (.live (owner := owner) saved waiting)) :=
  compile_providers_with (fun checked => checked) (fun checked => checked.certified) recipe known available inside outside disposal compatible tailCompatible supplied

/-- Specialize the policy-parametric proof to the original recipe policy. -/
theorem compile {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans)
    (known : actions owner = some rights) (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (.spent (owner := owner) waiting))
    (outside : Pending outward actions (spend phases owner) world waiting .nil)
    (disposal : rights.dispose = true → captured.held = false ∧
      SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
      Pending outward actions (spend phases owner) world
        saved.forClosing (.running (.spent (owner := owner) waiting)))
    (compatible : Compatible (.live (owner := owner) savedHints waitingHints) .nil)
    (tailCompatible : Compatible waitingHints .nil)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    Local outward actions phases world (plans owner) (.live (owner := owner) saved waiting) :=
  compile_with (fun checked => checked) (fun checked => checked.certified) recipe known available inside outside disposal compatible tailCompatible supplied

/-- Specialize the policy-parametric proof to the original recipe policy. -/
theorem capture {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : Recipe rights required plans)
    {forest : Forest hints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : rights.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    Local outward (actions.insert owner rights) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner rights) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil :=
  capture_with (fun checked => checked) (fun checked => checked.certified) recipe cut request retained compatible fresh consumed permission supplied

/-- Specialize the policy-parametric proof to the original recipe policy. -/
theorem declaration_capture {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (selected : Selected operation captured.held declarations parameter binder body plans)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : body.requiredActions.dispose = true → contract.dispose = true)
    (supplied : checkRequirements tail required = true) :
    SourceDependencyCapture.modeDependencies captured.held modes = some family ∧
    Local outward (actions.insert owner body.requiredActions) (introduce phases owner) world (plans owner)
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner body.requiredActions) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil :=
  declaration_capture_with (fun checked => checked) (fun checked => checked.certified) recipes selected declared cut request retained compatible fresh consumed permission supplied

/-- The actual source-selected plan may use every constructor. Its explicit
site obligations are checked at the captured forest; no restricted recipe or
complete successor-state premise occurs in this rule. Deriving the obligations
at each source request remains a separate admission obligation. -/
theorem capture_body_from_requirements
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {plans : ClausePlans clauses families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (declared : lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (supplied : ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      Selected operation captured.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
        (introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation captured.held plans parameter binder code bodies ∧
      modeDependencies captured.held modes = some family ∧
      Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourcePlannedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close, chosen, body⟩ :=
    SourcePlannedSelectedSources.selected_body source selected found available
  obtain ⟨live, inside, outside, disposal⟩ :=
    SourceScheduledCapturePrep.captured_checks cut request retained fresh consumed
  have offeredFamily : modeDependencies captured.held modes = some family := by
    simpa only [declared, Option.bind_some] using chosen.lookup
  exact ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, SourceScheduledRequirements.compile _ _ _ (supplied chosen), live, body owner⟩

/-- Source typing and execution checking now select the same actual clause
plan. This is a capture component, before clause substitution and runtime-store
integration; it does not assert preservation of an entire runtime state. -/
theorem capture_body {plans : ClausePlans clauses families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required plans)
    (clauseModes : SourceTemplates.ClauseModes clauses table)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (declared : lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (supplied : checkRequirements tail required = true) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation captured.held plans parameter binder code bodies ∧
      modeDependencies captured.held modes = some family ∧
      Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourcePlannedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  apply capture_body_from_requirements source selected found available declared cut request retained fresh consumed
  intro family bodies chosen
  obtain ⟨actual, actualFound, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected clauseModes
  cases Option.some.inj (found.symm.trans actualFound)
  obtain ⟨offeredFamily, checked, pending⟩ := declaration_capture recipes chosen declared cut request retained compatible fresh consumed
    disposalPermission supplied
  exact SourceScheduledRequirements.necessary checked

end Ash.OneShot.SourceScheduledClauses

#print axioms Ash.OneShot.SourceScheduledClauses.silent
#print axioms Ash.OneShot.SourceScheduledClauses.request_prefix
#print axioms Ash.OneShot.SourceScheduledClauses.compile
#print axioms Ash.OneShot.SourceScheduledClauses.capture

#print axioms Ash.OneShot.SourceScheduledClauses.declaration_capture
#print axioms Ash.OneShot.SourceScheduledClauses.capture_body

#print axioms Ash.OneShot.SourceScheduledClauses.capture_body_from_requirements

#print axioms Ash.OneShot.SourceScheduledClauses.compile_providers

#print axioms Ash.OneShot.SourceScheduledClauses.handled_request_local

#print axioms Ash.OneShot.SourceScheduledClauses.handled_request_local_with

#print axioms Ash.OneShot.SourceScheduledClauses.compile_providers_with

#print axioms Ash.OneShot.SourceScheduledClauses.compile_with

#print axioms Ash.OneShot.SourceScheduledClauses.capture_with

#print axioms Ash.OneShot.SourceScheduledClauses.declaration_capture_with
