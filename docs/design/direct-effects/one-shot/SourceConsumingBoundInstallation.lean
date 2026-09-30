import SourceConsumingStoredBounds
import SourceAnnotatedRuntimeHandlers

/-! Handler registration transports retained bound packets at unchanged
activations. Installation records the source bounds and admission route in the
new frame; dormant captures retain their original packets as well. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingClauseAnnotations (ClauseBounds)
open SourceAnnotatedRuntime (Handler Stack)
open SourceScheduledHandlers (register register_agrees)

variable {families nextFamilies : SourceDependencyCapture.Families}
variable {required nextRequired : SourceContextualRechecking.Required}

def HandlerBounds.registries_congr {handler : Handler} (packet : HandlerBounds families handler)
    (same : families handler.erase = nextFamilies handler.erase) : HandlerBounds nextFamilies handler := by
  let data : (Σ plans : ClausePlans handler.clauses.erase (nextFamilies handler.erase), ClauseBounds plans) :=
    same ▸ ⟨packet.plans, packet.bounds⟩
  exact ⟨data.1, data.2, packet.admission⟩

theorem HandlerBounds.registries_congr_admission {handler : Handler} (packet : HandlerBounds families handler)
    (same : families handler.erase = nextFamilies handler.erase) :
    (packet.registries_congr same).admission = packet.admission := by
  rfl

theorem HandlerBounds.registries_congr_lookup {handler : Handler} (packet : HandlerBounds families handler)
    (same : families handler.erase = nextFamilies handler.erase) :
    (packet.registries_congr same).bounds.lookup operation held = packet.bounds.lookup operation held := by
  rcases packet with ⟨plans, bounds, admission⟩
  simp only [HandlerBounds.registries_congr]
  generalize before : families handler.erase = first at *
  generalize after : nextFamilies handler.erase = second at *
  cases same
  rfl

/-- Registry transport changes the family index while retaining source typing
at the same recorded plan. It does not reconstruct a declaration witness. -/
theorem HandlerBounds.registries_congr_source {handler : Handler} (packet : HandlerBounds families handler)
    (same : families handler.erase = nextFamilies handler.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table packet.plans) :
    SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table (packet.registries_congr same).plans := by
  rcases packet with ⟨plans, bounds, admission⟩
  change SourceAnnotatedSources.Declarations operations policy contracts world environment residual
    handler.effectInst answer handler.clauses table plans at source
  simp only [HandlerBounds.registries_congr]
  generalize before : families handler.erase = first at *
  generalize after : nextFamilies handler.erase = second at *
  cases same
  exact source

def FrameBounds.registries_congr {frame : SourceAnnotatedRuntime.Frame} (source : FrameBounds families frame)
    (agree : ∀ handler, handler.activation ∈ frame.erase.erase.activation → families handler = nextFamilies handler) :
    FrameBounds nextFamilies frame :=
  match source with
  | .plain => .plain
  | .handler packet => .handler (packet.registries_congr (agree _ List.mem_cons_self))
  | .cell => .cell
  | .armed => .armed
  | .running => .running
  | .closing => .closing
  | .retiring => .retiring

def StackBounds.registries_congr {stack : Stack} (source : StackBounds families stack)
    (agree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → families handler = nextFamilies handler) :
    StackBounds nextFamilies stack :=
  match source with
  | .nil => .nil
  | .push head tail =>
      .push (head.registries_congr (fun handler member => agree handler (List.mem_append_left _ member)))
        (tail.registries_congr (fun handler member => agree handler (List.mem_append_right _ member)))
  | .live saved tail =>
      .live (saved.registries_congr (fun handler member => agree handler (List.mem_append_left _ member)))
        (tail.registries_congr (fun handler member => agree handler (List.mem_append_right _ member)))
  | .spent tail => .spent (tail.registries_congr agree)

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem HandlerBounds.Admitted.registries_congr {handler : Handler} {packet : HandlerBounds families handler}
    (admitted : packet.Admitted world required)
    (sameFamily : families handler.erase = nextFamilies handler.erase)
    (sameRequired : required handler.erase = nextRequired handler.erase) :
    (packet.registries_congr sameFamily).Admitted world nextRequired := by
  rcases packet with ⟨plans, bounds, admission⟩
  cases admitted with
  | bounded route annotated checked =>
      change SourceConsumingClauseAnnotations.Declarations world plans at annotated
      change SourceConsumingClauseAnnotations.Bounded bounds annotated (required handler.erase) at checked
      change admission = .bounded at route
      obtain ⟨nextAnnotation, nextChecked⟩ :
          ∃ annotation : SourceConsumingClauseAnnotations.Declarations world
            ((HandlerBounds.mk plans bounds admission).registries_congr sameFamily).plans,
          SourceConsumingClauseAnnotations.Bounded
            ((HandlerBounds.mk plans bounds admission).registries_congr sameFamily).bounds
            annotation (required handler.erase) := by
        simp only [HandlerBounds.registries_congr]
        generalize before : families handler.erase = first at *
        generalize after : nextFamilies handler.erase = second at *
        cases sameFamily
        exact ⟨annotated, checked⟩
      exact .bounded route nextAnnotation (sameRequired ▸ nextChecked)
  | inherited route recipes =>
      change SourcePlannedRecipeDeclarations.Declarations (required handler.erase) plans at recipes
      change admission = .inherited at route
      have nextRecipes : SourcePlannedRecipeDeclarations.Declarations (required handler.erase)
          ((HandlerBounds.mk plans bounds admission).registries_congr sameFamily).plans := by
        simp only [HandlerBounds.registries_congr]
        generalize before : families handler.erase = first at *
        generalize after : nextFamilies handler.erase = second at *
        cases sameFamily
        exact recipes
      exact .inherited route (sameRequired ▸ nextRecipes)

theorem FrameBounds.Admitted.registries_congr {frame : SourceAnnotatedRuntime.Frame}
    {source : FrameBounds families frame} (admitted : source.Admitted world required)
    (familiesAgree : ∀ handler, handler.activation ∈ frame.erase.erase.activation → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ frame.erase.erase.activation → required handler = nextRequired handler) :
    (source.registries_congr familiesAgree).Admitted world nextRequired := by
  cases admitted with
  | plain => exact .plain
  | handler checked => exact .handler (checked.registries_congr
      (familiesAgree _ List.mem_cons_self) (requiredAgree _ List.mem_cons_self))
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

theorem StackBounds.Admitted.registries_congr {stack : Stack} {source : StackBounds families stack}
    (admitted : source.Admitted world required)
    (familiesAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → required handler = nextRequired handler) :
    (source.registries_congr familiesAgree).Admitted world nextRequired := by
  induction admitted with
  | nil => exact .nil
  | push head tail ih =>
      exact .push (head.registries_congr
          (fun handler member => familiesAgree handler (List.mem_append_left _ member))
          (fun handler member => requiredAgree handler (List.mem_append_left _ member)))
        (ih (fun handler member => familiesAgree handler (List.mem_append_right _ member))
          (fun handler member => requiredAgree handler (List.mem_append_right _ member)))
  | live saved tail ihSaved ihTail =>
      exact .live (ihSaved
          (fun handler member => familiesAgree handler (List.mem_append_left _ member))
          (fun handler member => requiredAgree handler (List.mem_append_left _ member)))
        (ihTail (fun handler member => familiesAgree handler (List.mem_append_right _ member))
          (fun handler member => requiredAgree handler (List.mem_append_right _ member)))
  | spent tail ih => exact .spent (ih familiesAgree requiredAgree)

end

/-- The exact source plans, bounds and proof route become the new handler's
packet. Fresh registration changes only its activation's registry entry. -/
def HandlerBounds.installed (handler : Handler) (plans : ClausePlans handler.clauses.erase clauseFamilies)
    (bounds : ClauseBounds plans) (admission : DeclarationRoute) :
    HandlerBounds (register families handler.activation clauseFamilies) handler :=
  (show HandlerBounds (fun _ => clauseFamilies) handler from ⟨plans, bounds, admission⟩).registries_congr
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true])

/-- Installation retains source typing at the actual recorded clause plans.
The existing structural declaration judgment is the alignment evidence. -/
theorem HandlerBounds.installed_source (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (route : DeclarationRoute)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table plans) :
    SourceAnnotatedSources.Declarations operations policy contracts world environment residual
      handler.effectInst answer handler.clauses table
      (HandlerBounds.installed (families := families) handler plans bounds route).plans := by
  exact HandlerBounds.registries_congr_source
    (show HandlerBounds (fun _ => clauseFamilies) handler from ⟨plans, bounds, route⟩)
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true]) source

theorem HandlerBounds.installed_lookup (handler : Handler) (plans : ClausePlans handler.clauses.erase clauseFamilies)
    (bounds : ClauseBounds plans) (admission : DeclarationRoute) :
    (HandlerBounds.installed (families := families) handler plans bounds admission).bounds.lookup operation held =
      bounds.lookup operation held :=
  HandlerBounds.registries_congr_lookup _ _

theorem HandlerBounds.installed_admission (handler : Handler) (plans : ClausePlans handler.clauses.erase clauseFamilies)
    (bounds : ClauseBounds plans) (admission : DeclarationRoute) :
    (HandlerBounds.installed (families := families) handler plans bounds admission).admission = admission := rfl

def StackBounds.install {stack : Stack} (source : StackBounds families stack) (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (admission : DeclarationRoute) (fresh : handler.activation ∉ stack.erase.erase.activations) :
    StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack) :=
  .push (.handler (HandlerBounds.installed handler plans bounds admission))
    (source.registries_congr (register_agrees fresh))

/-- Dispatch immediately selects precisely the packet installed from source. -/
theorem StackBounds.install_lookup {stack : Stack} (source : StackBounds families stack) (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (admission : DeclarationRoute) (fresh : handler.activation ∉ stack.erase.erase.activations) :
    (source.install handler plans bounds admission fresh).handlerAt handler.effectInst =
      some ⟨handler, HandlerBounds.installed handler plans bounds admission⟩ := by
  simp only [StackBounds.install, StackBounds.handlerAt, if_true]

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem StackBounds.Admitted.install {stack : Stack} {source : StackBounds families stack}
    (admitted : source.Admitted world required) (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (admission : DeclarationRoute) (fresh : handler.activation ∉ stack.erase.erase.activations)
    (declaration : (HandlerBounds.installed (families := families) handler plans bounds admission).Admitted
      world (register required handler.activation declarationRequired)) :
    (source.install handler plans bounds admission fresh).Admitted
      world (register required handler.activation declarationRequired) :=
  .push (.handler declaration) (admitted.registries_congr (register_agrees fresh) (register_agrees fresh))

/-- The inherited route uses the old structural proof for the actual source
clauses. It adds no assumption about a future captured body. -/
theorem HandlerBounds.installed_inherited (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations declarationRequired plans) :
    (HandlerBounds.installed (families := families) handler plans bounds .inherited).Admitted
      world (register required handler.activation declarationRequired) := by
  have before : HandlerBounds.Admitted world (fun _ => declarationRequired)
      (show HandlerBounds (fun _ => clauseFamilies) handler from ⟨plans, bounds, .inherited⟩) :=
    .inherited rfl recipes
  exact before.registries_congr
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true])
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true])

theorem HandlerBounds.installed_bounded (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (annotated : SourceConsumingClauseAnnotations.Declarations world plans)
    (checked : SourceConsumingClauseAnnotations.Bounded bounds annotated declarationRequired) :
    (HandlerBounds.installed (families := families) handler plans bounds .bounded).Admitted
      world (register required handler.activation declarationRequired) := by
  have before : HandlerBounds.Admitted world (fun _ => declarationRequired)
      (show HandlerBounds (fun _ => clauseFamilies) handler from ⟨plans, bounds, .bounded⟩) :=
    .bounded rfl annotated checked
  exact before.registries_congr
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true])
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true])

/-- Derive admission for the actual installed clauses from the checking
declaration's structural derivation. Reindexing preserves both modes' recorded
bounds; signature transport supplies the missing admission proof. -/
theorem HandlerBounds.installed_from_signature
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (handler : Handler) {checking : ClausePlans checkingClauses clauseFamilies}
    (actual : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds checking)
    (annotated : SourceConsumingClauseAnnotations.Declarations world checking)
    (checked : SourceConsumingClauseAnnotations.Bounded bounds annotated declarationRequired)
    (same : SourcePlanSignatures.clauseSignatures checking = SourcePlanSignatures.clauseSignatures actual) :
    (HandlerBounds.installed (families := families) handler actual (bounds.reindex actual) .bounded).Admitted
      world (register required handler.activation declarationRequired) ∧
    ∀ operation held,
      (HandlerBounds.installed (families := families) handler actual (bounds.reindex actual) .bounded).bounds.lookup operation held =
        bounds.lookup operation held := by
  obtain ⟨actualAnnotation, actualChecked⟩ := checked.signature_congr transport same
  refine ⟨HandlerBounds.installed_bounded handler actual (bounds.reindex actual) actualAnnotation actualChecked, ?_⟩
  intro operation held
  rw [HandlerBounds.installed_lookup, ClauseBounds.lookup_reindex]

theorem StackBounds.Admitted.install_from_signature {stack : Stack} {source : StackBounds families stack}
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    (admitted : source.Admitted world required) (handler : Handler)
    {checking : ClausePlans checkingClauses clauseFamilies}
    (actual : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds checking)
    (annotated : SourceConsumingClauseAnnotations.Declarations world checking)
    (checked : SourceConsumingClauseAnnotations.Bounded bounds annotated declarationRequired)
    (same : SourcePlanSignatures.clauseSignatures checking = SourcePlanSignatures.clauseSignatures actual)
    (fresh : handler.activation ∉ stack.erase.erase.activations) :
    (source.install handler actual (bounds.reindex actual) .bounded fresh).Admitted
      world (register required handler.activation declarationRequired) :=
  admitted.install handler actual (bounds.reindex actual) .bounded fresh
    (HandlerBounds.installed_from_signature transport handler actual bounds annotated checked same).1

/-- The stored annotations follow the actual handler-entry transition. This
preserves declaration admission and exact metadata, independently of the rich
source-state proof; it does not assume a valid successor state. -/
theorem StackBounds.Admitted.enter_handler {stack : Stack} {source : StackBounds families stack}
    (admitted : source.Admitted world required) (handler : Handler)
    (plans : ClausePlans handler.clauses.erase clauseFamilies) (bounds : ClauseBounds plans)
    (admission : DeclarationRoute) (fresh : handler.activation ∉ stack.erase.erase.activations)
    (declaration : (HandlerBounds.installed (families := families) handler plans bounds admission).Admitted
      world (register required handler.activation declarationRequired)) (code : SourceAnnotatedCode.Term) :
    ScopedExecution.RawStep
      ⟨.handle (Instantiation.freezeEffect handler.effectInst) code.erase handler.clauses.erase, handler.scope, stack.erase⟩
      ⟨code.erase, handler.scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
    (source.install handler plans bounds admission fresh).Admitted
      world (register required handler.activation declarationRequired) :=
  ⟨.enterHandler handler.erase code.erase stack.erase,
    admitted.install handler plans bounds admission fresh declaration⟩

end
end Ash.OneShot.SourceConsumingStoredBounds

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.registries_congr_admission
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.registries_congr_lookup
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.Admitted.registries_congr
#print axioms Ash.OneShot.SourceConsumingStoredBounds.FrameBounds.Admitted.registries_congr
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.registries_congr
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.install_lookup
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.install

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_lookup
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_admission
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_inherited
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_bounded
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.enter_handler

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_from_signature
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.install_from_signature

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_source

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.registries_congr_source
