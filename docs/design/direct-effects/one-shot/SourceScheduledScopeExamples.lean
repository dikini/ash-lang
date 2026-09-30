import SourceScheduledScopedInvocations
import SourceScheduledNeutralChecks
import SourceScheduledClauses
import SourceScheduledProviderChecks
import SourceScheduledHandlerRequests
import SourceScheduledHandlerInvocations
import SourceScheduledFreshRequests
import SourceScheduledHandlerTransport
import SourceScheduledHandlerAdaptation

/-! Concrete checks for scope-bearing clauses and a failed transport rule.
These are local source-checker examples, not complete admitted executions. -/
namespace Ash.OneShot.SourceScheduledScopeExamples
open ScopedExpressions ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledScopedInvocations
open SourceContextualClauses (RequestCapability)
open SourceDependencyCapture (select check_capture_iff)


open SourceDependencyCapture.Examples (effectE effectF resumeTable resumeDependencies)
open SourceDependencyHandlerGap (rights actions phases)

def savedHints : Hints (.plain (.request effectF 0) .nil) := .plain .nil
def saved : Forest savedHints := .plain .request .nil
def tailHints : Hints (SourceDependencyCapture.Examples.handlerF .nil) := .handler [] .nil
def tail : Forest tailHints := .handler .nil

def nestedHints : Hints (.handler effectE [] [] (.cell 17 (.cleanup [] .pure .nil))) :=
  .handler [] (.cell (.cleanup .nil))
def nested : Forest nestedHints := .handler (.cell (.cleanup .pure .nil))

/-- The saved request resumes through a handler, resource and armed cleanup
scope in the caller. Its operation still reaches the existing outer handler. -/
theorem nested_resume : Local [] actions phases [17] (.invoke (key := ⟨19, .resume⟩))
    (nested.append (.live (owner := 19) saved tail)) := by
  apply resume_from_parts (front := nested) (saved := saved) (tail := tail)
    (.handler (.cell (.cleanup .hit))) rfl rfl rfl
  · exact .plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil
  · exact .handler rfl (.cell (.cleanup .pure .nil))
  · exact .handler rfl .nil
  · exact SourceContextualHintChecking.check_iff _ |>.mp (by rfl)

def resumeClause := SourceDeclarationPlans.Plan.handler (effect := effectE) (table := []) [] .nil
  (.resource (fun _ => .cleanup (needs := []) .pure (.invoke (key := ⟨19, .resume⟩))))

/-- The complete local clause plan installs all three scope constructors,
with the invocation inside their bodies rather than after a silent prefix. -/
theorem resume_clause_scopes : Local [] actions phases [] resumeClause (.live (owner := 19) saved tail) := by
  apply SourceScheduledRequirements.compile_from_templates
  intro requirement atWorld frontScope frontHints front source
  cases source with
  | install => exact ⟨.nil, .nil, rfl⟩
  | handler next => cases next with
    | resource fresh next => cases next with
      | callback next => cases next
      | cleanup next => cases next with
        | resume =>
            apply SourceScheduledRequirements.resume_iff.mpr
            apply resume_from_parts (front := .cleanup (needs := []) .pure (.cell
              (.handler (effect := effectE) (table := []) (families := []) (required := []) .nil)))
              (saved := saved) (tail := tail) (.cleanup (.cell (.handler .hit))) rfl rfl rfl
            · exact .plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil
            · exact .cleanup .pure (.cell (.handler rfl .nil))
            · exact .handler rfl .nil
            · exact SourceContextualHintChecking.check_iff _ |>.mp (by rfl)

def closingHints : Hints (.cleanup [effectF] (.request effectF 0) .nil) := .cleanup .nil
def closing : Forest closingHints := .cleanup .request .nil
def disposeActions : Syntax.UsageTickets := fun _ => some ⟨false, true⟩
def disposeClause := SourceDeclarationPlans.Plan.handler (effect := effectE) (table := []) [] .nil
  (.resource (fun _ => .cleanup (needs := []) .pure (.invoke (key := ⟨19, .dispose⟩))))

/-- Disposal beneath the same scopes checks an effectful retained callback
under running protection, while the resource and caller cleanup remain outside. -/
theorem dispose_clause_scopes : Local [effectF] disposeActions phases [] disposeClause
    (.live (owner := 19) closing tail) := by
  apply Local.handler (admission := SourceScheduledChecks.recipePolicy) .nil .nil rfl
  apply Local.resource
  intro identity fresh
  apply Local.cleanup
  · apply dispose_from_parts (front := .cleanup (needs := []) .pure (.cell (identity := identity)
      (.handler (effect := effectE) (table := []) (families := []) (required := []) .nil)))
      (saved := closing) (tail := tail) (.cleanup (.cell (.handler .hit))) rfl rfl rfl rfl
      (SourceDependencyCapture.check_closing_iff.mp (by rfl))
    · exact .cleanup (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil
    · exact .cleanup .pure (.cell (.handler rfl .nil))
    · exact .handler rfl .nil
    · exact SourceContextualHintChecking.check_iff _ |>.mp (by rfl)
  · exact .pure

/-- The same saved request is valid before inserting a caller interpretation. -/
theorem head_resume : Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
    (.live (owner := 19) saved tail) := by
  apply SourceScheduledRecomposition.resume_clause rfl rfl rfl
  · exact .plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil
  · exact .handler rfl .nil
  · exact SourceContextualHintChecking.check_iff _ |>.mp (by rfl)

def shadowHints : Hints (.handler effectF [] [] .nil) := .handler [] .nil
def shadow : Forest shadowHints := .handler .nil

/-- The dormant saved code checks at its original receiving tail, and the
independent resume permission/phase/handler-requirement test succeeds. -/
theorem shadowed_preconditions :
    Pending [] actions phases [] (shadow.append (.live (owner := 19) saved tail)) .nil ∧
    (SourceContextualInvocationHints.checkResume actions phases 19
      (shadowHints.append (.live (owner := 19) savedHints tailHints))).isSome = true := by
  constructor
  · exact .handler rfl (.live
      (.plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil)
      (.handler rfl .nil))
  · decide

/-- Those preconditions cannot justify arbitrary handler insertion around
resume. The nearer exact interpretation lacks the requested operation. -/
theorem shadowed_resume_rejected :
    ¬ Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
      (shadow.append (.live (owner := 19) saved tail)) := by
  intro checked
  have inside := ((resume_iff (front := shadow) (saved := saved) (tail := tail) (.handler .hit)).mp checked).2.1
  cases inside with
  | plain request rest =>
      have guarded := SourceDependencySchemes.checked_request request.erase.erase
      change false = true at guarded
      cases guarded

/-- Reuse the existing missing-operation counterexample: a structural
adaptation cannot bypass the callback's nearest-handler check. -/
theorem shadowing_adaptation_rejected :
    ¬ SourceScheduledHandlerAdaptation.Adapt [] actions (.handler effectF [] [] []) phases []
      (.invoke (key := ⟨19, .resume⟩)) (.live (owner := 19) saved tail)
      (shadow.append (.live (owner := 19) saved tail)) := by
  intro adapted
  exact shadowed_resume_rejected (adapted.sound head_resume)


def protectedHints : Hints (.running (.handler effectF SourceDependencyCapture.Examples.disposeTable
    SourceDependencyCapture.Examples.disposeDependencies .nil)) := .running (.handler [] .nil)
def protectedCaller : Forest protectedHints := .running (.handler .nil)

/-- The failure is not limited to missing operations. This nearer handler has
the requested operation, but disposal would capture running cleanup protection. -/
theorem protected_override_rejected :
    Pending [] actions phases [] (protectedCaller.append (.live (owner := 19) saved tail)) .nil ∧
    (SourceContextualInvocationHints.checkResume actions phases 19
      (protectedHints.append (.live (owner := 19) savedHints tailHints))).isSome = true ∧
    ¬ Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
      (protectedCaller.append (.live (owner := 19) saved tail)) := by
  refine ⟨.running (.handler rfl (.live
      (.plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil)
      (.handler rfl .nil))), by decide, ?_⟩
  intro checked
  have inside := ((resume_iff (front := protectedCaller) (saved := saved) (tail := tail)
    (.running (.handler .hit))).mp checked).2.1
  cases inside with
  | plain request rest =>
      have guarded := SourceDependencySchemes.checked_request request.erase.erase
      change false = true at guarded
      cases guarded

/-- Wrapping a consumer reuses its existing proof, including rechecking an
effectful saved request when the caller's cleanup is inserted at resumption. -/
theorem cleanup_resume : Local [] actions phases []
    (.cleanup (needs := []) .pure (.invoke (key := ⟨19, .resume⟩)))
    (.live (owner := 19) saved tail) :=
  SourceScheduledNeutralChecks.pure_cleanup head_resume

/-- The same rule composes with an already checked handler/resource/cleanup
clause whose captured completion performs an effectful request. -/
theorem cleanup_dispose : Local [effectF] disposeActions phases []
    (.cleanup (needs := []) .pure disposeClause) (.live (owner := 19) closing tail) :=
  SourceScheduledNeutralChecks.pure_cleanup dispose_clause_scopes

/-- Pure cleanup is not an equality of closing schedules. The callback must
still be represented, scheduled and completed by the existing runtime rules. -/
theorem pure_cleanup_changes_closing :
    (SourceDependencyCapture.Scope.cleanup [] .pure .nil).forClosing ≠
      SourceDependencyCapture.Scope.nil.forClosing := by
  intro same
  cases same

open SourceDependencyCapture.Examples (disposeTable disposeDependencies)
def disposingHints : Hints (SourceDependencyCapture.Examples.handlerE .nil) := .handler [] .nil
def disposing : Forest disposingHints := .handler .nil

private theorem disposing_request : Local [] actions phases []
    (.request (effect := effectE) (operation := 0)) disposing := by
  apply Local.request
  · apply SourceDependencyChecks.Local.request_selected (captured := SourceDependencyCapture.Examples.handlerE .nil)
      (tail := .nil) (by rfl)
    · exact SourceDependencyCapture.check_capture_iff.mpr (.handler rfl rfl rfl rfl (fun _ => .handler .nil))
    · intro permission; exact .nil
    · intro permission; exact .handler .nil
  · intro captured outside savedHints outsideHints contract modes cut savedForest outsideForest same permission
    cases cut with
    | hit known declared =>
      cases savedForest with
      | handler rest => cases rest; exact .nil
    | handler different next => exact False.elim (different rfl)

/-- A disposing request really captures the new callback. This exercises the
closing-forest transport, not only the resume-only request shortcut. -/
theorem cleanup_disposing_request : Local [] actions phases []
    (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0))) disposing :=
  SourceScheduledNeutralChecks.pure_cleanup disposing_request

/-- Repeated wrappers compose without dropping either captured callback. -/
theorem nested_cleanup_disposing_request : Local [] actions phases []
    (.cleanup (needs := []) .pure
      (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0)))) disposing :=
  SourceScheduledNeutralChecks.pure_cleanup cleanup_disposing_request

namespace Providers

/-- Resource bodies can use the newly acquired provider before consuming their
continuation. The original waiting tail supplies no such resource operation.
This checks the actual local plan; declaration-recipe admission remains separate. -/
def resourceBody := SourceDeclarationPlans.Plan.resource (fun identity =>
  .sequence (.request (effect := .cell identity) (operation := 0)) (.invoke (key := ⟨19, .resume⟩)))

theorem local_resource_request : Local [] actions phases [] resourceBody (.live (owner := 19) saved tail) := by
  apply Local.resource
  intro identity fresh
  apply Local.sequence
  · exact request_from_capability (.builtin (identity := identity) (by simp [select, SourceDependencyCapture.Selection.prepend]))
  · apply SourceScheduledProviderChecks.local_transport (changed := .here)
    exact SourceScheduledTransport.local_transport_world head_resume
      (fun _ available => available) (fun _ _ known => known) (by intro _ member; cases member)

/-- The inserted provider can preempt an existing source handler, including
inside the source code restored by a resume. -/
def handledHints : Hints (.handler (.cell 4) resumeTable resumeDependencies .nil) := .handler [] .nil
def handled : Forest handledHints := .handler .nil
def requestedHints : Hints (.plain (.request (.cell 4) 0) .nil) := .plain .nil
def requested : Forest requestedHints := .plain .request .nil

private theorem original_resume : Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
    (.live (owner := 19) requested handled) := by
  apply SourceScheduledRecomposition.resume_clause rfl rfl rfl
  · exact .plain (request_from_capability (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil
  · exact .handler rfl .nil
  · exact SourceContextualHintChecking.check_iff _ |>.mp (by rfl)

theorem resume_changes_interpreter :
    Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
      (.cell (identity := 4) (.live (owner := 19) requested handled)) ∧
    select (.cell 4) 0 (.cell 4 (.spent 19 (.handler (.cell 4) resumeTable resumeDependencies .nil))) =
      some (.builtin 4) ∧
    select (.cell 4) 0 (.spent 19 (.handler (.cell 4) resumeTable resumeDependencies .nil)) ≠ some (.builtin 4) :=
  ⟨SourceScheduledProviderChecks.local_transport original_resume .here, rfl, by intro impossible; cases impossible⟩

/-- The disposing-request schedule retains an inserted cell through an armed
callback, using the general transport rather than a separately checked schedule. -/
theorem disposing_request_schedule : Local [] actions phases []
    (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0)))
    (.cell (identity := 4) disposing) :=
  SourceScheduledProviderChecks.local_transport cleanup_disposing_request .here

/-- Reuse the existing disposing-cleanup proof. The new handler is inside
the captured prefix and disappears from the same actual closing schedule. -/
theorem handler_inside_disposing_capture : Local [] actions phases []
    (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0)))
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := []) disposing) := by
  cases cleanup_disposing_request with
  | cleanup body completion =>
      apply Local.cleanup ?_ .pure
      apply SourceScheduledHandlerTransport.request_transport (.cleanup .here) body
      · exact check_capture_iff.mp (by decide)
      · intro captured tail savedHints waitingHints saved waiting contract modes intercepted disposes
        have same : (⟨false, some [], some []⟩ : ClauseContract) = contract := Option.some.inj intercepted.entry.1
        cases same
        cases disposes
      · intro captured tail savedHints waitingHints saved waiting contract modes oldCut disposes
          dependencies oldScope targetScope plan oldHints targetHints old target site inserted checked
        cases oldCut with
        | cleanup next => cases next with
          | hit known declared =>
              cases site with
              | callback => exact .pure
              | cleanup next => cases next
          | handler different next => exact False.elim (different rfl)

/-- The inserted handler is in the selected disposing handler's waiting
scope. Reuse its original captured callback and transport each actual code
site; no replacement pending schedule is supplied. -/
theorem handler_in_disposal_waiting : Local [] actions phases []
    (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0)))
    (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := [])
      (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := []) .nil)) := by
  cases cleanup_disposing_request with
  | cleanup body completion =>
      apply Local.cleanup ?_ .pure
      apply SourceScheduledHandlerTransport.request_transport (.cleanup (.handler .here)) body
      · exact check_capture_iff.mp (by decide)
      · intro captured tail savedHints waitingHints saved waiting contract modes intercepted disposes
        have same : (⟨false, some [], some []⟩ : ClauseContract) = contract := Option.some.inj intercepted.entry.1
        cases same
        cases disposes
      · intro captured tail savedHints waitingHints saved waiting contract modes oldCut disposes
          dependencies oldScope targetScope plan oldHints targetHints old target site inserted checked
        cases oldCut with
        | cleanup next => cases next with
          | hit known declared =>
              cases site with
              | callback => exact .pure
              | cleanup next => cases next
          | handler different next => exact False.elim (different rfl)

/-- Existing independent resumptive capabilities also cover a handler that
takes over an operation formerly supplied by a builtin, beneath a pending
sequencing frame. The selected interpretation is allowed to change. -/
theorem handler_preempts_builtin_request : Local [] actions phases []
    (.request (effect := .cell 4) (operation := 0))
    (.plain .pure (.handler (effect := .cell 4) (table := resumeTable) (families := resumeDependencies)
      (required := []) (.cell (identity := 4) .nil))) := by
  apply request_from_capability
  apply SourceContextualRequirements.capability_prefix (front := .plain .pure .nil) rfl
  exact .handler rfl rfl (fun held => by cases held <;> exact ⟨[], rfl⟩)
    (fun held => by cases held <;> exact ⟨_, rfl⟩)

/-- Disposal beneath an additional provider reuses the complete existing
handler/resource/cleanup clause check, including its effectful saved callback. -/
theorem effectful_disposal : Local [effectF] disposeActions phases [] disposeClause
    (.cell (identity := 4) (.live (owner := 19) closing tail)) :=
  SourceScheduledProviderChecks.local_transport dispose_clause_scopes .here

/-- The waiting-request obligation is a structural derivation over its
retained callback, with no local proof-transformer field. -/
theorem structural_request_waiting : Local [] actions phases []
    (.cleanup (needs := []) .pure (.request (effect := effectE) (operation := 0)))
    (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := [])
      (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := []) .nil)) := by
  apply SourceScheduledHandlerAdaptation.Adapt.sound
    (frame := .handler effectF resumeTable resumeDependencies []) (checked := cleanup_disposing_request)
  apply SourceScheduledHandlerAdaptation.Adapt.cleanup ?_ .pure
  apply SourceScheduledHandlerAdaptation.Adapt.request (.cleanup (.hit rfl rfl)) (.cleanup (.hit rfl rfl))
    (.outside .here) (check_capture_iff.mp (by decide))
  intro disposes
  exact .cleanup .pure .nil

end Providers

namespace PendingTransport

def pureSavedHints : Hints (.cleanup [] .pure .nil) := .cleanup .nil
def pureSaved : Forest pureSavedHints := .cleanup .pure .nil
def both : Syntax.UsageTickets := fun _ => some ⟨true, true⟩

theorem original_resume : Local [] both phases [] (.invoke (key := ⟨19, .resume⟩))
    (.live (owner := 19) pureSaved .nil) := by
  apply resume_from_parts (front := .nil) (saved := pureSaved) (tail := .nil) .hit rfl rfl rfl
  · exact .cleanup .pure .nil
  · exact .nil
  · exact .nil
  · exact (SourceContextualHintChecking.check_iff _).mp rfl

theorem handler_resume : Local [] both phases [] (.invoke (key := ⟨19, .resume⟩))
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := [])
      (.live (owner := 19) pureSaved .nil)) := by
  exact (SourceScheduledHandlerAdaptation.Adapt.resume (front := .nil) (saved := pureSaved) (tail := .nil)
    .hit (.handler .hit) (.inside .here) (.cleanup .pure (.install rfl))).sound original_resume

theorem original_dispose : Local [] both phases [] (.invoke (key := ⟨19, .dispose⟩))
    (.live (owner := 19) pureSaved .nil) := by
  apply dispose_from_parts (front := .nil) (saved := pureSaved) (tail := .nil) .hit rfl rfl rfl rfl
  · exact .cleanup (fun _ member => by cases member) .nil
  · exact .cleanup .pure .nil
  · exact .nil
  · exact .nil
  · exact (SourceContextualHintChecking.check_iff _).mp rfl

theorem handler_dispose : Local [] both phases [] (.invoke (key := ⟨19, .dispose⟩))
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := [])
      (.live (owner := 19) pureSaved .nil)) := by
  exact (SourceScheduledHandlerAdaptation.Adapt.dispose (front := .nil) (saved := pureSaved) (tail := .nil)
    .hit (.handler .hit) (.inside .here) (.cleanup .pure (.running (.install rfl)))).sound original_dispose

end PendingTransport

namespace LocallyHandledClause
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledRequirements (Site)

def innerClauses : Clauses := .cons 0 1 9 (.discard 9) .nil

def innerPlans : ClausePlans innerClauses disposeDependencies :=
  .cons (.available (fun _ => .invoke)) .unavailable .nil

def handledRequest (effect : Instance) :=
  Plan.handler (effect := effect) (table := disposeTable) [] innerPlans
    (.sequence .pure (.request (effect := effect) (operation := 0)))

theorem inner_declarations : SourcePlannedRecipeDeclarations.Declarations [] innerPlans :=
  .cons (.available (.dispose rfl)) .unavailable .nil

/-- The source site itself determines the newly installed interpreter. This
annotation uses neither a pre-entry body check nor an adaptation of that check. -/
theorem request_site {hints : Hints scope} (forest : Forest hints) (after : Plan dependencies) :
    Site (.sequence (handledRequest effect) after) world forest (.request effect 0) world
      (.handler (effect := effect) (table := disposeTable) (families := disposeDependencies)
        (required := []) (.plain after forest)) :=
  .first (.handler (.second .request))

/-- A handler that consumes its own empty capture can precede any checked
remainder. The remainder stays outside that capture, including its owner uses. -/
theorem prefix_checked {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    {hints : Hints scope} {forest : Forest hints} {after : Plan dependencies}
    (next : Local outward actions phases world after forest) :
    Local outward actions phases world (.sequence (handledRequest effect) after) forest :=
  .sequence (SourceScheduledClauses.handled_request_local rfl) next

def resumeOuter (owner : Nat) := Plan.sequence .pure (.invoke (key := ⟨owner, .resume⟩))

/-- The nested disposer and outer resumer are distinct one-shot uses. The
outer continuation remains in the waiting suffix of the inner request. -/
theorem followed_by_outer_resume :
    Local [] PendingTransport.both phases [] (.sequence (handledRequest effectE) (resumeOuter 19))
      (.live (owner := 19) .nil .nil) := by
  apply prefix_checked
  refine .sequence .pure ?_
  exact resume_from_parts (front := .nil) (saved := .nil) (tail := .nil)
    .hit rfl rfl rfl .nil .nil .nil ((SourceContextualHintChecking.check_iff _).mp rfl)

/-- Requiring the handler body to check before installation would exclude this
valid local composition: no outer interpreter supplies its operation. -/
theorem body_before_installation_rejected :
    ¬ Local [] PendingTransport.both phases []
      (.sequence .pure (.request (effect := effectE) (operation := 0)))
      (.plain (resumeOuter 19) (.live (owner := 19) .nil .nil)) := by
  intro checked
  cases checked with
  | sequence initial request =>
      have guarded := SourceDependencySchemes.checked_request request.erase.erase
      change false = true at guarded
      cases guarded

end LocallyHandledClause

namespace StructuralAdaptation
open SourceScheduledHandlerAdaptation (Adapt Retained)

def active := OwnerPhaseTransitions.available [19, 23]
def callbackHints : Hints (.cleanup [.cell 7] (.request (.cell 7) 0) (.cell 7 .nil)) := .cleanup (.cell .nil)
def callbacks : Forest callbackHints := .cleanup .request (.cell .nil)
def savedHints : Hints (.plain (.invoke ⟨23, .dispose⟩) .nil) := .plain .nil
def saved : Forest savedHints := .plain .invoke .nil
def waitingHints : Hints (.live 23 (.cleanup [.cell 7] (.request (.cell 7) 0) (.cell 7 .nil)) .nil) := .live callbackHints .nil
def waiting : Forest waitingHints := .live callbacks .nil

theorem original_inner_dispose : Local [] PendingTransport.both (OwnerPhaseTransitions.spend active 19) [7]
    (.invoke (key := ⟨23, .dispose⟩)) (.spent (owner := 19) waiting) := by
  apply dispose_from_parts (front := .spent (owner := 19) .nil) (saved := callbacks) (tail := .nil)
    (.spent .hit) rfl rfl (by decide) rfl
  · exact .cleanup (fun _ member => by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; subst member; exact ⟨some 7, .cell rfl, .cell rfl⟩)
      (.cell .nil)
  · exact .cleanup (request_from_capability (.builtin rfl)) (.cell .nil)
  · exact .spent .nil
  · exact .nil
  · exact (SourceContextualHintChecking.check_iff _).mp rfl

theorem original_outer_resume : Local [] PendingTransport.both active [7]
    (.invoke (key := ⟨19, .resume⟩)) (.live (owner := 19) saved waiting) := by
  apply resume_from_parts (front := .nil) (saved := saved) (tail := waiting) .hit rfl rfl (by decide)
  · exact .plain original_inner_dispose .nil
  · exact .nil
  · exact .live (.cleanup (request_from_capability (.builtin rfl)) (.cell .nil)) .nil
  · exact (SourceContextualHintChecking.check_iff _).mp rfl

/-- The recursive retained rule follows resume19 into its saved dispose23,
then checks the actual cell7 callback after both owners are spent. There is no
whole replacement schedule, callback transformer or extra invocation interface. -/
theorem nested_adaptation : Adapt [] PendingTransport.both (.handler effectF resumeTable resumeDependencies []) active [7]
    (.invoke (key := ⟨19, .resume⟩)) (.live (owner := 19) saved waiting)
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := [])
      (.live (owner := 19) saved waiting)) := by
  apply Adapt.resume (front := .nil) (saved := saved) (tail := waiting) .hit (.handler .hit) (.inside .here)
  apply Retained.plain ?_ (.install rfl)
  apply Adapt.dispose (front := .spent (owner := 19) .nil) (saved := callbacks) (tail := .nil)
    (.spent .hit) (.handler (.spent .hit)) (.inside .here)
  exact .cleanup (.capability (.builtin rfl)) (.cell (.running (.install rfl)))

theorem nested_checked : Local [] PendingTransport.both active [7]
    (.invoke (key := ⟨19, .resume⟩))
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) (required := [])
      (.live (owner := 19) saved waiting)) :=
  nested_adaptation.sound original_outer_resume

end StructuralAdaptation

namespace FreshDisposal

def frontHints : Hints (.plain (.invoke ⟨19, .resume⟩)
    (.cleanup [.cell 7] (.request (.cell 7) 0) (.cell 7 (.live 19 .nil .nil)))) :=
  .plain (.cleanup (.cell (.live .nil .nil)))
def front : Forest frontHints := .plain .invoke (.cleanup .request (.cell (.live .nil .nil)))
def waitingHints : Hints (.cell 4 .nil) := .cell .nil
def waiting : Forest waitingHints := .cell .nil

/-- Before insertion the request is a builtin operation and supplies no
captured disposal schedule. -/
theorem builtin_request : Local [] PendingTransport.both phases [7]
    (.request (effect := .cell 4) (operation := 0)) (front.append waiting) :=
  request_from_capability (SourceContextualRequirements.check_capability_iff.mp rfl)

/-- The new disposer captures a pending use of owner 19 together with that
owner, an effectful callback, and its resource. The callback is checked at its
actual closing position using the retained builtin; no old disposal schedule
or target Pending certificate is assumed. -/
theorem newly_disposing_request : Local [] PendingTransport.both phases [7]
    (.request (effect := .cell 4) (operation := 0))
    (front.append (.handler (effect := .cell 4) (table := disposeTable) (families := disposeDependencies)
      (required := []) waiting)) := by
  apply SourceScheduledFreshRequests.installed_request_from_prefix front waiting rfl rfl rfl
  · exact check_capture_iff.mp (by decide)
  · intro disposes
    exact .plain (.invoke (by decide)) (.cleanup (.cell (.live .nil .nil)))
  · intro disposes
    exact .plain (.cleanup
      (request_from_capability (SourceContextualRequirements.check_capability_iff.mp rfl))
      (.cell (.live .nil .nil)))

/-- The exhaustive transport theorem also handles the former builtin case.
Its fresh-branch obligations come from explicit owner and callback derivations,
not from the separately established target request check. -/
theorem transported_disposing_request : Local [] PendingTransport.both phases [7]
    (.request (effect := .cell 4) (operation := 0))
    (front.append (.handler (effect := .cell 4) (table := disposeTable) (families := disposeDependencies)
      (required := []) waiting)) := by
  apply SourceScheduledHandlerTransport.request_transport
    (SourceScheduledInterpretationInsertion.Insertion.prefix front .here) builtin_request
  · exact check_capture_iff.mp (by decide)
  · intro captured tail savedHints waitingHints saved waiting contract modes intercepted disposes
    cases intercepted with
    | plain next => cases next with
      | cleanup next => cases next with
        | cell different next => cases next with
          | live next => cases next with
            | hit known declared =>
                have same : (⟨true, some [], none⟩ : ClauseContract) = contract := Option.some.inj known
                cases same
                refine ⟨.plain (.invoke (by decide)) (.cleanup (.cell (.live .nil (.handler .nil)))), ?_⟩
                exact .plain (.cleanup
                  (request_from_capability (SourceContextualRequirements.check_capability_iff.mp rfl))
                  (.cell (.live .nil (.handler .nil))))
  · intro captured tail savedHints waitingHints saved waiting contract modes oldCut disposes
    have impossible := oldCut.erase.lookup
    change some (SourceDependencyCapture.Selection.builtin 4) = some (.handler captured tail contract modes) at impossible
    cases impossible

end FreshDisposal

namespace CleanupRecipes
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlannedRecipeDeclarations (Declarations)

def code : Code := .cleanup (.lambda 7 .unit) (.discard 9)
def family (owner : Nat) : Dependencies := .sequence .pure (.cleanup [] .pure (.invoke ⟨owner, .dispose⟩))
def bodies (owner : Nat) : Plan (family owner) := .sequence .pure (.cleanup .pure .invoke)
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, none)]
def clauses : Clauses := .cons 0 1 9 code .nil
def plans : ClausePlans clauses families := .cons (.available bodies) .unavailable .nil

/-- Pure callback creation is an ordinary silent prefix. The cleanup body
consumes its continuation under the newly admitted armed scope. -/
theorem declarations : Declarations [] plans :=
  .cons (.available (.silent .pure (.cleanup (.dispose rfl)))) .unavailable .nil

def hints : Hints (.handler effectE disposeTable families .nil) := .handler [] .nil
def forest : Forest hints := .handler .nil
def noActions : Syntax.UsageTickets := fun _ => none

private theorem request : Local [] noActions OwnerPhaseTransitions.empty []
    (.request (effect := effectE) (operation := 0)) forest := by
  apply Local.request
  · apply SourceDependencyChecks.Local.request_selected
      (captured := .handler effectE disposeTable families .nil) (tail := .nil) (by rfl)
    · exact SourceDependencyCapture.check_capture_iff.mpr (.handler rfl rfl rfl rfl (fun _ => .handler .nil))
    · intro permission; exact .nil
    · intro permission; exact .handler .nil
  · intro captured outside savedHints outsideHints contract modes cut savedForest outsideForest same permission
    cases cut with
    | hit known declared =>
      cases savedForest with
      | handler rest => cases rest; exact .nil
    | handler different next => exact False.elim (different rfl)

/-- The declaration-selection path now derives the cleanup-bearing body and
retained capture checks from the pre-capture request. No body-success premise
or separate cleanup obligation is supplied at this call site. -/
theorem captured :
    Local [] (noActions.insert 19 code.requiredActions) (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) forest .nil) ∧
    Pending [] (noActions.insert 19 code.requiredActions) (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) forest .nil) .nil := by
  have result := SourceScheduledClauses.declaration_capture (owner := 19) declarations
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies)) rfl
    (SourceScheduledNeutral.Cut.hit (rest := Forest.nil) rfl rfl) request
    (Pending.handler rfl Pending.nil)
    (SourceContextualHintChecking.check_iff _ |>.mp (by rfl))
    rfl rfl (fun _ => rfl) rfl
  exact result.2

def resumeCode : Code := .cleanup (.lambda 7 .unit) (.resume 9 (.variable 2))
def resumeFamily (owner : Nat) : Dependencies :=
  .sequence .pure (.cleanup [] .pure (.sequence .pure (.invoke ⟨owner, .resume⟩)))
def resumeBodies (owner : Nat) : Plan (resumeFamily owner) :=
  .sequence .pure (.cleanup .pure (.sequence .pure .invoke))
def resumeClauses : Clauses := .cons 0 1 9 resumeCode .nil
def resumePlans : ClausePlans resumeClauses [(0, some resumeFamily, none)] :=
  .cons (.available resumeBodies) .unavailable .nil

/-- Substitution really changes this cleanup clause's resume argument and
retains its structural recipe through the existing signature transport. -/
theorem substituted_declaration :
    resumeClauses.subst 2 .unit ≠ resumeClauses ∧
    Declarations [] (SourcePlanSignatures.substituteClauses resumePlans 2 .unit) := by
  constructor
  · intro same; cases same
  · have admitted : Declarations [] resumePlans :=
      .cons (.available (.silent .pure (.cleanup (.silent .pure (.resume rfl))))) .unavailable .nil
    exact admitted.signature_congr (SourcePlanSignatures.substitution_signature resumePlans (name := 2) (value := .unit) trivial).symm

end CleanupRecipes

namespace ResourceRecipes
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlannedRecipeDeclarations (Declarations)
open SourcePlannedClauseRecipes (Recipe)

/-- This clause acquires a cell, requests its local operation, then disposes
its continuation. No local-cell request is exported as an outer requirement. -/
def code : Code := .resource 7 (.integer 0)
  (.bind 8 (.perform (.cell (.bound 7)) 0 .unit) (.discard 9))
def family (owner : Nat) : Dependencies := .sequence .pure (.resource (fun identity =>
  .sequence (.sequence .pure (.request (.cell identity) 0)) (.invoke ⟨owner, .dispose⟩)))
def bodies (owner : Nat) : Plan (family owner) := .sequence .pure (.resource (fun _ =>
  .sequence (.sequence .pure .request) .invoke))
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, none)]
def clauses : Clauses := .cons 0 1 9 code .nil
def plans : ClausePlans clauses families := .cons (.available bodies) .unavailable .nil

theorem declarations : Declarations [] plans :=
  .cons (.available (.silent .pure (.resource (fun _ => .localRequest List.mem_cons_self (.dispose rfl))))) .unavailable .nil

def hints : Hints (.handler effectE disposeTable families .nil) := .handler [] .nil
def forest : Forest hints := .handler .nil

private theorem request : Local [] CleanupRecipes.noActions OwnerPhaseTransitions.empty []
    (.request (effect := effectE) (operation := 0)) forest := by
  apply Local.request
  · apply SourceDependencyChecks.Local.request_selected
      (captured := .handler effectE disposeTable families .nil) (tail := .nil) (by rfl)
    · exact SourceDependencyCapture.check_capture_iff.mpr (.handler rfl rfl rfl rfl (fun _ => .handler .nil))
    · intro permission; exact .nil
    · intro permission; exact .handler .nil
  · intro captured outside savedHints outsideHints contract modes cut savedForest outsideForest same permission
    cases cut with
    | hit known declared =>
      cases savedForest with
      | handler rest => cases rest; exact .nil
    | handler different next => exact False.elim (different rfl)

/-- Actual declaration selection now derives the entire resource-bearing
body check from pre-capture evidence, with an empty outer requirement list. -/
theorem captured :
    Local [] (CleanupRecipes.noActions.insert 19 code.requiredActions) (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) forest .nil) ∧
    Pending [] (CleanupRecipes.noActions.insert 19 code.requiredActions) (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) forest .nil) .nil := by
  have result := SourceScheduledClauses.declaration_capture (owner := 19) declarations
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies)) rfl
    (SourceScheduledNeutral.Cut.hit (rest := Forest.nil) rfl rfl) request
    (Pending.handler rfl Pending.nil)
    (SourceContextualHintChecking.check_iff _ |>.mp (by rfl))
    rfl rfl (fun _ => rfl) rfl
  exact result.2

/-- Both providers are usable in the inner body, and repeated requests do not
consume the one-shot continuation permission. Cleanup still wraps consumption. -/
def nestedFamily (owner : Nat) : Dependencies := .resource (fun first => .resource (fun second =>
  .sequence (.sequence .pure (.request (.cell first) 0))
    (.sequence (.sequence .pure (.request (.cell second) 0))
      (.sequence (.sequence .pure (.request (.cell first) 0)) (.cleanup [] .pure (.invoke ⟨owner, .resume⟩))))))
def nestedBodies (owner : Nat) : Plan (nestedFamily owner) := .resource (fun _ => .resource (fun _ =>
  .sequence (.sequence .pure .request) (.sequence (.sequence .pure .request)
    (.sequence (.sequence .pure .request) (.cleanup .pure .invoke)))))

theorem nested_declaration_recipe : Recipe ⟨true, false⟩ [] nestedBodies :=
  .resource (fun _ => .resource (fun _ =>
    .localRequest (List.mem_cons_of_mem _ List.mem_cons_self)
      (.localRequest List.mem_cons_self
        (.localRequest (List.mem_cons_of_mem _ List.mem_cons_self) (.cleanup (.resume rfl))))))

theorem absent_provider_rejected :
    ¬ Recipe ⟨true, false⟩ [] (fun owner => .sequence
      (.sequence .pure (.request (effect := .cell 4) (operation := 0))) (.invoke (key := ⟨owner, .resume⟩))) := by
  intro recipe
  have checked := recipe.compile (outward := []) (actions := fun _ => some ⟨true, false⟩)
    (phases := fun _ => .available) (world := []) (owner := 19) (saved := Hints.nil) (waiting := Hints.nil)
    rfl rfl .nil .nil (by intro impossible; cases impossible) (.live .nil .nil) .nil
    (by intro request member; cases member)
  have request := (SourceDependencyChecks.Local.sequence_iff.mp
    (SourceDependencyChecks.Local.sequence_iff.mp checked.erase).1).2
  have guarded := SourceDependencyChecks.Local.request_guard request
  change false = true at guarded
  cases guarded

/-- Substitution changes the request payload while preserving the resource
recipe and its local-provider requirement accounting. -/
def variableCode : Code := .resource 7 (.integer 0)
  (.bind 8 (.perform (.cell (.bound 7)) 0 (.variable 2)) (.discard 9))
def variableClauses : Clauses := .cons 0 1 9 variableCode .nil
def variablePlans : ClausePlans variableClauses families := .cons (.available bodies) .unavailable .nil

theorem substituted_declaration :
    variableClauses.subst 2 .unit ≠ variableClauses ∧
    Declarations [] (SourcePlanSignatures.substituteClauses variablePlans 2 .unit) := by
  constructor
  · intro same; cases same
  · have admitted : Declarations [] variablePlans :=
      .cons (.available (.silent .pure (.resource (fun _ => .localRequest List.mem_cons_self (.dispose rfl))))) .unavailable .nil
    exact admitted.signature_congr (SourcePlanSignatures.substitution_signature variablePlans (name := 2) (value := .unit) trivial).symm

end ResourceRecipes

namespace HandledRecipes
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlannedRecipeDeclarations (Declarations)
open SourceDeclarationPlans

def code : Code := .bind 8
  (.handle (Instantiation.freezeEffect effectE)
    (.perform (Instantiation.freezeEffect effectE) 0 .unit) (HandledRequest.clauses 0))
  (.discard 9)
def family (owner : Nat) : Dependencies :=
  .sequence (HandledRequest.dependencies effectE 0) (.invoke ⟨owner, .dispose⟩)
def bodies (owner : Nat) : Plan (family owner) := .sequence (HandledRequest.plan effectE 0) .invoke
def families : SourceDependencyAnnotations.ClauseDependencies := [(0, some family, none)]
def clauses : Clauses := .cons 0 1 9 code .nil
def plans : ClausePlans clauses families := .cons (.available bodies) .unavailable .nil

/-- This is a consuming declaration recipe, not a supplied local body proof.
The inner handler shadows the same effect instance as the outer handler. -/
theorem declarations : Declarations [] plans :=
  .cons (.available (.handledRequest (fun _ => rfl) (.dispose rfl))) .unavailable .nil

def hints : Hints (.handler effectE disposeTable families .nil) := .handler [] .nil
def forest : Forest hints := .handler .nil

private theorem request : Local [] CleanupRecipes.noActions OwnerPhaseTransitions.empty []
    (.request (effect := effectE) (operation := 0)) forest := by
  apply SourceScheduledFreshRequests.request_from_callbacks (.hit rfl rfl)
  · exact .handler rfl rfl rfl rfl (fun _ => .handler .nil)
  · intro permission; exact .handler .nil
  · intro permission; exact .handler .nil

/-- Selection compiles the nested handler-bearing body from its declaration
recipe and the original request/capture checks. No target body is a premise. -/
theorem captured :
    Local [] (CleanupRecipes.noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) forest .nil) ∧
    Pending [] (CleanupRecipes.noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) forest .nil) .nil := by
  have result := SourceScheduledClauses.declaration_capture (owner := 19) declarations
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies)) rfl
    (SourceScheduledNeutral.Cut.hit (rest := Forest.nil) rfl rfl) request
    (Pending.handler rfl Pending.nil)
    (SourceContextualHintChecking.check_iff _ |>.mp (by rfl))
    rfl rfl (fun _ => rfl) rfl
  exact result.2

def resumeCode : Code := .bind 8
  (.handle (Instantiation.freezeEffect effectE)
    (.perform (Instantiation.freezeEffect effectE) 0 .unit) (HandledRequest.clauses 0))
  (.resume 9 (.variable 2))
def resumeFamily (owner : Nat) : Dependencies :=
  .sequence (HandledRequest.dependencies effectE 0) (.sequence .pure (.invoke ⟨owner, .resume⟩))
def resumeBodies (owner : Nat) : Plan (resumeFamily owner) :=
  .sequence (HandledRequest.plan effectE 0) (.sequence .pure .invoke)
def resumeClauses : Clauses := .cons 0 1 9 resumeCode .nil
def resumePlans : ClausePlans resumeClauses [(0, some resumeFamily, none)] :=
  .cons (.available resumeBodies) .unavailable .nil

/-- Actual source substitution changes the outer resumption payload while
signature transport preserves the nested-handler recipe. -/
theorem substituted_declaration :
    resumeClauses.subst 2 .unit ≠ resumeClauses ∧
    Declarations [] (SourcePlanSignatures.substituteClauses resumePlans 2 .unit) := by
  constructor
  · intro same; cases same
  · have admitted : Declarations [] resumePlans :=
      .cons (.available (.handledRequest (fun _ => rfl) (.silent .pure (.resume rfl)))) .unavailable .nil
    exact admitted.signature_congr
      (SourcePlanSignatures.substitution_signature resumePlans (name := 2) (value := .unit) trivial).symm

end HandledRecipes

end Ash.OneShot.SourceScheduledScopeExamples

#print axioms Ash.OneShot.SourceScheduledScopeExamples.nested_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.shadowed_preconditions
#print axioms Ash.OneShot.SourceScheduledScopeExamples.shadowed_resume_rejected

#print axioms Ash.OneShot.SourceScheduledScopeExamples.resume_clause_scopes
#print axioms Ash.OneShot.SourceScheduledScopeExamples.dispose_clause_scopes

#print axioms Ash.OneShot.SourceScheduledScopeExamples.head_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.protected_override_rejected

#print axioms Ash.OneShot.SourceScheduledScopeExamples.cleanup_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.cleanup_dispose
#print axioms Ash.OneShot.SourceScheduledScopeExamples.pure_cleanup_changes_closing
#print axioms Ash.OneShot.SourceScheduledScopeExamples.cleanup_disposing_request
#print axioms Ash.OneShot.SourceScheduledScopeExamples.nested_cleanup_disposing_request

#print axioms Ash.OneShot.SourceScheduledScopeExamples.CleanupRecipes.declarations
#print axioms Ash.OneShot.SourceScheduledScopeExamples.CleanupRecipes.captured
#print axioms Ash.OneShot.SourceScheduledScopeExamples.CleanupRecipes.substituted_declaration

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.local_resource_request

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.resume_changes_interpreter

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.disposing_request_schedule

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.effectful_disposal

#print axioms Ash.OneShot.SourceScheduledScopeExamples.ResourceRecipes.declarations

#print axioms Ash.OneShot.SourceScheduledScopeExamples.ResourceRecipes.captured

#print axioms Ash.OneShot.SourceScheduledScopeExamples.ResourceRecipes.nested_declaration_recipe

#print axioms Ash.OneShot.SourceScheduledScopeExamples.ResourceRecipes.absent_provider_rejected

#print axioms Ash.OneShot.SourceScheduledScopeExamples.ResourceRecipes.substituted_declaration

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.handler_inside_disposing_capture
#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.handler_preempts_builtin_request

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.handler_in_disposal_waiting

#print axioms Ash.OneShot.SourceScheduledScopeExamples.PendingTransport.original_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.PendingTransport.handler_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.PendingTransport.original_dispose
#print axioms Ash.OneShot.SourceScheduledScopeExamples.PendingTransport.handler_dispose

#print axioms Ash.OneShot.SourceScheduledScopeExamples.FreshDisposal.builtin_request
#print axioms Ash.OneShot.SourceScheduledScopeExamples.FreshDisposal.newly_disposing_request

#print axioms Ash.OneShot.SourceScheduledScopeExamples.FreshDisposal.transported_disposing_request

#print axioms Ash.OneShot.SourceScheduledScopeExamples.StructuralAdaptation.original_inner_dispose
#print axioms Ash.OneShot.SourceScheduledScopeExamples.StructuralAdaptation.original_outer_resume
#print axioms Ash.OneShot.SourceScheduledScopeExamples.StructuralAdaptation.nested_adaptation
#print axioms Ash.OneShot.SourceScheduledScopeExamples.StructuralAdaptation.nested_checked

#print axioms Ash.OneShot.SourceScheduledScopeExamples.Providers.structural_request_waiting

#print axioms Ash.OneShot.SourceScheduledScopeExamples.shadowing_adaptation_rejected

#print axioms Ash.OneShot.SourceScheduledScopeExamples.LocallyHandledClause.inner_declarations

#print axioms Ash.OneShot.SourceScheduledScopeExamples.LocallyHandledClause.request_site

#print axioms Ash.OneShot.SourceScheduledScopeExamples.LocallyHandledClause.prefix_checked

#print axioms Ash.OneShot.SourceScheduledScopeExamples.LocallyHandledClause.followed_by_outer_resume

#print axioms Ash.OneShot.SourceScheduledScopeExamples.LocallyHandledClause.body_before_installation_rejected

#print axioms Ash.OneShot.SourceScheduledScopeExamples.HandledRecipes.declarations

#print axioms Ash.OneShot.SourceScheduledScopeExamples.HandledRecipes.captured

#print axioms Ash.OneShot.SourceScheduledScopeExamples.HandledRecipes.substituted_declaration
