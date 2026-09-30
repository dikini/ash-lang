import SourceScheduledSourceInterfaces

/-! Source callback interfaces for a newly selected disposer. An annotation
retains finite operation lists and structural footprints of actual callback
plans. Direct compilation consumes source declaration annotations and a finite
receiving-scope check, without an old schedule or checked target callback body. -/
namespace Ash.OneShot.SourceScheduledCallbackInterfaces
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledInterpretationInsertion (Interpretation)
open SourceScheduledChecks (Pending)
open SourceScheduledClosingCallbacks (Callbacks)
open SourceHandlerRequirements (reaches outwardRequirements)
open SourceContextualHints (checkCapability)

private def receiving {hints : Hints scope} (_ : Forest hints) : Scope := scope

theorem reaches_append (front : Scope) :
    reaches effect (front.append tail) = (reaches effect front && reaches effect tail) := by
  induction front <;> simp_all [reaches, Scope.append, Bool.and_assoc]

private theorem capability_running :
    checkCapability (.running scope) effect operation = checkCapability scope effect operation :=
  SourceHandlerRequirements.capability_prepend rfl

/-- A closing prefix contains builtin providers but no source handlers. Each
operation is either supplied there or passes to its receiving scope. -/
private theorem closing_capability (scope : Scope) :
    checkCapability scope.forClosing effect operation = !reaches effect scope.forClosing := by
  induction scope with
  | nil => rfl
  | plain dependencies rest ih | handler other table families rest ih | spent owner rest ih => exact ih
  | cell identity rest ih =>
      by_cases same : effect = .cell identity
      · simp [Scope.forClosing, checkCapability, SourceDependencyCapture.select, reaches, same]
      · have passed := SourceHandlerRequirements.capability_prepend
          (first := .cell identity rest.forClosing) (second := rest.forClosing)
          (layer := .cell identity) (effect := effect) (operation := operation) (if_neg same)
        simpa only [Scope.forClosing, reaches, if_neg same, passed] using ih
  | cleanup needs callback rest ih =>
      have passed := SourceHandlerRequirements.capability_prepend
        (first := .cleanup needs callback rest.forClosing) (second := rest.forClosing)
        (effect := effect) (operation := operation) rfl
      simpa only [Scope.forClosing, reaches, passed] using ih
  | running rest ih => simpa only [Scope.forClosing, reaches, capability_running] using ih
  | live owner saved rest ihSaved ihRest =>
      simp only [Scope.forClosing, SourceHandlerRequirements.capability_append,
        reaches_append, reaches, capability_running, ihSaved, ihRest]
      cases reaches effect saved.forClosing <;> rfl

/-- Factor requirements through a closing prefix without assuming that any
earlier disposal was admitted. Builtins discharge exactly the filtered entries. -/
theorem requirements_closing_iff (scope : Scope) :
    checkRequirements (scope.forClosing.append outside) required = true ↔
      checkRequirements outside (outwardRequirements scope.forClosing required) = true := by
  constructor
  · exact SourceHandlerRequirements.requirements_outward
  · intro supplied
    apply List.all_eq_true.mpr
    intro request member
    rw [SourceHandlerRequirements.capability_append, closing_capability]
    by_cases passed : reaches request.1 scope.forClosing = true
    · rw [if_pos passed]
      exact List.all_eq_true.mp supplied request (List.mem_filter.mpr ⟨member, passed⟩)
    · simp [passed]

/-- Plain pending code is discarded; only actual cleanup bodies need request
footprints. Dormant captures retain their own annotation and closing order. -/
inductive Interfaces : {scope : Scope} → {hints : Hints scope} → Forest hints → Type where
  | nil : Interfaces .nil
  | plain : Interfaces rest → Interfaces (.plain plan rest)
  | handler : Interfaces rest →
      Interfaces (.handler (effect := effect) (table := table) (families := families) (required := required) rest)
  | cell : Interfaces rest → Interfaces (.cell (identity := identity) rest)
  | cleanup {hints : Hints scope} (rest : Forest hints) (required : List Requirement)
      (footprint : RequestFootprint plan required) (tail : Interfaces rest) :
      Interfaces (.cleanup (needs := needs) plan rest)
  | running : Interfaces rest → Interfaces (.running rest)
  | live {hints : Hints scope} (rest : Forest hints) :
      Interfaces saved → Interfaces rest → Interfaces (.live (owner := owner) saved rest)
  | spent : Interfaces rest → Interfaces (.spent (owner := owner) rest)

/-- A finite check at exact closing positions, including the extra running
boundary between a dormant capture and its closing tail. -/
def Interfaces.check {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces forest) (outside : Scope) : Bool :=
  match interfaces with
  | .nil => true
  | .plain next | .handler next | .cell next | .running next | .spent next => next.check outside
  | .cleanup rest required _ next =>
      checkRequirements (.running ((receiving rest).forClosing.append outside)) required && next.check outside
  | .live rest saved next => saved.check ((Scope.running (receiving rest).forClosing).append outside) && next.check outside

/-- The finite callback operations exposed at the capture boundary. Local
builtins filter requirements at their actual closing suffix; repeated entries
remain ordinary reusable capability requirements. -/
def Interfaces.exposed {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces forest) : List Requirement :=
  match interfaces with
  | .nil => []
  | .plain next | .handler next | .cell next | .running next | .spent next => next.exposed
  | .cleanup rest required _ next =>
      outwardRequirements (Scope.running (receiving rest).forClosing) required ++ next.exposed
  | .live rest saved next =>
      outwardRequirements (Scope.running (receiving rest).forClosing) saved.exposed ++ next.exposed

/-- One finite list exactly replaces all per-callback operation checks. This
does not replace the separate capture-route or continuation-owner judgments. -/
theorem Interfaces.check_iff {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces forest) :
    interfaces.check outside = true ↔ checkRequirements outside interfaces.exposed = true := by
  induction interfaces generalizing outside with
  | nil => rfl
  | plain next ih | handler next ih | cell next ih | running next ih | spent next ih => exact ih
  | cleanup rest required footprint next ih =>
      simp only [Interfaces.check, Interfaces.exposed, Bool.and_eq_true]
      have closing := requirements_closing_iff (.running (receiving rest)) (outside := outside) (required := required)
      simp only [Scope.forClosing, Scope.append] at closing
      rw [closing, ih]
      simp only [checkRequirements, List.all_append, Bool.and_eq_true]
  | live rest saved next ihSaved ihRest =>
      simp only [Interfaces.check, Interfaces.exposed, Bool.and_eq_true]
      rw [ihSaved]
      simp only [Scope.append]
      have closing := requirements_closing_iff (.running (receiving rest)) (outside := outside) (required := saved.exposed)
      simp only [Scope.forClosing, Scope.append] at closing
      rw [closing, ihRest]
      simp only [checkRequirements, List.all_append, Bool.and_eq_true]

/-- Source declarations retained at each callback signature. This annotation
contains no checked callback body or target closing schedule. -/
inductive Declared (world : List Nat) : {scope : Scope} → {hints : Hints scope} →
    {forest : Forest hints} → Interfaces forest → Prop where
  | nil : Declared world .nil
  | plain : Declared world next → Declared world (Interfaces.plain (plan := plan) next)
  | handler : Declared world next → Declared world
      (Interfaces.handler (effect := effect) (table := table) (families := families) (required := required) next)
  | cell : Declared world next → Declared world (Interfaces.cell (identity := identity) next)
  | cleanup {hints : Hints scope} {rest : Forest hints} {next : Interfaces rest}
      (source : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature plan))
      (tail : Declared world next) :
      Declared world (Interfaces.cleanup (needs := needs) (plan := plan) rest required footprint next)
  | running : Declared world next → Declared world (Interfaces.running next)
  | live {hints : Hints scope} {rest : Forest hints} {next : Interfaces rest} :
      Declared world saved → Declared world next →
      Declared world (Interfaces.live (owner := owner) rest saved next)
  | spent : Declared world next → Declared world (Interfaces.spent (owner := owner) next)

/-- Existing normal scheduling provides these annotations without assuming
that disposal was previously permitted. -/
theorem Interfaces.declared_of_pending {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (interfaces : Interfaces forest)
    (original : Pending outward actions phases world forest outside) : Declared world interfaces := by
  induction interfaces generalizing outsideScope with
  | nil => exact .nil
  | plain next ih => cases original with | plain code tail => exact .plain (ih tail)
  | handler next ih => cases original with | handler supplied tail => exact .handler (ih tail)
  | cell next ih => cases original with | cell tail => exact .cell (ih tail)
  | cleanup rest required footprint next ih => cases original with
    | cleanup callback tail =>
      exact .cleanup (SourceScheduledSourceInterfaces.declared_of_local callback) (ih tail)
  | running next ih => cases original with | running tail => exact .running (ih tail)
  | live rest saved next ihSaved ihRest => cases original with
    | live inside tail => exact .live (ihSaved inside) (ihRest tail)
  | spent next ih => cases original with | spent tail => exact .spent (ih tail)

/-- Compile closing directly from source annotations and finite operation
checks. No previous normal Pending or complete callback Local proof is needed. -/
theorem Interfaces.compile_declared {hints : Hints scope} {forest : Forest hints}
    {afterHints : Hints second} {after : Forest afterHints}
    (interfaces : Interfaces forest) (declared : Declared world interfaces)
    (supplied : interfaces.check second = true) :
    Callbacks outward actions phases world forest after := by
  induction interfaces generalizing second with
  | nil => exact .nil
  | plain next ih => cases declared with | plain tail => exact .plain (ih tail supplied)
  | handler next ih => cases declared with | handler tail => exact .handler (ih tail supplied)
  | cell next ih => cases declared with | cell tail => exact .cell (ih tail supplied)
  | cleanup rest required footprint next ih => cases declared with
    | cleanup source tail =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .cleanup (SourceScheduledSourceInterfaces.compile footprint source requests) (ih tail remaining)
  | running next ih => cases declared with | running tail => exact .running (ih tail supplied)
  | live rest saved next ihSaved ihRest => cases declared with
    | live inside tail =>
      obtain ⟨savedRequests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .live (ihSaved inside savedRequests) (ihRest tail remaining)
  | spent next ih => cases declared with | spent tail => exact .spent (ih tail supplied)

/-- Preserve the existing interface for clients with a normal retained source.
It now extracts declaration annotations and uses the direct source compiler. -/
theorem Interfaces.compile {hints : Hints scope} {forest : Forest hints}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (interfaces : Interfaces forest) (_frame : Interpretation)
    (original : Pending outward actions phases world forest before)
    (supplied : interfaces.check second = true) :
    Callbacks outward actions phases world forest after :=
  interfaces.compile_declared (interfaces.declared_of_pending original) supplied

/-- Source annotations suffice to install a disposer, without an old normal
schedule or an old disposal schedule. The finite callback check is independent
of the capture route and captured-owner bound. -/
theorem installed_request_declared {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) (waiting : Forest waitingHints)
    (interfaces : Interfaces front)
    (declaredCallbacks : Declared world interfaces)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (known : ProtectionContracts.lookup operation table = some contract)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (guarded : SourceDependencyCapture.checkCapture outward
      (frontScope.append (.handler effect table families waitingScope)) effect operation = true)
    (bounded : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners frontScope) frontScope)
    (supplied : contract.dispose = true → checkRequirements (.running waitingScope) interfaces.exposed = true) :
    SourceScheduledChecks.Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) waiting)) :=
  SourceScheduledFreshRequests.installed_request_from_prefix front waiting passed known declared
    (SourceDependencyCapture.check_capture_iff.mp guarded) bounded
    (fun disposes => interfaces.compile_declared declaredCallbacks
      (interfaces.check_iff.mpr (supplied disposes)))

/-- Install a disposer using source callback interfaces. Previous normal
pending checks establish callback source evidence; the new finite checks
choose their closing interpretations. Capture routing and ownership bounds
remain independent premises, as required by the existing request rule. -/
theorem installed_request {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) (waiting : Forest waitingHints)
    (interfaces : Interfaces front)
    (original : Pending outward actions phases world front waiting)
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (known : ProtectionContracts.lookup operation table = some contract)
    (declared : SourceDependencyCapture.lookupDependencies operation families = some modes)
    (guarded : SourceDependencyCapture.checkCapture outward
      (frontScope.append (.handler effect table families waitingScope)) effect operation = true)
    (bounded : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners frontScope) frontScope)
    (supplied : contract.dispose = true → checkRequirements (.running waitingScope) interfaces.exposed = true) :
    SourceScheduledChecks.Local outward actions phases world (.request (effect := effect) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) waiting)) :=
  installed_request_declared front waiting interfaces (interfaces.declared_of_pending original)
    passed known declared guarded bounded supplied

namespace Examples
open SourceDependencyCapture.Examples (effectE effectF resumeTable resumeDependencies disposeTable disposeDependencies)
open SourceScheduledChecks (Local)

def waitingHints : Hints (.handler effectE resumeTable resumeDependencies
    (.handler effectF resumeTable resumeDependencies .nil)) := .handler [] (.handler [] .nil)
def waiting : Forest waitingHints := .handler (.handler .nil)
def frontHints : Hints (.cleanup [effectF] (.request effectF 0) .nil) := .cleanup .nil
def front : Forest frontHints := .cleanup .request .nil
def callbackInterfaces : Interfaces front := .cleanup .nil [(effectF, 0)] .request .nil
def noActions : Syntax.UsageTickets := fun _ => none

private theorem original : Pending [effectF] noActions OwnerPhaseTransitions.empty [] front waiting :=
  .cleanup (SourceScheduledScopedInvocations.request_from_capability
    (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil

/-- A new disposer replaces a resumer for the same effect. Its effectful
callback is compiled from the original normal source check. The old request
does not need to have carried any disposal schedule. -/
theorem new_disposer_from_source :
    Local [effectF] noActions OwnerPhaseTransitions.empty [] (.request (effect := effectE) (operation := 0))
      (front.append (.handler (effect := effectE) (table := disposeTable)
        (families := disposeDependencies) (required := []) waiting)) :=
  installed_request front waiting callbackInterfaces original (by rfl) (by rfl) (by rfl)
    (by decide) (fun _ => .cleanup .nil) (fun _ => by rfl)

/-- This successful request cannot be justified by the resumptive footprint
checker. The independent disposal rule supplies its capture and callbacks. -/
theorem disposer_not_a_resumptive_capability :
    SourceContextualHints.checkCapability
      (.cleanup [effectF] (.request effectF 0) (.handler effectE disposeTable disposeDependencies
        (.handler effectE resumeTable resumeDependencies (.handler effectF resumeTable resumeDependencies .nil))))
      effectE 0 = false := rfl

def capturedHints : Hints (.cleanup [effectF] (.request effectF 0)
    (.handler effectE disposeTable disposeDependencies .nil)) := .cleanup (.handler [] .nil)
def captured : Forest capturedHints := .cleanup .request (.handler .nil)

private theorem selected : SourceScheduledNeutral.Cut effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    (captured.append waiting) captured waiting := .cleanup (.hit (by rfl) (by rfl))

/-- The selected disposer remains the same while a new F handler in its
waiting suffix reinterprets the closing callback under protection. -/
theorem retained_disposer_reinterprets_callback :
    Local [effectF] noActions OwnerPhaseTransitions.empty [] (.request (effect := effectE) (operation := 0))
      (captured.append (.handler (effect := effectF) (table := resumeTable)
        (families := resumeDependencies) (required := []) waiting)) := by
  have adapted := SourceScheduledAdaptationCompilation.request selected
    (SourceScheduledNeutral.Cut.cleanup (.hit (by rfl) (by rfl)))
    (SourceScheduledInterpretationInsertion.Split.outside .here) (by decide)
    (outward := [effectF]) (actions := noActions) (phases := OwnerPhaseTransitions.empty) (world := [])
    (table := resumeTable) (families := resumeDependencies) (required := []) (installed := effectF)
    (by
      intro disposes dependencies oldScope nextScope plan oldHints nextHints old next source target changed
      cases target with
      | callback => exact RequestFootprint.request.adapt (by rfl)
      | cleanup next => cases next)
  exact adapted.sound new_disposer_from_source

/-- An unrelated captured handler disappears during closing. The original
callback schedule is reused, with no per-callback adaptation premise. -/
theorem captured_handler_reuses_callbacks :
    Local [effectF] noActions OwnerPhaseTransitions.empty [] (.request (effect := effectE) (operation := 0))
      (.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0))
        (.handler (effect := .user 93 []) (table := []) (families := []) (required := [])
          (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) waiting))) := by
  have adapted := SourceScheduledAdaptationCompilation.request_inside selected
    (SourceScheduledNeutral.Cut.cleanup (.handler (by decide) (.hit (by rfl) (by rfl))))
    (SourceScheduledInterpretationInsertion.Insertion.cleanup .here) (by decide)
    (outward := [effectF]) (actions := noActions) (phases := OwnerPhaseTransitions.empty) (world := [])
    (installed := .user 93 []) (table := []) (families := []) (required := [])
  exact adapted.sound new_disposer_from_source

/-- Callback capabilities alone do not authorize capture: placing its F
handler inside the discarded capture changes a required closing route. -/
theorem captured_callback_handler_rejected :
    callbackInterfaces.check (.running (.handler effectF resumeTable resumeDependencies .nil)) = true ∧
    SourceDependencyCapture.checkCapture [effectF]
      (.cleanup [effectF] (.request effectF 0) (.handler effectF resumeTable resumeDependencies
        (.handler effectE disposeTable disposeDependencies .nil))) effectE 0 = false := by decide

theorem exported_callback_requirement : callbackInterfaces.exposed = [(effectF, 0)] := rfl

theorem missing_callback_provider_rejected : callbackInterfaces.check .nil = false := rfl

def dormantHints : Hints (.live 27 (.cleanup [.cell 7] (.request (.cell 7) 0) .nil) (.cell 7 .nil)) :=
  .live (.cleanup .nil) (.cell .nil)
def dormant : Forest dormantHints := .live (.cleanup .request .nil) (.cell .nil)
def dormantInterfaces : Interfaces dormant :=
  .live (.cell .nil) (.cleanup .nil [(.cell 7, 0)] .request .nil) (.cell .nil)

/-- A builtin in the closing tail supplies the dormant callback before that
tail closes. Its operation therefore does not escape the finite interface. -/
theorem dormant_builtin_supplies_callback :
    dormantInterfaces.exposed = [] ∧ dormantInterfaces.check .nil = true := ⟨rfl, rfl⟩

/-- Without the closing tail's builtin, the dormant callback's requirement
must remain visible in the exported interface. -/
def unprovidedDormantHints : Hints (.live 27 (.cleanup [.cell 7] (.request (.cell 7) 0) .nil) .nil) :=
  .live (.cleanup .nil) .nil
def unprovidedDormant : Forest unprovidedDormantHints := .live (.cleanup .request .nil) .nil
def unprovidedDormantInterfaces : Interfaces unprovidedDormant :=
  .live .nil (.cleanup .nil [(.cell 7, 0)] .request .nil) .nil

theorem dormant_requirement_preserved :
    unprovidedDormantInterfaces.exposed = [(.cell 7, 0)] ∧
    unprovidedDormantInterfaces.check .nil = false := ⟨rfl, rfl⟩

end Examples

end Ash.OneShot.SourceScheduledCallbackInterfaces

#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Interfaces.compile
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.requirements_closing_iff
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Interfaces.check_iff
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.installed_request
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.new_disposer_from_source
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.disposer_not_a_resumptive_capability
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.retained_disposer_reinterprets_callback
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.captured_handler_reuses_callbacks
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.captured_callback_handler_rejected
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.exported_callback_requirement
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.missing_callback_provider_rejected
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.dormant_builtin_supplies_callback
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Examples.dormant_requirement_preserved

#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Interfaces.declared_of_pending
#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Interfaces.compile_declared

#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.installed_request_declared

#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.reaches_append
