import SourceScheduledCallbackInterfaces

/-! Structural operation interfaces for retained code. Unlike closing-only
interfaces, these retain ordinary pending code as well as callbacks. Compilation
checks each position at its actual receiving suffix, including dormant captures.
Free continuation invocations require a separate capability interface. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourceScheduledChecks (Pending)

private def receiving {hints : Hints scope} (_ : Forest hints) : Scope := scope

/-- Source annotations at every retained code position. Neither a previously
checked body nor a schedule for the receiving forest is stored here. -/
inductive Interfaces (world : List Nat) :
    {scope : Scope} → {hints : Hints scope} → Forest hints → Type where
  | nil : Interfaces world .nil
  | plain {hints : Hints scope} (rest : Forest hints) (required : List Requirement)
      (footprint : RequestFootprint plan required) (declared : Declared world (signature plan))
      (tail : Interfaces world rest) : Interfaces world (.plain plan rest)
  | handler {hints : Hints scope} (rest : Forest hints) (tail : Interfaces world rest) :
      Interfaces world (.handler (effect := effect) (table := table)
        (families := families) (required := required) rest)
  | cell : Interfaces world rest → Interfaces world (.cell (identity := identity) rest)
  | cleanup {hints : Hints scope} (rest : Forest hints) (required : List Requirement)
      (footprint : RequestFootprint plan required) (declared : Declared world (signature plan))
      (tail : Interfaces world rest) : Interfaces world (.cleanup (needs := needs) plan rest)
  | running : Interfaces world rest → Interfaces world (.running rest)
  | live {hints : Hints scope} (rest : Forest hints) :
      Interfaces world saved → Interfaces world rest → Interfaces world (.live (owner := owner) saved rest)
  | spent : Interfaces world rest → Interfaces world (.spent (owner := owner) rest)

/-- The check follows the normal receiving order. A dormant saved segment
receives its tail; a cleanup body additionally runs under protection. -/
def Interfaces.check {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (outside : Scope) : Bool :=
  match interfaces with
  | .nil => true
  | .plain rest required _ _ next =>
      checkRequirements ((receiving rest).append outside) required && next.check outside
  | .handler (required := required) rest next =>
      checkRequirements ((receiving rest).append outside) required && next.check outside
  | .cell next | .running next | .spent next => next.check outside
  | .cleanup rest required _ _ next =>
      checkRequirements (.running ((receiving rest).append outside)) required && next.check outside
  | .live rest saved next => saved.check ((receiving rest).append outside) && next.check outside

/-- Derive the whole retained schedule from source annotations and finite
operation checks. Actions and phases are arbitrary: operation requirements
cannot grant permission to invoke a continuation. -/
theorem Interfaces.compile {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (interfaces : Interfaces world forest) (supplied : interfaces.check outsideScope = true) :
    Pending outward actions phases world forest outside := by
  induction interfaces generalizing outsideScope with
  | nil => exact .nil
  | plain rest required footprint declared next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .plain (SourceScheduledSourceInterfaces.compile footprint declared requests) (ih remaining)
  | handler rest next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .handler requests (ih remaining)
  | cell next ih => exact .cell (ih supplied)
  | cleanup rest required footprint declared next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .cleanup (SourceScheduledSourceInterfaces.compile footprint declared requests) (ih remaining)
  | running next ih => exact .running (ih supplied)
  | live rest saved next ihSaved ihRest =>
      obtain ⟨inside, remaining⟩ := Bool.and_eq_true_iff.mp supplied
      exact .live (ihSaved inside) (ihRest remaining)
  | spent next ih => exact .spent (ih supplied)

/-- The same annotation supplies disposal's callback-only interface. Ordinary
pending code is deliberately omitted because closing discards that code. -/
def Interfaces.callbacks {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) : SourceScheduledCallbackInterfaces.Interfaces forest :=
  match interfaces with
  | .nil => .nil
  | .plain _ _ _ _ next => .plain next.callbacks
  | .handler _ next => .handler next.callbacks
  | .cell next => .cell next.callbacks
  | .cleanup rest required footprint _ next => .cleanup rest required footprint next.callbacks
  | .running next => .running next.callbacks
  | .live rest saved next => .live rest saved.callbacks next.callbacks
  | .spent next => .spent next.callbacks

theorem Interfaces.callback_declarations {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) :
    SourceScheduledCallbackInterfaces.Declared world interfaces.callbacks := by
  induction interfaces with
  | nil => exact .nil
  | plain rest required footprint declared next ih => exact .plain ih
  | handler rest next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup rest required footprint declared next ih => exact .cleanup declared ih
  | running next ih => exact .running ih
  | live rest saved next ihSaved ihRest => exact .live ihSaved ihRest
  | spent next ih => exact .spent ih

end Ash.OneShot.SourceScheduledRetainedInterfaces

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.compile
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.callback_declarations
