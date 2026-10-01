import CoreCallableContractRegistries

/-! Receiver-dependent checking for the experimental common callable source.
The code and accounting interfaces remain the existing interfaces. Only private
checking consumes authenticated current support. This does not establish M4
validity or a restored-world saved-frame invariant. -/
namespace Ash.OneShot.CoreCallableReceiverRefinement
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlanSignatures (Signature signature)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableRootRefinement (Refines RootTransport)

/-- Finite lexical resource data. Missing names are not authenticated by the
variable rule; the total projection is only the existing Bounds API. -/
abbrev LexicalBounds := List (Nat × List Nat)

def LexicalBounds.lookup : LexicalBounds → Nat → Option (List Nat)
  | [], _ => none
  | (key, resources) :: rest, name => if name = key then some resources else LexicalBounds.lookup rest name

def LexicalBounds.environment (bounds : LexicalBounds) : ScopedPorts.Support.Env :=
  fun name => (bounds.lookup name).getD []

def LexicalBounds.extend (bounds : LexicalBounds) (name : Nat) (resources : List Nat) : LexicalBounds :=
  (name, resources) :: bounds

@[simp] theorem LexicalBounds.environment_extend :
    (LexicalBounds.extend bounds name resources).environment =
      ScopedPorts.Support.extend bounds.environment name resources := by
  funext other
  by_cases same : other = name
  · subst other; simp [LexicalBounds.extend, LexicalBounds.environment, ScopedPorts.Support.extend, LexicalBounds.lookup]
  · simp [LexicalBounds.extend, LexicalBounds.environment, ScopedPorts.Support.extend, LexicalBounds.lookup, same]

/-- Finite call data. The parameter's actual support is bounded by the current
receiver, independently of its public contract. -/
structure CallBounds (creationWorld : List Nat) where
  world : List Nat
  receiver : List Nat
  argument : List Nat
  worldExtended : creationWorld ⊆ world
  receivingIssued : receiver ⊆ world
  argumentReceived : argument ⊆ receiver

def CallBounds.current (world : List Nat) : CallBounds world :=
  ⟨world, world, [], List.Subset.refl _, List.Subset.refl _, by simp⟩

/-- Rebase a call from an extended creation world without changing its actual
current world, receiver or argument support. -/
def CallBounds.rebase (call : CallBounds later) (larger : earlier ⊆ later) : CallBounds earlier :=
  ⟨call.world, call.receiver, call.argument, larger.trans call.worldExtended,
    call.receivingIssued, call.argumentReceived⟩

/-- Private checking is conditional on the current resource receiver. No
successor source, execution or validity is a field. -/
structure ReceiverRefines {contractDependencies actualDependencies : Dependencies}
    {contractSignature : Signature contractDependencies} {actualSignature : Signature actualDependencies}
    (contractRows : Rows contractSignature) (actualRows : Rows actualSignature)
    (receiverBound requiredSupport : List Nat) : Prop where
  code : ∀ (outward : List Instance) (actions : Syntax.UsageTickets) (budget : Footprint)
      (phases : OwnerPhaseTransitions.Phases) (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints),
      SourceAdmission.Pending outward actions budget phases world installations context .nil
        .ordinary (hints.returnMode .ordinary) →
      SourceAdmission.Code outward actions budget phases world installations contractRows context →
      SourceAdmission.Code outward actions budget phases world installations actualRows context
  checked : ∀ (ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
      (budget : Footprint) (phases : OwnerPhaseTransitions.Phases) (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints)
      (retained : SourceAdmission.Pending outward actions budget phases world installations context .nil
        .ordinary (hints.returnMode .ordinary))
      (certificate : SourceAdmission.Code outward actions budget phases world installations contractRows context),
      requiredSupport ⊆ receiverBound → receiverBound ⊆ world →
      receiverBound ⊆ scope.visibleResources ++ ambient →
      InstallationSupport.PendingChecked ambient outward retained →
      InstallationSupport.CodeChecked ambient outward certificate →
      InstallationSupport.CodeChecked ambient outward
        (code outward actions budget phases world installations context retained certificate)
  accounting : ∀ (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints)
      {demand : List Nat} (root : Requirements demand),
      Accounting.Run world installations contractRows context root →
      ∃ actualRoot : Requirements demand,
        Accounting.Run world installations actualRows context actualRoot ∧ RootTransport root actualRoot

/-- Old universally checked refinements are retained as a special case. -/
theorem ReceiverRefines.of_universal (refinement : Refines contractRows actualRows)
    (receiverBound requiredSupport : List Nat) : ReceiverRefines contractRows actualRows receiverBound requiredSupport where
  code := by
    intro outward actions budget phases world installations scope hints context retained certificate
    exact refinement.code outward actions budget phases world installations context certificate
  checked := by
    intro ambient outward actions budget phases world installations scope hints context retained certificate _ _ _ retainedChecked checked
    exact refinement.checked ambient outward actions budget phases world installations context certificate checked
  accounting := refinement.accounting

/-- Both bounds are facts about the actual lexical dependencies. In particular
requiredSupport is not an unconnected list inferred from public ports. -/
structure OpenSupport (supportEnvironment : ScopedPorts.Support.Env)
    (parameter : Nat) (body value : Code) (argumentBound requiredSupport : List Nat) : Prop where
  bodyBound : SourceSupport.Bounds (ScopedPorts.Support.extend supportEnvironment parameter argumentBound)
    body.dependencies requiredSupport
  argumentBounded : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies argumentBound

/-- Closed substitution supplies the actual successor dependency bound from
current open-body and actual-argument evidence. -/
theorem OpenSupport.substituted
    (supported : OpenSupport supportEnvironment parameter body value argumentBound requiredSupport)
    (closed : ClosedValue value) :
    SourceSupport.Bounds supportEnvironment (body.subst parameter value).dependencies requiredSupport := by
  apply SourceSupport.bounds_iff.mpr
  exact (ScopedPorts.Support.substitution_support_bound body parameter closed supported.argumentBounded.resources).trans
    (SourceSupport.bounds_iff.mp supported.bodyBound)

/-- Receiver membership for the actual substituted body follows by the same
computed dependency bound, rather than a desired successor support premise. -/
theorem OpenSupport.received
    (supported : OpenSupport supportEnvironment parameter body value argumentBound requiredSupport)
    (closed : ClosedValue value) (received : requiredSupport ⊆ receiver) :
    ScopedPorts.Support.evaluate supportEnvironment (body.subst parameter value).dependencies ⊆ receiver :=
  (SourceSupport.bounds_iff.mp (supported.substituted closed)).trans received

/-- A closed payload crossing a selected cut is checked at the clause receiver,
which can be smaller than the original request receiver. -/
structure ClauseInputSupport (value : Code) (formalBound clauseReceiver : List Nat) : Prop where
  actual : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies formalBound
  received : formalBound ⊆ clauseReceiver

theorem ClauseInputSupport.actual_received
    (support : ClauseInputSupport value formalBound clauseReceiver) :
    ScopedPorts.Support.evaluate ScopedPorts.Support.empty value.dependencies ⊆ clauseReceiver :=
  (SourceSupport.bounds_iff.mp support.actual).trans support.received

/-- A finite caller specialization in an extended world. The callback retains
cell0 while its declared pure callable port is independent of this evidence. -/
def retainingCallback : Code := .lambda 3 (.bind 4 (.resourceRef (.activation 0)) .unit)
def openInvocation : Code := .app (.variable 2) .unit

def cellCall : CallBounds [] where
  world := [0]
  receiver := [0]
  argument := [0]
  worldExtended := by simp
  receivingIssued := List.Subset.refl _
  argumentReceived := List.Subset.refl _

theorem cell_open_support :
    OpenSupport ScopedPorts.Support.empty 2 openInvocation retainingCallback [0] [0] := by
  constructor <;> apply SourceSupport.bounds_iff.mpr <;>
    simp [openInvocation, retainingCallback, Code.dependencies, Syntax.without,
      ScopedPorts.Support.evaluate, ScopedPorts.Support.extend, ScopedPorts.Support.empty]

theorem retaining_outside_receiver :
    ¬ ClauseInputSupport retainingCallback [0] [] := by
  intro support
  have impossible := support.received (show (0 : Nat) ∈ [0] by simp)
  simp at impossible

#print axioms ReceiverRefines.of_universal
#print axioms OpenSupport.substituted
#print axioms OpenSupport.received
#print axioms ClauseInputSupport.actual_received
#print axioms cell_open_support
#print axioms retaining_outside_receiver
end Ash.OneShot.CoreCallableReceiverRefinement
