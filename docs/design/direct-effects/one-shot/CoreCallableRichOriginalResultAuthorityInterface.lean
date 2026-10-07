import CoreCallableRichNormalCleanupPhases

/-! Source-only candidate extending the passed phase anchor with the original
full result and typed tail retained from current armed inversion. No finish
consumer or Core/M4 rule is added. Generated still excludes Boolean. -/
namespace Ash.OneShot.CoreCallableRichOriginalResultAuthority
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology
open CoreCallableInitialChronology CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedCleanupCompletion CoreCallableReachableResume
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableContractSource (Contract Environment)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)
open CoreCallableRichNormalCleanupPhases
open CoreCallableInitialAdmission (Program)
open RecursiveRequirements (Requirements)

variable {graph : Graph} {originalEndpoint : Endpoint graph}
variable [evidence : DeclarationPolicy]

/-- The constructor-selected callback and original typed tail are retained as
data, alongside the original full saved Source/Auth. Signature/row alignment is
stored in the forward direction; it never identifies private Plans. The package
is produced under Nonempty by current armed inversion, not extracted into Type
from arbitrary running Pending. -/
structure OriginalResultAuthority
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints} {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (related : CoreValueRelation.ValueRel graph originalEndpoint.owners
      originalEndpoint.state.heap runtimeValue value) where
  original : PhaseSavedValueAuthority site related
  savedSource : Source globals outward world allowed data.scope Environment.empty value result
    [] (.request [] []) .pure Rows.pure
  savedSame : savedSource =
    IndexedSource.value_allowed original.source related.closed.1 allowed data.scope
  savedAuthentication : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
    Authenticated globals.registry outward savedSource lexical
      (actualReceiver world receiving ambient)
  publicDependencies : Dependencies
  publicPlan : Plan publicDependencies
  publicRows : Rows (signature publicPlan)
  signatureSame : HEq (signature publicPlan) callbackSignature
  rowsSame : HEq publicRows callbackRows
  callbackDemand : List Nat
  callbackRequirements : Requirements callbackDemand
  privateDependencies : Dependencies
  privatePlan : Plan privateDependencies
  privateRows : Rows (signature privatePlan)
  callbackSource : Source globals outward world allowed data.scope Environment.empty data.action
    (Contract.function .unit .unit requests latent publicPlan publicRows)
    callbackDemand callbackRequirements privatePlan privateRows
  callbackAuthentication : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
    Authenticated globals.registry outward callbackSource lexical
      (actualReceiver world receiving ambient)
  certified : Certified outward world publicPlan
  requestsSame : data.requests = requests
  answerSame : ScopedPorts.eraseType data.answer = result.port
  tail : Pending globals outward world allowed ambient stack result final context
  next : PhaseSite globals outward world requests actions phases budget ambient installations
    (.app data.action .unit) .none (.push (.running data value related.closed) stack)
    .unit final (Context.normal context) root
  waiting : Accounting.Wait world installations
    (Context.cleanup (needs := requests) latent callbackRows context) .ordinary root

/-- This current carrier retains the same original-result package and immutable
actual start. Its current endpoint must still expose that exact runtime boundary
and original tail. Nonallocating beta/Boolean may transport those observations;
no desired successor carrier is a premise. -/
structure OriginalResultCurrent
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints} {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    {site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root}
    {related : CoreValueRelation.ValueRel graph originalEndpoint.owners
      originalEndpoint.state.heap runtimeValue value}
    (authority : OriginalResultAuthority site related)
    (start : RunningStartPast graph cleanupOwners action environment data runtimeValue value
      physical stack)
    (currentEndpoint : Endpoint graph) where
  predecessor : start.predecessor = originalEndpoint.state
  heapSame : currentEndpoint.state.heap = start.predecessor.heap
  physicalSame : currentEndpoint.physical = .cleanupCompletion data.identity runtimeValue :: physical
  lexicalSame : currentEndpoint.lexical = .push (.running data value related.closed) stack

/-- Normal start produces original-result authority, the same actual boundary
carrier and the current callback receipt together. All successor rich/current
fields are outputs of current armed inversion and the existing actual kernel. -/
structure OriginalResultNormalStartEvent
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints} {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (current : PhaseCurrent program originalEndpoint site)
    (related : CoreValueRelation.ValueRel graph originalEndpoint.owners
      originalEndpoint.state.heap runtimeValue value)
    (origin : ArmedOrigin originalEndpoint data stack) where
  authority : OriginalResultAuthority site related
  start : RunningStartPast graph origin.cleanupOwners origin.action origin.environment data
    runtimeValue value origin.physical stack
  carrier : OriginalResultCurrent authority start (started start)
  after : PhaseCurrent program (started start) authority.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph originalEndpoint.state = .stepped (started start).state
  counter : (started start).state.nextCleanup = originalEndpoint.state.nextCleanup
  positive : CoreUnwindRelation.Positive originalEndpoint.point.machine
    (started start).point.machine [] []
  matching : Matching graph originalEndpoint (started start) [] []
  ownership : CurrentOwnership graph origin.cleanupOwners (started start).state .none
    (.push (.running data value related.closed) stack)

end Ash.OneShot.CoreCallableRichOriginalResultAuthority
