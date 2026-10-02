import CoreCallableCompositionalResourceOpening
import CoreCallableGeneralResourceInitialRoot
namespace Ash.OneShot.CoreCallableCompositionalResourceRoot
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableCompositionalResourceBody
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev entries := CoreCallableGeneralResourceInitialRoot.entries
abbrev policy := CoreCallableGeneralResourceInitialRoot.policy
abbrev globals := CoreCallableGeneralResourceInitialRoot.globals
abbrev initializerAnnotation := CoreCallableGeneralResourceInitialRoot.initializerAnnotation
abbrev resourceInitializer := CoreCallableGeneralResourceInitialRoot.resourceInitializer
abbrev original : CoreCallableStaticProducer.Bindings := [(7,.integer)]
abbrev outside : CoreCallableCompositionalResourceBody.Context := [(7,.old (.slot 0))]
abbrev handles : CoreCallableCompositionalResourceBody.Context := (9,.old (.reference (.bound 3)))::outside

def patternOf (_body : Body original context code pattern checking needs) : Pattern := pattern
def codeOf (_body : Body original context code pattern checking needs) : Code := code
def checkingOf (_body : Body original context code pattern checking needs) : Checking := checking
def needsOf (_body : Body original context code pattern checking needs) : Need := needs

def oldRead : CoreCallableFiniteResourceTemplate.Body [(9,.reference (.bound 3)),(7,.slot 0)]
    (.perform (.cell (.bound 3)) 0 (.variable 9)) .integer := .read (.variable .head)
def oldUnit : CoreCallableFiniteResourceTemplate.Body [] .unit .unit := .unit

def reader := Body.lambda (original := original) (context := handles) (parameter := 10)
  (.old .unit) [.cell (.bound 3)] (Body.embedded (context := (10,.old .unit)::handles) oldRead)
def readerPattern := patternOf reader
abbrev withReader : CoreCallableCompositionalResourceBody.Context := (12,readerPattern)::handles

def applyFormal := Body.app (Body.variable (original := original)
    (context := (11,readerPattern)::withReader) Ref.head)
  (Body.embedded (context := (11,readerPattern)::withReader) oldUnit)
def higherOrder := Body.lambda (parameter := 11) readerPattern [.cell (.bound 3)] applyFormal
def higherPattern := patternOf higherOrder
abbrev withHigher : CoreCallableCompositionalResourceBody.Context := (13,higherPattern)::withReader

def actualCall := Body.app (Body.variable (original := original) (context := withHigher) Ref.head)
  (Body.variable (Ref.tail Ref.head))
abbrev afterCall : CoreCallableCompositionalResourceBody.Context := (5,.old .integer)::withHigher

def condition := Body.embedded (original := original) (context := afterCall)
  (CoreCallableFiniteResourceTemplate.Body.boolean (context := []) true)
def returned := Body.variable (original := original) (context := afterCall)
  (Ref.tail (Ref.tail (Ref.tail (Ref.tail Ref.head))))
def choice := Body.branch condition returned returned

def body := Body.bind (parameter := 9)
  (Body.embedded (original := original) (context := outside)
    (CoreCallableFiniteResourceTemplate.Body.reference (context := [(7,.slot 0)]) (.bound 3)))
  (Body.bind (parameter := 12) reader
    (Body.bind (parameter := 13) higherOrder (Body.bind (parameter := 5) actualCall choice)))

theorem resource_checked : CoreCallableCompositionalResourceOpening.resourceCheck original body
    CoreCallableFiniteCellRegistry.original 3 [] [] [] [(7,[])] [] = true := by
  rfl

theorem compositional_checked : ∃ receipt,
    CoreCallableCompositionalResourceOpening.check_compositional initializerAnnotation body CoreCallableFiniteCellRegistry.original
      policy [] [] [] [] .none 3 [(7,[])] [] = .ok receipt := ⟨_,rfl⟩

def rootCode : Code := .bind 7 (.integer 17) (.resource 3 resourceInitializer (codeOf body))
def rootPlan := Plan.sequence Plan.pure
  (CoreCallableCompositionalResourceOpening.combinedPlan body (Plan.sequence Plan.pure Plan.pure))
def rootRows : Rows (signature rootPlan) := sequenceRows Rows.pure
  (CoreCallableCompositionalResourceOpening.combinedRows body (sequenceRows Rows.pure Rows.pure))
def rootRequirements : Requirements [] := .sequence (.request [] [])
  (.sequence (.sequence (.request [] []) (.request [] [])) (needsOf body).outsideRequirements)

theorem closed_original_source : ∃ source : Source globals [] [] [] .none Environment.empty rootCode .integer [] rootRequirements rootPlan rootRows,
    Authenticated globals.registry [] source ([] : LexicalBounds) [] := by
  obtain ⟨receipt,accepted⟩ := CoreCallableGeneralResourceInitialRoot.original_initializer_checked
  obtain ⟨initializer,_tree,authenticated,_⟩ := CoreCallableFiniteRegistryBridge.recheck_success accepted
  obtain ⟨resourceReceipt,resourceAccepted⟩ := compositional_checked
  let resource := CoreCallableCompositionalResourceOpening.check_success resourceAccepted
  refine ⟨.bind initializer resource.source,.checked ?_ (.bind authenticated resource.authenticated)⟩
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  change ([] : List Nat) ⊆ []
  exact List.Subset.refl _


abbrev readerType : CoreSyntax.ValueType := .function .unit .integer [.cell (.bound 3)]
abbrev higherType : CoreSyntax.ValueType := .function readerType .integer [.cell (.bound 3)]

/-- The SAME original graph has the ordinary handle wrapper, the nonliteral
initializer, a stored reader passed through an ordinary higher-order slot, and
an exhaustive Bool branch returning outer7. Shape/translation is conditional
representation evidence, not initial StaticProducer or Rust admission. -/
def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 17) .integer,
  CoreTranslation.Examples.node 1 (.integer 0) .integer,
  CoreTranslation.Examples.node 2 (.variable 20) .integer,
  CoreTranslation.Examples.node 3 (.bind ⟨20,.integer⟩ 1 2) .integer,
  CoreTranslation.Examples.node 4 (.variable 9) (.reference (.bound 3)),
  CoreTranslation.Examples.node 5 (.request (.cell (.bound 3)) 0 4) .integer,
  CoreTranslation.Examples.node 6 (.function ⟨10,.unit⟩ 5) readerType,
  CoreTranslation.Examples.node 7 (.variable 11) readerType,
  CoreTranslation.Examples.node 8 .unit .unit,
  CoreTranslation.Examples.node 9 (.apply 7 8) .integer,
  CoreTranslation.Examples.node 10 (.function ⟨11,readerType⟩ 9) higherType,
  CoreTranslation.Examples.node 11 (.variable 13) higherType,
  CoreTranslation.Examples.node 12 (.variable 12) readerType,
  CoreTranslation.Examples.node 13 (.apply 11 12) .integer,
  CoreTranslation.Examples.node 14 (.boolean true) .boolean,
  CoreTranslation.Examples.node 15 (.variable 7) .integer,
  CoreTranslation.Examples.node 16 (.variable 7) .integer,
  CoreTranslation.Examples.node 17 (.matchCases 14 [⟨.boolean true,15⟩,⟨.boolean false,16⟩]) .integer,
  CoreTranslation.Examples.node 18 (.bind ⟨5,.integer⟩ 13 17) .integer,
  CoreTranslation.Examples.node 19 (.bind ⟨13,higherType⟩ 10 18) .integer,
  CoreTranslation.Examples.node 20 (.bind ⟨12,readerType⟩ 6 19) .integer,
  CoreTranslation.Examples.node 21 (.resource 3 ⟨9,.reference (.bound 3)⟩ 3 20) .integer,
  CoreTranslation.Examples.node 22 (.bind ⟨7,.integer⟩ 0 21) .integer],22⟩

theorem original_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl
theorem original_graph_translation : CoreTranslation.translate graph = .ok rootCode := rfl
theorem original_closed_support : rootCode.dependencies = [] := rfl

def pureReader := Body.lambda (original := original) (context := handles) (parameter := 10)
  (.old .unit) [] (Body.embedded (context := (10,.old .unit)::handles) oldRead)
theorem pure_reader_rejected : pureReader.check original 3 [] [] [.cell (.bound 3)] = false := rfl

def escapingReader := Body.bind (parameter := 9)
  (Body.embedded (original := original) (context := outside)
    (CoreCallableFiniteResourceTemplate.Body.reference (context := [(7,.slot 0)]) (.bound 3))) reader

theorem fresh_read_callable_escape_rejected : CoreCallableCompositionalResourceOpening.resourceCheck original escapingReader
    CoreCallableFiniteCellRegistry.original 3 [] [] [] [(7,[])] [] = false := rfl

def shadowed := Body.variable (original := original) (context := [(7,.old .unit),(7,.old (.slot 0))])
  (Ref.tail Ref.head)
theorem shadowed_slot_rejected : shadowed.check original 3 [] [] [] = false := rfl

theorem unsupported_exact_recipe_rejected
    (ref : Ref context name (.old (.slot index)))
    (slot : FunctionSlot originalBindings index input output requests latent plan rows) :
    (Body.slotCallable ref slot (.unsupported plan)).check originalBindings binder world residual allowed = false := by
  simp [Body.check,CoreCallableStaticProducer.RecipeTag.check]

/-- Every identity uses the same produced initializer and full computed
private checking Plan/Rows; the family is an output of the finite tree. -/
theorem opening_at_every_fresh_identity (identity : Nat) : ∃ source : IndexedSource
    globals.registry [] globals.owners [identity] [.cell identity] .none
    (CoreCallableStaticProducer.environment original)
    ((codeOf body).instantiate (Instantiation.Environment.empty.bind 3 identity))
    .integer [] ((needsOf body).requirements identity) ((checkingOf body).plan identity) ((checkingOf body).rows identity),
    Authenticated globals.registry [] source ([(7,[])] : LexicalBounds) [identity] := by
  obtain ⟨receipt,accepted⟩ := compositional_checked
  let result := CoreCallableCompositionalResourceOpening.check_success accepted
  exact ⟨result.opening.source identity (by simp),result.opening.auth identity (by simp)⟩

#print axioms original_graph_shape
#print axioms original_graph_translation
#print axioms original_closed_support
#print axioms pure_reader_rejected
#print axioms fresh_read_callable_escape_rejected
#print axioms shadowed_slot_rejected
#print axioms unsupported_exact_recipe_rejected
#print axioms opening_at_every_fresh_identity

#print axioms resource_checked
#print axioms compositional_checked
#print axioms closed_original_source
end Ash.OneShot.CoreCallableCompositionalResourceRoot
