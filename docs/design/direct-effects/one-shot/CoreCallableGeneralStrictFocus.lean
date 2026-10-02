import CoreStrictFocus
import CoreCallableInitialChronology
namespace Ash.OneShot.CoreCallableGeneralStrictFocus
open CoreSyntax CoreMachine CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableInitialChronology

inductive PairApplication where | pair | application

def PairApplication.node (kind : PairApplication) (left right : Nat) : CoreSyntax.Kind :=
  match kind with | .pair => .tuple [left,right] | .application => .apply left right

def PairApplication.code (kind : PairApplication) (left right : Code) : Code :=
  match kind with | .pair => .pair left right | .application => .app left right

def PairApplication.leftContext (kind : PairApplication) (right : Code) : Context :=
  match kind with | .pair => .pairLeft right | .application => .appFunction right

def PairApplication.leftFrame (kind : PairApplication) (right : Nat) (environment : Environment) : CoreMachine.Frame :=
  match kind with | .pair => .tupleLeft right environment | .application => .applyFunction right environment

def PairApplication.rightContext (kind : PairApplication) (left : Code) : Context :=
  match kind with | .pair => .pairRight left | .application => .appArgument left

def PairApplication.rightFrame (kind : PairApplication) (value : CoreMachine.Value) : CoreMachine.Frame :=
  match kind with | .pair => .tupleRight value | .application => .applyArgument value

/-- Literal current guards only. The full graph node and original closing
relation stay attached; no installed frame or future origin enters here. -/
structure EntryReady (kind : PairApplication) (current : Endpoint graph) where
  site : Nat
  left : Nat
  right : Nat
  environment : Environment
  plain : PlainData
  node : CoreSyntax.Node
  known : graph.node site = some node
  shape : node.kind = kind.node left right
  fuel : Nat
  rawLeft : Code
  rawRight : Code
  leftCode : Code
  rightCode : Code
  leftTranslated : translateFuel graph fuel current.owners left = .ok rawLeft
  rightTranslated : translateFuel graph fuel current.owners right = .ok rawRight
  closing : EnvCloses graph current.owners current.state.heap environment
    (kind.code rawLeft rawRight) (kind.code leftCode rightCode)
  notValue : ¬ leftCode.IsValue
  context : plain.context = kind.leftContext rightCode
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (kind.code leftCode rightCode) plain.scope

/-- SAME physical installation. All original literal/map/history data are
indices, and the two site and dynamic receipts are produced at entry. -/
structure EntryReceipt {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) : Prop where
  leftClosing : EnvCloses graph current.owners current.state.heap ready.environment ready.rawLeft ready.leftCode
  rightClosing : EnvCloses graph current.owners current.state.heap ready.environment ready.rawRight ready.rightCode
  saved : SavedFrameOrigin graph current.owners current.state.heap
    (kind.leftFrame ready.right ready.environment) ready.plain current.physical
  leftSite : SiteLineage graph current.owners ready.plain.scope ready.left
  rightSite : SiteLineage graph current.owners ready.plain.scope ready.right

private theorem components {kind : PairApplication} {current : Endpoint graph} (ready : EntryReady kind current) :
    EnvCloses graph current.owners current.state.heap ready.environment ready.rawLeft ready.leftCode ∧
    EnvCloses graph current.owners current.state.heap ready.environment ready.rawRight ready.rightCode := by
  cases kind with
  | pair => exact CoreCellWriteFrames.pair_components ready.closing
  | application => exact ready.closing.app_components

private theorem left_frame {kind : PairApplication} {current : Endpoint graph} (ready : EntryReady kind current) :
    PlainFrameRel graph current.owners current.state.heap (kind.leftFrame ready.right ready.environment) ready.plain := by
  have right := (components ready).2
  change FrameRel graph current.owners current.state.heap _ ready.plain.context
  rw [ready.context]
  cases kind with
  | pair => exact .tupleLeft ready.rightTranslated right
  | application => exact .applyFunction ready.rightTranslated right

theorem installed {kind : PairApplication} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current) (scopes : EvaluatedScopeOrigins current)
    (ready : EntryReady kind current) : EntryReceipt ready := by
  have lineage : SiteLineage graph current.owners ready.plain.scope ready.site := by
    simpa only [ready.empty.focus] using sites.at ready.control
  have origin : CurrentScopeOrigin graph current.owners ready.plain.scope current.physical := by
    simpa only [ready.empty.focus] using scopes.at ready.control
  have left : ready.left ∈ ready.node.kind.children := by
    rw [ready.shape]; cases kind <;> simp [PairApplication.node,CoreSyntax.Kind.children]
  have right : ready.right ∈ ready.node.kind.children := by
    rw [ready.shape]; cases kind <;> simp [PairApplication.node,CoreSyntax.Kind.children]
  exact ⟨(components ready).1,(components ready).2,
    SavedFrameOrigin.install origin (left_frame ready),lineage.child ordered ready.known left,
    lineage.child ordered ready.known right⟩

noncomputable def entry_after {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (receipt : EntryReceipt ready) : Endpoint graph := {
  state := {current.state with
    control := .evaluate ready.left ready.environment
    frames := kind.leftFrame ready.right ready.environment :: current.physical
    observations := current.state.observations ++ [.entered ready.site]}
  focus := ⟨ready.leftCode,ready.plain.scope,.nil⟩
  owners := current.owners
  maps := []
  physical := kind.leftFrame ready.right ready.environment :: current.physical
  lexical := .push (.plain ready.plain) current.lexical
  history := .push (.ordinary receipt.saved.related) (by cases kind <;> trivial) current.history
  frames := rfl }

theorem entry_actual {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (receipt : EntryReceipt ready) :
    CoreMachine.next graph current.state = .stepped (entry_after ready receipt).state := by
  have frames : current.state.frames = current.physical := by
    simpa [ready.empty.maps,framesOf] using current.frames
  have same : {current.state with control := .evaluate ready.site ready.environment,frames := current.physical} = current.state := by
    rw [← ready.control,← frames]
  cases kind with
  | pair =>
    have actual : CoreMachine.next graph {current.state with control := .evaluate ready.site ready.environment,frames := current.physical} =
        .stepped {current.state with
          control := .evaluate ready.left ready.environment
          frames := .tupleLeft ready.right ready.environment :: current.physical
          observations := current.state.observations ++ [.entered ready.site]} := by
      have shape := ready.shape
      cases h : ready.node with
      | mk original type effects source nodeKind =>
        have known := ready.known
        rw [h] at known shape
        cases shape
        simp only [CoreMachine.next,known]
    simpa only [same,entry_after,PairApplication.leftFrame] using actual
  | application =>
    have actual := (application_focus ready.known ready.shape ready.leftTranslated ready.rightTranslated
      ready.closing ready.notValue ready.plain ready.context current.physical current.lexical).1
    simpa only [same,entry_after,PairApplication.leftFrame] using actual

theorem entry_raw {kind : PairApplication} {current : Endpoint graph} (ready : EntryReady kind current) :
    RawStep ⟨kind.code ready.leftCode ready.rightCode,ready.plain.scope,current.lexical⟩
      ⟨ready.leftCode,ready.plain.scope,.push (.plain ready.plain) current.lexical⟩ [] [] := by
  cases kind with
  | pair => exact .focus ready.plain (by rw [ready.context]; exact .pairLeft ready.notValue) current.lexical
  | application => exact .focus ready.plain (by rw [ready.context]; exact .appFunction ready.notValue) current.lexical

theorem entry_positive {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (receipt : EntryReceipt ready) :
    CoreUnwindRelation.Positive current.point.machine (entry_after ready receipt).point.machine [] [] := by
  have before : current.point.machine = .eval ⟨kind.code ready.leftCode ready.rightCode,ready.plain.scope,current.lexical⟩ := by
    simp only [Endpoint.point,ready.empty.focus,CoreCleanupRunFrames.attach,Stack.append]
  rw [before]
  change CoreUnwindRelation.Positive _ (.eval ⟨ready.leftCode,ready.plain.scope,.push (.plain ready.plain) current.lexical⟩) [] []
  refine .one (.evaluate (entry_raw ready) ?_)
  cases kind <;> trivial

theorem entry_sites {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (receipt : EntryReceipt ready) : SiteOrigins (entry_after ready receipt) := by
  refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical receipt.saved.origin,?_,receipt.leftSite,?_⟩
  · simp [MapsCanonical,entry_after]
  · simp [SavedRightSites,entry_after]

theorem entry_scopes {kind : PairApplication} {current : Endpoint graph}
    (ready : EntryReady kind current) (receipt : EntryReceipt ready) : EvaluatedScopeOrigins (entry_after ready receipt) := by
  refine ⟨receipt.saved.origin.prepend_plain receipt.saved.related,?_⟩
  simp [SavedMapScopeOrigins,entry_after]

noncomputable def pair_left {current : Endpoint graph} (ordered : Postorder graph)
    (sites : SiteOrigins current) (scopes : EvaluatedScopeOrigins current) (ready : EntryReady .pair current) : Endpoint graph :=
  entry_after ready (installed ordered sites scopes ready)

noncomputable def application_function {current : Endpoint graph} (ordered : Postorder graph)
    (sites : SiteOrigins current) (scopes : EvaluatedScopeOrigins current) (ready : EntryReady .application current) : Endpoint graph :=
  entry_after ready (installed ordered sites scopes ready)

#print axioms installed
#print axioms entry_actual
#print axioms entry_raw
#print axioms entry_positive
#print axioms entry_sites
#print axioms entry_scopes
end Ash.OneShot.CoreCallableGeneralStrictFocus
