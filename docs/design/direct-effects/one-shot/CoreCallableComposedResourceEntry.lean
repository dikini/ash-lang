import CoreCallableComposedResourceOrigins
import CoreCallableInitialChronology
namespace Ash.OneShot.CoreCallableComposedResourceEntry
open ScopedExpressions ScopedExecution CoreSyntax CoreTranslation CoreMachine CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreInitialPrefix CoreStrictPotential CoreAdministrativeTransport
open CoreTranslationFuel CoreOrdinaryCompletion CoreEffectEntry CoreEffectFrames

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Initial syntax evidence is projected from the retained executed graph prior. -/
theorem initial_from_checked
    (checked : CoreCallableComposedResourceOrigins.CheckedGraphPrefix graph
      (path : CoreCallableComposedResourceOrigins.Prefix entries owners root code bindings) api policy declarations outward world allowed scope receiver) :
    CoreCallableInitialChronology.InitialInput graph root :=
  ⟨checked.shape,by simpa [CoreTranslation.translate,checked.shape,Bind.bind,Except.bind] using checked.translated⟩

private theorem integer_bind {base : CoreMachine.State}
    (ordered : CoreTranslationFuel.Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .bind binder initializer body)
    (iknown : graph.node initializer = some inode) (ikind : inode.kind = .integer payload)
    (it : translateFuel graph fuel [] initializer = .ok (.integer payload))
    (bt : translateFuel graph fuel [] body = .ok rawBody)
    (current : EnvCloses graph [] base.heap environment
      (.bind binder.id (.integer payload) rawBody) (.bind binder.id (.integer payload) suffix))
    (ready : ClosedExcept binder.id suffix) (plain : PlainData)
    (context : plain.context = .bind binder.id suffix)
    (tail : PushedWithMaps graph base.heap annotations target) :
    let entered := { base with
      control := .evaluate initializer environment,
      frames := .bind binder.id body environment :: framesOf annotations,
      observations := base.observations ++ [.entered site]}
    let returned := { entered with
      control := .returned (.integer payload),
      observations := entered.observations ++ [.entered initializer]}
    let completed := { returned with
      control := .evaluate body (.binding binder.id (.integer payload) environment),
      frames := framesOf annotations}
    let before : Point := ⟨{ base with
      control := .evaluate site environment,frames := framesOf annotations},
      ⟨.bind binder.id (.integer payload) suffix,plain.scope,target⟩,[],annotations⟩
    let middle : Point := ⟨entered,before.target,[],([], .bind binder.id body environment)::annotations⟩
    let value : Point := ⟨returned,before.target,[],middle.annotations⟩
    let after : Point := ⟨completed,⟨suffix.subst binder.id (.integer payload),plain.scope,target⟩,[],annotations⟩
    Chain graph before [middle,value,after] after ∧
    EnvCloses graph [] base.heap (.binding binder.id (.integer payload) environment)
      rawBody (suffix.subst binder.id (.integer payload)) := by
  dsimp only
  obtain ⟨init,saved⟩ := bind_components current
  have closed := (ValueRel.integer (graph := graph) (owners := []) (heap := base.heap) (value := payload)).closed
  have entry := bind_entry_same_target ordered known kind it bt current closed ready plain context tail
  have witness := (CoreAdministrativeSteps.integer_evaluate
    (base := {base with observations := base.observations ++ [.entered site]}) iknown ikind init
    (.bind binder.id body environment :: framesOf annotations)).1
  have frame : PlainFrameRel graph [] base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph [] base.heap _ plain.context
    rw [context]; exact .bind bt saved ready
  have stack := prepend_mapped frame closed (pushed_mapped tail) plain.scope
  simp only [context,Context.plug] at stack
  have transport := value_entry_mapped witness rfl rfl stack
  have related : ValueRel graph [] base.heap (.integer payload) (.integer payload) := .integer
  obtain ⟨_,next,_,bind,_⟩ := bind_return_mapped
    (base := {base with observations := base.observations ++ [.entered site] ++ [.entered initializer]})
    bt saved ready related plain context tail plain.scope
  exact ⟨.next (.traversal entry) (.next (.value transport)
    (.last (.positive transport.successor next (.one bind) (by
      exact ⟨rfl,_,plain.scope,.evaluate bt (saved.beta_argument related),pushed_mapped tail⟩)))),
    saved.beta_argument related⟩

/-- Only original finite graph selections and current readiness guards enter.
All environments and successor points are computed, never selected by a caller. -/
structure Selection (graph : Graph) where
  outer : Binder
  outerSite : Nat
  resourceSite : Nat
  initializerSite : Nat
  initializerLiteral : Nat
  initializerVariable : Nat
  bodySite : Nat
  inner : Binder
  resource : Nat
  handle : Binder
  outerValue : Int
  payload : Int
  rootNode : CoreSyntax.Node
  outerNode : CoreSyntax.Node
  resourceNode : CoreSyntax.Node
  initializerNode : CoreSyntax.Node
  literalNode : CoreSyntax.Node
  variableNode : CoreSyntax.Node
  rawBody : Code
  fuel : Nat
  rootKnown : graph.node graph.root = some rootNode
  rootKind : rootNode.kind = .bind outer outerSite resourceSite
  outerKnown : graph.node outerSite = some outerNode
  outerKind : outerNode.kind = .integer outerValue
  resourceKnown : graph.node resourceSite = some resourceNode
  resourceKind : resourceNode.kind = .resource resource handle initializerSite bodySite
  initializerKnown : graph.node initializerSite = some initializerNode
  initializerKind : initializerNode.kind = .bind inner initializerLiteral initializerVariable
  literalKnown : graph.node initializerLiteral = some literalNode
  literalKind : literalNode.kind = .integer payload
  variableKnown : graph.node initializerVariable = some variableNode
  variableKind : variableNode.kind = .variable inner.id
  bodyTranslated : translateFuel graph fuel [] bodySite = .ok rawBody
  resourceTranslated : translateFuel graph fuel [] resourceSite = .ok
    (.resource resource (.bind inner.id (.integer payload) (.variable inner.id))
      (.bind handle.id (.resourceRef (.bound resource)) rawBody))
  outerTranslated : translateFuel graph fuel [] outerSite = .ok (.integer outerValue)
  initialTranslated : translateFuel graph fuel [] initializerSite = .ok (.bind inner.id (.integer payload) (.variable inner.id))
  literalTranslated : translateFuel graph fuel [] initializerLiteral = .ok (.integer payload)
  variableTranslated : translateFuel graph fuel [] initializerVariable = .ok (.variable inner.id)
  innerDifferent : inner.id ≠ outer.id
  handleDifferent : handle.id ≠ outer.id
  outerReady : ClosedExcept outer.id
    (.resource resource (.bind inner.id (.integer payload) (.variable inner.id))
      (.bind handle.id (.resourceRef (.bound resource)) rawBody))
  bodyReady : ClosedExcept handle.id (rawBody.subst outer.id (.integer outerValue))
  outerNoTicket : Execution.Scope.none.translate
    (Context.bind outer.id (.resource resource (.bind inner.id (.integer payload) (.variable inner.id))
      (.bind handle.id (.resourceRef (.bound resource)) rawBody))).dependencies = some []
  resourceNoTicket : Execution.Scope.none.translate
    (Context.resource resource (.bind handle.id (.resourceRef (.bound resource))
      (rawBody.subst outer.id (.integer outerValue)))).dependencies = some []
  resourceClosed : (Code.resource resource (.integer payload)
    (.bind handle.id (.resourceRef (.bound resource)) (rawBody.subst outer.id (.integer outerValue)))).ResourceClosed

def Selection.rootCode (s : Selection graph) : Code :=
  .bind s.outer.id (.integer s.outerValue)
    (.resource s.resource (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
      (.bind s.handle.id (.resourceRef (.bound s.resource)) s.rawBody))

def Selection.outerEnvironment (s : Selection graph) : Environment :=
  .binding s.outer.id (.integer s.outerValue) .empty

def Selection.closedBody (s : Selection graph) : Code := s.rawBody.subst s.outer.id (.integer s.outerValue)
def Selection.resourceCode (s : Selection graph) : Code :=
  .resource s.resource (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
    (.bind s.handle.id (.resourceRef (.bound s.resource)) s.closedBody)
def Selection.outerPlain (s : Selection graph) : PlainData :=
  ⟨.bind s.outer.id (.resource s.resource (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
    (.bind s.handle.id (.resourceRef (.bound s.resource)) s.rawBody)),.none,.integer,.integer,[],s.outerNoTicket⟩
def Selection.resourcePlain (s : Selection graph) : PlainData :=
  ⟨.resource s.resource (.bind s.handle.id (.resourceRef (.bound s.resource)) s.closedBody),.none,.integer,.integer,[],s.resourceNoTicket⟩
def Selection.innerPlain (s : Selection graph) : PlainData :=
  ⟨.bind s.inner.id (.variable s.inner.id),.none,.integer,.integer,[],by simp [Context.dependencies,Context.plug,Code.dependencies,Syntax.without,Execution.Scope.translate]⟩

def Selection.s0 (_s : Selection graph) : CoreMachine.State := CoreMachine.initial graph
def Selection.s1 (s : Selection graph) : CoreMachine.State := {s.s0 with
  control := .evaluate s.outerSite .empty,frames := [.bind s.outer.id s.resourceSite .empty],
  observations := [.entered graph.root]}
def Selection.s2 (s : Selection graph) : CoreMachine.State := {s.s1 with
  control := .returned (.integer s.outerValue),observations := s.s1.observations ++ [.entered s.outerSite]}
def Selection.s3 (s : Selection graph) : CoreMachine.State := {s.s2 with
  control := .evaluate s.resourceSite s.outerEnvironment,frames := []}
def Selection.s4 (s : Selection graph) : CoreMachine.State := {s.s3 with
  control := .evaluate s.initializerSite s.outerEnvironment,
  frames := [.resourceInitializer s.resourceSite s.resource s.handle s.bodySite s.outerEnvironment],
  observations := s.s3.observations ++ [.entered s.resourceSite]}
def Selection.s5 (s : Selection graph) : CoreMachine.State := {s.s4 with
  control := .evaluate s.initializerLiteral s.outerEnvironment,
  frames := .bind s.inner.id s.initializerVariable s.outerEnvironment :: s.s4.frames,
  observations := s.s4.observations ++ [.entered s.initializerSite]}
def Selection.s6 (s : Selection graph) : CoreMachine.State := {s.s5 with
  control := .returned (.integer s.payload),observations := s.s5.observations ++ [.entered s.initializerLiteral]}
def Selection.s7 (s : Selection graph) : CoreMachine.State := {s.s6 with
  control := .evaluate s.initializerVariable (.binding s.inner.id (.integer s.payload) s.outerEnvironment),
  frames := s.s4.frames}
def Selection.s8 (s : Selection graph) : CoreMachine.State := {s.s7 with
  control := .returned (.integer s.payload),observations := s.s7.observations ++ [.entered s.initializerVariable]}
def Selection.acquiredEnvironment (s : Selection graph) : Environment :=
  .binding s.handle.id (.handle s.s8.nextActivation) (.resource s.resource s.s8.nextActivation s.outerEnvironment)
def Selection.openedBody (s : Selection graph) : Code :=
  (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)).subst s.handle.id
    (.resourceRef (.activation s.s8.nextActivation))
def Selection.s9 (s : Selection graph) : CoreMachine.State := {s.s8 with
  control := .evaluate s.bodySite s.acquiredEnvironment,
  frames := [.resourceBoundary s.resourceSite s.s8.nextActivation s.payload],
  nextActivation := s.s8.nextActivation+1,observations := s.s8.observations ++ [.acquired s.resourceSite s.s8.nextActivation]}

def Selection.p0 (s : Selection graph) : Point := ⟨s.s0,⟨s.rootCode,.none,.nil⟩,[],[]⟩
def Selection.p1 (s : Selection graph) : Point := ⟨s.s1,s.p0.target,[],[([], .bind s.outer.id s.resourceSite .empty)]⟩
def Selection.p2 (s : Selection graph) : Point := ⟨s.s2,s.p0.target,[],s.p1.annotations⟩
def Selection.p3 (s : Selection graph) : Point := ⟨s.s3,⟨s.resourceCode,.none,.nil⟩,[],[]⟩
def Selection.resourceMaps (s : Selection graph) : List MappedFrame :=
  [([], .resourceInitializer s.resourceSite s.resource s.handle s.bodySite s.outerEnvironment)]
def Selection.p4 (s : Selection graph) : Point := ⟨s.s4,
  ⟨.bind s.inner.id (.integer s.payload) (.variable s.inner.id),.none,.push (.plain s.resourcePlain) .nil⟩,
  [],s.resourceMaps⟩
def Selection.p5 (s : Selection graph) : Point := ⟨s.s5,s.p4.target,[],
  ([], .bind s.inner.id s.initializerVariable s.outerEnvironment)::s.resourceMaps⟩
def Selection.p6 (s : Selection graph) : Point := ⟨s.s6,s.p4.target,[],s.p5.annotations⟩
def Selection.p7 (s : Selection graph) : Point := ⟨s.s7,
  ⟨.integer s.payload,.none,.push (.plain s.resourcePlain) .nil⟩,[],s.resourceMaps⟩
def Selection.p8 (s : Selection graph) : Point := ⟨s.s8,s.p7.target,[],s.resourceMaps⟩
def Selection.p9 (s : Selection graph) : Point := ⟨s.s9,
  ⟨s.openedBody,.none,.push (.cell s.s8.nextActivation s.payload .none .integer) .nil⟩,
  [],[([], .resourceBoundary s.resourceSite s.s8.nextActivation s.payload)]⟩

private theorem outer_produced (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    Chain graph s.p0 [s.p1,s.p2,s.p3] s.p3 ∧
    EnvCloses graph [] [] s.outerEnvironment
      (.resource s.resource (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
        (.bind s.handle.id (.resourceRef (.bound s.resource)) s.rawBody)) s.resourceCode := by
  have produced := integer_bind (base := CoreMachine.initial graph) (annotations := []) (target := .nil)
    (checkShape_postorder graph input.shape) s.rootKnown s.rootKind s.outerKnown s.outerKind
    s.outerTranslated s.resourceTranslated (EnvCloses.empty (graph := graph) (owners := []) (heap := []))
    s.outerReady s.outerPlain rfl PushedWithMaps.nil
  simpa [Selection.p0,Selection.p1,Selection.p2,Selection.p3,Selection.rootCode,Selection.s0,
    Selection.s1,Selection.s2,Selection.s3,CoreMachine.initial,Selection.outerEnvironment,
    Selection.outerPlain,Selection.resourceCode,Selection.closedBody,Code.subst,
    s.innerDifferent,s.handleDifferent,Ne.symm s.innerDifferent,Ne.symm s.handleDifferent,framesOf] using produced

/-- Retain the installed unit-body carrier from original resource focus. -/
structure ResourcePast (s : Selection graph) : Prop where
  original : EnvCloses graph [] [] s.outerEnvironment
    (.resource s.resource (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
      (.bind s.handle.id (.resourceRef (.bound s.resource)) s.rawBody)) s.resourceCode
  carrier : InitializerRel graph [] []
    (.resourceInitializer s.resourceSite s.resource s.handle s.bodySite s.outerEnvironment) s.resourcePlain

private theorem resource_produced (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    ResourcePast s ∧ Link graph s.p3 s.p4 := by
  have original := (outer_produced s input).2
  have focused := CoreStrictFocus.resource_initializer_focus
    (base := s.s3) (annotations := []) (target := .nil)
    s.resourceKnown s.resourceKind s.initialTranslated s.bodyTranslated original
    (by simp [Code.IsValue]) s.resourcePlain rfl PushedWithMaps.nil
  obtain ⟨_,saved⟩ := resource_components original
  exact ⟨⟨original,.resource s.resourceKnown s.resourceKind s.bodyTranslated saved rfl⟩,
    by simpa [Selection.p3,Selection.p4,Selection.s4,Selection.resourceMaps,
      Selection.resourceCode,Selection.resourcePlain,Selection.s3,Selection.s2,Selection.s1,Selection.s0,CoreMachine.initial,framesOf] using focused.2.2.2.2⟩

private theorem inner_produced (s : Selection graph) (past : ResourcePast s)
    (ordered : CoreTranslationFuel.Postorder graph) :
    Chain graph s.p4 [s.p5,s.p6,s.p7] s.p7 ∧
    EnvCloses graph [] [] (.binding s.inner.id (.integer s.payload) s.outerEnvironment)
      (.variable s.inner.id) (.integer s.payload) := by
  have current : EnvCloses graph [] [] s.outerEnvironment
      (.bind s.inner.id (.integer s.payload) (.variable s.inner.id))
      (.bind s.inner.id (.integer s.payload) (.variable s.inner.id)) := by
    apply EnvCloses.binding ValueRel.integer
    simpa [Code.subst,s.innerDifferent,Ne.symm s.innerDifferent] using
      (EnvCloses.empty (graph := graph) (owners := []) (heap := [])
        (code := .bind s.inner.id (.integer s.payload) (.variable s.inner.id)))
  have older : PushedWithMaps graph [] s.resourceMaps (.push (.plain s.resourcePlain) .nil) :=
    .initializer past.carrier .nil
  have produced := integer_bind (base := s.s4) ordered s.initializerKnown s.initializerKind
    s.literalKnown s.literalKind s.literalTranslated s.variableTranslated current
    (by simp [ClosedExcept,Code.dependencies]) s.innerPlain rfl older
  simpa [Selection.p4,Selection.p5,Selection.p6,Selection.p7,Selection.s4,Selection.s5,
    Selection.s6,Selection.s7,Selection.innerPlain,Selection.resourceMaps,
    Selection.outerEnvironment,Selection.s3,Selection.s2,Selection.s1,Selection.s0,
    CoreMachine.initial,Code.subst,framesOf] using produced

private theorem variable_produced (s : Selection graph) (past : ResourcePast s) :
    Link graph s.p7 s.p8 := by
  have closing : EnvCloses graph [] [] (.binding s.inner.id (.integer s.payload) s.outerEnvironment)
      (.variable s.inner.id) (.integer s.payload) := by
    apply EnvCloses.binding ValueRel.integer
    apply EnvCloses.binding ValueRel.integer
    simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .integer s.payload))
  have closed := (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := s.payload)).closed
  obtain ⟨value,lookup,witness,_⟩ := CoreAdministrativeSteps.variable_evaluate (base := s.s7)
    s.variableKnown s.variableKind closing closed s.s7.frames
  have actualValue : value = .integer s.payload := by
    apply Option.some.inj
    simpa [Environment.lookup] using lookup.symm
  subst value
  have transport := value_entry_mapped (scope := .none) (resultScope := .none) witness rfl rfl
    (pushed_mapped (PushedWithMaps.initializer past.carrier PushedWithMaps.nil))
  exact .value (by simpa [Selection.p7,Selection.p8,Selection.s8,Selection.s7,Selection.s6,
    Selection.s5,Selection.s4,Selection.s3,Selection.s2,Selection.s1,Selection.s0,
    CoreMachine.initial,Selection.resourceMaps,framesOf] using transport)


/-- The original saved unit-resource carrier opens the SAME body at the actual
counter. No replacement environment or independent body closing is input. -/
theorem ResourcePast.opened {graph : Graph} {s : Selection graph} (past : ResourcePast s) :
    EnvCloses graph [] [] s.acquiredEnvironment s.rawBody s.openedBody := by
  have saved := (resource_components past.original).2
  have body := (resource_body saved s.s8.nextActivation).2
  simp only [Code.instantiate,Instantiation.ResourceName.instantiate,
    Instantiation.Environment.bind,↓reduceIte] at body
  exact (bind_components body).2.beta_argument ValueRel.handle

/-- The focused saved initializer is plugged, entered, then its synthetic
handle binding is reduced: exactly three selected Raw edges. -/
theorem acquisition_three_raw (s : Selection graph) :
    ∃ first second : Configuration, RawStep s.p8.target first [] [] ∧
      RawStep first second [.resource s.s8.nextActivation] [] ∧ RawStep second s.p9.target [] [] := by
  have closed : ClosedValue (.integer s.payload) :=
    (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := s.payload)).closed
  have plug := RawStep.plug s.resourcePlain (.integer s.payload) closed .none .nil
  have enter := RawStep.enterCell s.resource s.s8.nextActivation s.payload
    (.bind s.handle.id (.resourceRef (.bound s.resource)) s.closedBody) .none .integer .nil s.resourceClosed
  have openedReady : ClosedExcept s.handle.id
      (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)) := by
    intro name member
    have bounded := acquisition_dependency_bound s.resource s.s8.nextActivation s.closedBody member
    rcases List.mem_append.mp bounded with old | added
    · exact s.bodyReady name old
    · simp at added
  have bind := RawStep.bind s.handle.id (.resourceRef (.activation s.s8.nextActivation))
    (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation))
    .none (.push (.cell s.s8.nextActivation s.payload .none .integer) .nil)
    (ValueRel.handle (graph := graph) (owners := []) (heap := []) (key := s.s8.nextActivation)).closed openedReady
  refine ⟨⟨.resource s.resource (.integer s.payload)
      (.bind s.handle.id (.resourceRef (.bound s.resource)) s.closedBody),.none,.nil⟩,
    ⟨.bind s.handle.id (.resourceRef (.activation s.s8.nextActivation))
      (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)),
      .none,.push (.cell s.s8.nextActivation s.payload .none .integer) .nil⟩,?_,?_,?_⟩
  · simpa only [Selection.p8,Selection.p7,Selection.resourcePlain,Context.plug] using plug
  · simpa only [Code.instantiate,Instantiation.ResourceName.instantiate,
      Instantiation.Environment.bind,Instantiation.Environment.empty,↓reduceIte] using enter
  · simpa only [Selection.p9,Selection.openedBody] using bind

private theorem acquisition_produced (s : Selection graph) (past : ResourcePast s) :
    Link graph s.p8 s.p9 := by
  have closed : ClosedValue (.integer s.payload) := (ValueRel.integer (graph := graph) (owners := []) (heap := []) (value := s.payload)).closed
  have current : Related graph s.p8 := by
    refine ⟨rfl,.integer s.payload,.none,.returned ValueRel.integer,?_⟩
    exact pushed_mapped (.initializer past.carrier .nil)
  have next : CoreMachine.next graph s.s8 = .stepped s.s9 := by
    simp [CoreMachine.next,Selection.s9,Selection.s8,Selection.s7,Selection.s6,Selection.s5,
      Selection.s4,Selection.acquiredEnvironment,Selection.s3,Selection.s2,Selection.s1,Selection.s0,CoreMachine.initial]
  have plug := RawStep.plug s.resourcePlain (.integer s.payload) closed .none .nil
  have enter := RawStep.enterCell s.resource s.s8.nextActivation s.payload
    (.bind s.handle.id (.resourceRef (.bound s.resource)) s.closedBody) .none .integer .nil s.resourceClosed
  have openedReady : ClosedExcept s.handle.id
      (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)) := by
    intro name member
    have bounded := acquisition_dependency_bound s.resource s.s8.nextActivation s.closedBody member
    rcases List.mem_append.mp bounded with old | added
    · exact s.bodyReady name old
    · simp at added
  have bind := RawStep.bind s.handle.id (.resourceRef (.activation s.s8.nextActivation))
    (s.closedBody.instantiate (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation))
    .none (.push (.cell s.s8.nextActivation s.payload .none .integer) .nil)
    (ValueRel.handle (graph := graph) (owners := []) (heap := []) (key := s.s8.nextActivation)).closed openedReady
  have target : Positive s.p8.target s.p9.target := by
    apply Positive.next (by simpa only [Selection.p8,Selection.p7,Selection.resourcePlain,Context.plug] using plug)
    apply Positive.next (by simpa only [Code.instantiate,Instantiation.ResourceName.instantiate,
      Instantiation.Environment.bind,Instantiation.Environment.empty,↓reduceIte] using enter)
    simpa only [Selection.p9,Selection.openedBody] using Positive.one bind
  have after : Related graph s.p9 := by
    refine ⟨rfl,s.openedBody,.none,.evaluate s.bodyTranslated past.opened,?_⟩
    exact pushed_mapped (.boundary (.cell s.resourceKnown s.resourceKind) .nil)
  exact .positive current next target after

private theorem append_chain (first : Chain graph before points middle)
    (last : Chain graph middle later after) : Chain graph before (points ++ later) after := by
  induction first with
  | last link => exact .next link last
  | next link rest ih => exact .next link (ih last)

/-- Original initial graph → outer integer binding → nonliteral initializer
execution → actual acquisition. All nine edges are produced in one chronology. -/
theorem entry_chain (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    Chain graph s.p0 [s.p1,s.p2,s.p3,s.p4,s.p5,s.p6,s.p7,s.p8,s.p9] s.p9 := by
  obtain ⟨past,focus⟩ := resource_produced s input
  have inner := (inner_produced s past (checkShape_postorder graph input.shape)).1
  exact append_chain (outer_produced s input).1
    (.next focus (append_chain inner (.next (variable_produced s past) (.last (acquisition_produced s past)))))

private theorem link_step (link : Link graph before after) : CoreMachine.Step graph before.state after.state := by
  cases link with
  | positive _ core _ _ => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core

private theorem chain_steps (chain : Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  induction chain with
  | last link => exact .snoc (.refl _) (link_step link)
  | next link rest ih =>
    simpa [Nat.add_comm] using (CoreAllocationHistory.Steps.snoc (.refl _) (link_step link)).trans ih

theorem entry_steps (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    CoreAllocationHistory.Steps graph 9 (CoreMachine.initial graph) s.s9 :=
  chain_steps (entry_chain s input)

theorem entry_opened (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    EnvCloses graph [] [] s.acquiredEnvironment s.rawBody s.openedBody :=
  (resource_produced s input).1.opened

theorem entry_saved (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) : ResourcePast s :=
  (resource_produced s input).1

noncomputable def entry_history (s : Selection graph) :
    CoreCallableGeneralHistory.GeneralHistory graph s.s9.heap s.s9.frames
      (.push (.cell s.s8.nextActivation s.payload .none .integer) .nil) :=
  .push (.boundary (.cell (owners := []) s.resourceKnown s.resourceKind)) (by trivial) .nil

theorem entry_activation (s : Selection graph)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    s.s8.nextActivation = 0 ∧ s.s9.nextActivation = 1 ∧
    CoreAllocationHistory.History s.s9 ∧
    s.acquiredEnvironment = .binding s.handle.id (.handle 0) (.resource s.resource 0 s.outerEnvironment) := by
  exact ⟨rfl,rfl,CoreAllocationHistory.initial_steps_history graph (entry_steps s input),rfl⟩

#print axioms initial_from_checked
#print axioms ResourcePast.opened
#print axioms entry_chain
#print axioms entry_steps
#print axioms entry_opened
#print axioms entry_saved
#print axioms acquisition_three_raw
#print axioms entry_history
#print axioms entry_activation
end Ash.OneShot.CoreCallableComposedResourceEntry
