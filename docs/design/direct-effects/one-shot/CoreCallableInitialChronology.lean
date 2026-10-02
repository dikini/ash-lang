import CoreCallableGeneratedCurrentScopeConsumers
import CoreReadyBindings

/-! Initial chronology for the represented named operation families. Translation
is syntax metadata, not a claim of complete rich admission or transition availability. -/
namespace Ash.OneShot.CoreCallableInitialChronology
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreStrictStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableSiteLineage
open CoreCallableGeneralHistory CoreCallableGeneratedTicketBound

structure InitialInput (graph : Graph) (code : Code) : Prop where
  shape : checkShape graph = .ok ()
  translated : translateFuel graph (graph.nodes.length + 1) [] graph.root = .ok code

noncomputable def initial_endpoint (_input : InitialInput graph code) : Endpoint graph := {
  state := CoreMachine.initial graph
  focus := ⟨code,.none,.nil⟩
  owners := [],maps := [],physical := [],lexical := .nil,history := .nil
  frames := rfl }

theorem initial_exact (input : InitialInput graph code) :
    (initial_endpoint input).state = CoreMachine.initial graph ∧
    (initial_endpoint input).focus = ⟨code,.none,.nil⟩ ∧
    (initial_endpoint input).owners = [] ∧ (initial_endpoint input).maps = [] ∧
    (initial_endpoint input).physical = [] ∧ (initial_endpoint input).lexical = .nil :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem initial_closing (_input : InitialInput graph code) :
    EnvCloses graph [] [] .empty code code := .empty

theorem initial_site_origins (input : InitialInput graph code) :
    SiteOrigins (initial_endpoint input) := by
  refine ⟨.empty graph,?_,?_,?_⟩
  · simp [MapsCanonical,initial_endpoint]
  · exact .initial graph
  · simp [SavedRightSites,initial_endpoint]

theorem initial_scope_origins (input : InitialInput graph code) :
    EvaluatedScopeOrigins (initial_endpoint input) := by
  refine ⟨.inactive (.empty graph),?_⟩
  simp [SavedMapScopeOrigins,initial_endpoint]

theorem initial_ticket_bound (input : InitialInput graph code) :
    TicketBound (initial_endpoint input).state (initial_endpoint input).point.machine.stack := by
  intro ticket
  simp [initial_endpoint,Endpoint.point,CoreCleanupRunFrames.attach,CoreMachine.initial,
    LexicalUnwind.Machine.stack,Stack.erase,Control.ticketNames,CoreTicketHistory.capturedTickets]

/-- Only the exact initial empty-history lambda-bind bootstrap is admitted.
The existing named producer computes all three Core points and final closing. -/
structure ReadyBind (input : InitialInput graph code) where
  binder : Binder
  parameter : Binder
  initializer : Nat
  body : Nat
  fnBody : Nat
  fuel : Nat
  fnFuel : Nat
  bindNode : CoreSyntax.Node
  functionNode : CoreSyntax.Node
  rawInitializer : Code
  rawBody : Code
  rawFunction : Code
  initializerCode : Code
  suffix : Code
  known : graph.node graph.root = some bindNode
  kind : bindNode.kind = .bind binder initializer body
  fnKnown : graph.node initializer = some functionNode
  fnKind : functionNode.kind = .function parameter fnBody
  it : translateFuel graph fuel [] initializer = .ok rawInitializer
  bt : translateFuel graph fuel [] body = .ok rawBody
  ft : translateFuel graph fnFuel [] fnBody = .ok rawFunction
  fnRaw : rawInitializer = .lambda parameter.id rawFunction
  certificate : CallableCertificate graph parameter.id fnBody rawFunction
  codeSame : code = .bind binder.id initializerCode suffix
  rawSame : rawInitializer = initializerCode
  bodySame : rawBody = suffix
  closed : ClosedValue initializerCode
  ready : ClosedExcept binder.id suffix
  plain : PlainData
  scope : plain.scope = .none
  context : plain.context = .bind binder.id suffix

noncomputable def ready_entered {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : CoreMachine.State :=
  {(CoreMachine.initial graph) with
    control := .evaluate ready.initializer .empty
    frames := [.bind ready.binder.id ready.body .empty]
    observations := [.entered graph.root]}
noncomputable def ready_returned {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : CoreMachine.State :=
  {(ready_entered ready) with
    control := .returned (.closure ready.parameter.id ready.fnBody .empty)
    observations := [.entered graph.root,.entered ready.initializer]}
noncomputable def ready_endpoint {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : Endpoint graph := {
  state := {(ready_returned ready) with
    control := .evaluate ready.body (.binding ready.binder.id (.closure ready.parameter.id ready.fnBody .empty) .empty),frames := []}
  focus := ⟨ready.suffix.subst ready.binder.id ready.initializerCode,.none,.nil⟩
  owners := [],maps := [],physical := [],lexical := .nil,history := .nil,frames := rfl }
noncomputable def ready_before_point {graph : Graph} {code : Code} {input : InitialInput graph code}
    (_ready : ReadyBind input) : CoreInitialPrefix.Point :=
  ⟨(initial_endpoint input).state,⟨code,.none,.nil⟩,[],[]⟩
noncomputable def ready_middle_point {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : CoreInitialPrefix.Point :=
  ⟨ready_entered ready,⟨code,.none,.nil⟩,[],[([],.bind ready.binder.id ready.body .empty)]⟩
noncomputable def ready_value_point {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : CoreInitialPrefix.Point :=
  ⟨ready_returned ready,⟨code,.none,.nil⟩,[],[([],.bind ready.binder.id ready.body .empty)]⟩
noncomputable def ready_after_point {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : CoreInitialPrefix.Point :=
  ⟨(ready_endpoint ready).state,(ready_endpoint ready).focus,[],[]⟩

theorem ready_binding_produced {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) :
    CoreInitialPrefix.Chain graph (ready_before_point ready)
      [ready_middle_point ready,ready_value_point ready,ready_after_point ready] (ready_after_point ready) ∧
    EnvCloses graph [] [] (.binding ready.binder.id (.closure ready.parameter.id ready.fnBody .empty) .empty)
      ready.rawBody (ready.suffix.subst ready.binder.id ready.initializerCode) ∧
    RawStep ⟨code,.none,.nil⟩ (ready_endpoint ready).focus [] [] := by
  have current : EnvCloses graph [] [] .empty
      (.bind ready.binder.id ready.rawInitializer ready.rawBody)
      (.bind ready.binder.id ready.initializerCode ready.suffix) := by
    rw [ready.rawSame,ready.bodySame]; exact .empty
  have produced := CoreReadyBindings.lambda_binding_mapped (base := CoreMachine.initial graph)
    (owners := []) (annotations := []) (target := .nil)
    (checkShape_postorder graph input.shape) ready.known ready.kind ready.fnKnown ready.fnKind
    ready.it ready.bt ready.ft ready.fnRaw ready.certificate current ready.closed ready.ready
    ready.plain ready.context CoreStrictStack.PushedWithMaps.nil
  simpa [ready_before_point,ready_middle_point,ready_value_point,ready_after_point,ready_endpoint,
    ready_entered,ready_returned,initial_endpoint,CoreMachine.initial,framesOf,ready.codeSame,ready.scope] using produced

private theorem general_link_next {graph : Graph} {before after : CoreInitialPrefix.Point}
    (link : CoreInitialPrefix.Link graph before after) : CoreMachine.Step graph before.state after.state := by
  cases link with
  | positive current core target successor => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core
private theorem general_chain_steps {graph : Graph} {before after : CoreInitialPrefix.Point}
    {points : List CoreInitialPrefix.Point} (chain : CoreInitialPrefix.Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  induction chain with
  | last link => exact .snoc (.refl _) (general_link_next link)
  | next link rest ih =>
    simpa [Nat.add_comm] using (CoreAllocationHistory.Steps.snoc (.refl _) (general_link_next link)).trans ih

theorem ready_binding_steps {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) :
    CoreAllocationHistory.Steps graph 3 (CoreMachine.initial graph) (ready_endpoint ready).state := by
  simpa [ready_before_point,ready_after_point,initial_endpoint] using general_chain_steps (ready_binding_produced ready).1

theorem ready_site_origins {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : SiteOrigins (ready_endpoint ready) := by
  refine ⟨.empty graph,?_,.inactive (.empty graph),?_⟩
  · simp [MapsCanonical,ready_endpoint]
  · simp [SavedRightSites,ready_endpoint]
theorem ready_scope_origins {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : EvaluatedScopeOrigins (ready_endpoint ready) := by
  refine ⟨.inactive (.empty graph),?_⟩
  simp [SavedMapScopeOrigins,ready_endpoint]
theorem ready_ticket_bound {graph : Graph} {code : Code} {input : InitialInput graph code}
    (ready : ReadyBind input) : TicketBound (ready_endpoint ready).state (ready_endpoint ready).point.machine.stack := by
  intro ticket
  simp [ready_endpoint,Endpoint.point,CoreCleanupRunFrames.attach,LexicalUnwind.Machine.stack,
    Stack.erase,Control.ticketNames,ready_returned,CoreTicketHistory.capturedTickets]

inductive InitialChronology (input : InitialInput graph code) :
    Endpoint graph → Nat → List Owner → List Owner → Type where
  | initial : InitialChronology input (initial_endpoint input) 0 [] []
  | readyBind (ready : ReadyBind input) : InitialChronology input (ready_endpoint ready) 3 [] []
  | next (earlier : InitialChronology input before count created discharged)
      (operation : Operation before after added removed) :
      InitialChronology input after (count + 1) (created ++ added) (removed ++ discharged)

theorem InitialChronology.actual_steps
    {graph : Graph} {code : Code} {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) :
    CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) current.state := by
  induction run with
  | initial => exact CoreAllocationHistory.Steps.refl (CoreMachine.initial graph)
  | readyBind ready => exact ready_binding_steps ready
  | next earlier operation ih => exact .snoc ih operation.actual.1

theorem InitialChronology.target_trace
    {graph : Graph} {code : Code} {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) :
    CoreUnwindRelation.Trace (initial_endpoint input).point.machine current.point.machine created discharged := by
  induction run with
  | initial => exact .refl _
  | readyBind ready =>
    have raw := (ready_binding_produced ready).2.2
    simpa [initial_endpoint,Endpoint.point,CoreCleanupRunFrames.attach,ready_endpoint,Stack.append] using
      (CoreUnwindRelation.Positive.one (.evaluate raw (by rw [ready.codeSame]; trivial))).trace
  | next earlier operation ih => exact ih.append operation.actual.2.target_trace

theorem InitialChronology.site_origins
    {graph : Graph} {code : Code} {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) : SiteOrigins current := by
  have ordered := checkShape_postorder graph input.shape
  induction run with
  | initial => exact initial_site_origins input
  | readyBind ready => exact ready_site_origins ready
  | next earlier operation ih => exact operation.site_origins ordered ih

theorem InitialChronology.scope_origins
    {graph : Graph} {code : Code} {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) : EvaluatedScopeOrigins current := by
  induction run with
  | initial => exact initial_scope_origins input
  | readyBind ready => exact ready_scope_origins ready
  | next earlier operation ih => exact operation.evaluating_scope ih

theorem InitialChronology.ticket_bound
    {graph : Graph} {code : Code} {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) :
    TicketBound current.state current.point.machine.stack := by
  induction run with
  | initial => exact initial_ticket_bound input
  | readyBind ready => exact ready_ticket_bound ready
  | next earlier operation ih => exact CoreCallableGeneratedTicketBound.Operation.ticket_bound operation ih

#print axioms ready_binding_produced
#print axioms ready_binding_steps
#print axioms initial_exact
#print axioms initial_closing
#print axioms initial_site_origins
#print axioms initial_scope_origins
#print axioms initial_ticket_bound
#print axioms InitialChronology.actual_steps
#print axioms InitialChronology.target_trace
#print axioms InitialChronology.site_origins
#print axioms InitialChronology.scope_origins
#print axioms InitialChronology.ticket_bound
end Ash.OneShot.CoreCallableInitialChronology
