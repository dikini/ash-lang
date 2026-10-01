import CoreCallableReachableResume
import CoreExportedFixture

/-! Finite literal-handler identity checks and current evaluation-site lineage.
The checker is additional exported metadata evidence; checkShape alone does not
establish it. Rust's global handler-id validation and the identity-preserving
exporter justify checking the SAME exported graph. This is not a general proof
of Rust/export correspondence or dynamic activation uniqueness. -/
namespace Ash.OneShot.CoreCallableSiteLineage
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine
open CoreCallableReachableResume CoreGeneralCaptureResume CoreGeneralStack CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreRequestFrames ScopedExpressions ScopedExecution

def handlerId : CoreSyntax.Kind → Option Nat
  | .handler identity _ _ _ => some identity
  | _ => none

def UniqueHandlerSites (graph : Graph) : Prop :=
  ∀ left right : Fin graph.nodes.length,
    (handlerId graph.nodes[left].kind).isSome = true →
    handlerId graph.nodes[left].kind = handlerId graph.nodes[right].kind → left = right

instance (graph : Graph) : Decidable (UniqueHandlerSites graph) := by
  unfold UniqueHandlerSites
  infer_instance

def checkHandlerSites (graph : Graph) : Bool := decide (UniqueHandlerSites graph)

theorem checkHandlerSites_sound (accepted : checkHandlerSites graph = true) :
    UniqueHandlerSites graph := of_decide_eq_true accepted


theorem UniqueHandlerSites.lookup (unique : UniqueHandlerSites graph)
    (leftKnown : graph.node left = some leftNode)
    (leftKind : leftNode.kind = .handler handler leftEffect leftBody leftClauses)
    (rightKnown : graph.node right = some rightNode)
    (rightKind : rightNode.kind = .handler handler rightEffect rightBody rightClauses) :
    left = right := by
  obtain ⟨leftBound, leftValue⟩ := List.getElem?_eq_some_iff.mp leftKnown
  obtain ⟨rightBound, rightValue⟩ := List.getElem?_eq_some_iff.mp rightKnown
  have same := unique ⟨left, leftBound⟩ ⟨right, rightBound⟩
    (by simp [leftValue, leftKind, handlerId])
    (by simp [leftValue, rightValue, leftKind, rightKind, handlerId])
  exact congrArg Fin.val same

/-- This consumes the existing generated graph; it adds no fixture and does not
turn the weaker checkShape validator into an admission theorem. -/
theorem exported_handler_sites : UniqueHandlerSites CoreExportedFixture.graph :=
  checkHandlerSites_sound (by decide)

/-- Only current literal evaluation ancestry is recorded. A lambda call has its
own empty owner map; saved continuations retain their separately recorded site. -/
inductive SiteLineage (graph : Graph) : OwnerMap → Execution.Scope → Nat → Prop where
  | inactive (canonical : CanonicalOwnerMap graph owners) :
      SiteLineage graph owners .none site
  | clause (canonical : CanonicalOwnerMap graph owners)
      (known : graph.node handlerSite = some node)
      (kind : node.kind = .handler handler effect body clauses)
      (below : site < handlerSite) :
      SiteLineage graph (⟨handler, owner, ticket graph owner⟩ :: owners)
        (.ticket (ticket graph owner) dynamicTicket) site

theorem SiteLineage.initial (graph : Graph) : SiteLineage graph [] .none graph.root :=
  .inactive (.empty graph)

theorem SiteLineage.child {child : Nat} (receipt : SiteLineage graph owners scope site)
    (postorder : Postorder graph) (known : graph.node site = some node)
    (member : child ∈ node.kind.children) : SiteLineage graph owners scope child := by
  cases receipt with
  | inactive canonical => exact .inactive canonical
  | clause canonical handlerKnown handlerKind below =>
      exact .clause canonical handlerKnown handlerKind (Nat.lt_trans (postorder _ _ known _ member) below)

theorem SiteLineage.selected_clause {selectedClause : CoreSyntax.Clause}
    (postorder : Postorder graph) (canonical : CanonicalOwnerMap graph owners)
    (known : graph.node site = some node)
    (kind : node.kind = .handler handler effect body clauses)
    (selected : selectedClause ∈ clauses) :
    SiteLineage graph (⟨handler, selectedClause.owner, ticket graph selectedClause.owner⟩ :: owners)
      (.ticket (ticket graph selectedClause.owner) dynamicTicket) selectedClause.body := by
  apply SiteLineage.clause canonical known kind
  apply postorder _ _ known
  simp only [kind, Kind.children, List.mem_cons]
  exact Or.inr (List.mem_map.mpr ⟨selectedClause, selected, rfl⟩)

theorem SiteLineage.beta : SiteLineage graph [] .none body := .inactive (.empty graph)

/-- Literal descent cannot execute a second installation of its own enclosing
handler without first crossing a capability-reset or saved-site transition. -/
theorem SiteLineage.not_own_handler
    (unique : UniqueHandlerSites graph)
    (lineage : SiteLineage graph
      (⟨handler, owner, ticket graph owner⟩ :: owners)
      (.ticket (ticket graph owner) dynamicTicket) site)
    (known : graph.node site = some node)
    (kind : node.kind = .handler handler effect body clauses) : False := by
  cases lineage with
  | clause canonical handlerKnown handlerKind below =>
      have same := unique.lookup known kind handlerKnown handlerKind
      exact Nat.lt_irrefl _ (same ▸ below)

/-- Actual beta is retained alongside the produced empty-map site receipt;
older saved frame receipts are not changed by this current reset. -/
theorem beta_site {base : CoreMachine.State}
    (function : CoreValueRelation.ValueRel graph owners base.heap
      (.closure parameter body saved) (.lambda parameter result))
    (argument : CoreValueRelation.ValueRel graph owners base.heap value argumentCode)
    (coreTail : List CoreMachine.Frame) (scope : Execution.Scope)
    (target : ScopedExecution.Stack) :
    CoreStrictSteps.ApplicationWitness graph owners base parameter body saved value
      argumentCode result coreTail scope target ∧ SiteLineage graph [] .none body :=
  ⟨CoreStrictSteps.application_complete function argument coreTail scope target,
    SiteLineage.beta⟩

/-- Bind descent records both the actual initializer site and the saved literal
continuation site from the same parent, before either child is evaluated. -/
theorem bind_sites (lineage : SiteLineage graph owners scope site)
    (postorder : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .bind binder initializer body) :
    SiteLineage graph owners scope initializer ∧ SiteLineage graph owners scope body := by
  constructor
  · exact lineage.child postorder known (by simp [kind, CoreSyntax.Kind.children])
  · exact lineage.child postorder known (by simp [kind, CoreSyntax.Kind.children])

/-- Same selected literal clause and actual positive capture witness. -/
theorem capture_site {base : CoreMachine.State}
    (postorder : Postorder graph) (canonical : CanonicalOwnerMap graph savedOwners)
    (cut : GeneralHandlerCut graph base.heap requested whole target inside savedOwners site environment data outside cap tail)
    (known : graph.node site = some node) (kind : node.kind = .handler handler handled handlerBody clauses)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some selectedClause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
    (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Execution.Scope) :
    ∃ (argument : Nat) (body : Code),
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment whole,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base selectedClause argument value handler data.activation site environment inside outside,
          .eval ⟨body.subst argument operandCode,.ticket (ticket graph selectedClause.owner) base.nextOwner,
            .live base.nextOwner operationResult data.answer cap data.scope tail⟩,
          ⟨handler,selectedClause.owner,ticket graph selectedClause.owner⟩ :: savedOwners,[]⟩ [.ticket base.nextOwner] [] ∧
      SiteLineage graph (⟨handler, selectedClause.owner, ticket graph selectedClause.owner⟩ :: savedOwners)
        (.ticket (ticket graph selectedClause.owner) base.nextOwner) selectedClause.body := by
  obtain ⟨fuel, argument, rawBody, body, pattern, selectedBody, translated, closed, header, step⟩ :=
    capture_general cut known kind selected operand requestCarrier plain context ready operationResult runtimeScope
  exact ⟨argument.id, body, step,
    SiteLineage.selected_clause postorder canonical known kind (List.mem_of_find?_eq_some selected)⟩

/-- Saved bind site is indexed by the actual physical frame and the map/scope
that produced it; current callee maps do not replace this recorded site. -/
structure SavedBindSite (graph : Graph) (owners : OwnerMap) (heap : CoreMachine.Heap)
    (parameter body : Nat) (environment : CoreMachine.Environment)
    (plain : PlainData) (below : List CoreMachine.Frame) : Prop where
  saved : SavedFrameOrigin graph owners heap (.bind parameter body environment) plain below
  site : SiteLineage graph owners plain.scope body

theorem bind_focus_site {base : CoreMachine.State} (plain : PlainData)
    (postorder : Postorder graph) (lineage : SiteLineage graph owners plain.scope site)
    (known : graph.node site = some node) (kind : node.kind = .bind binder initializer body)
    (it : translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (ready : ClosedExcept binder.id suffix)
    (context : plain.context = .bind binder.id suffix)
    (ownership : CurrentOwnership graph owners {base with frames := framesOf annotations} plain.scope target)
    (older : PushedWithMaps graph base.heap annotations target) :
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    SavedBindSite graph owners base.heap binder.id body environment plain (framesOf annotations) ∧
    SiteLineage graph owners plain.scope initializer := by
  obtain ⟨before, next, raw, after, link, saved, owned⟩ :=
    bind_focus_owned known kind it bt current notValue ready plain context ownership older
  obtain ⟨child, continuation⟩ := bind_sites lineage postorder known kind
  exact ⟨next, raw, ⟨saved, continuation⟩, child⟩

theorem bind_return_site {base : CoreMachine.State}
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .bind parameter suffix)
    (receipt : SavedBindSite graph savedOwners base.heap parameter body environment plain (framesOf annotations))
    (bounded : TicketBound base (.push (.plain plain) target))
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Execution.Scope) :
    CoreMachine.next graph {base with control := .returned value, frames := .bind parameter body environment :: framesOf annotations} =
      .stepped {base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations} ∧
    RawStep ⟨argumentCode,runtimeScope,.push (.plain plain) target⟩
      ⟨.bind parameter argumentCode suffix,plain.scope,target⟩ [] [] ∧
    RawStep ⟨.bind parameter argumentCode suffix,plain.scope,target⟩
      ⟨suffix.subst parameter argumentCode,plain.scope,target⟩ [] [] ∧
    SiteLineage graph savedOwners plain.scope body := by
  obtain ⟨before, next, plug, bind, after, owned⟩ :=
    bind_return_owned argument plain context receipt.saved bounded tail runtimeScope
  exact ⟨next, plug, bind, receipt.site⟩

#print axioms checkHandlerSites_sound
#print axioms UniqueHandlerSites.lookup
#print axioms exported_handler_sites
#print axioms SiteLineage.initial
#print axioms SiteLineage.child
#print axioms SiteLineage.selected_clause
#print axioms SiteLineage.beta
#print axioms SiteLineage.not_own_handler
#print axioms beta_site
#print axioms bind_sites
#print axioms capture_site
#print axioms bind_focus_site
#print axioms bind_return_site

end Ash.OneShot.CoreCallableSiteLineage
