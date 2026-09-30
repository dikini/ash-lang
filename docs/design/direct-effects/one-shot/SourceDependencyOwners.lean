import SourceDependencyFrames

/-! Structural owner bounds on source dependencies and retained scopes.
The bounds describe explicit invocations, independently of effect multiplicity
and one-shot consumption. Their connection to actual pending owners reuses the
existing usage/dependency correspondence. -/
namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
abbrev Receiving := SourceDependencyCapture.Scope

inductive Within : List Nat → List Nat → Dependencies → Prop where
  | pure : Within world owned .pure
  | request : Within world owned (.request effect operation)
  | invoke (included : key.owner ∈ owned) : Within world owned (.invoke key)
  | sequence (first : Within world owned before) (second : Within world owned after) :
      Within world owned (.sequence before after)
  | choice (left : Within world owned first) (right : Within world owned second) :
      Within world owned (.choice first second)
  | handler (body : Within world owned dependencies) :
      Within world owned (.handler effect table families dependencies)
  | cleanup (callback : Within world owned completion) (body : Within world owned dependencies) :
      Within world owned (.cleanup needs completion dependencies)
  | resource (body : ∀ identity, identity ∉ world → Within (world ++ [identity]) owned (family identity)) :
      Within world owned (.resource family)

theorem Within.world_weaken (checked : Within world owned dependencies) (larger : world ⊆ nextWorld) :
    Within nextWorld owned dependencies := by
  induction checked generalizing nextWorld with
  | pure => exact .pure
  | request => exact .request
  | invoke included => exact .invoke included
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst larger) (ihSecond larger)
  | choice left right ihLeft ihRight => exact .choice (ihLeft larger) (ihRight larger)
  | handler body ih => exact .handler (ih larger)
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger)
  | resource body ih =>
      exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))

/-- If the current ticket scope supplies no owner admitted by the annotation,
the existing usage judgment proves that the code has no free ticket action. -/
theorem expression_external_idle
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (bounded : Within world owned dependencies)
    (outside : ∀ binder owner, scope.resolve binder = some owner → owner ∉ owned) :
    Uses policy .none .available code .available := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .resourceRef
  | «variable» => exact .variable
  | lambda body outward formed latentBound ih =>
      exact .lambda (SourceOwnerClosure.expression_usage
        (DeclaredSources.expression_erase (expression_erase body)) rfl)
  | purePair left right ihLeft ihRight => exact .pair (ihLeft .pure outside) (ihRight .pure outside)
  | pair left right ihLeft ihRight =>
      cases bounded with | sequence first second => exact .pair (ihLeft first outside) (ihRight second outside)
  | app function argument admitted ihFunction ihArgument =>
      cases bounded with | sequence first rest => cases rest with
        | sequence second latent => exact .app (ihFunction first outside) (ihArgument second outside)
  | bind initializer body ihInit ihBody =>
      cases bounded with | sequence first second => exact .bind (ihInit first outside) (ihBody second outside)
  | branch condition yes no same ihCondition ihYes ihNo =>
      cases bounded with | sequence first choices => cases choices with
        | choice left right => exact .branch (ihCondition first outside) (ihYes left outside) (ihNo right outside)
  | perform known admitted operand formed ih =>
      cases bounded with | sequence first request => exact .perform (ih first outside)
  | handler body clauses capabilities coverage unique admitted table modes declarations ih ihDeclarations =>
      cases bounded with | handler checked => exact .handle (ih checked outside) capabilities
  | resume known resolved permission operand admitted formed ih =>
      cases bounded with | sequence operandBound invocation => cases invocation with
        | invoke included => exact False.elim (outside _ _ resolved included)
  | discard known resolved permission unprotected admitted =>
      cases bounded with | invoke included => exact False.elim (outside _ _ resolved included)
  | cleanup callback body admitted ihCallback ihBody =>
      cases bounded with | sequence first completion => cases completion with
        | cleanup callbackBound bodyBound => exact .cleanup (ihCallback first outside) (ihBody bodyBound outside)
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      cases bounded with | sequence first resources => cases resources with
        | resource bodyBound =>
            obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
            exact .resource (ihInit first outside)
              ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh (bodyBound identity fresh) outside))
  | typed | annotated | unavailable | available | nil | cons => trivial

theorem context_external_idle
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed scope position input output demand requirements dependencies)
    (bounded : Within world owned dependencies)
    (outside : ∀ binder owner, scope.resolve binder = some owner → owner ∉ owned) :
    Uses policy .none .available (position.plug .unit) .available := by
  cases source with
  | pairLeft right => exact .pair .unit (expression_external_idle right bounded outside)
  | pairRight left => exact .pair (SourceOwnerClosure.expression_usage
      (DeclaredSources.expression_erase (expression_erase left)) rfl) .unit
  | appFunction argument admitted =>
      cases bounded with | sequence argumentBound latent =>
        exact .app .unit (expression_external_idle argument argumentBound outside)
  | appArgument function admitted => exact .app (SourceOwnerClosure.expression_usage
      (DeclaredSources.expression_erase (expression_erase function)) rfl) .unit
  | bind body => exact .bind .unit (expression_external_idle body bounded outside)
  | branch yes no same =>
      cases bounded with | choice left right =>
        exact .branch .unit (expression_external_idle yes left outside) (expression_external_idle no right outside)
  | perform => exact .perform .unit
  | resume known resolved permission admitted formed =>
      cases bounded with | invoke included => exact False.elim (outside _ _ resolved included)
  | cleanup body admitted =>
      cases bounded with | cleanup callback bodyBound => exact .cleanup .unit (expression_external_idle body bodyBound outside)
  | resource body formed effectsBound admitted hidden =>
      cases bounded with | resource bodyBound =>
        obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
        exact .resource .unit ((instantiation_preserves_usage_iff _ _).mp
          (expression_external_idle (body identity fresh) (bodyBound identity fresh) outside))

theorem plain_pending_bound {plain : PlainData}
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies)
    (bounded : Within world owned dependencies) : plain.pending ⊆ owned := by
  intro owner pending
  by_cases included : owner ∈ owned
  · exact included
  apply False.elim
  obtain ⟨binder, dependency, resolved⟩ := (Syntax.scope_translate_membership plain.translated owner).mp pending
  have outside : ∀ other target, plain.scope.resolve other = some target → target ∉ owned := by
    intro other target known
    cases scopeSame : plain.scope with
    | none => simp [scopeSame, Execution.Scope.resolve] at resolved
    | ticket localBinder actual =>
        simp only [scopeSame, Execution.Scope.resolve] at resolved known
        split at resolved <;> simp_all
  have idle := context_external_idle source bounded outside
  obtain ⟨rights, impossible, consumed⟩ := free_ticket_requires_consumption idle dependency
  cases impossible

/-- Recursively retained live owners; spent markers grant no new ownership. -/
def owners : Receiving → List Nat
  | .nil => []
  | .plain _ rest | .handler _ _ _ rest | .cell _ rest | .cleanup _ _ rest
  | .running rest | .spent _ rest => owners rest
  | .live owner captured rest => owner :: (owners captured ++ owners rest)

/-- Only plain frames retain pending ticket actions. Other frames retain
separate callback/declaration evidence; a live boundary checks both regions. -/
inductive PendingWithin (world owned : List Nat) : Receiving → Prop where
  | nil : PendingWithin world owned .nil
  | plain (code : Within world owned dependencies) (tail : PendingWithin world owned rest) :
      PendingWithin world owned (.plain dependencies rest)
  | handler (tail : PendingWithin world owned rest) : PendingWithin world owned (.handler effect table families rest)
  | cell (tail : PendingWithin world owned rest) : PendingWithin world owned (.cell identity rest)
  | cleanup (tail : PendingWithin world owned rest) : PendingWithin world owned (.cleanup needs callback rest)
  | running (tail : PendingWithin world owned rest) : PendingWithin world owned (.running rest)
  | live (captured : PendingWithin world owned saved) (tail : PendingWithin world owned rest) :
      PendingWithin world owned (.live owner saved rest)
  | spent (tail : PendingWithin world owned rest) : PendingWithin world owned (.spent owner rest)

theorem realized_owners
    (realized : SourceDependencyCapture.Realizes tables families scope stack) : owners scope = stack.erase.liveTickets := by
  induction realized with
  | nil => rfl
  | push frame rest ih => cases frame <;> exact ih
  | live inside outside ihInside ihOutside =>
      simp only [owners, Stack.erase, Control.liveTickets, ihInside, ihOutside]
  | spent tail ih => exact ih

theorem PendingWithin.world_weaken (checked : PendingWithin world owned scope) (larger : world ⊆ nextWorld) :
    PendingWithin nextWorld owned scope := by
  induction checked with
  | nil => exact .nil
  | plain code tail ih => exact .plain (code.world_weaken larger) ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup tail ih => exact .cleanup ih
  | running tail ih => exact .running ih
  | live captured tail ihCaptured ihTail => exact .live ihCaptured ihTail
  | spent tail ih => exact .spent ih

theorem segment_pending_bound
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing)
    (bounded : PendingWithin world owned scope) : stack.erase.pending ⊆ owned := by
  induction source with
  | nil => exact List.nil_subset _
  | push frame tail bound ih =>
      cases frame with
      | plain context scope inputAnnotation outputAnnotation =>
          cases bounded with
          | plain current later => exact List.append_subset.mpr ⟨plain_pending_bound context current, ih later⟩
      | handler scope annotation clauses coverage unique declarations capabilities modes =>
          cases bounded with | handler later => exact ih later
      | cell scope noEscape annotation interface => cases bounded with | cell later => exact ih later
      | armed scope callback annotation interface => cases bounded with | cleanup later => exact ih later
      | running scope callback saved annotation interface => cases bounded with | running later => exact ih later
      | closing scope interface => cases bounded with | running later => exact ih later
      | retiring known interface => cases bounded with | running later => exact ih later
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases bounded with | live inside outside => exact List.append_subset.mpr ⟨ihSaved inside, ihTail outside⟩
  | spent known annotation scope tail bound ih => cases bounded with | spent later => exact ih later

/-- This source judgment supplies the existing runtime disposal condition;
it does not introduce another interpretation or continuation-usage semantics. -/
theorem internal_uses
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing)
    (bounded : PendingWithin world (owners scope) scope) :
    InternalUses stack.erase.liveTickets stack.erase.pending := by
  apply OpenOwnerUses.internal_of_subset
  simpa only [realized_owners source.realizes] using segment_pending_bound source bounded

namespace Examples
open SourceDependencyCapture.Examples

def outside : Receiving := .plain (.invoke ⟨9, .resume⟩) (handlerE .nil)
def inside : Receiving := .plain (.invoke ⟨9, .resume⟩) (.live 9 .nil (handlerE .nil))

theorem outside_owner_rejected : ¬ PendingWithin [] (owners outside) outside := by
  intro checked
  cases checked with | plain code tail => cases code with | invoke included => cases included

theorem retained_owner_accepted : PendingWithin [] (owners inside) inside :=
  .plain (.invoke (by simp [inside, owners])) (.live .nil (.handler .nil))

end Examples
end Ash.OneShot.SourceDependencyOwners

#print axioms Ash.OneShot.SourceDependencyOwners.expression_external_idle
#print axioms Ash.OneShot.SourceDependencyOwners.context_external_idle
#print axioms Ash.OneShot.SourceDependencyOwners.plain_pending_bound
#print axioms Ash.OneShot.SourceDependencyOwners.realized_owners
#print axioms Ash.OneShot.SourceDependencyOwners.segment_pending_bound
#print axioms Ash.OneShot.SourceDependencyOwners.internal_uses
#print axioms Ash.OneShot.SourceDependencyOwners.Examples.outside_owner_rejected
#print axioms Ash.OneShot.SourceDependencyOwners.Examples.retained_owner_accepted
#print axioms Ash.OneShot.SourceDependencyOwners.Within.world_weaken
#print axioms Ash.OneShot.SourceDependencyOwners.PendingWithin.world_weaken


namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Only explicit source invocations contribute pending raw-code owners.
Latent function annotations remain checked separately by their callable proofs. -/
theorem expression_demand_external_idle
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (bounded : demand ⊆ owned)
    (outside : ∀ binder owner, scope.resolve binder = some owner → owner ∉ owned) :
    Uses policy .none .available code .available := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .resourceRef
  | «variable» => exact .variable
  | lambda body outward formed latentBound ih =>
      exact .lambda (SourceOwnerClosure.expression_usage
        (DeclaredSources.expression_erase (expression_erase body)) rfl)
  | purePair left right ihLeft ihRight =>
      exact .pair (ihLeft (List.nil_subset _) outside) (ihRight (List.nil_subset _) outside)
  | pair left right ihLeft ihRight =>
      exact .pair (ihLeft (List.append_subset.mp bounded).1 outside)
        (ihRight (List.append_subset.mp bounded).2 outside)
  | app function argument admitted ihFunction ihArgument =>
      exact .app (ihFunction (List.append_subset.mp bounded).1 outside)
        (ihArgument (List.append_subset.mp bounded).2 outside)
  | bind initializer body ihInit ihBody =>
      exact .bind (ihInit (List.append_subset.mp bounded).1 outside)
        (ihBody (List.append_subset.mp bounded).2 outside)
  | branch condition yes no same ihCondition ihYes ihNo =>
      have parts := List.append_subset.mp bounded
      exact .branch (ihCondition parts.1 outside) (ihYes parts.2 outside)
        (ihNo (fun _ member => parts.2 (same.mem_iff.mpr member)) outside)
  | perform known admitted operand formed ih => exact .perform (ih bounded outside)
  | handler body clauses capabilities coverage unique admitted table modes declarations ih ihDeclarations =>
      exact .handle (ih bounded outside) capabilities
  | resume known resolved permission operand admitted formed ih =>
      exact False.elim (outside _ _ resolved (bounded (List.mem_append_right _ List.mem_cons_self)))
  | discard known resolved permission unprotected admitted =>
      exact False.elim (outside _ _ resolved (bounded List.mem_cons_self))
  | cleanup callback body admitted ihCallback ihBody =>
      exact .cleanup (ihCallback (List.append_subset.mp bounded).1 outside)
        (ihBody (List.append_subset.mp bounded).2 outside)
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit (List.append_subset.mp bounded).1 outside)
        ((instantiation_preserves_usage_iff _ _).mp
          (ihBody identity fresh (List.append_subset.mp bounded).2 outside))
  | typed | annotated | unavailable | available | nil | cons => trivial

theorem context_demand_external_idle
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed scope position input output demand requirements dependencies)
    (bounded : demand ⊆ owned)
    (outside : ∀ binder owner, scope.resolve binder = some owner → owner ∉ owned) :
    Uses policy .none .available (position.plug .unit) .available := by
  cases source with
  | pairLeft right => exact .pair .unit (expression_demand_external_idle right bounded outside)
  | pairRight left => exact .pair (SourceOwnerClosure.expression_usage
      (DeclaredSources.expression_erase (expression_erase left)) rfl) .unit
  | appFunction argument admitted => exact .app .unit (expression_demand_external_idle argument bounded outside)
  | appArgument function admitted => exact .app (SourceOwnerClosure.expression_usage
      (DeclaredSources.expression_erase (expression_erase function)) rfl) .unit
  | bind body => exact .bind .unit (expression_demand_external_idle body bounded outside)
  | branch yes no same =>
      exact .branch .unit (expression_demand_external_idle yes bounded outside)
        (expression_demand_external_idle no (fun _ member => bounded (same.mem_iff.mpr member)) outside)
  | perform => exact .perform .unit
  | resume known resolved permission admitted formed =>
      exact False.elim (outside _ _ resolved (bounded List.mem_cons_self))
  | cleanup body admitted => exact .cleanup .unit (expression_demand_external_idle body bounded outside)
  | resource body formed effectsBound admitted hidden =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource .unit ((instantiation_preserves_usage_iff _ _).mp
        (expression_demand_external_idle (body identity fresh) bounded outside))

/-- Source demand bounds the actual pending-code owners, including higher-order
applications and callbacks. No dependency-locality or runtime-use premise is needed. -/
theorem plain_pending_demand {plain : PlainData}
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies) : plain.pending ⊆ demand := by
  intro owner pending
  by_cases included : owner ∈ demand
  · exact included
  apply False.elim
  obtain ⟨binder, dependency, resolved⟩ := (Syntax.scope_translate_membership plain.translated owner).mp pending
  have outside : ∀ other target, plain.scope.resolve other = some target → target ∉ demand := by
    intro other target known
    cases scopeSame : plain.scope with
    | none => simp [scopeSame, Execution.Scope.resolve] at resolved
    | ticket localBinder actual =>
        simp only [scopeSame, Execution.Scope.resolve] at resolved known
        split at resolved <;> simp_all
  have idle := context_demand_external_idle source (List.Subset.refl _) outside
  obtain ⟨rights, impossible, consumed⟩ := free_ticket_requires_consumption idle dependency
  cases impossible

/-- A source bound for actual retained code. Marker-only frames contribute no
    pending invocation; their typing, callbacks and protection are separate. -/
inductive PendingFrame (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world owned : List Nat) : ExecFrame → Prop where
  | plain (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies)
      (bounded : Within world owned dependencies) :
      PendingFrame operations policy contracts world owned (.plain plain)
  | demand (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies)
      (bounded : demand ⊆ owned) :
      PendingFrame operations policy contracts world owned (.plain plain)
  | empty (checked : frame.erase.pending = []) : PendingFrame operations policy contracts world owned frame

/-- This annotation follows the actual stack, including cleanup-return markers
    introduced by lexical unwinding. It bounds retained code only. -/
inductive PendingStack (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world owned : List Nat) : Stack → Prop where
  | nil : PendingStack operations policy contracts world owned .nil
  | push (frame : PendingFrame operations policy contracts world owned entry)
      (rest : PendingStack operations policy contracts world owned tail) :
      PendingStack operations policy contracts world owned (.push entry tail)
  | live (saved : PendingStack operations policy contracts world owned captured)
      (rest : PendingStack operations policy contracts world owned tail) :
      PendingStack operations policy contracts world owned (.live owner input answer captured caller tail)
  | spent (rest : PendingStack operations policy contracts world owned tail) :
      PendingStack operations policy contracts world owned (.spent owner answer caller tail)

theorem PendingFrame.bound
    (source : PendingFrame operations policy contracts world owned frame) : frame.erase.pending ⊆ owned := by
  cases source with
  | plain source bounded => exact plain_pending_bound source bounded
  | demand source bounded => exact (plain_pending_demand source).trans bounded
  | empty checked => rw [checked]; exact List.nil_subset _

theorem PendingStack.bound
    (source : PendingStack operations policy contracts world owned stack) : stack.erase.pending ⊆ owned := by
  induction source with
  | nil => exact List.nil_subset _
  | push frame rest ih => exact List.append_subset.mpr ⟨frame.bound, ih⟩
  | live saved rest ihSaved ihRest => exact List.append_subset.mpr ⟨ihSaved, ihRest⟩
  | spent rest ih => exact ih

theorem PendingStack.internal
    (source : PendingStack operations policy contracts world owned stack) :
    InternalUses owned stack.erase.pending := OpenOwnerUses.internal_of_subset source.bound

/-- Legacy source segments supply the annotation without changing their
    expression, resource, branch, callable or dependency judgments. -/
theorem segment_pending_stack
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing)
    (bounded : PendingWithin world owned scope) :
    PendingStack operations policy contracts world owned stack := by
  induction source with
  | nil => exact .nil
  | push frame tail bound ih => cases frame with
      | plain context scope inputAnnotation outputAnnotation => cases bounded with
          | plain current later => exact .push (.plain context current) (ih later)
      | handler scope annotation clauses coverage unique declarations capabilities modes => cases bounded with
          | handler later => exact .push (.empty rfl) (ih later)
      | cell scope noEscape annotation interface => cases bounded with
          | cell later => exact .push (.empty rfl) (ih later)
      | armed scope callback annotation interface => cases bounded with
          | cleanup later => exact .push (.empty rfl) (ih later)
      | running scope callback saved annotation interface => cases bounded with
          | running later => exact .push (.empty rfl) (ih later)
      | closing scope interface => cases bounded with
          | running later => exact .push (.empty rfl) (ih later)
      | retiring known interface => cases bounded with
          | running later => exact .push (.empty rfl) (ih later)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases bounded with | live inside outside => exact .live (ihSaved inside) (ihTail outside)
  | spent known annotation scope tail bound ih => cases bounded with | spent later => exact .spent (ih later)

/-- Source bounds discharge the three finite use checks for local disposal.
    Admission and preservation of the remaining facets are not assumed here. -/
theorem source_discard_use
    (checked : LexicalUnwind.MachineUse policy tickets (.eval ⟨.discard binder, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (unprotected : ProtectionContexts.protectedMode captured.erase = false)
    (frontSource : PendingStack operations policy contracts world
      (ownedTickets front ++ ownedTickets tail) front)
    (savedSource : PendingStack operations policy contracts world captured.erase.liveTickets captured)
    (tailSource : PendingStack operations policy contracts world (ownedTickets tail) tail) :
    LexicalUnwind.MachineUse policy tickets (.unwind runtimeScope
      (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) :=
  LexicalUnwind.discard_machine_use checked resolved unique unprotected
    frontSource.internal savedSource.internal tailSource.internal

/-- Source annotations distinguish ordinary return from return into unwinding.
    The latter checks the caller scopes and the same retained dependency bounds. -/
inductive ReentrySource (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world : List Nat) (front captured tail : Stack) : LexicalUnwind.UseMode → Prop where
  | ordinary : ReentrySource operations policy contracts world front captured tail .ordinary
  | unwind (scopes : LexicalUnwind.UnwindPrefix front)
      (frontSource : PendingStack operations policy contracts world front.erase.liveTickets front)
      (savedSource : PendingStack operations policy contracts world
        (ownedTickets captured ++ ownedTickets tail) captured)
      (tailSource : PendingStack operations policy contracts world (ownedTickets tail) tail) :
      ReentrySource operations policy contracts world front captured tail .unwind

theorem ReentrySource.bounds
    (source : ReentrySource operations policy contracts world front captured tail mode) :
    LexicalUnwind.ReentryBounds front captured tail mode := by
  cases source with
  | ordinary => exact .ordinary
  | unwind scopes frontSource savedSource tailSource =>
      exact .unwind scopes frontSource.internal savedSource.internal tailSource.internal

theorem source_resume_use
    (checked : LexicalUnwind.MachineUse policy tickets (.eval ⟨.resume binder value, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (resolved : runtimeScope.resolve binder = some owner) (isValue : value.IsValue)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (source : ReentrySource operations policy contracts world front captured tail
      (LexicalUnwind.returnMode captured .ordinary)) :
    LexicalUnwind.MachineUse policy tickets
      (.eval ⟨value, runtimeScope, captured.append (front.append (.spent owner answer caller tail))⟩) :=
  LexicalUnwind.resume_machine_use checked resolved isValue unique source.bounds

theorem PendingStack.append
    (front : PendingStack operations policy contracts world owned left)
    (tail : PendingStack operations policy contracts world owned right) :
    PendingStack operations policy contracts world owned (left.append right) := by
  induction front with
  | nil => exact tail
  | push frame rest ih => exact .push frame ih
  | live saved rest ihSaved ihRest => exact .live saved ihRest
  | spent rest ih => exact .spent ih

theorem PendingStack.decompose
    (source : PendingStack operations policy contracts world owned (left.append right)) :
    PendingStack operations policy contracts world owned left ∧
      PendingStack operations policy contracts world owned right := by
  induction left with
  | nil => exact ⟨.nil, source⟩
  | push entry rest ih => cases source with
      | push frame tail =>
          obtain ⟨inside, outside⟩ := ih tail
          exact ⟨.push frame inside, outside⟩
  | live owner input answer saved caller rest ihSaved ihRest => cases source with
      | live captured tail =>
          obtain ⟨inside, outside⟩ := ihRest tail
          exact ⟨.live captured inside, outside⟩
  | spent owner answer caller rest ih => cases source with
      | spent tail =>
          obtain ⟨inside, outside⟩ := ih tail
          exact ⟨.spent inside, outside⟩

/-- Local unwinding preserves the existing source evidence for every retained
    piece of code. This does not assert that the fixed owner bound is minimal. -/
theorem PendingStack.advance
    (step : LexicalUnwind.Advance before after discharged)
    (source : PendingStack operations policy contracts world owned before) :
    PendingStack operations policy contracts world owned after := by
  cases step with
  | plain | handler | cell | retire => cases source with
      | push frame rest => exact rest
  | spent => cases source with
      | spent rest => exact rest
  | live => cases source with
      | live saved rest => exact saved.append (.push (.empty rfl) rest)

theorem PendingStack.cleanup_marker
    (source : PendingStack operations policy contracts world owned (.push (.armed action) rest)) :
    PendingStack operations policy contracts world owned (.push (.unwinding action) rest) := by
  cases source with
  | push frame rest => exact .push (.empty rfl) rest

#print axioms Ash.OneShot.SourceDependencyOwners.PendingFrame.bound
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.bound
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.internal
#print axioms Ash.OneShot.SourceDependencyOwners.segment_pending_stack
#print axioms Ash.OneShot.SourceDependencyOwners.source_discard_use
#print axioms Ash.OneShot.SourceDependencyOwners.ReentrySource.bounds
#print axioms Ash.OneShot.SourceDependencyOwners.source_resume_use
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.append
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.decompose
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.advance
#print axioms Ash.OneShot.SourceDependencyOwners.PendingStack.cleanup_marker
end Ash.OneShot.SourceDependencyOwners


namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Source evidence constructs the checked resumption event without assuming
    its successor invariant. Accounting then follows from the common use proof. -/
theorem source_resume_use_transition
    (closed : ClosedValue value) (resolved : runtimeScope.resolve binder = some owner)
    (source : ReentrySource operations policy contracts world front captured tail
      (LexicalUnwind.returnMode captured .ordinary)) :
    LexicalUnwind.UseTransition
      (.eval ⟨.resume binder value, runtimeScope, front.append (.live owner input answer captured caller tail)⟩)
      (.eval ⟨value, runtimeScope, captured.append (front.append (.spent owner answer caller tail))⟩)
      [] [.ticket owner] :=
  .resume binder owner runtimeScope caller input answer front captured tail value closed resolved source.bounds

theorem source_discard_use_transition
    (resolved : runtimeScope.resolve binder = some owner)
    (unprotected : ProtectionContexts.protectedMode captured.erase = false)
    (frontSource : PendingStack operations policy contracts world
      (ownedTickets front ++ ownedTickets tail) front)
    (savedSource : PendingStack operations policy contracts world captured.erase.liveTickets captured)
    (tailSource : PendingStack operations policy contracts world (ownedTickets tail) tail) :
    LexicalUnwind.UseTransition
      (.eval ⟨.discard binder, runtimeScope, front.append (.live owner input answer captured caller tail)⟩)
      (.unwind runtimeScope (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) [.close identity] [.ticket owner] :=
  .discard binder owner identity runtimeScope caller input answer front captured tail resolved unprotected
    frontSource.internal savedSource.internal tailSource.internal

#print axioms Ash.OneShot.SourceDependencyOwners.source_resume_use_transition
#print axioms Ash.OneShot.SourceDependencyOwners.source_discard_use_transition
end Ash.OneShot.SourceDependencyOwners


namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Protection is a projection of the existing source contracts, independent
    of the permission to resume or dispose. No second registry is allocated. -/
def captureModes (contracts : Contracts) : LexicalUnwind.CaptureModes :=
  fun owner => (contracts owner).map Contract.held

theorem capture_modes_known (known : contracts owner = some contract) :
    captureModes contracts owner = some contract.held := by
  simp [captureModes, known]

theorem capture_modes_extend (extension : Contracts.Extends before after) :
    ∀ owner held, captureModes before owner = some held → captureModes after owner = some held := by
  intro owner held recorded
  cases known : before owner with
  | none => simp [captureModes, known] at recorded
  | some contract =>
      simpa only [captureModes, known, extension owner contract known] using recorded

theorem segment_capture_protection
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    LexicalUnwind.CaptureProtection (captureModes contracts) stack := by
  induction source with
  | nil => exact .nil
  | push head tail bound ih => exact .push ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live ((capture_modes_known known).trans (congrArg some held)) ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih

/-- Source capture records the actual protection of the lexical cut. Existing
    contract-extension evidence preserves all older captures. -/
theorem source_capture_protection
    (cut : HandlerCut requested whole captured tail handler)
    (checked : LexicalUnwind.CaptureProtection (captureModes contracts) whole)
    (fresh : contracts owner = none)
    (held : contract.held = ProtectionContexts.protectedMode captured.erase) :
    LexicalUnwind.CaptureProtection (captureModes (contracts.insert owner contract))
      (.live owner input answer captured caller tail) := by
  have retained := checked.extend (capture_modes_extend (insert_extends (contract := contract) contracts fresh))
  obtain ⟨saved, rest⟩ := LexicalUnwind.capture_protection_cut cut retained
  exact .live (by simp [captureModes, Contracts.insert, held]) saved rest

theorem source_protection_allocation
    (known : contracts owner = some contract)
    (held : contract.held = ProtectionContexts.protectedMode captured.erase) :
    LexicalUnwind.ProtectionAllocation (captureModes contracts) [.ticket owner]
      (.live owner input answer captured caller tail) :=
  .capture ((capture_modes_known known).trans (congrArg some held))

/-- Inverting the existing source discard rule supplies the guard on actual
    captured scopes, even when intervening handlers have been installed. -/
theorem source_discard_unprotected {front captured tail : Stack}
    (source : Expression operations policy contracts world allowed runtimeScope environment
      (.discard binder) result demand requirements dependencies)
    (resolved : runtimeScope.resolve binder = some owner)
    (checked : LexicalUnwind.CaptureProtection (captureModes contracts)
      (front.append (.live owner input answer captured caller tail))) :
    ProtectionContexts.protectedMode captured.erase = false := by
  cases source with
  | discard known sourceResolved permission unprotected admitted =>
      have same := Option.some.inj (sourceResolved.symm.trans resolved)
      apply LexicalUnwind.recorded_discard_unprotected checked
      rw [← same]
      exact (capture_modes_known known).trans (congrArg some unprotected)

/-- Both the protection guard and continuation-use bounds come from source
    evidence; the runtime successor is constructed, not supplied as safe. -/
theorem source_checked_discard_transition
    (source : Expression operations policy contracts world allowed runtimeScope environment
      (.discard binder) result demand requirements dependencies)
    (resolved : runtimeScope.resolve binder = some owner)
    (protection : LexicalUnwind.CaptureProtection (captureModes contracts)
      (front.append (.live owner input answer captured caller tail)))
    (frontSource : PendingStack operations policy contracts world
      (ownedTickets front ++ ownedTickets tail) front)
    (savedSource : PendingStack operations policy contracts world captured.erase.liveTickets captured)
    (tailSource : PendingStack operations policy contracts world (ownedTickets tail) tail) :
    LexicalUnwind.UseTransition
      (.eval ⟨.discard binder, runtimeScope, front.append (.live owner input answer captured caller tail)⟩)
      (.unwind runtimeScope (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) [.close identity] [.ticket owner] :=
  source_discard_use_transition resolved (source_discard_unprotected source resolved protection)
    frontSource savedSource tailSource

#print axioms Ash.OneShot.SourceDependencyOwners.capture_modes_known
#print axioms Ash.OneShot.SourceDependencyOwners.capture_modes_extend
#print axioms Ash.OneShot.SourceDependencyOwners.segment_capture_protection
#print axioms Ash.OneShot.SourceDependencyOwners.source_capture_protection
#print axioms Ash.OneShot.SourceDependencyOwners.source_protection_allocation
#print axioms Ash.OneShot.SourceDependencyOwners.source_discard_unprotected
#print axioms Ash.OneShot.SourceDependencyOwners.source_checked_discard_transition
end Ash.OneShot.SourceDependencyOwners


namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
/-- Source pending-owner bounds cover actual unwinding markers and dormant
    captures, using the same expression bounds as the ordinary source stack. -/
theorem lexical_segment_pending_stack
    (source : SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing)
    (bounded : PendingWithin world owned scope) :
    PendingStack operations policy contracts world owned stack := by
  induction source with
  | nil => exact .nil
  | push frame tail bound ih => cases frame with
    | ordinary frame => cases frame with
        | plain context scope inputAnnotation outputAnnotation => cases bounded with
            | plain current later => exact .push (.plain context current) (ih later)
        | handler scope annotation clauses coverage unique declarations capabilities modes => cases bounded with
            | handler later => exact .push (.empty rfl) (ih later)
        | cell scope noEscape annotation interface => cases bounded with
            | cell later => exact .push (.empty rfl) (ih later)
        | armed scope callback annotation interface => cases bounded with
            | cleanup later => exact .push (.empty rfl) (ih later)
        | running scope callback saved annotation interface => cases bounded with
            | running later => exact .push (.empty rfl) (ih later)
        | closing scope interface => cases bounded with
            | running later => exact .push (.empty rfl) (ih later)
        | retiring known interface => cases bounded with
            | running later => exact .push (.empty rfl) (ih later)
    | unwinding scope callback annotation interface => cases bounded with
        | running later => exact .push (.empty rfl) (ih later)
    | closing scope => cases bounded with
        | running later => exact .push (.empty rfl) (ih later)
    | retiring known => cases bounded with
        | running later => exact .push (.empty rfl) (ih later)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases bounded with | live inside outside => exact .live (ihSaved inside) (ihTail outside)
  | spent known annotation scope tail bound ih => cases bounded with | spent later => exact .spent (ih later)


#print axioms Ash.OneShot.SourceDependencyOwners.lexical_segment_pending_stack
end Ash.OneShot.SourceDependencyOwners


namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store Key Checked)
open OwnerPhaseTransitions (Phases available spendAll)
open RecursiveDisposalCapture

/-- Rich resume records retain the same actual-capture provenance as the
    established SourceTemplates certificate, including lexical return markers. -/
inductive ResumeCertified (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families)
    (actions : Syntax.UsageTickets) (world : List Nat) (root : Stack) :
    Key → RecursiveRequirements.Template → Prop where
  | resume (located : SourceTemplates.CapturedIn owner capture root)
      (known : contracts owner = some contract)
      (saved : LexicalSegment operations policy contracts tables families actions world capture
        contract.input contract.answer contract.resumeDemand requirements records dependencyScope incoming outgoing) :
      ResumeCertified operations policy contracts tables families actions world root
        ⟨owner, .resume⟩ ⟨contract.resumeDemand, requirements⟩

theorem ResumeCertified.transport
    (source : ResumeCertified operations policy contracts tables families actions world first key body)
    (move : ∀ owner capture, SourceTemplates.CapturedIn owner capture first → SourceTemplates.CapturedIn owner capture second) :
    ResumeCertified operations policy contracts tables families actions world second key body := by
  cases source with
  | resume located known saved => exact .resume (move _ _ located) known saved

theorem records_certified
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (member : (key, body) ∈ records) :
    ResumeCertified operations policy contracts tables families actions world stack key body := by
  induction source with
  | nil => cases member
  | push head tail bound ih => exact (ih member).transport (fun _ _ located => .push located)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · cases same; exact .resume .here known saved
      · rcases List.mem_append.mp later with nested | remaining
        · exact (ihSaved nested).transport (fun _ _ located => .saved located)
        · exact (ihTail remaining).transport (fun _ _ located => .tail located)
  | spent known annotation scope tail bound ih => exact (ih member).transport (fun _ _ located => .spent located)

/-- The extra lexical frames introduce only their actual retirement, never
    an invented invocation or completion obligation. Ordinary frames reuse the
    established source erasure and retirement proof. -/
theorem frame_retirements
    (source : LexicalFrame operations policy contracts tables families world
      frame input output demand requirements layer incoming outgoing) :
    directRetirements requirements ⊆ ScopedRetirement.scheduled (.push frame .nil) := by
  cases source with
  | ordinary frame => exact RecursiveDisposalCapture.frame_retirements (DeclaredSourceFrames.frame_erase frame.erase.source)
  | unwinding | closing => exact List.nil_subset _
  | retiring => exact List.Subset.refl _

theorem segment_retirements
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    directRetirements requirements ⊆ ScopedRetirement.scheduled stack := by
  induction source with
  | nil => exact List.nil_subset _
  | push head tail bound ih =>
      have headBound := frame_retirements head
      rw [directRetirements, retirements_prepend, scheduled_push]
      intro owner member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (headBound first)
      · exact List.mem_append_right _ (ih second)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact fun _ member => List.mem_append_right _ (ihTail member)
  | spent known annotation scope tail bound ih => exact ih

theorem frame_call_pending
    (source : LexicalFrame operations policy contracts tables families world
      frame input output demand requirements layer incoming outgoing)
    (member : owner ∈ directCalls requirements) : owner ∈ frame.erase.pending := by
  cases source with
  | ordinary frame => exact RecursiveDisposalCapture.frame_call_pending (DeclaredSourceFrames.frame_erase frame.erase.source) member
  | unwinding | closing | retiring => cases member

theorem segment_call_pending
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (member : owner ∈ directCalls requirements) : owner ∈ stack.erase.pending := by
  induction source with
  | nil => cases member
  | push head tail bound ih =>
      rw [directCalls, calls_prepend] at member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (frame_call_pending head first)
      · exact List.mem_append_right _ (ih second)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact List.mem_append_right _ (ihTail member)
  | spent known annotation scope tail bound ih => exact ih member

/-- The original spine-consumption induction applies to rich segments; the
    new return markers add no owner, and retirement uses the existing trace law. -/
theorem segment_spine_consumed
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (checked : Checked store receiving before requirements row) :
    ∀ owner ∈ spineOwners stack, spendAll before demand owner = .consumed := by
  induction source generalizing before receiving row with
  | nil => simp [spineOwners]
  | push head tail bound ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have later := ih secondCheck
      rw [PhaseRechecking.spendAll_append]
      cases head with
      | ordinary head => cases head with
        | retiring known interface =>
            intro owner member
            rcases List.mem_cons.mp member with equal | member
            · subst owner
              exact RecursiveTransport.phases_spendAll_later _
                (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace firstCheck) List.mem_cons_self)
            · exact later owner member
        | plain | handler | cell | armed | running | closing => exact later
      | unwinding | closing => exact later
      | retiring known =>
          intro owner member
          rcases List.mem_cons.mp member with equal | member
          · subst owner
            exact RecursiveTransport.phases_spendAll_later _
              (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace firstCheck) List.mem_cons_self)
          · exact later owner member
  | @live owner contract rights inputType answerType caller capture body nested savedScope savedBoundary rest output demand requirements remaining restScope
      boundary outgoing incoming known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have consumed : before owner = .consumed := by
        have evaluated := RecursiveRequirements.checked_complete firstCheck
        rw [RecursiveRecomposition.evaluate_spent] at evaluated
        split at evaluated
        · assumption
        · cases evaluated
      intro other member
      rcases List.mem_cons.mp member with equal | member
      · subst other
        exact RecursiveTransport.phases_spendAll_later _ consumed
      · exact ihTail secondCheck other member
  | spent known annotation scope tail bound ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      exact ih secondCheck

theorem lookup_resume_certified
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ (resumes ++ disposals) = some body) :
    ResumeCertified operations policy contracts tables families actions world root ⟨owner, .resume⟩ body := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member found) with original | added
  · exact records_certified source original
  · have impossible := closing.record_mode added
    cases impossible

theorem lookup_unwind_certified
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (found : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body) :
    UnwindCertified operations policy contracts tables world root ⟨owner, .dispose⟩ body := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member found) with original | added
  · have impossible := source.record_mode original
    cases impossible
  · exact closing.certified added

/-- Reuse the established checked-derivation induction. Disposal obtains its
    ownership equation from the lexical summary instead of a generated plan. -/
theorem checked_capture_spines
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (retirements : directRetirements requirements ⊆ ScopedRetirement.scheduled root) :
    ∀ owner capture, SourceTemplates.CapturedIn owner capture root → owner ∈ demand →
      ∀ nested ∈ spineOwners capture, spendAll before demand nested = .consumed := by
  induction checked with
  | request | spent => intro owner capture located member; cases member
  | retire ready =>
      intro owner capture located member
      exact False.elim (scheduled_not_captured unique located (retirements member))
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      cases key with
      | mk called mode => cases mode with
        | resume =>
            have certificate := lookup_resume_certified source closing known
            cases certificate with
            | resume actual contractKnown saved =>
                have bodySafe := (segment_retirements saved).trans (captured_scheduled_subset actual)
                intro owner capture located member nested present
                rcases List.mem_cons.mp member with same | later
                · subst owner
                  have sameCapture := SourceTemplates.captured_in_unique unique actual located
                  subst capture
                  exact segment_spine_consumed saved next nested present
                · exact ih bodySafe owner capture located later nested present
        | dispose =>
            have certificate := lookup_unwind_certified source closing known
            cases certificate with
            | dispose actual unprotected summary =>
                intro owner capture located member nested present
                have inside : nested ∈ demand := by
                  apply summary.ownership.mem_iff.mpr
                  have captured : nested ∈ ownedTickets capture :=
                    (ownership_partition capture).mem_iff.mpr (List.mem_append_left _ present)
                  rcases List.mem_cons.mp member with same | later
                  · subst owner
                    have sameCapture := SourceTemplates.captured_in_unique unique actual located
                    simpa only [sameCapture] using captured
                  · exact captured_ownership_closed unique actual located
                      (summary.ownership.mem_iff.mp later) captured
                exact OwnerPhaseTransitions.trace_consumed (PhaseRechecking.check_owners_iff.mp ready)
                  (List.mem_cons_of_mem _ inside)
  | sequence first second ihFirst ihSecond =>
      intro owner capture located member nested present
      rw [PhaseRechecking.spendAll_append]
      rcases List.mem_append.mp member with earlier | later
      · exact RecursiveTransport.phases_spendAll_later _
          (ihFirst (fun _ member => retirements (List.mem_append_left _ member)) owner capture located earlier nested present)
      · exact ihSecond (fun _ member => retirements (List.mem_append_right _ member)) owner capture located later nested present
  | emitAfter body exported ih => exact ih retirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun _ member => retirements (List.mem_append_left _ member))

theorem checked_internal_demand
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary region root)
    (internal : InternalUses region.erase.liveTickets region.erase.pending)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (calls : directCalls requirements ⊆ ownedTickets region)
    (retirements : directRetirements requirements ⊆ ownedTickets region) : demand ⊆ ownedTickets region := by
  induction checked with
  | request | spent => exact List.nil_subset _
  | retire ready => exact retirements
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      have called := calls List.mem_cons_self
      cases key with
      | mk owner mode => cases mode with
        | resume =>
            have certificate := lookup_resume_certified source closing known
            cases certificate with
            | resume actual knownContract saved =>
                rename_i actualCapture actualContract actualRequirements actualRecords actualScope actualIncoming actualOutgoing
                have localCapture := captured_in_region unique outer actual called
                have bodyCalls : directCalls actualRequirements ⊆ ownedTickets region := by
                  intro nested member
                  exact recursive_live_tickets_owned region (internalUses_subset internal
                    (captured_pending_subset localCapture (segment_call_pending saved member)))
                have bodyRetirements := (segment_retirements saved).trans
                  ((scheduled_owned _).trans (captured_owned_subset localCapture))
                have inside := ih bodyCalls bodyRetirements
                intro nested member
                rcases List.mem_cons.mp member with same | later
                · simpa only [same] using called
                · exact inside later
        | dispose =>
            have certificate := lookup_unwind_certified source closing known
            cases certificate with
            | dispose actual unprotected summary =>
                have included := captured_ownership_closed unique outer actual called
                intro nested member
                rcases List.mem_cons.mp member with same | later
                · simpa only [same] using called
                · exact included (summary.ownership.mem_iff.mp later)
  | sequence first second ihFirst ihSecond =>
      have left := ihFirst (fun _ member => calls (List.mem_append_left _ member))
        (fun _ member => retirements (List.mem_append_left _ member))
      have right := ihSecond (fun _ member => calls (List.mem_append_right _ member))
        (fun _ member => retirements (List.mem_append_right _ member))
      exact List.append_subset.mpr ⟨left, right⟩
  | emitAfter body exported ih => exact ih calls retirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun _ member => calls (List.mem_append_left _ member))
        (fun _ member => retirements (List.mem_append_left _ member))

theorem captured_segment_balance
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary capture root)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture argument answer demand requirements records capturedScope capturedIncoming capturedOutgoing)
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available) :
    demand.Perm (ownedTickets capture) := by
  have retirements := (segment_retirements saved).trans (scheduled_owned capture)
  have calls : directCalls requirements ⊆ ownedTickets capture := by
    intro owner member
    exact recursive_live_tickets_owned capture (internalUses_subset internal (segment_call_pending saved member))
  have inside := checked_internal_demand source closing unique outer internal checked calls retirements
  have transition := RecursiveRequirements.checked_trace checked
  have complete := ownership_tree_consumed capture _ (segment_spine_consumed saved checked) (by
    intro owner nested located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [ready owner (SourceTemplates.captured_in_owned located), consumed]
      decide)
    exact checked_capture_spines source closing unique checked
      ((segment_retirements saved).trans (captured_scheduled_subset outer))
      owner nested (captured_inside outer located) demanded)
  apply (List.perm_ext_iff_of_nodup (RecursiveRequirements.checked_once checked)
    ((captured_owned_sublist outer).nodup unique)).mpr
  intro owner
  constructor
  · intro member; exact inside member
  · intro owned
    apply (OwnerSource.trace_member_iff_changes transition).mpr
    rw [ready owner owned, complete owner owned]
    decide

theorem checked_ownership_balance
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output pendingDemand pending resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row)
    (retirements : directRetirements requirements ⊆ ScopedRetirement.scheduled stack)
    (spine : ∀ owner ∈ spineOwners stack, spendAll (available (ownedTickets stack)) demand owner = .consumed) :
    demand.Perm (ownedTickets stack) := by
  have transition := RecursiveRequirements.checked_trace checked
  have complete := ownership_tree_consumed stack _ spine (by
    intro owner capture located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [consumed]
      simp [available, SourceTemplates.captured_in_owned located])
    exact checked_capture_spines source closing unique checked retirements owner capture located demanded)
  have endpoint : spendAll (available (ownedTickets stack)) demand = OwnerPhaseTransitions.empty := by
    funext owner
    by_cases owned : owner ∈ ownedTickets stack
    · exact complete owner owned
    · exact RecursiveTransport.phases_spendAll_later _ (by simp [available, owned])
  rw [endpoint] at transition
  exact OwnerSource.trace_same_endpoints transition (OwnerPhaseTransitions.trace_all_owned (.refl _) unique)

theorem segment_ownership_balance
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row) :
    demand.Perm (ownedTickets stack) :=
  checked_ownership_balance source closing unique checked (segment_retirements source)
    (segment_spine_consumed source checked)

theorem segment_all_owned_consumed
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row) :
    ∀ owner ∈ ownedTickets stack, spendAll (available (ownedTickets stack)) demand owner = .consumed := by
  intro owner member
  have demanded := (segment_ownership_balance source closing unique checked).mem_iff.mpr member
  rw [OwnerPhaseTransitions.spendAll_at, if_pos demanded]

/-- The same captured owners are accounted for by normal execution and
    lexical disposal. Neither budget equality nor a generated plan is assumed. -/
theorem captured_modes_balance
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary capture root)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture argument answer demand requirements records capturedScope capturedIncoming capturedOutgoing)
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available)
    (summary : UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements) :
    closingDemand.Perm demand :=
  summary.ownership.trans (captured_segment_balance source closing unique outer internal saved checked ready).symm

/-- Construct the disposal requirements and their balance with the saved
    ordinary source demand, retaining the independent row-check obligation. -/
theorem captured_closing_requirements
    (source : LexicalSegment operations policy contracts tables families actions world
      root input output rootDemand rootRequirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary capture root)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture argument answer demand requirements records capturedScope capturedIncoming capturedOutgoing)
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available)
    (unprotected : ProtectionContexts.protectedMode capture.erase = false) :
    ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
      UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements ∧
      closingDemand.Perm demand := by
  obtain ⟨closingDemand, closingRequirements, summary⟩ := saved.unwind_template unprotected
  exact ⟨closingDemand, closingRequirements, summary,
    captured_modes_balance source closing unique outer internal saved checked ready summary⟩

/-- A present source expression and its pending lexical stack account for
    every owned continuation. Balance is derived from their checked requirements,
    rather than added as an admission premise. -/
theorem source_ownership_balance
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      code input currentDemand currentRequirements dependencies)
    (pending : LexicalSegment operations policy contracts tables families actions world
      stack input output pendingDemand pendingRequirements resumes dependencyScope allowed outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack))
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row) :
    (currentDemand ++ pendingDemand).Perm (ownedTickets stack) := by
  apply checked_ownership_balance pending closing unique checked
  · have noRetirements := RecursiveDisposalCapture.expression_no_retirements
      (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase current))
    simpa only [directRetirements, retirements_prepend, noRetirements, List.nil_append] using
      segment_retirements pending
  · obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
    simpa only [PhaseRechecking.spendAll_append] using segment_spine_consumed pending pendingCheck

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.source_ownership_balance

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.checked_ownership_balance
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.segment_ownership_balance
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.segment_all_owned_consumed
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.captured_modes_balance
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.captured_closing_requirements

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.lookup_resume_certified
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.lookup_unwind_certified
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.checked_capture_spines
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.checked_internal_demand
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.captured_segment_balance

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.ResumeCertified.transport
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.records_certified
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.frame_retirements
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.segment_retirements
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.frame_call_pending
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.segment_call_pending
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.segment_spine_consumed
end Ash.OneShot.SourceDependencyOwners.Lexical

namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution
open RecursiveRequirements (Store)
open SourceDependencyFrames (unwindStore)
open SourceTemplates (CapturedIn)

/-- Existing capture provenance moves to the same saved subtree when its
record survives the administrative store update. -/
theorem unwind_record_location
    (step : LexicalUnwind.Advance before after discharged)
    (located : CapturedIn key.owner capture before)
    (kept : (key, body) ∈ unwindStore before entries) :
    CapturedIn key.owner capture after := by
  cases step with
  | plain | handler | cell | retire => cases located with | push rest => exact rest
  | spent => cases located with | spent rest => exact rest
  | live =>
      rw [unwindStore, RecursiveRecomposition.remove_owner_filter] at kept
      have different := (List.mem_filter.mp kept).2
      cases located with
      | here => simp at different
      | saved inside => exact SavedCaptureIdentity.located_append.mpr (Or.inl inside)
      | tail outside => exact SavedCaptureIdentity.located_append.mpr (Or.inr (.push outside))

theorem resume_records_advance
    (step : LexicalUnwind.Advance before after discharged)
    (sources : ∀ key body, (key, body) ∈ records →
      ResumeCertified operations policy contracts tables families actions world before key body) :
    ∀ key body, (key, body) ∈ unwindStore before records →
      ResumeCertified operations policy contracts tables families actions world after key body := by
  intro key body member
  have source := sources key body (SourceDependencyFrames.unwind_store_sublist.subset member)
  cases source with
  | resume located known saved =>
      exact .resume (unwind_record_location step located member) known saved
end Ash.OneShot.SourceDependencyOwners.Lexical
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.unwind_record_location
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.resume_records_advance


namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution
open RecursiveRequirements (Key Store)
/-- The existing record-removal check excludes the invoked owner. Every
surviving capture keeps its identity across the lexical resumption splice. -/
theorem resume_record_location {front captured tail : Stack}
    (located : SourceTemplates.CapturedIn key.owner saved
      (front.append (.live owner input answer captured caller tail)))
    (kept : (key, body) ∈ RecursiveTransport.removeOwner owner entries) :
    SourceTemplates.CapturedIn key.owner saved
      (captured.append (front.append (.spent owner answer caller tail))) := by
  rw [RecursiveRecomposition.remove_owner_filter] at kept
  have different := (List.mem_filter.mp kept).2
  rcases SavedCaptureIdentity.located_append.mp located with inside | outside
  · exact SavedCaptureIdentity.located_append.mpr (Or.inr
      (SavedCaptureIdentity.located_append.mpr (Or.inl inside)))
  · cases outside with
    | here => simp at different
    | saved nested => exact SavedCaptureIdentity.located_append.mpr (Or.inl nested)
    | tail rest => exact SavedCaptureIdentity.located_append.mpr (Or.inr
        (SavedCaptureIdentity.located_append.mpr (Or.inr (.spent rest))))
end Ash.OneShot.SourceDependencyOwners.Lexical
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.resume_record_location



namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store Key Checked)
open OwnerPhaseTransitions (Phases available spendAll)
open RecursiveDisposalCapture

/-- A mixed frame introduces only its own explicit retirement. -/
theorem mode_frame_retirements
    (source : ModeSourceFrame operations policy contracts tables families world
      frame input output demand requirements layer) :
    directRetirements requirements ⊆ ScopedRetirement.scheduled (.push frame .nil) := by
  cases source with
  | ordinary frame => exact RecursiveDisposalCapture.frame_retirements (DeclaredSourceFrames.frame_erase frame.erase.source)
  | retiring => exact List.Subset.refl _
  | unwinding | closing | skipped | handler | cell | cleanup => exact List.nil_subset _

/-- Opening a capture adds retirement of its live owner; all such retirements
remain within the physical owners of the same source stack. -/
theorem mode_segment_retirements_owned
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope) :
    directRetirements requirements ⊆ ownedTickets stack := by
  induction source with
  | nil => exact List.nil_subset _
  | @push entry input middle firstDemand first layer rest output tailDemand second restScope head tail ih =>
      have headBound := (mode_frame_retirements head).trans (scheduled_owned _)
      rw [directRetirements, retirements_prepend]
      have parts : ownedTickets (.push entry rest) = ownedTickets (.push entry .nil) ++ ownedTickets rest := by
        cases head.realizes <;> simp [ownedTickets]
      rw [parts]
      exact List.append_subset.mpr ⟨headBound.trans (List.subset_append_left _ _), ih.trans (List.subset_append_right _ _)⟩
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      exact fun _ member => List.mem_cons_of_mem _ (List.mem_append_right _ (ihTail member))
  | opening saved tail ihSaved ihTail =>
      simp only [directRetirements, retirements_prepend]
      intro owner member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihSaved first))
      · rcases List.mem_cons.mp second with same | later
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihTail later))
  | spent known annotation caller tail ih | skippedSpent tail ih => exact ih

/-- Checked mixed source discharges its active spine. The opening case uses
the existing saved-body and retirement sequence checks. -/
theorem mode_segment_spine_consumed
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (checked : Checked store receiving before requirements row) :
    ∀ owner ∈ spineOwners stack, spendAll before demand owner = .consumed := by
  induction source generalizing before receiving row with
  | nil => simp [spineOwners]
  | push head tail ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have later := ih secondCheck
      rw [PhaseRechecking.spendAll_append]
      cases head with
      | ordinary head => cases head with
        | retiring known interface =>
            intro owner member
            rcases List.mem_cons.mp member with equal | member
            · subst owner
              exact RecursiveTransport.phases_spendAll_later _
                (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace firstCheck) List.mem_cons_self)
            · exact later owner member
        | plain | handler | cell | armed | running | closing => exact later
      | unwinding | closing | skipped | handler | cell | cleanup => exact later
      | retiring =>
          intro owner member
          rcases List.mem_cons.mp member with equal | member
          · subst owner
            exact RecursiveTransport.phases_spendAll_later _
              (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace firstCheck) List.mem_cons_self)
          · exact later owner member
  | @live owner contract rights inputType answerType caller captured boundary body savedScope rest output demand requirements restScope known rightsKnown inputAnnotation answerAnnotation callerKnown held saved answer tail ihSaved ihTail =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have consumed : before owner = .consumed := by
        have evaluated := RecursiveRequirements.checked_complete firstCheck
        rw [RecursiveRecomposition.evaluate_spent] at evaluated
        split at evaluated
        · assumption
        · cases evaluated
      intro other member
      rcases List.mem_cons.mp member with equal | member
      · subst other
        exact RecursiveTransport.phases_spendAll_later _ consumed
      · exact ihTail secondCheck other member
  | opening saved tail ihSaved ihTail =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨retiredRow, tailRow, retiredCheck, tailCheck, restSame⟩ := RecursiveRequirements.checked_sequence_parts secondCheck
      rw [PhaseRechecking.spendAll_append, PhaseRechecking.spendAll_append]
      intro owner member
      rcases List.mem_cons.mp member with equal | member
      · subst owner
        exact RecursiveTransport.phases_spendAll_later _
          (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace retiredCheck) List.mem_cons_self)
      · exact ihTail tailCheck owner member
  | spent known annotation caller tail ih | skippedSpent tail ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      exact ih secondCheck

/-- A retirement of a still-present capture occurs only after its saved
unwind source has discharged the capture's spine. Ordinary retirements cannot
refer to a live capture with the same unique identity. -/
theorem mode_segment_retirement_spines
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked store receiving before requirements row)
    (located : SourceTemplates.CapturedIn owner capture stack)
    (retired : owner ∈ directRetirements requirements) :
    ∀ nested ∈ spineOwners capture, spendAll before demand nested = .consumed := by
  induction source generalizing owner capture before receiving row with
  | nil => cases located
  | @push entry input middle firstDemand first layer rest output tailDemand second restScope head tail ih =>
      have tailUnique : (ownedTickets rest).Nodup := by
        cases entry <;> first | exact unique | exact (List.nodup_cons.mp unique).2
      cases located with
      | push located =>
          obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          rw [directRetirements, retirements_prepend] at retired
          rcases List.mem_append.mp retired with earlier | later
          · have scheduled := mode_frame_retirements head earlier
            have impossible := scheduled_not_captured unique (SourceTemplates.CapturedIn.push located)
            apply False.elim
            apply impossible
            rw [scheduled_push]
            exact List.mem_append_left _ scheduled
          · simpa only [PhaseRechecking.spendAll_append] using ih tailUnique secondCheck located later
  | @live active contract rights inputType answerType caller captured boundary body savedScope rest output demand requirements restScope known rightsKnown inputAnnotation answerAnnotation callerKnown held saved answer tail ihSaved ihTail =>
      obtain ⟨notActive, bothUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨savedUnique, tailUnique, disjoint⟩ := List.nodup_append.mp bothUnique
      have ownerTail := mode_segment_retirements_owned tail retired
      cases located with
      | here => exact False.elim (notActive (List.mem_append_right _ ownerTail))
      | saved located => exact False.elim (disjoint _ (SourceTemplates.captured_in_owned located) _ ownerTail rfl)
      | tail located =>
          obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          exact ihTail tailUnique secondCheck located retired
  | @opening captured savedDemand savedRequirements savedScope rest output tailDemand tailRequirements restScope active input answer caller saved tail ihSaved ihTail =>
      obtain ⟨notActive, bothUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨savedUnique, tailUnique, disjoint⟩ := List.nodup_append.mp bothUnique
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨retiredRow, tailRow, retiredCheck, tailCheck, restSame⟩ := RecursiveRequirements.checked_sequence_parts secondCheck
      have savedCheck := RecursiveRequirements.checked_prepend_iff.mp firstCheck
      have liftSaved : ∀ name, spendAll before savedDemand name = .consumed →
          spendAll before (savedDemand ++ ([active] ++ tailDemand)) name = .consumed := by
        intro name consumed
        rw [PhaseRechecking.spendAll_append]
        exact RecursiveTransport.phases_spendAll_later name consumed
      cases located with
      | here =>
          intro nested member
          exact liftSaved nested (mode_segment_spine_consumed saved savedCheck nested member)
      | saved located =>
          simp only [directRetirements, retirements_prepend] at retired
          rcases List.mem_append.mp retired with inside | outside
          · intro nested member
            exact liftSaved nested (ihSaved savedUnique savedCheck located inside nested member)
          · rcases List.mem_cons.mp outside with sameOwner | inTail
            · exact False.elim (notActive (List.mem_append_left _ (sameOwner ▸ SourceTemplates.captured_in_owned located)))
            · exact False.elim (disjoint _ (SourceTemplates.captured_in_owned located) _
                (mode_segment_retirements_owned tail inTail) rfl)
      | tail located =>
          simp only [directRetirements, retirements_prepend] at retired
          rcases List.mem_append.mp retired with inside | outside
          · exact False.elim (disjoint _ (mode_segment_retirements_owned saved inside) _
              (SourceTemplates.captured_in_owned located) rfl)
          · rcases List.mem_cons.mp outside with sameOwner | inTail
            · exact False.elim (notActive (List.mem_append_right _ (sameOwner ▸ SourceTemplates.captured_in_owned located)))
            · simpa only [PhaseRechecking.spendAll_append] using ihTail tailUnique tailCheck located inTail
  | spent known annotation caller tail ih | skippedSpent tail ih =>
      cases located with
      | spent located =>
          obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          exact ih unique secondCheck located retired

/-- The old checked-derivation induction also covers mixed-mode records.
A direct retirement is deferred to its source proof; this permits an opening
capture to retire its owner after, rather than instead of, cleaning its body. -/
theorem mode_checked_capture_spines
    (resumes : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .resume⟩ entries = some ⟨demand, body⟩ →
      ∃ capture input output scope, SourceTemplates.CapturedIn owner capture root ∧
        ModeSource operations policy contracts tables families actions world capture input output demand body scope)
    (disposals : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ entries = some ⟨demand, body⟩ →
      ∃ capture, SourceTemplates.CapturedIn owner capture root ∧ demand.Perm (ownedTickets capture))
    (unique : (ownedTickets root).Nodup)
    (checked : Checked entries receiving before (requirements : Requirements demand) row) :
    ∀ owner capture, SourceTemplates.CapturedIn owner capture root → owner ∈ demand →
      owner ∈ directRetirements requirements ∨
        ∀ nested ∈ spineOwners capture, spendAll before demand nested = .consumed := by
  induction checked with
  | request | spent => intro owner capture located member; cases member
  | retire ready => exact fun _ _ _ member => .inl member
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      cases key with
      | mk called mode => cases mode with
        | resume =>
            obtain ⟨actualCapture, input, output, scope, actual, source⟩ := resumes called demand body known
            intro owner capture located member
            apply Or.inr
            rcases List.mem_cons.mp member with same | later
            · subst owner
              have sameCapture := SourceTemplates.captured_in_unique unique actual located
              subst capture
              simpa only [spendAll] using mode_segment_spine_consumed source next
            · rcases ih owner capture located later with retired | consumed
              · have inside := captured_in_region unique actual located
                  (mode_segment_retirements_owned source retired)
                simpa only [spendAll] using mode_segment_retirement_spines source ((captured_owned_sublist actual).nodup unique)
                  next inside retired
              · exact consumed
        | dispose =>
            obtain ⟨actualCapture, actual, balance⟩ := disposals called demand body known
            intro owner capture located member
            apply Or.inr
            intro nested present
            have inside : nested ∈ demand := by
              apply balance.mem_iff.mpr
              have captured : nested ∈ ownedTickets capture :=
                (ownership_partition capture).mem_iff.mpr (List.mem_append_left _ present)
              rcases List.mem_cons.mp member with same | later
              · subst owner
                have sameCapture := SourceTemplates.captured_in_unique unique actual located
                simpa only [sameCapture] using captured
              · exact captured_ownership_closed unique actual located (balance.mem_iff.mp later) captured
            exact OwnerPhaseTransitions.trace_consumed (PhaseRechecking.check_owners_iff.mp ready)
              (List.mem_cons_of_mem _ inside)
  | sequence first second ihFirst ihSecond =>
      intro owner capture located member
      rcases List.mem_append.mp member with earlier | later
      · rcases ihFirst owner capture located earlier with retired | consumed
        · exact .inl (List.mem_append_left _ retired)
        · apply Or.inr
          intro nested present
          rw [PhaseRechecking.spendAll_append]
          exact RecursiveTransport.phases_spendAll_later _ (consumed nested present)
      · rcases ihSecond owner capture located later with retired | consumed
        · exact .inl (List.mem_append_right _ retired)
        · exact .inr (by simpa only [PhaseRechecking.spendAll_append] using consumed)
  | emitAfter body exported ih => exact ih
  | choice first second ihFirst ihSecond =>
      intro owner capture located member
      rcases ihFirst owner capture located member with retired | consumed
      · exact .inl (List.mem_append_left _ retired)
      · exact .inr consumed

/-- Exact mixed-mode record sources and direct-retirement evidence suffice
for the existing ownership-tree and trace-endpoint argument. -/
theorem mode_checked_ownership_balance
    (resumes : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .resume⟩ entries = some ⟨demand, body⟩ →
      ∃ capture input output scope, SourceTemplates.CapturedIn owner capture root ∧
        ModeSource operations policy contracts tables families actions world capture input output demand body scope)
    (disposals : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ entries = some ⟨demand, body⟩ →
      ∃ capture, SourceTemplates.CapturedIn owner capture root ∧ demand.Perm (ownedTickets capture))
    (unique : (ownedTickets root).Nodup)
    (checked : Checked entries receiving (available (ownedTickets root)) (requirements : Requirements demand) row)
    (retirements : ∀ owner capture, SourceTemplates.CapturedIn owner capture root →
      owner ∈ directRetirements requirements → ∀ nested ∈ spineOwners capture,
        spendAll (available (ownedTickets root)) demand nested = .consumed)
    (spine : ∀ owner ∈ spineOwners root, spendAll (available (ownedTickets root)) demand owner = .consumed) :
    demand.Perm (ownedTickets root) := by
  have transition := RecursiveRequirements.checked_trace checked
  have complete := ownership_tree_consumed root _ spine (by
    intro owner capture located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [consumed]
      simp [available, SourceTemplates.captured_in_owned located])
    rcases mode_checked_capture_spines resumes disposals unique checked owner capture located demanded with retired | complete
    · exact retirements owner capture located retired
    · exact complete)
  have endpoint : spendAll (available (ownedTickets root)) demand = OwnerPhaseTransitions.empty := by
    funext owner
    by_cases owned : owner ∈ ownedTickets root
    · exact complete owner owned
    · exact RecursiveTransport.phases_spendAll_later _ (by simp [available, owned])
  rw [endpoint] at transition
  exact OwnerSource.trace_same_endpoints transition (OwnerPhaseTransitions.trace_all_owned (.refl _) unique)
end Ash.OneShot.SourceDependencyOwners.Lexical
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_frame_retirements
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_segment_retirements_owned
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_segment_spine_consumed
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_segment_retirement_spines
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_checked_capture_spines
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_checked_ownership_balance


namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store Key Checked)
open OwnerPhaseTransitions (Phases available spendAll)
open RecursiveDisposalCapture

theorem mode_frame_call_pending
    (source : ModeSourceFrame operations policy contracts tables families world
      frame input output demand requirements layer)
    (member : owner ∈ directCalls requirements) : owner ∈ frame.erase.pending := by
  cases source with
  | ordinary frame => exact RecursiveDisposalCapture.frame_call_pending (DeclaredSourceFrames.frame_erase frame.erase.source) member
  | unwinding | closing | retiring | skipped | handler | cell | cleanup => cases member

theorem mode_segment_call_pending
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (member : owner ∈ directCalls requirements) : owner ∈ stack.erase.pending := by
  induction source with
  | nil => cases member
  | push head tail ih =>
      rw [directCalls, calls_prepend] at member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (mode_frame_call_pending head first)
      · exact List.mem_append_right _ (ih second)
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      exact List.mem_append_right _ (ihTail member)
  | opening saved tail ihSaved ihTail =>
      rw [directCalls, calls_prepend] at member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (ihSaved first)
      · exact List.mem_append_right _ (ihTail second)
  | spent known annotation caller tail ih | skippedSpent tail ih => exact ih member

/-- Check only membership of demanded owners. Effect interpretation and
multiplicity remain governed by the original checked derivation. -/
theorem checked_demand_bound
    (resumes : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .resume⟩ entries = some ⟨demand, body⟩ → owner ∈ allowed →
        directCalls body ⊆ allowed ∧ directRetirements body ⊆ allowed)
    (disposals : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ entries = some ⟨demand, body⟩ → owner ∈ allowed → demand ⊆ allowed)
    (checked : Checked entries receiving before (requirements : Requirements demand) row)
    (calls : directCalls requirements ⊆ allowed)
    (retirements : directRetirements requirements ⊆ allowed) : demand ⊆ allowed := by
  induction checked with
  | request | spent => exact List.nil_subset _
  | retire ready => exact retirements
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      have called := calls List.mem_cons_self
      cases key with
      | mk owner mode => cases mode with
        | resume =>
            obtain ⟨bodyCalls, bodyRetirements⟩ := resumes owner demand body known called
            exact List.cons_subset_cons _ (ih bodyCalls bodyRetirements) |>.trans (by
              intro other member
              rcases List.mem_cons.mp member with same | member
              · exact same ▸ called
              · exact member)
        | dispose =>
            intro other member
            rcases List.mem_cons.mp member with same | member
            · exact same ▸ called
            · exact disposals owner demand body known called member
  | sequence first second ihFirst ihSecond =>
      exact List.append_subset.mpr
        ⟨ihFirst (fun _ member => calls (List.mem_append_left _ member))
          (fun _ member => retirements (List.mem_append_left _ member)),
         ihSecond (fun _ member => calls (List.mem_append_right _ member))
          (fun _ member => retirements (List.mem_append_right _ member))⟩
  | emitAfter body exported ih => exact ih calls retirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun _ member => calls (List.mem_append_left _ member))
        (fun _ member => retirements (List.mem_append_left _ member))

/-- A preserved lexical region keeps its capture identities and retirement
markers. Unique ownership then authenticates every lookup into that region. -/
theorem captured_in_preserved_region
    (unique : (ownedTickets root).Nodup)
    (captures : ∀ owner capture, SourceTemplates.CapturedIn owner capture region →
      SourceTemplates.CapturedIn owner capture root)
    (retirements : ScopedRetirement.scheduled region ⊆ ScopedRetirement.scheduled root)
    (located : SourceTemplates.CapturedIn owner capture root)
    (member : owner ∈ ownedTickets region) : SourceTemplates.CapturedIn owner capture region := by
  rcases owned_origin member with ⟨actual, here⟩ | scheduled
  · have same := SourceTemplates.captured_in_unique unique (captures _ _ here) located
    subst actual
    exact here
  · exact False.elim (scheduled_not_captured unique located (retirements scheduled))
end Ash.OneShot.SourceDependencyOwners.Lexical

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_frame_call_pending
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_segment_call_pending
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.checked_demand_bound
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.captured_in_preserved_region


namespace Ash.OneShot.SourceDependencyOwners.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyOwners
open RecursiveRequirements (Requirements Store)
open RecursiveDisposalCapture

/-- Bounds apply to code that the source executes. A skipped frame contributes
no invocation, so its abandoned raw code needs no pending-code reconstruction. -/
theorem mode_frame_calls_within
    (source : ModeSourceFrame operations policy contracts tables families world
      entry input output demand requirements layer)
    (bounded : PendingWithin world owned (layer restScope)) :
    directCalls requirements ⊆ owned := by
  intro owner member
  have physical := mode_frame_call_pending source member
  cases source with
  | ordinary frame => cases frame with
      | plain context scope inputAnnotation outputAnnotation => cases bounded with
          | plain code tail => exact plain_pending_bound context code physical
      | handler | cell | armed | running | closing | retiring => cases physical
  | unwinding | closing | retiring | skipped | handler | cell | cleanup => cases member

theorem mode_source_calls_within
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (bounded : PendingWithin world owned scope) : directCalls requirements ⊆ owned := by
  induction source with
  | nil => exact List.nil_subset _
  | @push entry input middle firstDemand first layer rest output tailDemand second restScope head tail ih =>
      have later : PendingWithin world owned restScope := by
        cases head.realizes <;> cases bounded <;> assumption
      rw [directCalls, calls_prepend]
      exact List.append_subset.mpr ⟨mode_frame_calls_within head bounded, ih later⟩
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      cases bounded with | live inside outside => exact ihTail outside
  | opening saved tail ihSaved ihTail =>
      cases bounded with | live inside outside =>
        rw [directCalls, calls_prepend]
        exact List.append_subset.mpr ⟨ihSaved inside, ihTail outside⟩
  | spent known annotation caller tail ih | skippedSpent tail ih =>
      cases bounded with | spent later => exact ih later

end Ash.OneShot.SourceDependencyOwners.Lexical

#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_frame_calls_within
#print axioms Ash.OneShot.SourceDependencyOwners.Lexical.mode_source_calls_within

namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Initially owner-free source contexts construct the existing pending-frame
annotation directly; no latent-signature owner annotation is required. -/
theorem PendingFrame.of_empty_demand {plain : PlainData}
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output [] requirements dependencies) :
    PendingFrame operations policy contracts world owned (.plain plain) := by
  apply PendingFrame.empty
  exact List.eq_nil_iff_forall_not_mem.mpr (fun owner member =>
    List.not_mem_nil (plain_pending_demand source member))
end Ash.OneShot.SourceDependencyOwners

#print axioms Ash.OneShot.SourceDependencyOwners.plain_pending_demand
#print axioms Ash.OneShot.SourceDependencyOwners.PendingFrame.of_empty_demand

namespace Ash.OneShot.SourceDependencyOwners
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)

/-- A finite source annotation for a retained frame: source typing authenticates
its owner demand, and membership places that demand in the lexical region.
Unlike full dependency locality, this does not inspect imported latent signatures. -/
inductive DemandPendingFrame (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world owned : List Nat) : ExecFrame → Prop where
  | plain (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies)
      (bounded : demand ⊆ owned) :
      DemandPendingFrame operations policy contracts world owned (.plain plain)
  | empty (checked : frame.erase.pending = []) :
      DemandPendingFrame operations policy contracts world owned frame

/-- Annotation follows the existing finite stack tree, including dormant
captures, and checks a source demand at each actual plain frame. -/
inductive DemandPendingStack (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world owned : List Nat) : Stack → Prop where
  | nil : DemandPendingStack operations policy contracts world owned .nil
  | push (frame : DemandPendingFrame operations policy contracts world owned entry)
      (rest : DemandPendingStack operations policy contracts world owned tail) :
      DemandPendingStack operations policy contracts world owned (.push entry tail)
  | live (saved : DemandPendingStack operations policy contracts world owned captured)
      (rest : DemandPendingStack operations policy contracts world owned tail) :
      DemandPendingStack operations policy contracts world owned (.live owner input answer captured caller tail)
  | spent (rest : DemandPendingStack operations policy contracts world owned tail) :
      DemandPendingStack operations policy contracts world owned (.spent owner answer caller tail)

theorem DemandPendingFrame.bound
    (source : DemandPendingFrame operations policy contracts world owned frame) : frame.erase.pending ⊆ owned := by
  cases source with
  | plain source bounded => exact (plain_pending_demand source).trans bounded
  | empty checked => rw [checked]; exact List.nil_subset _

theorem DemandPendingStack.bound
    (source : DemandPendingStack operations policy contracts world owned stack) : stack.erase.pending ⊆ owned := by
  induction source with
  | nil => exact List.nil_subset _
  | push frame rest ih => exact List.append_subset.mpr ⟨frame.bound, ih⟩
  | live saved rest ihSaved ihRest => exact List.append_subset.mpr ⟨ihSaved, ihRest⟩
  | spent rest ih => exact ih

theorem DemandPendingStack.internal
    (source : DemandPendingStack operations policy contracts world owned stack) :
    InternalUses owned stack.erase.pending := OpenOwnerUses.internal_of_subset source.bound

theorem DemandPendingFrame.owner_weaken
    (source : DemandPendingFrame operations policy contracts world owned frame)
    (larger : owned ⊆ nextOwned) :
    DemandPendingFrame operations policy contracts world nextOwned frame := by
  cases source with
  | plain source bounded => exact .plain source (bounded.trans larger)
  | empty checked => exact .empty checked

theorem DemandPendingStack.owner_weaken
    (source : DemandPendingStack operations policy contracts world owned stack)
    (larger : owned ⊆ nextOwned) :
    DemandPendingStack operations policy contracts world nextOwned stack := by
  induction source with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame.owner_weaken larger) ih
  | live saved rest ihSaved ihRest => exact .live ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem DemandPendingStack.append
    (front : DemandPendingStack operations policy contracts world owned left)
    (back : DemandPendingStack operations policy contracts world owned right) :
    DemandPendingStack operations policy contracts world owned (left.append right) := by
  induction front with
  | nil => exact back
  | push frame rest ih => exact .push frame ih
  | live saved rest ihSaved ihRest => exact .live saved ihRest
  | spent rest ih => exact .spent ih

theorem DemandPendingStack.decompose
    (source : DemandPendingStack operations policy contracts world owned (left.append right)) :
    DemandPendingStack operations policy contracts world owned left ∧
      DemandPendingStack operations policy contracts world owned right := by
  induction left with
  | nil => exact ⟨.nil, source⟩
  | push frame tail ih => cases source with
      | push head rest => obtain ⟨front, back⟩ := ih rest; exact ⟨.push head front, back⟩
  | live owner input answer captured caller tail ihSaved ihTail => cases source with
      | live saved rest => obtain ⟨front, back⟩ := ihTail rest; exact ⟨.live saved front, back⟩
  | spent owner answer caller tail ih => cases source with
      | spent rest => obtain ⟨front, back⟩ := ih rest; exact ⟨.spent front, back⟩

/-- Reuse the existing checked-demand induction. Only direct calls,
retirements, and the same looked-up continuation records need membership checks. -/
theorem DemandPendingFrame.of_checked {plain : PlainData}
    (source : SourceDependencyFrames.Context operations policy contracts world environment allowed plain.scope
      plain.context input output demand requirements dependencies)
    (resumes : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .resume⟩ entries = some ⟨demand, body⟩ → owner ∈ owned →
        RecursiveDisposalCapture.directCalls body ⊆ owned ∧ RecursiveDisposalCapture.directRetirements body ⊆ owned)
    (disposals : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ entries = some ⟨demand, body⟩ → owner ∈ owned → demand ⊆ owned)
    (checked : Checked entries receiving before requirements row)
    (calls : RecursiveDisposalCapture.directCalls requirements ⊆ owned)
    (retirements : RecursiveDisposalCapture.directRetirements requirements ⊆ owned) :
    DemandPendingFrame operations policy contracts world owned (.plain plain) :=
  .plain source (Lexical.checked_demand_bound resumes disposals checked calls retirements)

/-- Retain the actual source witness while entering the existing frame
interface through its demand-backed constructor. -/
theorem DemandPendingFrame.to_pending
    (source : DemandPendingFrame operations policy contracts world owned frame) :
    PendingFrame operations policy contracts world owned frame := by
  cases source with
  | plain source bounded => exact .demand source bounded
  | empty checked => exact .empty checked

/-- Existing discard, resume and unwind consumers can use the finite demand
annotation without an additional dependency-locality premise. -/
theorem DemandPendingStack.to_pending
    (source : DemandPendingStack operations policy contracts world owned stack) :
    PendingStack operations policy contracts world owned stack := by
  induction source with
  | nil => exact .nil
  | push frame rest ih => exact .push frame.to_pending ih
  | live saved rest ihSaved ihRest => exact .live ihSaved ihRest
  | spent rest ih => exact .spent ih

/-- Reuse the established source reentry interface at the same regional owner
sets. Scope and source-demand evidence are supplied only for the predecessor. -/
theorem ReentrySource.of_demand_unwind
    (scopes : LexicalUnwind.UnwindPrefix front)
    (frontSource : DemandPendingStack operations policy contracts world front.erase.liveTickets front)
    (savedSource : DemandPendingStack operations policy contracts world
      (ownedTickets captured ++ ownedTickets tail) captured)
    (tailSource : DemandPendingStack operations policy contracts world (ownedTickets tail) tail) :
    ReentrySource operations policy contracts world front captured tail .unwind :=
  .unwind scopes frontSource.to_pending savedSource.to_pending tailSource.to_pending

/-- Construct the existing runtime reentry guard from finite source demands.
The scope premise is the existing lexical unwind-prefix evidence. -/
theorem demand_reentry_bounds
    (scopes : LexicalUnwind.UnwindPrefix front)
    (frontSource : DemandPendingStack operations policy contracts world front.erase.liveTickets front)
    (savedSource : DemandPendingStack operations policy contracts world
      (ownedTickets captured ++ ownedTickets tail) captured)
    (tailSource : DemandPendingStack operations policy contracts world (ownedTickets tail) tail) :
    LexicalUnwind.ReentryBounds front captured tail .unwind :=
  (ReentrySource.of_demand_unwind scopes frontSource savedSource tailSource).bounds

/-- The same finite annotations discharge the established discard-use proof;
no successor-use or future-admission premise is added. -/
theorem source_demand_discard_use
    (checked : LexicalUnwind.MachineUse policy tickets (.eval ⟨.discard binder, runtimeScope,
      front.append (.live owner input answer captured caller tail)⟩))
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner input answer captured caller tail))).Nodup)
    (unprotected : ProtectionContexts.protectedMode captured.erase = false)
    (frontSource : DemandPendingStack operations policy contracts world
      (ownedTickets front ++ ownedTickets tail) front)
    (savedSource : DemandPendingStack operations policy contracts world captured.erase.liveTickets captured)
    (tailSource : DemandPendingStack operations policy contracts world (ownedTickets tail) tail) :
    LexicalUnwind.MachineUse policy tickets (.unwind runtimeScope
      (captured.append (.push (.closing identity runtimeScope)
        (front.append (.spent owner answer caller tail))))) :=
  source_discard_use checked resolved unique unprotected
    frontSource.to_pending savedSource.to_pending tailSource.to_pending
end Ash.OneShot.SourceDependencyOwners

#print axioms Ash.OneShot.SourceDependencyOwners.DemandPendingFrame.of_checked
#print axioms Ash.OneShot.SourceDependencyOwners.demand_reentry_bounds
#print axioms Ash.OneShot.SourceDependencyOwners.source_demand_discard_use

#print axioms Ash.OneShot.SourceDependencyOwners.DemandPendingFrame.to_pending
#print axioms Ash.OneShot.SourceDependencyOwners.DemandPendingStack.to_pending
#print axioms Ash.OneShot.SourceDependencyOwners.ReentrySource.of_demand_unwind
