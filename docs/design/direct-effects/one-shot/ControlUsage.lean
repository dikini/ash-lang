import Demand

/-!
Scheduled continuation consumption across retained control. Code checking,
active accessibility, and the balance against owned tickets are explicit
components; recursively owned dormant tickets do not become active providers.
This is a usage layer, not a combined type/effect/resource safety theorem.
-/

namespace Ash.OneShot.Syntax
open Execution Typing

inductive FrameDemand (policy : TicketPolicy) (tickets : UsageTickets) :
    ExecFrame → List Nat → Prop where
  | plain (code : CodeDemand policy tickets data.scope (data.context.plug .unit) demand) :
      FrameDemand policy tickets (.plain data) demand
  | handler (scope : UsageScopeKnown tickets handler.scope)
      (clauses : ClausesUse policy handler.clauses) :
      FrameDemand policy tickets (.handler handler) []
  | cell (scope : UsageScopeKnown tickets runtimeScope) :
      FrameDemand policy tickets (.cell identity payload runtimeScope answer) []
  | armed (scope : UsageScopeKnown tickets action.scope)
      (code : Uses policy .none .available action.action .available) :
      FrameDemand policy tickets (.armed action) []
  | running (scope : UsageScopeKnown tickets action.scope)
      (code : Uses policy .none .available action.action .available)
      (result : Uses policy .none .available saved .available) :
      FrameDemand policy tickets (.running action saved closed) []
  | closing (scope : UsageScopeKnown tickets runtimeScope) :
      FrameDemand policy tickets (.closing identity runtimeScope) []
  | retiring (known : tickets owner = some rights) :
      FrameDemand policy tickets (.retiring owner) [owner]

/-- Retirement is an internal consumption, not a request to resume a ticket. -/
def frameActiveDemand (frame : ExecFrame) (demand : List Nat) : List Nat :=
  match frame with
  | .retiring _ => []
  | _ => demand

theorem frame_active_demand_subset (frame : ExecFrame) (demand : List Nat) :
    frameActiveDemand frame demand ⊆ demand := by
  cases frame <;> simp [frameActiveDemand]

/-- Only live boundaries on the active spine supply continuation access. -/
def activeTickets : Stack → List Nat
  | .nil => []
  | .push _ rest => activeTickets rest
  | .live owner _ _ _ _ rest => owner :: activeTickets rest
  | .spent _ _ _ rest => activeTickets rest

/-- Ticket ownership also includes dormant captures and scheduled retirement. -/
def ownedTickets : Stack → List Nat
  | .nil => []
  | .push (.retiring owner) rest => owner :: ownedTickets rest
  | .push _ rest => ownedTickets rest
  | .live owner _ _ saved _ rest => owner :: (ownedTickets saved ++ ownedTickets rest)
  | .spent _ _ _ rest => ownedTickets rest

theorem active_tickets_append (left right : Stack) :
    activeTickets (left.append right) = activeTickets left ++ activeTickets right := by
  induction left <;> simp_all [Stack.append, activeTickets]

theorem owned_tickets_append (left right : Stack) :
    ownedTickets (left.append right) = ownedTickets left ++ ownedTickets right := by
  induction left with
  | nil => rfl
  | push frame rest ih => cases frame <;> simp_all [Stack.append, ownedTickets]
  | live => simp_all [Stack.append, ownedTickets, List.append_assoc]
  | spent => simp_all [Stack.append, ownedTickets]

inductive StackUsage (policy : TicketPolicy) (tickets : UsageTickets) :
    Stack → List Nat → List Nat → Prop where
  | nil : StackUsage policy tickets .nil outside []
  | push (frame : FrameDemand policy tickets entry frameDemand)
      (accessible : frameActiveDemand entry frameDemand ⊆ activeTickets tail ++ outside)
      (rest : StackUsage policy tickets tail outside restDemand) :
      StackUsage policy tickets (.push entry tail) outside (frameDemand ++ restDemand)
  | live (known : tickets owner = some rights) (scope : UsageScopeKnown tickets callerScope)
      (saved : StackUsage policy tickets capture (activeTickets tail ++ outside) captureDemand)
      (rest : StackUsage policy tickets tail outside restDemand) :
      StackUsage policy tickets (.live owner input answer capture callerScope tail)
        outside (captureDemand ++ restDemand)
  | spent (known : tickets owner = some rights) (scope : UsageScopeKnown tickets callerScope)
      (rest : StackUsage policy tickets tail outside demand) :
      StackUsage policy tickets (.spent owner answer callerScope tail) outside demand

/-- Replace an external interface only for names actually demanded by code. -/
theorem stack_usage_change_external
    (checked : StackUsage policy tickets stack outside demand)
    (retain : ∀ owner, owner ∈ demand → owner ∈ outside → owner ∈ other) :
    StackUsage policy tickets stack other demand := by
  induction checked generalizing other with
  | nil => exact .nil
  | push frame accessible rest ih =>
      refine .push frame ?_ (ih ?_)
      · intro owner present
        rcases List.mem_append.mp (accessible present) with within | external
        · exact List.mem_append_left _ within
        · exact List.mem_append_right _ (retain owner
            (List.mem_append_left _ (frame_active_demand_subset _ _ present)) external)
      · intro owner present external
        exact retain owner (List.mem_append_right _ present) external
  | live known scope saved rest ihSaved ihRest =>
      refine .live known scope (ihSaved ?_) (ihRest ?_)
      · intro owner present accessible
        rcases List.mem_append.mp accessible with within | external
        · exact List.mem_append_left _ within
        · exact List.mem_append_right _ (retain owner (List.mem_append_left _ present) external)
      · intro owner present external
        exact retain owner (List.mem_append_right _ present) external
  | spent known scope rest ih => exact .spent known scope (ih retain)

theorem stack_usage_external_weaken
    (checked : StackUsage policy tickets stack outside demand) (larger : outside ⊆ other) :
    StackUsage policy tickets stack other demand :=
  stack_usage_change_external checked (fun _ _ present => larger present)

theorem stack_usage_remove_unused_external
    (checked : StackUsage policy tickets stack (owner :: outside) demand)
    (unused : owner ∉ demand) : StackUsage policy tickets stack outside demand := by
  apply stack_usage_change_external checked
  intro name demanded accessible
  rcases List.mem_cons.mp accessible with same | external
  · subst name
    exact False.elim (unused demanded)
  · exact external

theorem stack_usage_append
    (front : StackUsage policy tickets left (activeTickets right ++ outside) leftDemand)
    (tail : StackUsage policy tickets right outside rightDemand) :
    StackUsage policy tickets (left.append right) outside (leftDemand ++ rightDemand) := by
  induction left generalizing leftDemand with
  | nil => cases front; exact tail
  | push entry rest ih =>
      cases front with
      | push frame accessible checked =>
          simpa only [Stack.append, List.append_assoc] using StackUsage.push frame
            (by simpa only [active_tickets_append, List.append_assoc] using accessible)
            (ih checked)
  | live owner input answer saved caller rest ihSaved ihRest =>
      cases front with
      | live known scope savedChecked restChecked =>
          simpa only [Stack.append, List.append_assoc] using StackUsage.live known scope
            (by simpa only [active_tickets_append, List.append_assoc] using savedChecked)
            (ihRest restChecked)
  | spent owner answer caller rest ih =>
      cases front with
      | spent known scope restChecked => exact .spent known scope (ih restChecked)

theorem stack_usage_decompose
    (checked : StackUsage policy tickets (left.append right) outside demand) :
    ∃ leftDemand rightDemand,
      demand = leftDemand ++ rightDemand ∧
      StackUsage policy tickets left (activeTickets right ++ outside) leftDemand ∧
      StackUsage policy tickets right outside rightDemand := by
  induction left generalizing demand with
  | nil => exact ⟨[], demand, rfl, .nil, checked⟩
  | push entry rest ih =>
      cases checked with
      | push frame accessible next =>
          obtain ⟨leftDemand, rightDemand, same, inside, tail⟩ := ih next
          exact ⟨_, rightDemand, by simp [same, List.append_assoc],
            .push frame (by simpa only [active_tickets_append, List.append_assoc] using accessible) inside, tail⟩
  | live owner input answer saved caller rest ihSaved ihRest =>
      cases checked with
      | live known scope savedChecked next =>
          rename_i rights captureDemand restDemand
          obtain ⟨leftDemand, rightDemand, same, inside, tail⟩ := ihRest next
          exact ⟨captureDemand ++ leftDemand, rightDemand, by simp [same, List.append_assoc],
            .live known scope
              (by simpa only [active_tickets_append, List.append_assoc] using savedChecked) inside, tail⟩
  | spent owner answer caller rest ih =>
      cases checked with
      | spent known scope next =>
          obtain ⟨leftDemand, rightDemand, same, inside, tail⟩ := ih next
          exact ⟨leftDemand, rightDemand, same, .spent known scope inside, tail⟩

theorem handler_cut_usage_decomposition
    (cut : HandlerCut requested whole capture tail handler)
    (checked : StackUsage policy tickets whole outside demand) :
    ∃ captureDemand tailDemand,
      demand = captureDemand ++ tailDemand ∧
      StackUsage policy tickets capture (activeTickets tail ++ outside) captureDemand ∧
      StackUsage policy tickets tail outside tailDemand := by
  rw [handler_cut_reconstructs cut] at checked
  exact stack_usage_decompose checked

def ticketProjection : Owner → Option Nat
  | .ticket owner => some owner
  | _ => none

theorem owned_tickets_project (stack : Stack) :
    ownedTickets stack = stack.erase.owners.filterMap ticketProjection := by
  induction stack with
  | nil => rfl
  | push frame rest ih =>
      cases frame <;> simp_all [ownedTickets, Stack.erase, ExecFrame.erase,
        PlainData.erase, HandlerData.erase, ActionData.erase, closeFrame,
        CloseItem.frame, Control.owners, Frame.owners, ticketProjection, List.filterMap_cons]
  | live => simp_all [ownedTickets, Stack.erase, Control.owners, ticketProjection]
  | spent => simp_all [ownedTickets, Stack.erase, Control.owners]

theorem ticket_projection_nodup {owners : List Owner} (unique : owners.Nodup) :
    (owners.filterMap ticketProjection).Nodup := by
  induction owners with
  | nil => simp
  | cons entry rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      have next := ih unique
      cases entry with
      | resource | cleanup | close => simpa [ticketProjection, List.filterMap_cons] using next
      | ticket owner =>
          simp only [List.filterMap_cons, ticketProjection, List.nodup_cons]
          refine ⟨?_, next⟩
          intro present
          obtain ⟨entry, inside, selected⟩ := List.mem_filterMap.mp present
          cases entry <;> simp_all [ticketProjection]

theorem owned_tickets_unique (unique : Unique stack.erase) : (ownedTickets stack).Nodup := by
  rw [owned_tickets_project]
  exact ticket_projection_nodup unique

theorem resume_usage_recomposition {front capture tail : Stack}
    (checked : StackUsage policy tickets (front.append (.live owner input answer capture caller tail)) outside demand)
    (unused : owner ∉ demand) :
    ∃ afterDemand,
      StackUsage policy tickets (capture.append (front.append (.spent owner answer caller tail))) outside afterDemand ∧
      afterDemand.Perm demand := by
  obtain ⟨frontDemand, boundaryDemand, same, frontChecked, boundary⟩ := stack_usage_decompose checked
  subst demand
  cases boundary with
  | live known scope saved rest =>
      rename_i rights captureDemand tailDemand
      have frontUnused : owner ∉ frontDemand := fun present => unused (List.mem_append_left _ present)
      have narrow : StackUsage policy tickets front (activeTickets tail ++ outside) frontDemand :=
        stack_usage_remove_unused_external
          (by simpa only [activeTickets, List.cons_append] using frontChecked) frontUnused
      have restoredFront := stack_usage_append (right := .spent owner answer caller tail) narrow (StackUsage.spent known scope rest)
      have restoredCapture : StackUsage policy tickets capture
          (activeTickets (front.append (.spent owner answer caller tail)) ++ outside) captureDemand := by
        apply stack_usage_external_weaken saved
        intro name present
        simp only [active_tickets_append, activeTickets, List.append_assoc]
        exact List.mem_append_right _ present
      refine ⟨_, stack_usage_append restoredCapture restoredFront, ?_⟩
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand

def ConfigurationUsage (policy : TicketPolicy) (tickets : UsageTickets)
    (configuration : Configuration) : Prop :=
  ∃ currentDemand controlDemand,
    CodeDemand policy tickets configuration.scope configuration.expression currentDemand ∧
    StackUsage policy tickets configuration.stack [] controlDemand ∧
    currentDemand ⊆ activeTickets configuration.stack ∧
    (currentDemand ++ controlDemand).Perm (ownedTickets configuration.stack) ∧
    (ownedTickets configuration.stack).Nodup

theorem resume_code_demand
    (checked : CodeDemand policy tickets scope (.resume binder value) demand)
    (resolved : scope.resolve binder = some owner) : demand = [owner] := by
  cases checked with
  | idle scope used => cases used
  | consume known used =>
      cases used with
      | resume permitted operand =>
          simp [Scope.resolve] at resolved
          exact congrArg (fun n => [n]) resolved

theorem resume_preserves_configuration_usage {front capture tail : Stack}
    (before : ConfigurationUsage policy tickets
      ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ConfigurationUsage policy tickets
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  have currentSame := resume_code_demand code resolved
  subst currentDemand
  have demandedUnique : (owner :: controlDemand).Nodup := balance.symm.nodup unique
  obtain ⟨unused, controlUnique⟩ := List.nodup_cons.mp demandedUnique
  obtain ⟨afterDemand, restored, reordered⟩ := resume_usage_recomposition control unused
  have projected : controlDemand.Perm
      (ownedTickets front ++ (ownedTickets capture ++ ownedTickets tail)) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets] using List.perm_middle)
  have afterBalance : afterDemand.Perm
      (ownedTickets (capture.append (front.append (.spent owner answer caller tail)))) := by
    refine (reordered.trans projected).trans ?_
    simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using
      (List.perm_append_comm (l₁ := ownedTickets front) (l₂ := ownedTickets capture)).append_right (ownedTickets tail)
  refine ⟨[], afterDemand, ?_, restored, List.nil_subset _, afterBalance,
    afterBalance.nodup (reordered.symm.nodup controlUnique)⟩
  cases code with
  | consume known used =>
      cases used with
      | resume permitted operand =>
          exact .idle (.bound known) (value_use_transport isValue operand _ .available)

def UsageExtension (before after : UsageTickets) : Prop :=
  ∀ owner rights, before owner = some rights → after owner = some rights

def UsageTickets.insert (tickets : UsageTickets) (owner : Nat) (rights : OneShotRights) : UsageTickets :=
  fun name => if name = owner then some rights else tickets name

theorem fresh_usage_insert_extends (fresh : tickets owner = none) :
    UsageExtension tickets (UsageTickets.insert tickets owner rights) := by
  intro name old known
  by_cases same : name = owner
  · subst name
    simp [fresh] at known
  · simp [UsageTickets.insert, same, known]

theorem usage_scope_extension (scope : UsageScope before runtimeScope useScope)
    (extension : UsageExtension before after) : UsageScope after runtimeScope useScope := by
  cases scope with
  | none => exact .none
  | bound known => exact .bound (extension _ _ known)

theorem usage_scope_known_extension (scope : UsageScopeKnown before runtimeScope)
    (extension : UsageExtension before after) : UsageScopeKnown after runtimeScope := by
  obtain ⟨useScope, checked⟩ := scope
  exact ⟨useScope, usage_scope_extension checked extension⟩

theorem code_demand_extension (code : CodeDemand policy before scope expression demand)
    (extension : UsageExtension before after) : CodeDemand policy after scope expression demand := by
  cases code with
  | idle scope used => exact .idle (usage_scope_extension scope extension) used
  | consume known used => exact .consume (extension _ _ known) used

theorem frame_demand_extension (frame : FrameDemand policy before entry demand)
    (extension : UsageExtension before after) : FrameDemand policy after entry demand := by
  cases frame with
  | plain code => exact .plain (code_demand_extension code extension)
  | handler scope clauses => exact .handler (usage_scope_known_extension scope extension) clauses
  | cell scope => exact .cell (usage_scope_known_extension scope extension)
  | armed scope code => exact .armed (usage_scope_known_extension scope extension) code
  | running scope code result => exact .running (usage_scope_known_extension scope extension) code result
  | closing scope => exact .closing (usage_scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ known)

theorem stack_usage_extension (checked : StackUsage policy before stack outside demand)
    (extension : UsageExtension before after) : StackUsage policy after stack outside demand := by
  induction checked with
  | nil => exact .nil
  | push frame accessible rest ih => exact .push (frame_demand_extension frame extension) accessible ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (extension _ _ known) (usage_scope_known_extension scope extension) ihSaved ihRest
  | spent known scope rest ih => exact .spent (extension _ _ known) (usage_scope_known_extension scope extension) ih

theorem owned_tickets_registered
    (checked : StackUsage policy tickets stack outside demand) (present : owner ∈ ownedTickets stack) :
    ∃ rights, tickets owner = some rights := by
  induction checked with
  | nil => cases present
  | push frame accessible rest ih =>
      cases frame with
      | plain | handler | cell | armed | running | closing => exact ih present
      | retiring known =>
          rcases List.mem_cons.mp present with same | remaining
          · subst owner
            exact ⟨_, known⟩
          · exact ih remaining
  | live known scope saved rest ihSaved ihRest =>
      rcases List.mem_cons.mp present with same | remaining
      · subst owner
        exact ⟨_, known⟩
      · rcases List.mem_append.mp remaining with inside | outside
        · exact ihSaved inside
        · exact ihRest outside
  | spent known scope rest ih => exact ih present

theorem handler_cut_checked_usage
    (cut : HandlerCut requested whole capture tail handler)
    (checked : StackUsage policy tickets whole outside demand) :
    UsageScopeKnown tickets handler.scope ∧ ClausesUse policy handler.clauses := by
  induction cut generalizing outside demand with
  | hit => cases checked with
      | push frame accessible rest => cases frame with
          | handler scope clauses => exact ⟨scope, clauses⟩
  | push entry rest capture tail handler miss next ih => cases checked with
      | push frame accessible rest => exact ih rest
  | live owner input answer saved caller rest capture tail handler next ih => cases checked with
      | live known scope saved rest => exact ih rest
  | spent owner answer caller rest capture tail handler next ih => cases checked with
      | spent known scope rest => exact ih rest

theorem perform_value_demand_empty
    (code : CodeDemand policy tickets scope (.perform requested operation operand) demand)
    (isValue : operand.IsValue) : demand = [] := by
  cases code with
  | idle scope used => rfl
  | consume known used => cases used with
      | perform operand => cases value_use_preserves_state isValue operand

theorem capture_preserves_configuration_usage
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (before : ConfigurationUsage policy tickets ⟨.perform requested operation operand, scope, whole⟩)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ConfigurationUsage policy (UsageTickets.insert tickets owner (policy binder))
      ⟨body.subst parameter operand, .ticket binder owner,
        .live owner input handler.answer capture handler.scope tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  have currentSame := perform_value_demand_empty code isValue
  subst currentDemand
  obtain ⟨handlerScope, clauses⟩ := handler_cut_checked_usage cut control
  obtain ⟨captureDemand, tailDemand, same, saved, rest⟩ := handler_cut_usage_decomposition cut control
  have extension := fresh_usage_insert_extends (rights := policy binder) fresh
  have known : UsageTickets.insert tickets owner (policy binder) owner = some (policy binder) := by
    simp [UsageTickets.insert]
  have ownerFresh : owner ∉ ownedTickets whole := by
    intro present
    obtain ⟨rights, registered⟩ := owned_tickets_registered control present
    simp [fresh] at registered
  have ownership : ownedTickets whole = ownedTickets capture ++ ownedTickets tail := by
    rw [handler_cut_reconstructs cut, owned_tickets_append]
  have tailUsage := stack_usage_extension rest extension
  have savedUsage := stack_usage_extension saved extension
  refine ⟨[owner], captureDemand ++ tailDemand, ?_,
    .live known (usage_scope_known_extension handlerScope extension) savedUsage tailUsage,
    ?_, ?_, ?_⟩
  · apply CodeDemand.consume known
    apply usage_substitution (selected_clause_usage selected clauses) isValue
    cases code with
    | idle scope used => cases used with
        | perform operand => exact value_use_transport isValue operand .none .available
  · simp [activeTickets]
  · simpa only [List.nil_append, same, ownership, ownedTickets, List.singleton_append] using balance.cons owner
  · simpa only [ownership, ownedTickets, List.nodup_cons] using And.intro ownerFresh unique

theorem active_tickets_owned (stack : Stack) : activeTickets stack ⊆ ownedTickets stack := by
  induction stack with
  | nil => exact List.Subset.refl _
  | push frame rest ih =>
      cases frame <;> first | exact ih | exact fun _ present => List.mem_cons_of_mem _ (ih present)
  | live owner input answer saved caller rest ihSaved ihRest =>
      intro name present
      rcases List.mem_cons.mp present with same | remaining
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest remaining))
  | spent owner answer caller rest ih => exact ih

theorem recursive_live_tickets_owned (stack : Stack) : stack.erase.liveTickets ⊆ ownedTickets stack := by
  induction stack with
  | nil => exact List.Subset.refl _
  | push frame rest ih =>
      cases frame <;> first | exact ih | exact fun _ present => List.mem_cons_of_mem _ (ih present)
  | live owner input answer saved caller rest ihSaved ihRest =>
      intro name present
      rcases List.mem_cons.mp present with same | remaining
      · exact List.mem_cons.mpr (Or.inl same)
      · rcases List.mem_append.mp remaining with inside | outside
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihSaved inside))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest outside))
  | spent owner answer caller rest ih => exact ih

theorem frame_demand_is_active_or_retiring
    (checked : FrameDemand policy tickets frame demand) (present : owner ∈ demand) :
    owner ∈ frameActiveDemand frame demand ∨ frame = .retiring owner := by
  cases checked with
  | plain => exact Or.inl present
  | handler | cell | armed | running | closing => cases present
  | retiring =>
      simp only [List.mem_singleton] at present
      subst owner
      exact Or.inr rfl

theorem stack_demand_access_bound
    (checked : StackUsage policy tickets stack outside demand) :
    demand ⊆ ownedTickets stack ++ outside := by
  induction checked with
  | nil => exact List.nil_subset _
  | push frame accessible rest ih =>
      intro owner present
      rcases List.mem_append.mp present with here | later
      · rcases frame_demand_is_active_or_retiring frame here with active | retiring
        · have visible := accessible active
          rcases List.mem_append.mp visible with within | external
          · have owned := active_tickets_owned _ within
            cases frame <;> simp_all [ownedTickets]
          · exact List.mem_append_right _ external
        · subst retiring
          simp [ownedTickets]
      · have bound := ih later
        cases frame <;> simp_all [ownedTickets]
  | live known scope saved rest ihSaved ihRest =>
      intro owner present
      rcases List.mem_append.mp present with inside | outside
      · rcases List.mem_append.mp (ihSaved inside) with within | external
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ within))
        · rcases List.mem_append.mp external with within | external
          · exact List.mem_append_left _ (List.mem_cons_of_mem _
              (List.mem_append_right _ (active_tickets_owned _ within)))
          · exact List.mem_append_right _ external
      · rcases List.mem_append.mp (ihRest outside) with within | external
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ within))
        · exact List.mem_append_right _ external
  | spent known scope rest ih => exact ih

theorem frame_demand_pending_or_retiring
    (checked : FrameDemand policy tickets frame demand) (present : owner ∈ demand) :
    owner ∈ frame.erase.pending ∨ frame = .retiring owner := by
  cases checked with
  | plain code =>
      rename_i data
      exact Or.inl ((translated_demand_membership code data.translated owner).mp present)
  | handler | cell | armed | running | closing => cases present
  | retiring =>
      simp only [List.mem_singleton] at present
      subst owner
      exact Or.inr rfl

theorem stack_demand_pending_or_owned
    (checked : StackUsage policy tickets stack outside demand) :
    demand ⊆ stack.erase.pending ++ ownedTickets stack := by
  induction checked with
  | nil => exact List.nil_subset _
  | push frame accessible rest ih =>
      intro owner present
      rcases List.mem_append.mp present with here | later
      · rcases frame_demand_pending_or_retiring frame here with pending | retiring
        · exact List.mem_append_left _ (List.mem_append_left _ pending)
        · subst retiring
          exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
      · rcases List.mem_append.mp (ih later) with pending | owned
        · exact List.mem_append_left _ (List.mem_append_right _ pending)
        · cases frame <;> simp_all [Stack.erase, Control.pending, ownedTickets]
  | live known scope saved rest ihSaved ihRest =>
      intro owner present
      rcases List.mem_append.mp present with inside | outside
      · rcases List.mem_append.mp (ihSaved inside) with pending | owned
        · exact List.mem_append_left _ (List.mem_append_left _ pending)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ owned))
      · rcases List.mem_append.mp (ihRest outside) with pending | owned
        · exact List.mem_append_left _ (List.mem_append_right _ pending)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ owned))
  | spent known scope rest ih => exact ih

theorem internally_demanded_tickets_are_owned
    (checked : StackUsage policy tickets stack outside demand)
    (internal : InternalUses stack.erase.liveTickets stack.erase.pending) : demand ⊆ ownedTickets stack := by
  intro owner present
  rcases List.mem_append.mp (stack_demand_pending_or_owned checked present) with pending | owned
  · exact recursive_live_tickets_owned _ (internalUses_subset internal pending)
  · exact owned

theorem balanced_middle_demands {a b c x y z : List Nat}
    (balance : (a ++ b ++ c).Perm (x ++ y ++ z)) (unique : (x ++ y ++ z).Nodup)
    (front : a ⊆ x ++ z) (middle : b ⊆ y) (tail : c ⊆ z) : b.Perm y := by
  have demandUnique := balance.symm.nodup unique
  have bUnique := (List.nodup_append.mp (List.nodup_append.mp demandUnique).1).2.1
  have yUnique := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.1
  apply (List.perm_ext_iff_of_nodup bUnique yUnique).mpr
  intro owner
  constructor
  · exact fun present => middle present
  · intro owned
    have absentX : owner ∉ x := by
      intro present
      exact (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2 owner present owner owned rfl
    have absentZ : owner ∉ z := by
      intro present
      exact (List.nodup_append.mp unique).2.2 owner (List.mem_append_right _ owned) owner present rfl
    have demanded := balance.mem_iff.mpr (List.mem_append_left _ (List.mem_append_right _ owned))
    rcases List.mem_append.mp demanded with earlier | last
    · rcases List.mem_append.mp earlier with first | selected
      · rcases List.mem_append.mp (front first) with left | right
        · exact False.elim (absentX left)
        · exact False.elim (absentZ right)
      · exact selected
    · exact False.elim (absentZ (tail last))

inductive PlanContentsUsage (policy : TicketPolicy) (tickets : UsageTickets) : List CloseEntry → Prop where
  | nil : PlanContentsUsage policy tickets []
  | release (rest : PlanContentsUsage policy tickets tail) :
      PlanContentsUsage policy tickets (.release identity payload :: tail)
  | invoke (code : Uses policy .none .available action.action .available)
      (rest : PlanContentsUsage policy tickets tail) :
      PlanContentsUsage policy tickets (.invoke action :: tail)
  | retire (known : tickets owner = some rights) (rest : PlanContentsUsage policy tickets tail) :
      PlanContentsUsage policy tickets (.retire owner :: tail)

theorem plan_usage_append (front : PlanContentsUsage policy tickets left)
    (tail : PlanContentsUsage policy tickets right) : PlanContentsUsage policy tickets (left ++ right) := by
  induction front with
  | nil => exact tail
  | release rest ih => exact .release ih
  | invoke code rest ih => exact .invoke code ih
  | retire known rest ih => exact .retire known ih

theorem make_plan_retains_usage
    (checked : StackUsage policy tickets stack outside demand)
    (built : makePlan stack = some plan) : PlanContentsUsage policy tickets plan := by
  induction checked generalizing plan with
  | nil => cases built; exact .nil
  | push frame accessible rest ih =>
      rename_i entry frameDemand tail outside restDemand
      cases frame with
      | plain | handler => exact ih built
      | cell scope =>
          cases remaining : makePlan tail with
          | none => simp [makePlan, remaining] at built
          | some suffix =>
              simp only [makePlan, remaining, Option.some.injEq] at built
              subst plan
              exact .release (ih remaining)
      | armed scope code =>
          cases remaining : makePlan tail with
          | none => simp [makePlan, remaining] at built
          | some suffix =>
              simp only [makePlan, remaining, Option.some.injEq] at built
              subst plan
              exact .invoke code (ih remaining)
      | running | closing | retiring => simp [makePlan] at built
  | live known scope saved rest ihSaved ihRest =>
      rename_i owner rights caller capture tail outside captureDemand tailDemand input answer
      cases savedPlan : makePlan capture <;> cases tailPlan : makePlan tail <;>
        simp [makePlan, savedPlan, tailPlan] at built
      case some.some inside outside =>
        subst plan
        exact plan_usage_append (ihSaved savedPlan) (.retire known (ihRest tailPlan))
  | spent known scope rest ih => exact ih built

theorem close_control_usage
    (plan : PlanContentsUsage policy tickets entries) (scope : UsageScopeKnown tickets runtimeScope) :
    StackUsage policy tickets (closeControl runtimeScope entries) outside
      (ownedTickets (closeControl runtimeScope entries)) := by
  induction plan with
  | nil => exact .nil
  | release rest ih => exact .push (.cell scope) (List.nil_subset _) ih
  | invoke code rest ih =>
      rename_i tail action
      exact .push (.armed (action := { action with scope := runtimeScope, answer := .unit }) scope code)
        (List.nil_subset _) ih
  | retire known rest ih => exact .push (.retiring known) (List.nil_subset _) ih

theorem make_plan_preserves_owned_tickets (built : makePlan stack = some plan) :
    (ownedTickets (closeControl scope plan)).Perm (ownedTickets stack) := by
  have erased : rawPlan stack.erase = some (plan.map CloseEntry.erase) := by
    rw [← make_plan_erases, built]
    rfl
  rw [owned_tickets_project, owned_tickets_project, close_control_erases, plan_control_owners]
  exact (raw_plan_accounting stack.erase erased).filterMap ticketProjection

theorem discard_code_demand
    (checked : CodeDemand policy tickets scope (.discard binder) demand)
    (resolved : scope.resolve binder = some owner) : demand = [owner] := by
  cases checked with
  | idle scope used => cases used
  | consume known used =>
      cases used with
      | discard permitted =>
          simp [Scope.resolve] at resolved
          exact congrArg (fun n => [n]) resolved

theorem discard_preserves_configuration_usage {front capture tail : Stack}
    (before : ConfigurationUsage policy tickets
      ⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩)
    (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ConfigurationUsage policy tickets
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  have currentSame := discard_code_demand code resolved
  subst currentDemand
  have demandedUnique : (owner :: controlDemand).Nodup := balance.symm.nodup unique
  obtain ⟨unused, controlUnique⟩ := List.nodup_cons.mp demandedUnique
  have projected : controlDemand.Perm
      (ownedTickets front ++ (ownedTickets capture ++ ownedTickets tail)) := by
    apply List.Perm.cons_inv
    exact balance.trans (by simpa only [owned_tickets_append, ownedTickets] using List.perm_middle)
  have projectedUnique := projected.nodup controlUnique
  obtain ⟨frontDemand, boundaryDemand, same, frontChecked, boundary⟩ := stack_usage_decompose control
  subst controlDemand
  cases boundary with
  | live known callerScope saved rest =>
      rename_i rights captureDemand tailDemand
      have narrow : StackUsage policy tickets front (activeTickets tail ++ []) frontDemand :=
        stack_usage_remove_unused_external
          (by simpa only [activeTickets, List.cons_append] using frontChecked)
          (fun present => unused (List.mem_append_left _ present))
      have frontBound : frontDemand ⊆ ownedTickets front ++ ownedTickets tail := by
        intro name present
        rcases List.mem_append.mp (stack_demand_access_bound narrow present) with within | external
        · exact List.mem_append_left _ within
        · exact List.mem_append_right _ (active_tickets_owned _ (by simpa using external))
      have tailBound : tailDemand ⊆ ownedTickets tail := by
        simpa only [List.append_nil] using stack_demand_access_bound rest
      have captureBalance : captureDemand.Perm (ownedTickets capture) :=
        balanced_middle_demands (by simpa only [List.append_assoc] using projected)
          (by simpa only [List.append_assoc] using projectedUnique) frontBound
          (internally_demanded_tickets_are_owned saved internal) tailBound
      have callerUsage := code_demand_scope code
      have closeUsage := close_control_usage (outside := []) (make_plan_retains_usage saved built) callerUsage
      have planBalance := make_plan_preserves_owned_tickets (scope := scope) built
      have clause := stack_usage_append (right := .spent owner answer caller tail) narrow
        (StackUsage.spent known callerScope rest)
      have closing := StackUsage.push (FrameDemand.closing (identity := closeId) callerUsage)
        (List.nil_subset _) clause
      have closeWide := stack_usage_external_weaken closeUsage (List.nil_subset
        (activeTickets (.push (.closing closeId scope) (front.append (.spent owner answer caller tail))) ++ []))
      have afterControl := stack_usage_append closeWide closing
      have reordered :
          (ownedTickets (closeControl scope plan) ++ (frontDemand ++ tailDemand)).Perm
            (frontDemand ++ (captureDemand ++ tailDemand)) := by
        refine ((planBalance.trans captureBalance.symm).append_right (frontDemand ++ tailDemand)).trans ?_
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand
      have afterBalance :
          (ownedTickets (closeControl scope plan) ++ (frontDemand ++ tailDemand)).Perm
            (ownedTickets ((closeControl scope plan).append
              (.push (.closing closeId scope) (front.append (.spent owner answer caller tail))))) := by
        refine (reordered.trans projected).trans ?_
        have exchange := (List.perm_append_comm (l₁ := ownedTickets front)
          (l₂ := ownedTickets capture)).append_right (ownedTickets tail)
        have replace := planBalance.symm.append_right (ownedTickets front ++ ownedTickets tail)
        simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using exchange.trans (by simpa only [← List.append_assoc] using replace)
      refine ⟨[], _, ?_, afterControl, List.nil_subset _, afterBalance,
        afterBalance.nodup (reordered.symm.nodup controlUnique)⟩
      obtain ⟨useScope, scopeChecked⟩ := callerUsage
      exact .idle scopeChecked .unit

theorem live_clause_cannot_return_unconsumed (isValue : value.IsValue) :
    ¬ ConfigurationUsage policy tickets ⟨value, scope, .live owner input answer capture caller tail⟩ := by
  rintro ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩
  have same := code_demand_value_is_empty code isValue
  subst currentDemand
  cases control with
  | live known callerScope saved rest =>
      have absent := (List.nodup_cons.mp unique).1
      have demanded := balance.mem_iff.mpr (by simp [ownedTickets] : owner ∈ ownedTickets
        (.live owner input answer capture caller tail))
      simp only [List.nil_append] at demanded
      rcases List.mem_append.mp demanded with inside | outside
      · rcases List.mem_append.mp (stack_demand_access_bound saved inside) with captured | external
        · exact absent (List.mem_append_left _ captured)
        · exact absent (List.mem_append_right _ (active_tickets_owned _ (by simpa using external)))
      · exact absent (List.mem_append_right _ (by simpa using stack_demand_access_bound rest outside))

theorem context_replace_unit_usage (context : Context)
    (checked : Uses policy scope before (context.plug .unit) after)
    (isValue : value.IsValue) (valueUse : Uses policy .none .available value .available) :
    Uses policy scope before (context.plug value) after := by
  cases context with
  | pairLeft => cases checked with
      | pair hole suffix => cases hole; exact .pair (value_use_transport isValue valueUse _ _) suffix
  | pairRight => cases checked with
      | pair first hole => cases hole; exact .pair first (value_use_transport isValue valueUse _ _)
  | appFunction => cases checked with
      | app hole argument => cases hole; exact .app (value_use_transport isValue valueUse _ _) argument
  | appArgument => cases checked with
      | app function hole => cases hole; exact .app function (value_use_transport isValue valueUse _ _)
  | bind => cases checked with
      | bind hole suffix => cases hole; exact .bind (value_use_transport isValue valueUse _ _) suffix
  | branch => cases checked with
      | branch hole yes no => cases hole; exact .branch (value_use_transport isValue valueUse _ _) yes no
  | perform => cases checked with
      | perform hole => cases hole; exact .perform (value_use_transport isValue valueUse _ _)
  | resume => cases checked with
      | resume permitted hole => cases hole; exact .resume permitted (value_use_transport isValue valueUse _ _)
  | resource => cases checked with
      | resource hole body => cases hole; exact .resource (value_use_transport isValue valueUse _ _) body
  | cleanup => cases checked with
      | cleanup hole body => cases hole; exact .cleanup (value_use_transport isValue valueUse _ _) body

theorem code_demand_plug_value {frame : Context}
    (context : CodeDemand policy tickets scope (frame.plug .unit) demand)
    (isValue : value.IsValue) (valueUse : Uses policy .none .available value .available) :
    CodeDemand policy tickets scope (frame.plug value) demand := by
  cases context with
  | idle scope checked => exact .idle scope (context_replace_unit_usage _ checked isValue valueUse)
  | consume known checked => exact .consume known (context_replace_unit_usage _ checked isValue valueUse)

theorem raw_value_step_preserves_configuration_usage
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (checked : ConfigurationUsage policy tickets before) : ConfigurationUsage policy tickets after := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := checked
  have currentEmpty := code_demand_value_is_empty code closed.1
  subst currentDemand
  cases step with
  | focus plain focus tail => exact False.elim (focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases control with
      | push frame accessible rest => cases frame with
          | plain context =>
              exact ⟨_, _, code_demand_plug_value context valueClosed.1 (code_demand_value_usage code valueClosed.1),
                rest, by simpa only [frameActiveDemand, List.append_nil] using accessible, balance, unique⟩
  | leaveHandler handler value valueClosed scope tail => cases control with
      | push frame accessible rest => cases frame with
          | handler caller clauses =>
              exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest,
                List.nil_subset _, balance, unique⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases control with
      | push frame accessible rest => cases frame with
          | cell caller =>
              exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest,
                List.nil_subset _, balance, unique⟩
  | startCleanup action saved savedClosed scope tail => cases control with
      | push frame accessible rest => cases frame with
          | armed caller callable =>
              exact ⟨[], _, .idle .none (.app callable .unit),
                .push (.running caller callable (code_demand_value_usage code savedClosed.1)) (List.nil_subset _) rest,
                List.nil_subset _, balance, unique⟩
  | finishCleanup action saved savedClosed scope tail => cases control with
      | push frame accessible rest => cases frame with
          | running caller callable result =>
              obtain ⟨useScope, caller⟩ := caller
              exact ⟨[], _, .idle caller (value_use_transport savedClosed.1 result _ .available), rest,
                List.nil_subset _, balance, unique⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases control with
      | spent known caller rest =>
          exact ⟨[], _, code_demand_value_transport code valueClosed.1 caller, rest,
            List.nil_subset _, balance, unique⟩
  | finishClose identity scope callerScope tail => cases control with
      | push frame accessible rest => cases frame with
          | closing caller =>
              exact ⟨[], _, code_demand_value_transport code closed.1 caller, rest,
                List.nil_subset _, balance, unique⟩
  | retire owner scope tail => cases control with
      | push frame accessible rest => cases frame with
          | retiring known =>
              exact ⟨[], _, code, rest, List.nil_subset _, balance.cons_inv, (List.nodup_cons.mp unique).2⟩

namespace ControlUsageExamples

def rights : OneShotRights := ⟨true, true⟩
def policy : TicketPolicy := fun _ => rights
def emptyTickets : UsageTickets := fun _ => none
def tickets : UsageTickets := ((emptyTickets.insert 3 rights).insert 5 rights).insert 7 rights

theorem none_known (registry : UsageTickets) : UsageScopeKnown registry .none := ⟨.none, .none⟩

def demoHandler : HandlerData :=
  ⟨8, .user 1 [], .cons 0 1 9 (.resume 9 .unit) .nil, .none, .unit, rfl⟩
def terminalAt (activation : Nat) : Stack := .push (.handler { demoHandler with activation := activation }) .nil
def terminal : Stack := terminalAt 8

theorem terminal_at_usage (registry : UsageTickets) (activation : Nat) :
    StackUsage policy registry (terminalAt activation) outside [] :=
  .push (.handler (none_known registry) (.cons (.resume rfl .unit) .nil)) (List.nil_subset _) .nil

theorem terminal_usage (registry : UsageTickets) : StackUsage policy registry terminal outside [] :=
  terminal_at_usage registry 8

def waiting (binder owner : Nat) : PlainData :=
  ⟨.resume binder, .ticket binder owner, .unit, .unit, [owner], by simp [Context.dependencies,
    Context.plug, Expr.dependencies, Scope.translate, Scope.resolve]⟩

theorem waiting_usage (known : tickets owner = some rights) :
    FrameDemand policy tickets (.plain (waiting binder owner)) [owner] :=
  .plain (.consume known (.resume rfl .unit))

/-- The inner live capture retains code that must consume outside owner 7. -/
def nestedFront : Stack :=
  .push (.plain (waiting 10 5))
    (.live 5 .unit .unit (.push (.plain (waiting 11 7)) (terminalAt 18)) .none .nil)
def outerTail : Stack := .live 7 .unit .unit (terminalAt 28) .none .nil
def nestedBefore : Configuration :=
  ⟨.resume 9 .unit, .ticket 9 3, nestedFront.append (.live 3 .unit .unit terminal .none outerTail)⟩

theorem nested_front_usage : StackUsage policy tickets nestedFront [3, 7] [5, 7] := by
  refine .push (waiting_usage rfl) ?_ (.live (captureDemand := [7]) rfl (none_known tickets) ?_ .nil)
  · simp [frameActiveDemand, activeTickets]
  · exact .push (waiting_usage rfl) (by simp [frameActiveDemand, activeTickets, terminalAt])
      (terminal_at_usage tickets 18)

theorem outer_tail_usage : StackUsage policy tickets outerTail [] [] :=
  .live rfl (none_known tickets) (terminal_at_usage tickets 28) .nil

theorem nested_configuration_usage : ConfigurationUsage policy tickets nestedBefore := by
  refine ⟨[3], [5, 7], .consume rfl (.resume rfl .unit), ?_, ?_, ?_, ?_⟩
  · exact stack_usage_append nested_front_usage
      (.live rfl (none_known tickets) (terminal_usage tickets) outer_tail_usage)
  · simp [nestedBefore, active_tickets_append, activeTickets, nestedFront, outerTail]
  · decide
  · decide

theorem nested_control_names_distinct : DistinctNames nestedBefore.stack.erase := by
  unfold DistinctNames
  constructor <;> decide

theorem nested_resume_preserves_dormant_outside_demand :
    ConfigurationUsage policy tickets
      ⟨.unit, .ticket 9 3, terminal.append (nestedFront.append (.spent 3 .unit .none outerTail))⟩ :=
  resume_preserves_configuration_usage nested_configuration_usage rfl (by trivial)

theorem nested_resume_executes :
    RawStep nestedBefore
      ⟨.unit, .ticket 9 3, terminal.append (nestedFront.append (.spent 3 .unit .none outerTail))⟩
      [] [.ticket 3] :=
  .resume 9 3 (.ticket 9 3) .none .unit .unit nestedFront terminal outerTail .unit Execution.Examples.closed_unit rfl

/-- Counts balance, but current owner 5 exists only inside a dormant capture. -/
def inaccessibleStack : Stack :=
  .push (.plain (waiting 9 3)) (.live 3 .unit .unit (.live 5 .unit .unit terminal .none .nil) .none .nil)

theorem dormant_counts_and_code_are_inhabited :
    CodeDemand policy tickets (.ticket 10 5) (.resume 10 .unit) [5] ∧
    StackUsage policy tickets inaccessibleStack [] [3] ∧
    ([5, 3] : List Nat).Perm (ownedTickets inaccessibleStack) ∧
    (ownedTickets inaccessibleStack).Nodup := by
  refine ⟨.consume rfl (.resume rfl .unit), ?_, by decide, by decide⟩
  refine .push (waiting_usage rfl) ?_ (.live rfl (none_known tickets)
    (.live rfl (none_known tickets) (terminal_usage tickets) .nil) .nil)
  simp [frameActiveDemand, activeTickets]

theorem dormant_ticket_cannot_supply_current_resume :
    ¬ ConfigurationUsage policy tickets ⟨.resume 10 .unit, .ticket 10 5, inaccessibleStack⟩ := by
  rintro ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩
  have same := resume_code_demand code (owner := 5) rfl
  subst currentDemand
  have impossible := accessible (by simp : 5 ∈ ([5] : List Nat))
  simp [inaccessibleStack, activeTickets] at impossible

theorem retirement_owns_without_exposing_resume :
    FrameDemand policy tickets (.retiring 3) [3] ∧
    ownedTickets (.push (.retiring 3) .nil) = [3] ∧
    activeTickets (.push (.retiring 3) .nil) = [] := ⟨.retiring rfl, rfl, rfl⟩

theorem cleanup_capture_source_usage : ConfigurationUsage policy emptyTickets
    ⟨.perform (.user 1 []) 0 .unit, .none, Execution.Examples.captureStack⟩ := by
  refine ⟨[], [], .idle .none (.perform .unit), ?_, List.nil_subset _, .refl _, by decide⟩
  exact .push (.running (none_known emptyTickets) (.lambda (.perform .unit)) .integer)
    (List.nil_subset _) (.push (.handler (none_known emptyTickets) (.cons (.resume rfl .unit) .nil))
      (List.nil_subset _) .nil)

theorem cleanup_capture_usage : ConfigurationUsage policy (emptyTickets.insert 3 rights)
    Execution.Examples.capturedState := by
  apply capture_preserves_configuration_usage (owner := 3)
    (HandlerCut.push _ _ _ _ _ (by decide) (.hit Execution.Examples.handler .nil rfl))
    ClauseAt.hit cleanup_capture_source_usage (by trivial) rfl

theorem cell_disposal_source_usage : ConfigurationUsage policy tickets
    ⟨.discard 9, Execution.Examples.closeScope,
      .live 3 .unit .unit Execution.Examples.abandoned .none .nil⟩ := by
  refine ⟨[3], [], .consume rfl (.discard rfl), ?_, ?_, .refl _, by decide⟩
  · refine .live (owner := 3) (captureDemand := []) (restDemand := []) rfl (none_known tickets) ?_ .nil
    exact .push (.armed (none_known tickets) (.lambda (.bind (.perform .resourceRef) .unit)))
      (List.nil_subset _) (.push (.cell (none_known tickets)) (List.nil_subset _)
        (.push (.handler (none_known tickets) (.cons (.discard rfl) .nil)) (List.nil_subset _) .nil))
  · simp [activeTickets]

theorem cell_disposal_usage : ConfigurationUsage policy tickets
    ⟨.unit, Execution.Examples.closeScope,
      (closeControl Execution.Examples.closeScope Execution.Examples.closePlan).append
        (.push (.closing 8 Execution.Examples.closeScope) (.spent 3 .unit .none .nil))⟩ :=
  discard_preserves_configuration_usage (front := .nil) cell_disposal_source_usage rfl rfl .nil

/-- Disposal replaces the inner owner 5's scheduled resume with retirement. -/
def abandonedTicket : Stack := .push (.plain (waiting 10 5))
  (.live 5 .unit .unit (terminalAt 18) .none terminal)
def ticketCloseScope : Scope := .ticket 9 3
def ticketCloseTail : Stack := .push (.closing 31 ticketCloseScope) (.spent 3 .unit .none .nil)

theorem internal_ticket_disposal_source : ConfigurationUsage policy tickets
    ⟨.discard 9, ticketCloseScope, .live 3 .unit .unit abandonedTicket .none .nil⟩ := by
  refine ⟨[3], [5], .consume rfl (.discard rfl), ?_, ?_, by decide, by decide⟩
  refine .live (owner := 3) (captureDemand := [5]) (restDemand := []) rfl (none_known tickets) ?_ .nil
  · exact .push (waiting_usage rfl) (by simp [frameActiveDemand, activeTickets])
      (.live rfl (none_known tickets) (terminal_at_usage tickets 18) (terminal_usage tickets))
  · simp [activeTickets]

theorem internal_ticket_disposal_usage : ConfigurationUsage policy tickets
    ⟨.unit, ticketCloseScope, .push (.retiring 5) ticketCloseTail⟩ := by
  exact discard_preserves_configuration_usage (front := .nil) (closeId := 31)
    internal_ticket_disposal_source rfl (plan := [.retire 5]) rfl (.cons 5 [] (by decide) .nil)

theorem internal_ticket_disposal_executes : RawStep
    ⟨.discard 9, ticketCloseScope, .live 3 .unit .unit abandonedTicket .none .nil⟩
    ⟨.unit, ticketCloseScope, .push (.retiring 5) ticketCloseTail⟩ [.close 31] [.ticket 3] :=
  .discard 9 3 31 ticketCloseScope .none .unit .unit .nil abandonedTicket .nil [.retire 5] rfl rfl

theorem internal_ticket_retirement_usage : ConfigurationUsage policy tickets
    ⟨.unit, ticketCloseScope, ticketCloseTail⟩ :=
  raw_value_step_preserves_configuration_usage (.retire 5 ticketCloseScope ticketCloseTail)
    Execution.Examples.closed_unit internal_ticket_disposal_usage

end ControlUsageExamples

end Ash.OneShot.Syntax

#print axioms Ash.OneShot.Syntax.stack_usage_append
#print axioms Ash.OneShot.Syntax.stack_usage_decompose
#print axioms Ash.OneShot.Syntax.handler_cut_usage_decomposition
#print axioms Ash.OneShot.Syntax.owned_tickets_unique
#print axioms Ash.OneShot.Syntax.resume_usage_recomposition
#print axioms Ash.OneShot.Syntax.resume_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.capture_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.discard_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.live_clause_cannot_return_unconsumed
#print axioms Ash.OneShot.Syntax.raw_value_step_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.ControlUsageExamples.nested_resume_preserves_dormant_outside_demand
#print axioms Ash.OneShot.Syntax.ControlUsageExamples.dormant_ticket_cannot_supply_current_resume
#print axioms Ash.OneShot.Syntax.ControlUsageExamples.cleanup_capture_usage
#print axioms Ash.OneShot.Syntax.ControlUsageExamples.cell_disposal_usage

#print axioms Ash.OneShot.Syntax.ControlUsageExamples.nested_control_names_distinct
#print axioms Ash.OneShot.Syntax.ControlUsageExamples.internal_ticket_retirement_usage
