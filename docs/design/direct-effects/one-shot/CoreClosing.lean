import Admission

/-!
Bounded implementation evidence for TASK-0032, governed by DN-0033.
Shared Control encodes frame shapes and ghost owner identities, not an exported
Rust heap or machine configuration. This models `src/eval/machine.rs`'s successful discard close-control projection
for ordinary one-shot clauses, cells and cleanup boundaries. It is not an
Effect Core evaluator or complete C3 simulation. Rust vectors store outer
frames first; Control stores the next inner frame first. `vector` records that
conversion. `PopAppend` models work.pop and nested work.append; its constructors
neither mention calculus Event nor assume simulation.

The projection begins after successful capacity, work, trace, retained-cell,
capability and disposal preflight. It assumes disposal checks during mutation
also succeed. Registration clauses/boundaries and native buffers are excluded.
Running actions and unfinished close/resource completions are excluded by
`Ready`. Callback typing, interpreter agreement and outside support remain
independent obligations supplied by OpenCloses.
-/
namespace Ash.OneShot.CoreClosing

def Allowed (frame : Frame) : Prop :=
  match frame.kind with
  | .bind | .handler _ _ | .resource _ | .armed _ => True
  | _ => False

inductive Ready : Control → Prop where
  | nil : Ready .nil
  | push (allowed : Allowed frame) (rest : Ready tail) : Ready (.push frame tail)
  | live (saved : Ready capture) (rest : Ready tail) :
      Ready (.live owner input answer capture tail)
  | spent (rest : Ready tail) : Ready (.spent owner answer tail)

def keep (frame : Frame) : List CloseItem :=
  match frame.kind with
  | .resource identity => [.release identity]
  | .armed identity => [.invoke identity frame.access frame.requests]
  | _ => []

def retained : Control → List CloseItem
  | .nil => []
  | .push frame rest => keep frame ++ retained rest
  | .live _ _ _ saved rest => retained saved ++ retained rest
  | .spent _ _ rest => retained rest

/-- Taking the selected capability and nested captures consumes tickets;
    Rust retains no ClauseBoundary in its closing vector. -/
def consumed : Control → List Nat
  | .nil => []
  | .push _ rest => consumed rest
  | .live owner _ _ saved rest => owner :: (consumed saved ++ consumed rest)
  | .spent _ _ rest => consumed rest

inductive CoreFrame where
  | ordinary : Frame → CoreFrame
  | live : Nat → Control → CoreFrame
  | spent : Nat → CoreFrame
  deriving DecidableEq, Repr

/-- Rust vector orientation, outer to inner. Captures remain nested. -/
def vector : Control → List CoreFrame
  | .nil => []
  | .push frame rest => vector rest ++ [.ordinary frame]
  | .live owner _ _ saved rest => vector rest ++ [.live owner saved]
  | .spent owner _ rest => vector rest ++ [.spent owner]

/-- Work has its pop end first. Appending an outer-to-inner nested vector
    prepends its reversal to the remaining work. -/
inductive PopAppend : List CoreFrame → List CloseItem → List Nat → Prop where
  | nil : PopAppend [] [] []
  | ordinary (allowed : Allowed frame) (next : PopAppend rest closing tickets) :
      PopAppend (.ordinary frame :: rest) (keep frame ++ closing) tickets
  | live (saved : Ready capture)
      (next : PopAppend ((vector capture).reverse ++ rest) closing tickets) :
      PopAppend (.live owner capture :: rest) closing (owner :: tickets)
  | spent (next : PopAppend rest closing tickets) :
      PopAppend (.spent owner :: rest) closing tickets

/-- Successful preflight constructs a finite traversal, including remaining
    work. No future calculus execution premise is used. -/
theorem ready_traversal {control : Control} (ready : Ready control)
    (next : PopAppend rest closing tickets) :
    PopAppend ((vector control).reverse ++ rest)
      (retained control ++ closing) (consumed control ++ tickets) := by
  induction ready generalizing rest closing tickets with
  | nil => simpa [vector, retained, consumed] using next
  | push allowed checked ih =>
      simpa [vector, retained, consumed, List.reverse_append, List.append_assoc] using
        PopAppend.ordinary allowed (ih next)
  | live saved checked ihSaved ihRest =>
      simpa [vector, retained, consumed, List.reverse_append, List.append_assoc] using
        PopAppend.live saved (ihSaved (ihRest next))
  | spent checked ih =>
      simpa [vector, retained, consumed, List.reverse_append] using PopAppend.spent (ih next)

def frameClosing : CoreFrame → List CloseItem
  | .ordinary frame => keep frame
  | .live _ capture => retained capture
  | .spent _ => []

def frameTickets : CoreFrame → List Nat
  | .ordinary _ => []
  | .live owner capture => owner :: consumed capture
  | .spent _ => []

@[simp] theorem vector_closing (control : Control) :
    ((vector control).reverse.flatMap frameClosing) = retained control := by
  induction control <;> simp_all [vector, retained, frameClosing, List.reverse_append]

@[simp] theorem vector_tickets (control : Control) :
    ((vector control).reverse.flatMap frameTickets) = consumed control := by
  induction control <;> simp_all [vector, consumed, frameTickets, List.reverse_append]

/-- All completed runs have exactly the same ordered output. -/
theorem pop_append_outputs (run : PopAppend work closing tickets) :
    closing = work.flatMap frameClosing ∧ tickets = work.flatMap frameTickets := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | ordinary allowed next ih => simpa [frameClosing, frameTickets] using ih
  | live saved next ih => simpa [frameClosing, frameTickets, List.append_assoc] using ih
  | spent next ih => simpa [frameClosing, frameTickets] using ih

theorem discard_projection_exact
    (run : PopAppend (vector capture).reverse closing tickets) :
    closing = retained capture ∧ tickets = consumed capture := by
  simpa using pop_append_outputs run

/-- Rust installs closing.into_iter().rev(). Its next pop returns the first
    retained item. -/
def installedVector (capture : Control) : List CloseItem := (retained capture).reverse

@[simp] theorem installed_pop_order (capture : Control) :
    (installedVector capture).reverse = retained capture := by simp [installedVector]

/-- Calculus retirement entries correspond to consumption during traversal. -/
def eraseRetire : List CloseItem → List CloseItem
  | [] => []
  | .retire _ :: rest => eraseRetire rest
  | item :: rest => item :: eraseRetire rest

def planTickets : List CloseItem → List Nat
  | [] => []
  | .retire owner :: rest => owner :: planTickets rest
  | _ :: rest => planTickets rest

@[simp] theorem eraseRetire_append (left right : List CloseItem) :
    eraseRetire (left ++ right) = eraseRetire left ++ eraseRetire right := by
  induction left with
  | nil => rfl
  | cons item rest ih => cases item <;> simp_all [eraseRetire]

@[simp] theorem planTickets_append (left right : List CloseItem) :
    planTickets (left ++ right) = planTickets left ++ planTickets right := by
  induction left with
  | nil => rfl
  | cons item rest ih => cases item <;> simp_all [planTickets]

/-- Exact ordered bridge to the existing structural closing judgment. -/
theorem closes_retained (checked : Closes capture original surviving plan) :
    eraseRetire plan = retained capture := by
  induction checked <;> simp_all [eraseRetire, retained, keep]

theorem closes_ready (checked : Closes capture original surviving plan) : Ready capture := by
  induction checked with
  | nil => exact .nil
  | bind frame rest original surviving plan kind next ih =>
      exact .push (by simp [Allowed, kind]) ih
  | handler frame effect activation rest original surviving plan kind next ih =>
      exact .push (by simp [Allowed, kind]) ih
  | resource frame identity rest original surviving plan kind next ih =>
      exact .push (by simp [Allowed, kind]) ih
  | armed frame identity rest original surviving plan kind pending access requests next ih =>
      exact .push (by simp [Allowed, kind]) ih
  | live owner input answer saved rest original surviving inside outside capture next ihSaved ihRest =>
      exact .live ihSaved ihRest
  | spent owner answer rest original surviving plan next ih => exact .spent ih

/-- Pop consumption and calculus retirement order contain the same tickets. -/
theorem closes_tickets (checked : Closes capture original surviving plan) :
    (planTickets plan).Perm (consumed capture) := by
  induction checked with
  | nil => exact .refl _
  | bind frame rest original surviving plan kind next ih => simpa [consumed] using ih
  | handler frame effect activation rest original surviving plan kind next ih => simpa [consumed] using ih
  | resource frame identity rest original surviving plan kind next ih => simpa [planTickets, consumed] using ih
  | armed frame identity rest original surviving plan kind pending access requests next ih =>
      simpa [planTickets, consumed] using ih
  | live owner input answer saved rest original surviving inside outside capture next ihSaved ihRest =>
      simp only [planTickets_append, planTickets, consumed]
      exact List.perm_middle.trans ((ihSaved.append ihRest).cons owner)
  | spent owner answer rest original surviving plan next ih => simpa [consumed] using ih

/-- Partition every close-plan owner into a retained frame or consumed ticket.
    This is accounting, not an assumption about future callbacks. -/
theorem plan_partition (plan : List CloseItem) :
    (planOwners (eraseRetire plan) ++ (planTickets plan).map Owner.ticket).Perm
      (planOwners plan) := by
  induction plan with
  | nil => exact .refl _
  | cons item rest ih =>
      cases item with
      | release identity =>
          simpa [eraseRetire, planTickets, planOwners, CloseItem.owner] using
            ih.cons (.resource identity)
      | invoke identity access requests =>
          simpa [eraseRetire, planTickets, planOwners, CloseItem.owner] using
            ih.cons (.cleanup identity)
      | retire owner =>
          simp only [eraseRetire, planTickets, List.map_cons, planOwners, CloseItem.owner]
          exact List.perm_middle.trans (ih.cons (.ticket owner))

/-- Only ticket owners disappear during projection. -/
def isRetainedOwner : Owner → Bool
  | .ticket _ => false
  | _ => true

theorem allowed_frame_partition (allowed : Allowed frame) :
    planOwners (keep frame) = frame.owners.filter isRetainedOwner ∧
    frame.owners.filter (fun owner => !isRetainedOwner owner) = [] := by
  cases kind : frame.kind <;>
    simp_all [Allowed, keep, Frame.owners, planOwners, CloseItem.owner,
      List.filter_cons, isRetainedOwner]

/-- Frame owners and contained tickets form independent structural partitions;
    callback support is unnecessary for this accounting claim. -/
theorem ready_owner_partition (ready : Ready capture) :
    planOwners (retained capture) = capture.owners.filter isRetainedOwner ∧
    (consumed capture).map Owner.ticket =
      capture.owners.filter (fun owner => !isRetainedOwner owner) := by
  induction ready with
  | nil => simp [retained, consumed, Control.owners, planOwners]
  | push allowed rest ih =>
      obtain ⟨frames, noTickets⟩ := allowed_frame_partition allowed
      simp only [retained, consumed, Control.owners, List.filter_append,
        planOwners, List.map_append] at *
      simp [frames, noTickets, ih.1, ih.2]
  | live saved rest ihSaved ihRest =>
      simp only [planOwners] at ihSaved ihRest ⊢
      simp [retained, consumed, Control.owners, List.map_append,
        isRetainedOwner, ihSaved.1, ihSaved.2, ihRest.1, ihRest.2]
  | spent rest ih => simpa [retained, consumed, Control.owners] using ih

theorem ready_accounting (ready : Ready capture) :
    (planOwners (retained capture) ++ (consumed capture).map Owner.ticket).Perm
      capture.owners := by
  obtain ⟨frames, tickets⟩ := ready_owner_partition ready
  rw [frames, tickets]
  exact List.filter_append_perm isRetainedOwner capture.owners

theorem ready_selected_accounting (ready : Ready capture) :
    (.ticket selected ::
      (planOwners (retained capture) ++ (consumed capture).map Owner.ticket)).Perm
      (Control.live selected input answer capture .nil).owners := by
  simpa [Control.owners] using (ready_accounting ready).cons (.ticket selected)

theorem ready_selected_no_duplicate_owners (ready : Ready capture)
    (unique : Unique (.live selected input answer capture .nil)) :
    (.ticket selected ::
      (planOwners (retained capture) ++ (consumed capture).map Owner.ticket)).Nodup :=
  (ready_selected_accounting ready).nodup_iff.mpr unique

/-- Exact multiset accounting includes recursively consumed capability owners. -/
theorem closes_accounting (checked : Closes capture original surviving plan) :
    (planOwners (retained capture) ++ (consumed capture).map Owner.ticket).Perm
      capture.owners := by
  have retainedSame := closes_retained checked
  have ticketsSame := (closes_tickets checked).map Owner.ticket
  have partition := (plan_partition plan).trans (close_owner_accounting checked)
  rw [retainedSame] at partition
  exact ((List.Perm.refl _).append ticketsSame.symm).trans partition

/-- The selected ticket is consumed before traversing the capture. -/
theorem selected_accounting (checked : Closes capture original surviving plan) :
    (.ticket selected ::
      (planOwners (retained capture) ++ (consumed capture).map Owner.ticket)).Perm
      (Control.live selected input answer capture .nil).owners := by
  simpa [Control.owners] using (closes_accounting checked).cons (.ticket selected)

/-- Existing uniqueness supplies exactly-once retained and consumed owners,
    including disjointness between both partitions. -/
theorem selected_no_duplicate_owners
    (checked : Closes capture original surviving plan)
    (unique : Unique (.live selected input answer capture .nil)) :
    (.ticket selected ::
      (planOwners (retained capture) ++ (consumed capture).map Owner.ticket)).Nodup :=
  (selected_accounting checked).nodup_iff.mpr unique

/-- Existing callback support/interpreter evidence suffices to construct the
    independent projection. Outside requirements remain explicit. -/
theorem open_closes_projection
    (checked : Admission.OpenCloses capture original surviving resources outward plan)
    (support : resources ⊆ outer.visible)
    (requests : RequestsResolved outer outward) :
    PopAppend (vector capture).reverse (eraseRetire plan) (consumed capture) ∧
    (planOwners (eraseRetire plan) ++ (consumed capture).map Owner.ticket).Perm
      capture.owners := by
  have closed := Admission.open_closes_materialize checked support requests
  have run := ready_traversal (closes_ready closed) PopAppend.nil
  have order := closes_retained closed
  constructor
  · simpa [order] using run
  · rw [order]
    exact closes_accounting closed

/-- A running action cannot pass structural preflight. -/
theorem running_excluded (frame : Frame) (kind : frame.kind = .running identity) :
    ¬ Ready (.push frame rest) := by
  intro checked
  cases checked with
  | push allowed next => simp [Allowed, kind] at allowed

namespace Examples

def cell (identity : Nat) : Frame := ⟨.resource identity, .unit, .unit, [], [], []⟩
def cleanup (identity : Nat) : Frame := ⟨.armed identity, .unit, .unit, [], [], []⟩
def plain : Frame := ⟨.bind, .unit, .unit, [], [], []⟩
def handler : Frame := ⟨.handler (.user 1 []) 90, .unit, .unit, [], [], []⟩

def nested : Control :=
  .push (cleanup 8) (.push (cell 4) (.push handler .nil))

def capture : Control :=
  .push (cleanup 7)
    (.live 12 .unit .unit nested
      (.spent 13 .unit (.push plain (.push (cell 5) .nil))))

/-- Rust's source vector puts the outer cell first and inner cleanup last. -/
theorem actual_outer_to_inner_vector : vector capture =
    [.ordinary (cell 5), .ordinary plain, .spent 13, .live 12 nested,
      .ordinary (cleanup 7)] := rfl

theorem nested_ready : Ready nested :=
  .push trivial (.push trivial (.push trivial .nil))

theorem capture_ready : Ready capture :=
  .push trivial (.live nested_ready (.spent (.push trivial (.push trivial .nil))))

/-- The nested vector is appended when live 12 is popped; its inner cleanup
    is visited before either nested cell 4 or outer cell 5. -/
theorem concrete_depth_first_run : PopAppend (vector capture).reverse
    [.invoke 7 [] [], .invoke 8 [] [], .release 4, .release 5] [12] := by
  simpa [capture, nested, retained, keep, cleanup, cell, handler, plain, consumed] using
    ready_traversal capture_ready PopAppend.nil

/-- Installation reverses append order, so subsequent pop restores that order. -/
theorem concrete_installed_vector : installedVector capture =
    [.release 5, .release 4, .invoke 8 [] [], .invoke 7 [] []] := rfl

end Examples
end Ash.OneShot.CoreClosing

#print axioms Ash.OneShot.CoreClosing.ready_traversal
#print axioms Ash.OneShot.CoreClosing.discard_projection_exact
#print axioms Ash.OneShot.CoreClosing.closes_retained
#print axioms Ash.OneShot.CoreClosing.selected_accounting
#print axioms Ash.OneShot.CoreClosing.selected_no_duplicate_owners
#print axioms Ash.OneShot.CoreClosing.open_closes_projection
#print axioms Ash.OneShot.CoreClosing.Examples.concrete_depth_first_run

#print axioms Ash.OneShot.CoreClosing.ready_accounting
#print axioms Ash.OneShot.CoreClosing.ready_selected_no_duplicate_owners
