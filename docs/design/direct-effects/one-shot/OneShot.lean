import Std

/-!
Direct, one-shot control evidence for DN-0033.

The expression layer supplies frame annotations. These definitions do not
assume expression typing, source-elaboration correctness, or semantic safety
as a premise of the structural lemmas.
-/

namespace Ash.OneShot

inductive TypeArgument where
  | nominal : Nat → TypeArgument
  | resource : Nat → TypeArgument
  | apply : TypeArgument → TypeArgument → TypeArgument
  deriving DecidableEq, Repr

def TypeArgument.resources : TypeArgument → List Nat
  | .nominal _ => []
  | .resource identity => [identity]
  | .apply head argument => head.resources ++ argument.resources

/-- Exact instances are separate from dynamic handler activations. Type
    arguments preserve tagged resource identities, including nested metadata. -/
inductive Instance where
  | user : Nat → List TypeArgument → Instance
  | cell : Nat → Instance
  deriving DecidableEq, Repr

def Instance.resources : Instance → List Nat
  | .user _ arguments => arguments.flatMap TypeArgument.resources
  | .cell identity => [identity]

/-- Monomorphic proof-fragment port types. Function annotations retain latent
    requests and resource support; they are not a change to current Core types. -/
inductive Ty where
  | unit | boolean | integer
  | product : Ty → Ty → Ty
  | reference : Nat → Ty
  | function : Ty → Ty → List Instance → List Nat → Ty
  deriving DecidableEq, Repr

def Ty.resources : Ty → List Nat
  | .unit | .boolean | .integer => []
  | .product left right => left.resources ++ right.resources
  | .reference identity => [identity]
  | .function input output requests retained =>
      input.resources ++ output.resources ++ requests.flatMap Instance.resources ++ retained

inductive Owner where
  | resource : Nat → Owner
  | cleanup : Nat → Owner
  | close : Nat → Owner
  | ticket : Nat → Owner
  deriving DecidableEq, Repr

inductive Kind where
  | bind
  | handler : Instance → Nat → Kind
  | resource : Nat → Kind
  | armed : Nat → Kind
  | running : Nat → Kind
  | closing : Nat → Kind
  | finishing : Nat → Kind
  | retiring : Nat → Kind
  deriving DecidableEq, Repr

structure Frame where
  kind : Kind
  input : Ty
  output : Ty
  access : List Nat := []
  /-- Retained/free ticket consumption obligations. Tickets created by a
      handler installed during this frame's future work are not free here. -/
  pending : List Nat := []
  requests : List Instance := []
  deriving DecidableEq, Repr

def Frame.target (f : Frame) : Option Instance :=
  match f.kind with
  | .handler i _ => some i
  | .resource a => some (.cell a)
  | _ => none

def Frame.owners (f : Frame) : List Owner :=
  match f.kind with
  | .resource a => [.resource a]
  | .armed a | .running a => [.cleanup a]
  | .closing a => [.close a]
  | .finishing a => [.resource a]
  | .retiring k => [.ticket k]
  | _ => []

/-- A live clause recursively owns a dormant capture, not an alias to it. -/
inductive Control where
  | nil
  | push : Frame → Control → Control
  | live : Nat → Ty → Ty → Control → Control → Control
  | spent : Nat → Ty → Control → Control
  deriving DecidableEq, Repr

def Control.append (c tail : Control) : Control :=
  match c with
  | .nil => tail
  | .push f rest => .push f (rest.append tail)
  | .live k q a cap rest => .live k q a cap (rest.append tail)
  | .spent k a rest => .spent k a (rest.append tail)

def Control.owners : Control → List Owner
  | .nil => []
  | .push f rest => f.owners ++ rest.owners
  | .live k _ _ cap rest => .ticket k :: (cap.owners ++ rest.owners)
  | .spent _ _ rest => rest.owners

def Control.ticketNames : Control → List Nat
  | .nil => []
  | .push f rest =>
      (match f.kind with | .retiring k => [k] | _ => []) ++ rest.ticketNames
  | .live k _ _ cap rest => k :: (cap.ticketNames ++ rest.ticketNames)
  | .spent k _ rest => k :: rest.ticketNames

def Unique (c : Control) : Prop := c.owners.Nodup

@[simp] theorem append_nil (c : Control) : c.append .nil = c := by
  induction c <;> simp_all [Control.append]

@[simp] theorem append_assoc (a b c : Control) :
    (a.append b).append c = a.append (b.append c) := by
  induction a <;> simp_all [Control.append]

@[simp] theorem owners_append (a b : Control) :
    (a.append b).owners = a.owners ++ b.owners := by
  induction a <;> simp_all [Control.append, Control.owners, List.append_assoc]

@[simp] theorem ticketNames_append (a b : Control) :
    (a.append b).ticketNames = a.ticketNames ++ b.ticketNames := by
  induction a <;> simp_all [Control.append, Control.ticketNames, List.append_assoc]

/-- Ground, structural nearest-exact selection. Dormant captures are not searched. -/
inductive Cut (i : Instance) : Control → Control → Control → Prop where
  | hit (f : Frame) (tail : Control) (matchExact : f.target = some i) :
      Cut i (.push f tail) (.push f .nil) tail
  | push (f : Frame) (rest cap tail : Control)
      (miss : f.target ≠ some i) (next : Cut i rest cap tail) :
      Cut i (.push f rest) (.push f cap) tail
  | live (k : Nat) (q a : Ty) (saved rest cap tail : Control)
      (next : Cut i rest cap tail) :
      Cut i (.live k q a saved rest) (.live k q a saved cap) tail
  | spent (k : Nat) (a : Ty) (rest cap tail : Control)
      (next : Cut i rest cap tail) :
      Cut i (.spent k a rest) (.spent k a cap) tail

theorem cut_decompose (h : Cut i whole cap tail) : whole = cap.append tail := by
  induction h <;> simp_all [Control.append]

theorem cut_unique (h : Cut i whole cap tail)
    (h' : Cut i whole cap' tail') : cap = cap' ∧ tail = tail' := by
  induction h generalizing cap' tail' with
  | hit f tail hm =>
      cases h' with
      | hit => exact ⟨rfl, rfl⟩
      | push _ _ _ _ hn _ => exact False.elim (hn hm)
  | push f rest cap tail hn h ih =>
      cases h' with
      | hit _ _ hm => exact False.elim (hn hm)
      | push _ _ _ _ _ hh =>
          obtain ⟨rfl, rfl⟩ := ih hh
          exact ⟨rfl, rfl⟩
  | live k q a saved rest cap tail h ih =>
      cases h' with
      | live _ _ _ _ _ _ _ hh =>
          obtain ⟨rfl, rfl⟩ := ih hh
          exact ⟨rfl, rfl⟩
  | spent k a rest cap tail h ih =>
      cases h' with
      | spent _ _ _ _ _ hh =>
          obtain ⟨rfl, rfl⟩ := ih hh
          exact ⟨rfl, rfl⟩

/-- Input/answer compatibility of annotated frames and recursively saved captures. -/
inductive Fits : Control → Ty → Ty → Prop where
  | nil (a : Ty) : Fits .nil a a
  | push (f : Frame) (rest : Control) (r : Ty)
      (next : Fits rest f.output r) : Fits (.push f rest) f.input r
  | live (k : Nat) (q a r : Ty) (saved rest : Control)
      (capture : Fits saved q a) (next : Fits rest a r) :
      Fits (.live k q a saved rest) a r
  | spent (k : Nat) (a r : Ty) (rest : Control)
      (next : Fits rest a r) : Fits (.spent k a rest) a r

theorem fits_append (left : Fits c a b) (right : Fits d b r) :
    Fits (c.append d) a r := by
  induction left with
  | nil => exact right
  | push f rest b next ih => exact .push f _ _ (ih right)
  | live k q a b saved rest capture next ihSaved ih =>
      exact .live k q a r saved _ capture (ih right)
  | spent k a b rest next ih => exact .spent k a r _ (ih right)

theorem fits_decompose (c : Control) (h : Fits (c.append d) a r) :
    ∃ b, Fits c a b ∧ Fits d b r := by
  induction c generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | push f rest ih =>
      cases h with
      | push _ _ _ ht =>
          obtain ⟨b, hl, hr⟩ := ih ht
          exact ⟨b, .push f rest b hl, hr⟩
  | live k q ans saved rest ihSaved ih =>
      cases h with
      | live _ _ _ _ _ _ hs ht =>
          obtain ⟨b, hl, hr⟩ := ih ht
          exact ⟨b, .live k q ans b saved rest hs hl, hr⟩
  | spent k ans rest ih =>
      cases h with
      | spent _ _ _ _ ht =>
          obtain ⟨b, hl, hr⟩ := ih ht
          exact ⟨b, .spent k ans b rest hl, hr⟩

theorem capture_type_decomposition (selection : Cut i whole cap tail)
    (typing : Fits whole q r) : ∃ a, Fits cap q a ∧ Fits tail a r := by
  rw [cut_decompose selection] at typing
  exact fits_decompose cap typing

theorem capture_clause_recomposition (saved : Fits cap q a)
    (outer : Fits tail a r) : Fits (.live k q a cap tail) a r :=
  .live k q a r cap tail saved outer

theorem resume_type_recomposition (saved : Fits cap q a)
    (clause : Fits rest a r) : Fits (cap.append rest) q r :=
  fits_append saved clause

theorem capture_owner_accounting (selection : Cut i whole cap tail) :
    (Control.live k q a cap tail).owners = .ticket k :: whole.owners := by
  rw [cut_decompose selection]
  simp [Control.owners]

theorem capture_preserves_unique (selection : Cut i whole cap tail)
    (unique : Unique whole) (fresh : Owner.ticket k ∉ whole.owners) :
    Unique (.live k q a cap tail) := by
  unfold Unique
  rw [capture_owner_accounting selection]
  exact List.nodup_cons.mpr ⟨fresh, unique⟩

/-- Resume moves the saved segment above the entire existing clause front.
    Only the consumed ticket disappears from the ownership list. -/
theorem resume_owner_accounting (front cap tail : Control) :
    (front.append (.live k q a cap tail)).owners.Perm
      (.ticket k :: (cap.append (front.append (.spent k a tail))).owners) := by
  simp only [owners_append, Control.owners]
  have move := List.perm_middle (a := Owner.ticket k)
    (l₁ := front.owners) (l₂ := cap.owners ++ tail.owners)
  have swap := List.Perm.append_right tail.owners
    (List.perm_append_comm (l₁ := front.owners) (l₂ := cap.owners))
  exact move.trans (List.Perm.cons _ (by simpa [List.append_assoc] using swap))

variable {front cap tail : Control} {k : Nat} {q a r : Ty}

theorem resume_preserves_unique
    (h : Unique (front.append (.live k q a cap tail))) :
    Unique (cap.append (front.append (.spent k a tail))) := by
  have h' := (resume_owner_accounting (k := k) (q := q) (a := a)
    front cap tail).nodup_iff.mp h
  exact (List.nodup_cons.mp h').2

theorem resume_removes_ticket
    (h : Unique (front.append (.live k q a cap tail))) :
    Owner.ticket k ∉ (cap.append (front.append (.spent k a tail))).owners := by
  have h' := (resume_owner_accounting (k := k) (q := q) (a := a)
    front cap tail).nodup_iff.mp h
  exact (List.nodup_cons.mp h').1

theorem resume_full_type_recomposition
    (h : Fits (front.append (.live k q a cap tail)) a r) :
    Fits (cap.append (front.append (.spent k a tail))) q r := by
  obtain ⟨b, hp, ht⟩ := fits_decompose front h
  cases ht with
  | live _ _ _ _ _ _ hc ho =>
      exact fits_append hc (fits_append hp (.spent k a r tail ho))

def Frame.visible (f : Frame) : List Nat :=
  match f.kind with
  | .resource a => [a]
  | _ => []

/-- Dormant captures are live ownership but not accessible resources. -/
def Control.visible : Control → List Nat
  | .nil => []
  | .push f rest => f.visible ++ rest.visible
  | .live _ _ _ _ rest => rest.visible
  | .spent _ _ rest => rest.visible

@[simp] theorem visible_append (a b : Control) :
    (a.append b).visible = a.visible ++ b.visible := by
  induction a <;> simp_all [Control.append, Control.visible, List.append_assoc]

/-- Each frame's retained access is justified by its enclosing accessible
    resources. A saved capture is checked separately in that same outer scope. -/
inductive Supported : Control → List Nat → Prop where
  | nil (ambient : List Nat) : Supported .nil ambient
  | push (f : Frame) (rest : Control) (ambient : List Nat)
      (next : Supported rest ambient)
      (access : f.access ⊆ rest.visible ++ ambient) :
      Supported (.push f rest) ambient
  | live (k : Nat) (q a : Ty) (saved rest : Control) (ambient : List Nat)
      (capture : Supported saved (rest.visible ++ ambient))
      (next : Supported rest ambient) :
      Supported (.live k q a saved rest) ambient
  | spent (k : Nat) (a : Ty) (rest : Control) (ambient : List Nat)
      (next : Supported rest ambient) : Supported (.spent k a rest) ambient

theorem supported_mono (h : Supported c ambient)
    (more : ambient ⊆ ambient') : Supported c ambient' := by
  induction h generalizing ambient' with
  | nil => exact .nil _
  | push f rest amb next access ih =>
      apply Supported.push f rest ambient' (ih more)
      intro x hx
      rcases List.mem_append.mp (access hx) with hr | ha
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (more ha)
  | live k q a saved rest amb capture next ihCap ihRest =>
      apply Supported.live k q a saved rest ambient'
      · apply ihCap
        intro x hx
        rcases List.mem_append.mp hx with hr | ha
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (more ha)
      · exact ihRest more
  | spent k a rest amb next ih => exact .spent k a rest ambient' (ih more)

theorem supported_append (h : Supported c (d.visible ++ ambient))
    (hd : Supported d ambient) : Supported (c.append d) ambient := by
  induction c with
  | nil => exact hd
  | push f rest ih =>
      cases h with
      | push _ _ _ next access =>
          apply Supported.push f _ _ (ih next)
          simpa [List.append_assoc] using access
  | live k q a saved rest ihSaved ih =>
      cases h with
      | live _ _ _ _ _ _ capture next =>
          apply Supported.live k q a saved _ _
          · simpa [List.append_assoc] using capture
          · exact ih next
  | spent k a rest ih =>
      cases h with
      | spent _ _ _ _ next => exact .spent k a _ _ (ih next)

theorem supported_decompose (c : Control)
    (h : Supported (c.append d) ambient) :
    Supported c (d.visible ++ ambient) ∧ Supported d ambient := by
  induction c with
  | nil => exact ⟨.nil _, h⟩
  | push f rest ih =>
      cases h with
      | push _ _ _ next access =>
          obtain ⟨hl, hr⟩ := ih next
          exact ⟨.push f rest _ hl (by simpa [List.append_assoc] using access), hr⟩
  | live k q a saved rest ihSaved ih =>
      cases h with
      | live _ _ _ _ _ _ capture next =>
          obtain ⟨hl, hr⟩ := ih next
          exact ⟨.live k q a saved rest _
            (by simpa [List.append_assoc] using capture) hl, hr⟩
  | spent k a rest ih =>
      cases h with
      | spent _ _ _ _ next =>
          obtain ⟨hl, hr⟩ := ih next
          exact ⟨.spent k a rest _ hl, hr⟩

theorem capture_preserves_support (selection : Cut i whole cap tail)
    (h : Supported whole ambient) :
    Supported (.live k q a cap tail) ambient := by
  rw [cut_decompose selection] at h
  obtain ⟨hc, ht⟩ := supported_decompose cap h
  exact .live k q a cap tail ambient hc ht

theorem resume_preserves_support
    (h : Supported (front.append (.live k q a cap tail)) ambient) :
    Supported (cap.append (front.append (.spent k a tail))) ambient := by
  obtain ⟨hp, ht⟩ := supported_decompose front h
  cases ht with
  | live _ _ _ _ _ _ hc ho =>
      have hp' : Supported (front.append (.spent k a tail)) ambient :=
        supported_append hp (.spent k a tail ambient ho)
      apply supported_append _ hp'
      apply supported_mono hc
      intro x hx
      simpa [Control.visible, List.append_assoc] using
        (List.mem_append_right front.visible hx)

inductive Target where
  | source : Nat → Target
  | builtin : Nat → Target
  deriving DecidableEq, Repr

def Frame.resolve (f : Frame) (i : Instance) : Option Target :=
  match f.kind with
  | .handler j h => if i = j then some (.source h) else none
  | .resource a => if i = .cell a then some (.builtin a) else none
  | _ => none

def Control.resolve (i : Instance) : Control → Option Target
  | .nil => none
  | .push f rest => match f.resolve i with
    | some target => some target
    | none => rest.resolve i
  | .live _ _ _ _ rest => rest.resolve i
  | .spent _ _ rest => rest.resolve i

/-- Residual requests must keep the same nearest interpretation, not merely
    find another provider of an equal effect instance. -/
inductive SameRequests (original surviving : Control) : List Instance → Prop where
  | nil : SameRequests original surviving []
  | cons (i : Instance) (rest : List Instance) (target : Target)
      (before : original.resolve i = some target)
      (after : surviving.resolve i = some target)
      (next : SameRequests original surviving rest) :
      SameRequests original surviving (i :: rest)

inductive CloseItem where
  | release : Nat → CloseItem
  | invoke : Nat → List Nat → List Instance → CloseItem
  | retire : Nat → CloseItem
  deriving DecidableEq, Repr

def CloseItem.owner : CloseItem → Owner
  | .release a => .resource a
  | .invoke a _ _ => .cleanup a
  | .retire k => .ticket k

def planOwners (p : List CloseItem) : List Owner := p.map CloseItem.owner

def CloseItem.frame : CloseItem → Frame
  | .release a => ⟨.resource a, .unit, .unit, [], [], []⟩
  | .invoke a access requests => ⟨.armed a, .unit, .unit, access, [], requests⟩
  | .retire k => ⟨.retiring k, .unit, .unit, [], [], []⟩

def planControl : List CloseItem → Control
  | [] => .nil
  | item :: rest => .push item.frame (planControl rest)

/-- Structural closing, with separate original and surviving outer contexts.
    Surviving contexts use the actual materialized plan suffix, including
    resources from recursively owned captures that will be closed later.
    There is intentionally no rule for running, closing, or finishing frames. -/
inductive Closes : Control → Control → Control → List CloseItem → Prop where
  | nil (original surviving : Control) : Closes .nil original surviving []
  | bind (f : Frame) (rest original surviving : Control) (plan : List CloseItem)
      (kind : f.kind = .bind) (next : Closes rest original surviving plan) :
      Closes (.push f rest) original surviving plan
  | handler (f : Frame) (i : Instance) (h : Nat)
      (rest original surviving : Control) (plan : List CloseItem)
      (kind : f.kind = .handler i h) (next : Closes rest original surviving plan) :
      Closes (.push f rest) original surviving plan
  | resource (f : Frame) (a : Nat) (rest original surviving : Control)
      (plan : List CloseItem) (kind : f.kind = .resource a)
      (next : Closes rest original surviving plan) :
      Closes (.push f rest) original surviving (.release a :: plan)
  | armed (f : Frame) (a : Nat) (rest original surviving : Control)
      (plan : List CloseItem) (kind : f.kind = .armed a)
      (ticketClosed : f.pending = [])
      (access : f.access ⊆ ((planControl plan).append surviving).visible)
      (requests : SameRequests (rest.append original)
        ((planControl plan).append surviving) f.requests)
      (next : Closes rest original surviving plan) :
      Closes (.push f rest) original surviving (.invoke a f.access f.requests :: plan)
  | live (k : Nat) (q a : Ty) (saved rest original surviving : Control)
      (inside outside : List CloseItem)
      (capture : Closes saved (rest.append original)
        ((planControl outside).append surviving) inside)
      (next : Closes rest original surviving outside) :
      Closes (.live k q a saved rest) original surviving
        (inside ++ .retire k :: outside)
  | spent (k : Nat) (a : Ty) (rest original surviving : Control)
      (plan : List CloseItem) (next : Closes rest original surviving plan) :
      Closes (.spent k a rest) original surviving plan

theorem close_owner_accounting (h : Closes c original surviving plan) :
    (planOwners plan).Perm c.owners := by
  induction h with
  | nil => exact .refl _
  | bind f rest original surviving plan kind next ih =>
      simpa [Control.owners, Frame.owners, kind] using ih
  | handler f i handlerId rest original surviving plan kind next ih =>
      simpa [Control.owners, Frame.owners, kind] using ih
  | resource f a rest original surviving plan kind next ih =>
      simpa [planOwners, CloseItem.owner, Control.owners, Frame.owners, kind] using
        ih.cons (.resource a)
  | armed f a rest original surviving plan kind ticketClosed access requests next ih =>
      simpa [planOwners, CloseItem.owner, Control.owners, Frame.owners, kind] using
        ih.cons (.cleanup a)
  | live k q a saved rest original surviving inside outside capture next ihCap ihRest =>
      simp only [planOwners, List.map_append, List.map_cons, CloseItem.owner,
        Control.owners]
      have reordered := List.perm_middle (a := Owner.ticket k)
        (l₁ := planOwners inside) (l₂ := planOwners outside)
      exact reordered.trans ((ihCap.append ihRest).cons (.ticket k))
  | spent k a rest original surviving plan next ih => exact ih

theorem close_plan_unique (h : Closes c original surviving plan)
    (unique : Unique c) : (planOwners plan).Nodup :=
  (close_owner_accounting h).nodup_iff.mpr unique

def Control.protected : Control → List Owner
  | .nil => []
  | .push f rest =>
      (match f.kind with
        | .running a => [.cleanup a]
        | .closing a => [.close a]
        | .finishing a => [.resource a]
        | .retiring k => [.ticket k]
        | _ => []) ++ rest.protected
  | .live _ _ _ cap rest => cap.protected ++ rest.protected
  | .spent _ _ rest => rest.protected

theorem close_excludes_protected (h : Closes c original surviving plan) :
    c.protected = [] := by
  induction h <;> simp_all [Control.protected]

/-- Cleanup closures cannot retain the structural clause resume capability.
    Pending entries on abandoned expression frames are checked separately. -/
def Control.ActionTicketsClosed : Control → Prop
  | .nil => True
  | .push f rest =>
      (match f.kind with | .armed _ => f.pending = [] | _ => True) ∧
      rest.ActionTicketsClosed
  | .live _ _ _ saved rest => saved.ActionTicketsClosed ∧ rest.ActionTicketsClosed
  | .spent _ _ rest => rest.ActionTicketsClosed

theorem close_actions_ticket_closed (h : Closes c original surviving plan) :
    c.ActionTicketsClosed := by
  induction h <;> simp_all [Control.ActionTicketsClosed]

def Control.pending : Control → List Nat
  | .nil => []
  | .push f rest => f.pending ++ rest.pending
  | .live _ _ _ cap rest => cap.pending ++ rest.pending
  | .spent _ _ rest => rest.pending

def Control.liveTickets : Control → List Nat
  | .nil => []
  | .push _ rest => rest.liveTickets
  | .live k _ _ cap rest => k :: (cap.liveTickets ++ rest.liveTickets)
  | .spent _ _ rest => rest.liveTickets

/-- This is a finite structural inclusion check, not a future-safety oracle. -/
inductive InternalUses (owned : List Nat) : List Nat → Prop where
  | nil : InternalUses owned []
  | cons (k : Nat) (rest : List Nat) (inside : k ∈ owned)
      (next : InternalUses owned rest) : InternalUses owned (k :: rest)

theorem internalUses_subset (h : InternalUses owned uses) : uses ⊆ owned := by
  induction h with
  | nil => simp
  | cons k rest inside next ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hr
      · exact inside
      · exact ih hr

inductive Discardable (c outer : Control) (plan : List CloseItem) : Prop where
  | checked (closing : Closes c outer outer plan)
      (uses : InternalUses c.liveTickets c.pending) : Discardable c outer plan

theorem discard_preserves_outside_consumption (h : Discardable c outer plan)
    (outside : k ∉ c.liveTickets) : k ∉ c.pending := by
  cases h with
  | checked _ uses => exact fun hk => outside (internalUses_subset uses hk)

theorem discard_preserves_protected (h : Discardable c outer plan) :
    c.protected = [] := by
  cases h with
  | checked closing _ => exact close_excludes_protected closing

theorem discard_accounts_for_every_owner (h : Discardable c outer plan) :
    (planOwners plan).Perm c.owners := by
  cases h with
  | checked closing _ => exact close_owner_accounting closing

def Frame.activation (f : Frame) : List Nat :=
  match f.kind with
  | .handler _ h => [h]
  | _ => []

def Control.activations : Control → List Nat
  | .nil => []
  | .push f rest => f.activation ++ rest.activations
  | .live _ _ _ cap rest => cap.activations ++ rest.activations
  | .spent _ _ rest => rest.activations

@[simp] theorem activations_append (c d : Control) :
    (c.append d).activations = c.activations ++ d.activations := by
  induction c <;> simp_all [Control.append, Control.activations, List.append_assoc]

def DistinctNames (c : Control) : Prop :=
  c.ticketNames.Nodup ∧ c.activations.Nodup

theorem capture_preserves_names (selection : Cut i whole cap tail)
    (h : DistinctNames whole) (fresh : k ∉ whole.ticketNames) :
    DistinctNames (.live k q a cap tail) := by
  rw [cut_decompose selection] at h fresh
  simpa [DistinctNames, Control.ticketNames, Control.activations] using
    And.intro (List.nodup_cons.mpr ⟨fresh, h.1⟩) h.2

theorem resume_preserves_names
    (h : DistinctNames (front.append (.live k q a cap tail))) :
    DistinctNames (cap.append (front.append (.spent k a tail))) := by
  have ticketMove : (front.append (.live k q a cap tail)).ticketNames.Perm
      (cap.append (front.append (.spent k a tail))).ticketNames := by
    simp only [ticketNames_append, Control.ticketNames]
    have p₁ := List.perm_middle (a := k) (l₁ := front.ticketNames)
      (l₂ := cap.ticketNames ++ tail.ticketNames)
    have p₂ := List.Perm.append_right tail.ticketNames
      (List.perm_append_comm (l₁ := front.ticketNames) (l₂ := cap.ticketNames))
    have p₃ := List.perm_middle (a := k)
      (l₁ := cap.ticketNames ++ front.ticketNames) (l₂ := tail.ticketNames)
    exact p₁.trans (by
      simpa [List.append_assoc] using (p₂.cons k).trans p₃.symm)
  have activationMove : (front.append (.live k q a cap tail)).activations.Perm
      (cap.append (front.append (.spent k a tail))).activations := by
    simp only [activations_append, Control.activations]
    simpa [List.append_assoc] using List.Perm.append_right tail.activations
      (List.perm_append_comm (l₁ := front.activations) (l₂ := cap.activations))
  exact ⟨ticketMove.nodup_iff.mp h.1, activationMove.nodup_iff.mp h.2⟩

/-- Kind-specific port restrictions for the result-preserving control kernel.
    A bind's output is the annotated suffix result. A running action consumes
    unit and may return a saved body result through its continuation frame. -/
def Frame.Shape (f : Frame) : Prop :=
  match f.kind with
  | .bind => True
  | .handler _ _ | .resource _ | .armed _ => f.input = f.output
  | .running _ | .finishing _ => f.input = .unit
  | .closing _ => f.input = .unit ∧ f.output = .unit
  | .retiring _ => f.input = .unit ∧ f.output = .unit

def Control.Shaped : Control → Prop
  | .nil => True
  | .push f rest => f.Shape ∧ rest.Shaped
  | .live _ _ _ saved rest => saved.Shaped ∧ rest.Shaped
  | .spent _ _ rest => rest.Shaped

@[simp] theorem shaped_append (c d : Control) :
    (c.append d).Shaped ↔ c.Shaped ∧ d.Shaped := by
  induction c <;> simp_all [Control.append, Control.Shaped, and_assoc]

theorem capture_preserves_shape (selection : Cut i whole cap tail)
    (h : whole.Shaped) : (Control.live k q a cap tail).Shaped := by
  rw [cut_decompose selection] at h
  exact (shaped_append cap tail).mp h

theorem resume_preserves_shape
    (h : (front.append (.live k q a cap tail)).Shaped) :
    (cap.append (front.append (.spent k a tail))).Shaped := by
  simp only [shaped_append, Control.Shaped] at h ⊢
  exact ⟨h.2.1, h.1, h.2.2⟩

/-- Source capture can pass a builtin only if its exact instance does not match. -/
inductive SourceCut (i : Instance) : Control → Control → Control → Prop where
  | hit (f : Frame) (h : Nat) (tail : Control) (source : f.kind = .handler i h) :
      SourceCut i (.push f tail) (.push f .nil) tail
  | push (f : Frame) (rest cap tail : Control)
      (miss : f.target ≠ some i) (next : SourceCut i rest cap tail) :
      SourceCut i (.push f rest) (.push f cap) tail
  | live (k : Nat) (q a : Ty) (saved rest cap tail : Control)
      (next : SourceCut i rest cap tail) :
      SourceCut i (.live k q a saved rest) (.live k q a saved cap) tail
  | spent (k : Nat) (a : Ty) (rest cap tail : Control)
      (next : SourceCut i rest cap tail) :
      SourceCut i (.spent k a rest) (.spent k a cap) tail

theorem sourceCut_is_cut (h : SourceCut i whole cap tail) : Cut i whole cap tail := by
  induction h with
  | hit f handlerId tail source =>
      exact .hit f tail (by simp [Frame.target, source])
  | push f rest cap tail miss next ih => exact .push f rest cap tail miss ih
  | live k q a saved rest cap tail next ih => exact .live k q a saved rest cap tail ih
  | spent k a rest cap tail next ih => exact .spent k a rest cap tail ih

theorem sourceCut_delimits (h : SourceCut i whole cap tail) :
    SourceCut i cap cap .nil := by
  induction h with
  | hit f handlerId tail source => exact .hit f handlerId .nil source
  | push f rest cap tail miss next ih => exact .push f cap cap .nil miss ih
  | live k q a saved rest cap tail next ih => exact .live k q a saved cap cap .nil ih
  | spent k a rest cap tail next ih => exact .spent k a cap cap .nil ih

def Delimited (c : Control) : Prop := ∃ i, SourceCut i c c .nil

def Control.DelimitedLives : Control → Prop
  | .nil => True
  | .push _ rest => rest.DelimitedLives
  | .live _ _ _ saved rest => Delimited saved ∧ saved.DelimitedLives ∧ rest.DelimitedLives
  | .spent _ _ rest => rest.DelimitedLives

@[simp] theorem delimitedLives_append (c d : Control) :
    (c.append d).DelimitedLives ↔ c.DelimitedLives ∧ d.DelimitedLives := by
  induction c <;> simp_all [Control.append, Control.DelimitedLives, and_assoc]

theorem capture_preserves_delimiters (selection : SourceCut i whole cap tail)
    (h : whole.DelimitedLives) :
    (Control.live k q a cap tail).DelimitedLives := by
  rw [cut_decompose (sourceCut_is_cut selection)] at h
  obtain ⟨hc, ht⟩ := (delimitedLives_append cap tail).mp h
  exact ⟨⟨i, sourceCut_delimits selection⟩, hc, ht⟩

theorem resume_preserves_delimiters
    (h : (front.append (.live k q a cap tail)).DelimitedLives) :
    (cap.append (front.append (.spent k a tail))).DelimitedLives := by
  simp only [delimitedLives_append, Control.DelimitedLives] at h ⊢
  exact ⟨h.2.2.1, h.1, h.2.2.2⟩

theorem source_provider_support (selection : SourceCut i whole cap tail)
    (support : Supported whole ambient) :
    ∃ (f : Frame) (h : Nat), f.kind = .handler i h ∧
      f.access ⊆ tail.visible ++ ambient := by
  induction selection with
  | hit f h tail source =>
      cases support with
      | push _ _ _ next access => exact ⟨f, h, source, access⟩
  | push f rest cap tail miss next ih =>
      cases support with
      | push _ _ _ hs _ => exact ih hs
  | live k q a saved rest cap tail next ih =>
      cases support with
      | live _ _ _ _ _ _ hc ht => exact ih ht
  | spent k a rest cap tail next ih =>
      cases support with
      | spent _ _ _ _ ht => exact ih ht

/-- Raw close-plan construction, without support or pending-use checks. Failure
    to construct a plan is distinct from static rejection of an unsafe plan. -/
def rawPlan : Control → Option (List CloseItem)
  | .nil => some []
  | .push f rest => match f.kind, rawPlan rest with
    | .bind, p | .handler _ _, p => p
    | .resource a, some p => some (.release a :: p)
    | .armed a, some p => some (.invoke a f.access f.requests :: p)
    | _, _ => none
  | .live k _ _ cap rest => match rawPlan cap, rawPlan rest with
    | some inside, some outside => some (inside ++ .retire k :: outside)
    | _, _ => none
  | .spent _ _ rest => rawPlan rest

theorem closes_constructs_raw_plan (h : Closes c original surviving p) :
    rawPlan c = some p := by
  induction h <;> simp_all [rawPlan]

theorem raw_plan_accounting (c : Control) (h : rawPlan c = some p) :
    (planOwners p).Perm c.owners := by
  induction c generalizing p with
  | nil =>
      cases h
      exact .refl _
  | push f rest ih =>
      cases hk : f.kind <;> simp [rawPlan, hk] at h
      case bind => simpa [Control.owners, Frame.owners, hk] using ih h
      case handler i id => simpa [Control.owners, Frame.owners, hk] using ih h
      case resource id =>
        cases hr : rawPlan rest <;> simp [hr] at h
        case some p' =>
          subst p
          simpa [planOwners, CloseItem.owner, Control.owners, Frame.owners, hk] using
            (ih hr).cons (.resource id)
      case armed id =>
        cases hr : rawPlan rest <;> simp [hr] at h
        case some p' =>
          subst p
          simpa [planOwners, CloseItem.owner, Control.owners, Frame.owners, hk] using
            (ih hr).cons (.cleanup id)
  | live k q a cap rest ihCap ihRest =>
      cases hc : rawPlan cap <;> cases hr : rawPlan rest <;> simp [rawPlan, hc, hr] at h
      case some.some inside outside =>
        subst p
        simp only [planOwners, List.map_append, List.map_cons, CloseItem.owner,
          Control.owners]
        exact List.perm_middle.trans (((ihCap hc).append (ihRest hr)).cons (.ticket k))
  | spent k a rest ih => exact ih h

@[simp] theorem plan_control_owners (p : List CloseItem) :
    (planControl p).owners = planOwners p := by
  induction p with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp_all [planControl, Control.owners, CloseItem.frame,
        Frame.owners, planOwners, CloseItem.owner]

def closeFrame (z : Nat) : Frame := ⟨.closing z, .unit, .unit, [], [], []⟩

@[simp] theorem plan_control_append (p q : List CloseItem) :
    planControl (p ++ q) = (planControl p).append (planControl q) := by
  induction p <;> simp_all [planControl, Control.append]

theorem resolve_append (c d : Control) (i : Instance) :
    (c.append d).resolve i = match c.resolve i with
      | some t => some t
      | none => d.resolve i := by
  induction c with
  | nil => rfl
  | push f rest ih =>
      cases h : f.resolve i <;> simp_all [Control.append, Control.resolve]
  | live k q a saved rest ihSaved ihRest => exact ihRest
  | spent k a rest ih => exact ih

def RequestsResolved (c : Control) (requests : List Instance) : Prop :=
  ∀ i, i ∈ requests → ∃ target, c.resolve i = some target

theorem sameRequests_resolved_after (h : SameRequests original surviving requests) :
    RequestsResolved surviving requests := by
  induction h with
  | nil => simp [RequestsResolved]
  | cons i rest target before after next ih =>
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨target, after⟩
      · exact ih j hj

/-- A finite structural check against the actual suffix at each invocation. -/
def PlanChecks : List CloseItem → Control → Prop
  | [], _ => True
  | .release _ :: rest, outer => PlanChecks rest outer
  | .retire _ :: rest, outer => PlanChecks rest outer
  | .invoke _ access requests :: rest, outer =>
      access ⊆ ((planControl rest).append outer).visible ∧
      RequestsResolved ((planControl rest).append outer) requests ∧
      PlanChecks rest outer

theorem planChecks_transport (h : PlanChecks p outer)
    (visible : outer.visible = other.visible)
    (resolved : ∀ i, outer.resolve i = other.resolve i) : PlanChecks p other := by
  induction p with
  | nil => trivial
  | cons item rest ih =>
      cases item with
      | release a => exact ih h
      | retire k => exact ih h
      | invoke a access requests =>
          refine ⟨?_, ?_, ih h.2.2⟩
          · simpa only [visible_append, visible] using h.1
          · intro i hi
            obtain ⟨target, ht⟩ := h.2.1 i hi
            refine ⟨target, ?_⟩
            simpa only [resolve_append, resolved] using ht

theorem planChecks_append {p q : List CloseItem}
    (left : PlanChecks p ((planControl q).append outer))
    (right : PlanChecks q outer) : PlanChecks (p ++ q) outer := by
  induction p with
  | nil => exact right
  | cons item rest ih =>
      cases item with
      | release a => exact ih left
      | retire k => exact ih left
      | invoke a access requests =>
          refine ⟨?_, ?_, ih left.2.2⟩
          · change access ⊆ ((planControl (rest ++ q)).append outer).visible
            rw [plan_control_append, append_assoc]
            exact left.1
          · change RequestsResolved ((planControl (rest ++ q)).append outer) requests
            rw [plan_control_append, append_assoc]
            exact left.2.1

theorem close_plan_checks (h : Closes c original surviving p) :
    PlanChecks p surviving := by
  induction h with
  | nil => trivial
  | bind f rest original surviving plan kind next ih => exact ih
  | handler f i handlerId rest original surviving plan kind next ih => exact ih
  | resource f a rest original surviving plan kind next ih => exact ih
  | armed f a rest original surviving plan kind ticketClosed access requests next ih =>
      exact ⟨access, sameRequests_resolved_after requests, ih⟩
  | live k q a saved rest original surviving inside outside capture next ihCap ihRest =>
      have prepared : PlanChecks inside
          ((planControl (.retire k :: outside)).append surviving) :=
        planChecks_transport ihCap rfl (fun _ => rfl)
      exact planChecks_append prepared ihRest
  | spent k a rest original surviving plan next ih => exact ih

theorem planChecks_supported (h : PlanChecks p outer) (support : Supported outer ambient) :
    Supported ((planControl p).append outer) ambient := by
  induction p with
  | nil => exact support
  | cons item rest ih =>
      cases item with
      | release a =>
          exact .push _ _ _ (ih h) (by simp [CloseItem.frame])
      | retire k =>
          exact .push _ _ _ (ih h) (by simp [CloseItem.frame])
      | invoke a access requests =>
          exact .push _ _ _ (ih h.2.2)
            (fun _ hx => List.mem_append_left _ (h.1 hx))

theorem close_plan_preserves_support (h : Closes c original surviving p)
    (support : Supported surviving ambient) :
    Supported ((planControl p).append surviving) ambient :=
  planChecks_supported (close_plan_checks h) support

theorem planChecks_at_invocation
    (h : PlanChecks (beforeItems ++ .invoke action access requests :: suffix) outer) :
    access ⊆ ((planControl suffix).append outer).visible ∧
      RequestsResolved ((planControl suffix).append outer) requests := by
  induction beforeItems with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons item rest ih =>
      cases item with
      | release a => exact ih h
      | retire k => exact ih h
      | invoke a access requests => exact ih h.2.2

theorem close_plan_invocations_ready
    (h : Closes c original surviving (beforeItems ++ .invoke action access requests :: suffix)) :
    access ⊆ ((planControl suffix).append surviving).visible ∧
      RequestsResolved ((planControl suffix).append surviving) requests :=
  planChecks_at_invocation (close_plan_checks h)

/-- An invocation occurrence records its actual remaining close-plan suffix. -/
inductive PlanAt : List CloseItem → Nat → List Nat → List Instance → List CloseItem → Prop where
  | here (action : Nat) (access : List Nat) (requests : List Instance)
      (rest : List CloseItem) : PlanAt (.invoke action access requests :: rest)
        action access requests rest
  | later (item : CloseItem) (rest : List CloseItem)
      (next : PlanAt rest action access requests suffix) :
      PlanAt (item :: rest) action access requests suffix

theorem planAt_append_cases {p q : List CloseItem}
    (h : PlanAt (p ++ q) action access requests suffix) :
    (∃ remaining, PlanAt p action access requests remaining ∧ suffix = remaining ++ q) ∨
      PlanAt q action access requests suffix := by
  induction p with
  | nil => exact Or.inr h
  | cons item rest ih =>
      cases h with
      | here => exact Or.inl ⟨rest, .here _ _ _ _, rfl⟩
      | later _ _ next =>
          rcases ih next with ⟨remaining, atRest, eq⟩ | atOuter
          · exact Or.inl ⟨remaining, .later item rest atRest, eq⟩
          · exact Or.inr atOuter

/-- The original context of an armed action, including its position inside
    recursively saved captures. This traversal does not inspect a close plan. -/
inductive CleanupOrigin : Control → Control → Nat → List Nat → List Instance → Control → Prop where
  | here (f : Frame) (rest outer : Control) (action : Nat)
      (kind : f.kind = .armed action) :
      CleanupOrigin (.push f rest) outer action f.access f.requests (rest.append outer)
  | push (f : Frame) (rest outer : Control)
      (next : CleanupOrigin rest outer action access requests context) :
      CleanupOrigin (.push f rest) outer action access requests context
  | saved (k : Nat) (q a : Ty) (capture rest outer : Control)
      (next : CleanupOrigin capture (rest.append outer) action access requests context) :
      CleanupOrigin (.live k q a capture rest) outer action access requests context
  | liveRest (k : Nat) (q a : Ty) (capture rest outer : Control)
      (next : CleanupOrigin rest outer action access requests context) :
      CleanupOrigin (.live k q a capture rest) outer action access requests context
  | spent (k : Nat) (a : Ty) (rest outer : Control)
      (next : CleanupOrigin rest outer action access requests context) :
      CleanupOrigin (.spent k a rest) outer action access requests context

theorem sameRequests_transport_after (h : SameRequests original surviving requests)
    (resolved : ∀ i, surviving.resolve i = other.resolve i) :
    SameRequests original other requests := by
  induction h with
  | nil => exact .nil
  | cons i rest target before after next ih =>
      exact .cons i rest target before ((resolved i).symm.trans after) ih

theorem close_plan_preserves_interpretation
    (closing : Closes c original surviving p)
    (position : PlanAt p action access requests suffix) :
    ∃ context, CleanupOrigin c original action access requests context ∧
      SameRequests context ((planControl suffix).append surviving) requests := by
  induction closing generalizing action access requests suffix with
  | nil => cases position
  | bind f rest original surviving plan kind next ih =>
      obtain ⟨context, origin, same⟩ := ih position
      exact ⟨context, .push f rest original origin, same⟩
  | handler f i handlerId rest original surviving plan kind next ih =>
      obtain ⟨context, origin, same⟩ := ih position
      exact ⟨context, .push f rest original origin, same⟩
  | resource f resource rest original surviving plan kind next ih =>
      cases position with
      | later _ _ atRest =>
          obtain ⟨context, origin, same⟩ := ih atRest
          exact ⟨context, .push f rest original origin, same⟩
  | armed f owner rest original surviving plan kind ticketClosed support checked next ih =>
      cases position with
      | here => exact ⟨rest.append original, .here f rest original owner kind, checked⟩
      | later _ _ atRest =>
          obtain ⟨context, origin, same⟩ := ih atRest
          exact ⟨context, .push f rest original origin, same⟩
  | live k q a saved rest original surviving inside outside capture next ihCap ihRest =>
      rcases planAt_append_cases position with ⟨remaining, atSaved, eq⟩ | atRest
      · subst suffix
        obtain ⟨context, origin, same⟩ := ihCap atSaved
        refine ⟨context, .saved k q a saved rest original origin,
          sameRequests_transport_after same ?_⟩
        intro i
        rw [plan_control_append, append_assoc]
        simp only [resolve_append, planControl, Control.resolve, CloseItem.frame, Frame.resolve]
      · cases atRest with
        | later _ _ atOutside =>
            obtain ⟨context, origin, same⟩ := ihRest atOutside
            exact ⟨context, .liveRest k q a saved rest original origin, same⟩
  | spent k a rest original surviving plan next ih =>
      obtain ⟨context, origin, same⟩ := ih position
      exact ⟨context, .spent k a rest original origin, same⟩

theorem supported_consume_live
    (h : Supported (front.append (.live k q a cap tail)) ambient) :
    Supported (front.append (.spent k a tail)) ambient := by
  obtain ⟨before, after⟩ := supported_decompose front h
  cases after with
  | live _ _ _ _ _ _ saved outside =>
      exact supported_append before (.spent k a tail ambient outside)

/-- The preflight checks the retained clause continuation. The administrative
    close frame contributes neither resource access nor an interpreter. -/
theorem discard_control_preserves_support
    (h : Supported (front.append (.live k q a cap tail)) ambient)
    (admitted : Discardable cap (front.append (.spent k a tail)) plan) :
    Supported ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))) ambient := by
  cases admitted with
  | checked closing uses =>
      have remaining := supported_consume_live h
      have closeSupported : Supported (.push (closeFrame closeId)
          (front.append (.spent k a tail))) ambient :=
        .push _ _ _ remaining (by simp [closeFrame])
      have prepared : PlanChecks plan (.push (closeFrame closeId)
          (front.append (.spent k a tail))) :=
        planChecks_transport (close_plan_checks closing) rfl (fun _ => rfl)
      exact planChecks_supported prepared closeSupported

theorem discard_invocation_preserves_interpretation
    (admitted : Discardable cap (front.append (.spent k a tail)) plan)
    (position : PlanAt plan action access requests suffix) :
    ∃ context,
      CleanupOrigin cap (front.append (.spent k a tail)) action access requests context ∧
      SameRequests context ((planControl suffix).append (.push (closeFrame closeId)
        (front.append (.spent k a tail)))) requests := by
  cases admitted with
  | checked closing uses =>
      obtain ⟨context, origin, same⟩ := close_plan_preserves_interpretation closing position
      refine ⟨context, origin, sameRequests_transport_after same ?_⟩
      intro i
      simp only [resolve_append, Control.resolve, closeFrame, Frame.resolve]

def Frame.Entry (f : Frame) : Prop :=
  match f.kind with
  | .bind | .handler _ _ | .resource _ | .armed _ => True
  | _ => False

/-- Raw structural events. In particular, discard uses rawPlan, not Discardable.
    Its additional static obligations are proved separately, not assumed here. -/
inductive Flow : Control → Control → List Owner → List Owner → Prop where
  | stay (control : Control) : Flow control control [] []
  | capture (i : Instance) (k : Nat) (q a : Ty) (whole cap tail : Control)
      (selection : SourceCut i whole cap tail) :
      Flow whole (.live k q a cap tail) [.ticket k] []
  | resume (k : Nat) (q a : Ty) (front cap tail : Control) :
      Flow (front.append (.live k q a cap tail))
        (cap.append (front.append (.spent k a tail))) [] [.ticket k]
  | discard (k z : Nat) (q a : Ty) (front cap tail : Control)
      (p : List CloseItem) (build : rawPlan cap = some p) :
      Flow (front.append (.live k q a cap tail))
        ((planControl p).append (.push (closeFrame z)
          (front.append (.spent k a tail)))) [.close z] [.ticket k]
  | enter (f : Frame) (tail : Control) (entry : f.Entry) :
      Flow tail (.push f tail) f.owners []
  | leavePlain (f : Frame) (tail : Control) (plain : f.owners = []) :
      Flow (.push f tail) tail [] []
  | leaveClause (k : Nat) (a : Ty) (tail : Control) :
      Flow (.spent k a tail) tail [] []
  | startAction (f : Frame) (a : Nat) (tail : Control) (savedAccess : List Nat)
      (kind : f.kind = .armed a) :
      Flow (.push f tail)
        (.push { f with kind := .running a, input := .unit, access := f.access ++ savedAccess } tail) [] []
  | finishAction (f : Frame) (a : Nat) (tail : Control) (kind : f.kind = .running a) :
      Flow (.push f tail) tail [] [.cleanup a]
  | release (f : Frame) (a : Nat) (tail : Control) (kind : f.kind = .resource a) :
      Flow (.push f tail) tail [] [.resource a]
  | startFinish (f : Frame) (a : Nat) (tail : Control) (kind : f.kind = .resource a) :
      Flow (.push f tail) (.push { f with kind := .finishing a, input := .unit } tail) [] []
  | finishResource (f : Frame) (a : Nat) (tail : Control) (kind : f.kind = .finishing a) :
      Flow (.push f tail) tail [] [.resource a]
  | finishClose (f : Frame) (z : Nat) (tail : Control) (kind : f.kind = .closing z) :
      Flow (.push f tail) tail [] [.close z]
  | retire (f : Frame) (k : Nat) (tail : Control) (kind : f.kind = .retiring k) :
      Flow (.push f tail) tail [] [.ticket k]

theorem flow_accounting (h : Flow before after created discharged) :
    (before.owners ++ created).Perm (after.owners ++ discharged) := by
  apply List.perm_iff_count.mpr
  intro owner
  induction h with
  | stay => simp
  | capture i k q a whole cap tail selection =>
      rw [capture_owner_accounting (sourceCut_is_cut selection)]
      simp [List.count_append, List.count_cons]
  | resume k q a front cap tail =>
      have eq := (resume_owner_accounting (k := k) (q := q) (a := a)
        front cap tail).count_eq owner
      simp only [List.count_append, List.count_nil, Nat.add_zero,
        List.count_cons] at eq ⊢
      omega
  | discard k z q a front cap tail p build =>
      have eq := (raw_plan_accounting cap build).count_eq owner
      simp only [owners_append, Control.owners, plan_control_owners, closeFrame,
        Frame.owners, List.count_append, List.count_cons, List.count_nil] at eq ⊢
      omega
  | enter f tail entry =>
      simp [Control.owners, List.count_append, Nat.add_comm]
  | leavePlain f tail plain => simp [Control.owners, plain]
  | leaveClause => simp [Control.owners]
  | startAction f a tail savedAccess kind => simp [Control.owners, Frame.owners, kind]
  | finishAction f a tail kind =>
      simp [Control.owners, Frame.owners, kind, List.count_append,
        List.count_cons]
  | release f a tail kind =>
      simp [Control.owners, Frame.owners, kind, List.count_append,
        List.count_cons]
  | startFinish f a tail kind => simp [Control.owners, Frame.owners, kind]
  | finishResource f a tail kind =>
      simp [Control.owners, Frame.owners, kind, List.count_append,
        List.count_cons]
  | finishClose f z tail kind =>
      simp [Control.owners, Frame.owners, kind, List.count_append,
        List.count_cons]
  | retire f k tail kind =>
      simp [Control.owners, Frame.owners, kind, List.count_append,
        List.count_cons]

structure State where
  control : Control
  issued : List Owner
  completed : List Owner

/-- A structural ledger, not a definition in terms of reachable or safe states. -/
def Ledger (s : State) : Prop :=
  s.issued.Perm (s.control.owners ++ s.completed) ∧ s.issued.Nodup

/-- Fresh allocation is checked against lifetime history, including consumed
    tickets. No static safety predicate is used to define an ownership step. -/
inductive Step : State → State → Prop where
  | event (s : State) (after : Control) (created discharged : List Owner)
      (flow : Flow s.control after created discharged)
      (fresh : (s.issued ++ created).Nodup) :
      Step s ⟨after, s.issued ++ created, discharged ++ s.completed⟩

theorem step_preserves_ledger (h : Step s s') (valid : Ledger s) : Ledger s' := by
  cases h with
  | event after created discharged flow fresh =>
      constructor
      · have old := valid.1.append_right created
        have accounting := (flow_accounting flow).append_right s.completed
        have regroup : ((s.control.owners ++ s.completed) ++ created).Perm
            ((s.control.owners ++ created) ++ s.completed) := by
          apply List.perm_iff_count.mpr
          intro o
          simp only [List.count_append]
          omega
        simpa [List.append_assoc] using old.trans (regroup.trans accounting)
      · exact fresh

inductive Steps : State → State → Prop where
  | refl (s : State) : Steps s s
  | next (s t u : State) (first : Step s t) (rest : Steps t u) : Steps s u

theorem steps_preserve_ledger (h : Steps s t) (valid : Ledger s) : Ledger t := by
  induction h with
  | refl => exact valid
  | next s t u first rest ih => exact ih (step_preserves_ledger first valid)

/-- Static disposal admission supplies a raw ownership step whose result
    preserves both the lifetime ledger and accessible resource support. -/
theorem admitted_discard_joint_preservation
    (valid : Ledger ⟨front.append (.live k q a cap tail), issued, completed⟩)
    (support : Supported (front.append (.live k q a cap tail)) ambient)
    (admitted : Discardable cap (front.append (.spent k a tail)) plan)
    (fresh : (issued ++ [Owner.close closeId]).Nodup) :
    let before : State := ⟨front.append (.live k q a cap tail), issued, completed⟩
    let after : State := ⟨(planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail))), issued ++ [.close closeId], .ticket k :: completed⟩
    Step before after ∧ Ledger after ∧ Supported after.control ambient := by
  have raw : rawPlan cap = some plan := by
    cases admitted with
    | checked closing uses => exact closes_constructs_raw_plan closing
  have event := Step.event
    ⟨front.append (.live k q a cap tail), issued, completed⟩
    ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))) [.close closeId] [.ticket k]
    (.discard k closeId q a front cap tail plan raw) fresh
  exact ⟨event, step_preserves_ledger event valid,
    discard_control_preserves_support support admitted⟩

theorem ledger_unique_live (h : Ledger s) : Unique s.control :=
  (List.nodup_append.mp (h.1.nodup_iff.mp h.2)).1

theorem ledger_no_double_completion (h : Ledger s) : s.completed.Nodup :=
  (List.nodup_append.mp (h.1.nodup_iff.mp h.2)).2.1

theorem ledger_no_live_completed_alias (h : Ledger s)
    (live : o ∈ s.control.owners) : o ∉ s.completed := by
  intro done
  exact (List.nodup_append.mp (h.1.nodup_iff.mp h.2)).2.2 o live o done rfl

theorem ticket_owner_has_name {c : Control} (h : Owner.ticket k ∈ c.owners) :
    k ∈ c.ticketNames := by
  induction c with
  | nil => simp [Control.owners] at h
  | push f rest ih =>
      cases hk : f.kind <;>
        simp_all [Control.owners, Frame.owners, Control.ticketNames] <;> grind
  | live j q a cap rest ihCap ihRest =>
      simp only [Control.owners, List.mem_cons, List.mem_append] at h
      simp only [Control.ticketNames, List.mem_cons, List.mem_append]
      rcases h with eq | inside | outside
      · exact Or.inl (by cases eq; rfl)
      · exact Or.inr (Or.inl (ihCap inside))
      · exact Or.inr (Or.inr (ihRest outside))
  | spent j a rest ih => exact List.mem_cons_of_mem j (ih h)

theorem fits_consume_live
    (h : Fits (front.append (.live k q a cap tail)) input answer) :
    Fits (front.append (.spent k a tail)) input answer := by
  obtain ⟨middle, before, after⟩ := fits_decompose front h
  cases after with
  | live _ _ _ _ _ _ saved outside =>
      exact fits_append before (.spent k a answer tail outside)

theorem plan_control_fits (p : List CloseItem) (h : Fits outer .unit answer) :
    Fits ((planControl p).append outer) .unit answer := by
  induction p with
  | nil => exact h
  | cons item rest ih =>
      cases item <;> exact .push _ _ _ ih

theorem discard_type_recomposition
    (h : Fits (front.append (.live k q a cap tail)) .unit answer) :
    Fits ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))) .unit answer :=
  plan_control_fits plan (.push _ _ _ (fits_consume_live h))

theorem close_ticket_name_count_le (h : Closes c original surviving plan) (ticket : Nat) :
    (planControl plan).ticketNames.count ticket ≤ c.ticketNames.count ticket := by
  induction h with
  | nil => exact Nat.le_refl _
  | bind f rest original surviving plan kind next ih =>
      simpa [Control.ticketNames, kind] using ih
  | handler f i handlerId rest original surviving plan kind next ih =>
      simpa [Control.ticketNames, kind] using ih
  | resource f resource rest original surviving plan kind next ih =>
      simpa [planControl, Control.ticketNames, CloseItem.frame, kind] using ih
  | armed f owner rest original surviving plan kind ticketClosed access requests next ih =>
      simpa [planControl, Control.ticketNames, CloseItem.frame, kind] using ih
  | live k q a saved rest original surviving inside outside capture next ihCap ihRest =>
      simp only [plan_control_append, ticketNames_append, planControl, Control.ticketNames,
        CloseItem.frame, List.count_append, List.count_cons, List.count_nil]
      omega
  | spent k a rest original surviving plan next ih =>
      simp only [Control.ticketNames, List.count_cons]
      omega

@[simp] theorem plan_control_activations (plan : List CloseItem) :
    (planControl plan).activations = [] := by
  induction plan with
  | nil => rfl
  | cons item rest ih =>
      cases item <;> simp_all [planControl, Control.activations, CloseItem.frame, Frame.activation]

theorem discard_preserves_names
    (h : DistinctNames (front.append (.live k q a cap tail)))
    (closing : Closes cap original surviving plan) :
    DistinctNames ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))) := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro ticket
    have capCount := close_ticket_name_count_le closing ticket
    have beforeCount := List.nodup_iff_count.mp h.1 ticket
    simp only [ticketNames_append, Control.ticketNames, closeFrame, List.nil_append,
      List.count_append, List.count_cons] at beforeCount ⊢
    omega
  · apply List.nodup_iff_count.mpr
    intro handlerId
    have beforeCount := List.nodup_iff_count.mp h.2 handlerId
    simp only [activations_append, Control.activations, plan_control_activations,
      closeFrame, Frame.activation, List.nil_append, List.count_append] at beforeCount ⊢
    omega

@[simp] theorem plan_control_shaped (plan : List CloseItem) : (planControl plan).Shaped := by
  induction plan with
  | nil => trivial
  | cons item rest ih =>
      cases item <;> simp_all [planControl, Control.Shaped, CloseItem.frame, Frame.Shape]

@[simp] theorem plan_control_delimitedLives (plan : List CloseItem) :
    (planControl plan).DelimitedLives := by
  induction plan with
  | nil => trivial
  | cons item rest ih => exact ih

theorem discard_preserves_shape
    (h : (front.append (.live k q a cap tail)).Shaped) :
    ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))).Shaped := by
  simp only [shaped_append, Control.Shaped] at h
  simpa [Control.Shaped, closeFrame, Frame.Shape] using And.intro h.1 h.2.2

theorem discard_preserves_delimiters
    (h : (front.append (.live k q a cap tail)).DelimitedLives) :
    ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))).DelimitedLives := by
  simp only [delimitedLives_append, Control.DelimitedLives] at h
  simpa [Control.DelimitedLives] using And.intro h.1 h.2.2.2

structure WellFormed (c : Control) (input answer : Ty) (ambient : List Nat) : Prop where
  ports : Fits c input answer
  support : Supported c ambient
  unique : Unique c
  names : DistinctNames c
  shape : c.Shaped
  delimiters : c.DelimitedLives
  external : ∀ resource, resource ∈ ambient → Owner.resource resource ∉ c.owners

/-- Preservation of all fields of WellFormed at source capture.
    The executing operand has its own explicit outside-support premise below. -/
theorem capture_wellFormed (selection : SourceCut i whole cap tail)
    (valid : WellFormed whole q r ambient) (fresh : k ∉ whole.ticketNames) :
    ∃ a, WellFormed (.live k q a cap tail) a r ambient := by
  have cut := sourceCut_is_cut selection
  obtain ⟨a, hc, ht⟩ := capture_type_decomposition cut valid.ports
  refine ⟨a, ⟨.live k q a r cap tail hc ht,
    capture_preserves_support cut valid.support,
    capture_preserves_unique cut valid.unique ?_,
    capture_preserves_names cut valid.names fresh,
    capture_preserves_shape cut valid.shape,
    capture_preserves_delimiters selection valid.delimiters, ?_⟩⟩
  · exact fun owner => fresh (ticket_owner_has_name owner)
  · intro resource ha
    rw [capture_owner_accounting cut]
    simpa using valid.external resource ha

theorem resume_wellFormed
    (valid : WellFormed (front.append (.live k q a cap tail)) a r ambient) :
    WellFormed (cap.append (front.append (.spent k a tail))) q r ambient := by
  refine ⟨resume_full_type_recomposition valid.ports,
   resume_preserves_support valid.support,
   resume_preserves_unique valid.unique,
   resume_preserves_names valid.names,
   resume_preserves_shape valid.shape,
   resume_preserves_delimiters valid.delimiters, ?_⟩
  intro resource ha live
  apply valid.external resource ha
  exact (resume_owner_accounting (k := k) (q := q) (a := a)
    front cap tail).mem_iff.mpr (List.mem_cons_of_mem _ live)

theorem discard_wellFormed
    (valid : WellFormed (front.append (.live k q a cap tail)) .unit answer ambient)
    (admitted : Discardable cap (front.append (.spent k a tail)) plan)
    (fresh : Owner.close closeId ∉ (front.append (.live k q a cap tail)).owners) :
    WellFormed ((planControl plan).append (.push (closeFrame closeId)
      (front.append (.spent k a tail)))) .unit answer ambient := by
  have closing : Closes cap (front.append (.spent k a tail))
      (front.append (.spent k a tail)) plan := by
    cases admitted with
    | checked closing uses => exact closing
  have flow := Flow.discard k closeId q a front cap tail plan
    (closes_constructs_raw_plan closing)
  have freshOwners : ((front.append (.live k q a cap tail)).owners ++ [Owner.close closeId]).Nodup :=
    List.perm_append_comm.nodup_iff.mpr (List.nodup_cons.mpr ⟨fresh, valid.unique⟩)
  refine ⟨discard_type_recomposition valid.ports,
    discard_control_preserves_support valid.support admitted,
    (List.nodup_append.mp ((flow_accounting flow).nodup_iff.mp freshOwners)).1,
    discard_preserves_names valid.names closing,
    discard_preserves_shape valid.shape,
    discard_preserves_delimiters valid.delimiters, ?_⟩
  intro resource outside inside
  apply valid.external resource outside
  have before := (flow_accounting flow).mem_iff.mpr (List.mem_append_left _ inside)
  simpa using before

/-- The payload annotation is checked in the outside scope, not the pre-cut scope.
    Its sound extraction from values and metadata is a separate expression theorem. -/
inductive CaptureAdmission (i : Instance) (whole cap tail : Control)
    (payloadAccess ambient : List Nat) : Prop where
  | checked (selection : SourceCut i whole cap tail)
      (payload : payloadAccess ⊆ tail.visible ++ ambient) :
      CaptureAdmission i whole cap tail payloadAccess ambient

theorem admitted_capture_payload_available
    (h : CaptureAdmission i whole cap tail payloadAccess ambient) :
    payloadAccess ⊆ (Control.live k q a cap tail).visible ++ ambient := by
  cases h with
  | checked _ payload => exact payload

theorem visible_is_owned {c : Control} (h : resource ∈ c.visible) :
    Owner.resource resource ∈ c.owners := by
  induction c with
  | nil => simp [Control.visible] at h
  | push f rest ih =>
      cases hk : f.kind <;>
        simp_all [Control.visible, Frame.visible, Control.owners, Frame.owners] <;> grind
  | live k q a cap rest ihCap ihRest =>
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest h))
  | spent k a rest ih => exact ih h

theorem captured_private_access_cannot_cross
    (admission : CaptureAdmission i whole cap tail payloadAccess ambient)
    (valid : WellFormed whole q r ambient)
    (privateOwner : Owner.resource resource ∈ cap.owners) :
    resource ∉ payloadAccess := by
  cases admission with
  | checked selection payload =>
      intro hp
      have decomposition := cut_decompose (sourceCut_is_cut selection)
      have noDup : (cap.owners ++ tail.owners).Nodup := by
        simpa [decomposition, Unique] using valid.unique
      rcases List.mem_append.mp (payload hp) with outside | external
      · exact (List.nodup_append.mp noDup).2.2 _ privateOwner _
          (visible_is_owned outside) rfl
      · apply valid.external resource external
        rw [decomposition, owners_append]
        exact List.mem_append_left _ privateOwner

namespace Examples

def unitFrame (kind : Kind) (access pending : List Nat := [])
    (requests : List Instance := []) : Frame :=
  ⟨kind, .unit, .unit, access, pending, requests⟩

def cell4 : Frame := unitFrame (.resource 4)
def cleanup7 : Frame := unitFrame (.armed 7) [4] [] [.cell 4]
def override9 : Frame := unitFrame (.handler (.cell 4) 9)

theorem cleanup_uses_still_enclosing_cell :
    Closes (.push cleanup7 (.push cell4 .nil)) .nil .nil
      [.invoke 7 [4] [.cell 4], .release 4] := by
  apply Closes.armed cleanup7 7 (.push cell4 .nil) .nil .nil [.release 4] rfl
  · rfl
  · simp [cleanup7, unitFrame, planControl, CloseItem.frame,
      Control.visible, Frame.visible]
  · apply SameRequests.cons (.cell 4) [] (.builtin 4)
    · rfl
    · rfl
    · exact .nil
  · exact .resource cell4 4 .nil .nil .nil [] rfl (.nil .nil .nil)

theorem removed_override_cannot_fall_back :
    ¬ Closes (.push cleanup7 (.push override9 (.push cell4 .nil)))
      .nil .nil plan := by
  intro h
  cases h with
  | bind _ _ _ _ _ bad _ => cases bad
  | handler _ _ _ _ _ _ _ bad _ => cases bad
  | resource _ _ _ _ _ _ bad _ => cases bad
  | armed _ a _ _ _ _ hk _ _ requests next =>
      have built := closes_constructs_raw_plan next
      simp [rawPlan, override9, cell4, unitFrame] at built
      cases built
      cases requests with
      | cons _ _ target before after _ =>
          simp [override9, cell4, unitFrame, Control.resolve,
            Frame.resolve, Control.append] at before after
          cases before
          cases after

theorem running_cleanup_cannot_be_abandoned :
    ¬ Closes (.push (unitFrame (.running 7)) .nil) original surviving plan := by
  intro h
  have hp := close_excludes_protected h
  simp [Control.protected, unitFrame] at hp

theorem outside_running_cleanup_does_not_block_empty_discard :
    Discardable .nil (.push (unitFrame (.running 7)) .nil) [] :=
  .checked (.nil _ _) .nil

/-- The resource bag is empty in the lost suffix; it still owes an outside resume. -/
theorem pending_outside_resume_blocks_discard :
    ¬ Discardable (.push (unitFrame .bind [] [3]) .nil) outer plan := by
  intro h
  have lost := discard_preserves_outside_consumption (k := 3) h
    (by simp [Control.liveTickets])
  simp [Control.pending, unitFrame] at lost

theorem builtin_blocks_source_capture :
    ¬ SourceCut (.cell 4) (.push cell4 (.push override9 .nil)) cap tail := by
  intro h
  cases h with
  | hit _ _ _ bad => cases bad
  | push _ _ _ _ miss _ => exact miss rfl

theorem saved_resource_is_not_accessible_to_clause :
    ¬ ([4] ⊆ (Control.live 0 .unit .unit (.push cell4 .nil) .nil).visible) := by
  simp [Control.visible]

theorem duplicate_handler_activations_are_invalid :
    ¬ DistinctNames (.push override9 (.push override9 .nil)) := by
  simp [DistinctNames, Control.activations, Frame.activation, override9, unitFrame]

theorem live_and_spent_ticket_identity_cannot_alias :
    ¬ DistinctNames (.live 3 .unit .unit .nil (.spent 3 .unit .nil)) := by
  simp [DistinctNames, Control.ticketNames]

theorem raw_plan_can_lose_pending_consumption :
    rawPlan (.push (unitFrame .bind [] [3]) .nil) = some [] := rfl

def ownHandler : Frame := unitFrame (.handler (.user 1 []) 8)

def nestedCleanup : Control := .live 3 .unit .unit
  (.push cleanup7 (.push ownHandler .nil)) (.push cell4 .nil)

theorem nested_cleanup_retains_outer_cell :
    Closes nestedCleanup .nil .nil [.invoke 7 [4] [.cell 4], .retire 3, .release 4] := by
  apply Closes.live 3 .unit .unit _ _ .nil .nil
    [.invoke 7 [4] [.cell 4]] [.release 4]
  · apply Closes.armed cleanup7 7 (.push ownHandler .nil) _ _ [] rfl rfl
    · simp [cleanup7, unitFrame, planControl, CloseItem.frame, Control.visible, Frame.visible]
    · exact .cons (.cell 4) [] (.builtin 4) rfl rfl .nil
    · exact .handler ownHandler (.user 1 []) 8 .nil _ _ [] rfl (.nil _ _)
  · exact .resource cell4 4 .nil .nil .nil [] rfl (.nil _ _)

theorem nested_cleanup_plan_has_support_and_same_interpretation :
    Supported (planControl [.invoke 7 [4] [.cell 4], .retire 3, .release 4]) [] ∧
    ∃ context, CleanupOrigin nestedCleanup .nil 7 [4] [.cell 4] context ∧
      SameRequests context (planControl [.retire 3, .release 4]) [.cell 4] := by
  constructor
  · exact close_plan_preserves_support nested_cleanup_retains_outer_cell (.nil [])
  · exact close_plan_preserves_interpretation nested_cleanup_retains_outer_cell
      (.here 7 [4] [.cell 4] [.retire 3, .release 4])

def ticketUsingCleanup : Control := .live 3 .unit .unit
  (.push (unitFrame (.armed 7) [] [3]) (.push ownHandler .nil)) .nil

/-- Internal ownership alone cannot justify ticket uses in a cleanup closure. -/
theorem internally_owned_ticket_use_in_cleanup_is_rejected :
    InternalUses ticketUsingCleanup.liveTickets ticketUsingCleanup.pending ∧
      ¬ Discardable ticketUsingCleanup outer plan := by
  constructor
  · exact .cons 3 [] (by simp [ticketUsingCleanup, Control.liveTickets]) .nil
  · intro h
    cases h with
    | checked closing uses =>
        have closed := close_actions_ticket_closed closing
        simp [ticketUsingCleanup, unitFrame, Control.ActionTicketsClosed] at closed

def dormantCell : Control := .live 3 .unit .unit
  (.push cell4 (.push ownHandler .nil)) .nil

def residualCleanup : Frame := unitFrame (.armed 7) [] [] [.cell 4]

def outsideOverride : Control := .push override9 .nil

/-- The old builtin projection misses an interpreter exposed by materialization.
    This is an annotated-control counterexample, not an accepted source program. -/
theorem projection_misses_materialized_shadow :
    (dormantCell.append outsideOverride).resolve (.cell 4) =
      some (.source 9) ∧
    ((planControl [.release 4, .retire 3]).append outsideOverride).resolve
      (.cell 4) = some (.builtin 4) := ⟨rfl, rfl⟩

theorem materialized_shadow_blocks_close :
    ¬ Closes (.push residualCleanup dormantCell) outsideOverride outsideOverride plan := by
  intro h
  cases h with
  | bind _ _ _ _ _ bad _ => cases bad
  | handler _ _ _ _ _ _ _ bad _ => cases bad
  | resource _ _ _ _ _ _ bad _ => cases bad
  | armed _ a _ _ _ _ hk _ _ requests next =>
      have built := closes_constructs_raw_plan next
      simp [rawPlan, dormantCell, cell4, ownHandler, unitFrame] at built
      cases built
      cases requests with
      | cons _ _ target before after _ =>
          change some (.source 9) = some target at before
          change some (.builtin 4) = some target at after
          cases before
          cases after

def s0 : State := ⟨.nil, [], []⟩
def s1 : State := ⟨.push ownHandler .nil, [], []⟩
def s2 : State := ⟨.push cell4 s1.control, [.resource 4], []⟩
def s3 : State := ⟨.live 3 .unit .unit s2.control .nil,
  [.resource 4, .ticket 3], []⟩
def s4 : State := ⟨s2.control.append (.spent 3 .unit .nil),
  [.resource 4, .ticket 3], [.ticket 3]⟩
def s5 : State := ⟨.push ownHandler (.spent 3 .unit .nil),
  [.resource 4, .ticket 3], [.resource 4, .ticket 3]⟩
def s6 : State := ⟨.spent 3 .unit .nil,
  [.resource 4, .ticket 3], [.resource 4, .ticket 3]⟩
def s7 : State := ⟨.nil,
  [.resource 4, .ticket 3], [.resource 4, .ticket 3]⟩

/-- A resource-bearing state inhabits the structural premises of preservation. -/
theorem resource_handler_wellFormed : WellFormed s2.control .unit .unit [] := by
  refine ⟨.push cell4 s1.control .unit
    (.push ownHandler .nil .unit (.nil .unit)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .push cell4 s1.control []
      (.push ownHandler .nil [] (.nil []) (by simp [ownHandler, unitFrame]))
      (by simp [cell4, unitFrame])
  · simp [Unique, s2, s1, cell4, ownHandler, unitFrame, Control.owners, Frame.owners]
  · constructor <;> decide
  · simp [s2, s1, cell4, ownHandler, unitFrame, Control.Shaped, Frame.Shape]
  · trivial
  · simp

/-- Capture and resume preservation have a nonempty owned instance. -/
theorem capture_and_resume_are_inhabited :
    ∃ a, WellFormed (.live 3 .unit a s2.control .nil) a .unit [] ∧
      WellFormed (s2.control.append (.spent 3 a .nil)) .unit .unit [] := by
  have select : SourceCut (.user 1 []) s2.control s2.control .nil :=
    .push cell4 s1.control s1.control .nil (by decide)
      (.hit ownHandler 8 .nil rfl)
  obtain ⟨a, valid⟩ := capture_wellFormed select resource_handler_wellFormed
    (k := 3) (by decide)
  exact ⟨a, valid, resume_wellFormed (front := .nil) valid⟩

theorem captured_resource_wellFormed : WellFormed s3.control .unit .unit [] := by
  obtain ⟨answer, valid, resumed⟩ := capture_and_resume_are_inhabited
  have answerUnit : answer = .unit := by
    cases valid.ports with
    | live _ _ _ _ _ _ saved outside =>
        cases outside
        rfl
  subst answer
  exact valid

theorem resource_discard_is_admitted :
    Discardable s2.control (.spent 3 .unit .nil) [.release 4] :=
  .checked (.resource cell4 4 s1.control _ _ [] rfl
    (.handler ownHandler (.user 1 []) 8 .nil _ _ [] rfl (.nil _ _))) .nil

theorem resource_discard_wellFormed :
    WellFormed ((planControl [.release 4]).append
      (.push (closeFrame 10) (.spent 3 .unit .nil))) .unit .unit [] :=
  discard_wellFormed (front := .nil) captured_resource_wellFormed
    resource_discard_is_admitted (by decide)

theorem capture_resume_release_execution : Steps s0 s7 := by
  have enterHandler : Step s0 s1 :=
    .event s0 s1.control [] [] (.enter ownHandler .nil trivial) (by decide)
  have enterCell : Step s1 s2 :=
    .event s1 s2.control [.resource 4] [] (.enter cell4 s1.control trivial) (by decide)
  have select : SourceCut (.user 1 []) s2.control s2.control .nil :=
    .push cell4 s1.control s1.control .nil (by decide)
      (.hit ownHandler 8 .nil rfl)
  have capture : Step s2 s3 :=
    .event s2 s3.control [.ticket 3] []
      (.capture (.user 1 []) 3 .unit .unit s2.control s2.control .nil select) (by decide)
  have resume : Step s3 s4 :=
    .event s3 s4.control [] [.ticket 3]
      (.resume 3 .unit .unit .nil s2.control .nil) (by decide)
  have release : Step s4 s5 :=
    .event s4 s5.control [] [.resource 4]
      (.release cell4 4 s5.control rfl) (by decide)
  have leaveHandler : Step s5 s6 :=
    .event s5 s6.control [] [] (.leavePlain ownHandler s6.control rfl) (by decide)
  have leaveClause : Step s6 s7 :=
    .event s6 s7.control [] [] (.leaveClause 3 .unit .nil) (by decide)
  exact .next _ _ _ enterHandler (.next _ _ _ enterCell
    (.next _ _ _ capture (.next _ _ _ resume (.next _ _ _ release
      (.next _ _ _ leaveHandler (.next _ _ _ leaveClause (.refl s7)))))))

theorem completed_execution_has_no_duplicate_release : s7.completed.Nodup := by
  apply ledger_no_double_completion
  exact steps_preserve_ledger capture_resume_release_execution
    ⟨.refl [], by decide⟩

end Examples

end Ash.OneShot

#print axioms Ash.OneShot.capture_type_decomposition
#print axioms Ash.OneShot.resume_type_recomposition
#print axioms Ash.OneShot.capture_preserves_unique
#print axioms Ash.OneShot.resume_preserves_unique
#print axioms Ash.OneShot.resume_removes_ticket
#print axioms Ash.OneShot.capture_preserves_support
#print axioms Ash.OneShot.resume_preserves_support
#print axioms Ash.OneShot.discard_preserves_outside_consumption
#print axioms Ash.OneShot.discard_preserves_protected
#print axioms Ash.OneShot.discard_accounts_for_every_owner
#print axioms Ash.OneShot.close_plan_checks
#print axioms Ash.OneShot.close_actions_ticket_closed
#print axioms Ash.OneShot.close_plan_preserves_support
#print axioms Ash.OneShot.close_plan_preserves_interpretation
#print axioms Ash.OneShot.discard_control_preserves_support
#print axioms Ash.OneShot.discard_invocation_preserves_interpretation
#print axioms Ash.OneShot.admitted_discard_joint_preservation
#print axioms Ash.OneShot.Examples.materialized_shadow_blocks_close
#print axioms Ash.OneShot.Examples.nested_cleanup_plan_has_support_and_same_interpretation
#print axioms Ash.OneShot.Examples.internally_owned_ticket_use_in_cleanup_is_rejected
#print axioms Ash.OneShot.capture_preserves_names
#print axioms Ash.OneShot.resume_preserves_names
#print axioms Ash.OneShot.capture_preserves_delimiters
#print axioms Ash.OneShot.resume_preserves_delimiters
#print axioms Ash.OneShot.source_provider_support
#print axioms Ash.OneShot.capture_wellFormed
#print axioms Ash.OneShot.resume_wellFormed
#print axioms Ash.OneShot.discard_wellFormed
#print axioms Ash.OneShot.Examples.resource_discard_wellFormed
#print axioms Ash.OneShot.step_preserves_ledger
#print axioms Ash.OneShot.steps_preserve_ledger
#print axioms Ash.OneShot.ledger_no_double_completion
#print axioms Ash.OneShot.ledger_no_live_completed_alias
#print axioms Ash.OneShot.Examples.capture_and_resume_are_inhabited
#print axioms Ash.OneShot.Examples.capture_resume_release_execution
#print axioms Ash.OneShot.Examples.completed_execution_has_no_duplicate_release
