import OwnerUseContexts

/-! One ordered context retains actual clause tables and owner-use summaries.
Its projections reuse the established effect and ownership interpretations;
capability selection no longer needs a separately supplied table at a site. -/
namespace Ash.OneShot.OwnerOfferContexts
open ScopedExecution ProtectionContracts

structure Entry where
  layer : Layer
  uses : OwnerUseContexts.Uses
  deriving DecidableEq, Repr

abbrev Context := List Entry

def layers (context : Context) : ProtectionContracts.Context := context.map Entry.layer

def ownerEntry (entry : Entry) : OwnerUseContexts.Entry :=
  ⟨match entry.layer with
    | .barrier held => .barrier held
    | .builtin identity => .interpretation (.cell identity) (.builtin identity)
    | .handler effect activation _ => .interpretation effect (.source activation), entry.uses⟩

def owners (context : Context) : OwnerUseContexts.Context := context.map ownerEntry

def frameEntry (tables : CallableProtectionFrames.Tables) (frame : ExecFrame) : Entry :=
  ⟨match frame with
    | .handler data => .handler data.effectInst data.activation (tables data)
    | .cell identity _ _ _ => .builtin identity
    | _ => .barrier (ProtectionContexts.frameProtected frame.erase), ⟨[], frame.erase.pending⟩⟩

def ofStack (tables : CallableProtectionFrames.Tables) : Stack → Context
  | .nil => []
  | .push frame rest => frameEntry tables frame :: ofStack tables rest
  | .live owner _ _ saved _ rest =>
      ⟨.barrier (ProtectionContexts.protectedMode saved.erase),
        ⟨owner :: saved.erase.liveTickets, saved.erase.pending⟩⟩ :: ofStack tables rest
  | .spent _ _ _ rest => ofStack tables rest

theorem layers_stack (tables : CallableProtectionFrames.Tables) (stack : Stack) :
    layers (ofStack tables stack) = CallableProtectionFrames.contextOf tables stack := by
  induction stack with
  | nil => rfl
  | push frame rest ih => cases frame <;> simp_all [layers, ofStack, frameEntry,
      CallableProtectionFrames.contextOf, CallableProtectionFrames.pushContext]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simpa only [layers, ofStack, List.map_cons, CallableProtectionFrames.contextOf] using
        congrArg (List.cons (.barrier (ProtectionContexts.protectedMode saved.erase))) ihRest
  | spent owner answer scope rest ih => exact ih

theorem owners_stack (tables : CallableProtectionFrames.Tables) (stack : Stack) :
    owners (ofStack tables stack) = OwnerUseContexts.contextOf stack.erase := by
  induction stack with
  | nil => rfl
  | push frame rest ih => cases frame <;> simp_all [owners, ofStack, frameEntry, ownerEntry,
      Stack.erase, OwnerUseContexts.contextOf, OwnerUseContexts.frameEntry,
      ExecFrame.erase, PlainData.erase, HandlerData.erase, ActionData.erase, closeFrame, CloseItem.frame]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simpa only [owners, ofStack, List.map_cons, ownerEntry, Stack.erase, OwnerUseContexts.contextOf] using
        congrArg (List.cons (⟨.barrier (ProtectionContexts.protectedMode saved.erase),
          ⟨owner :: saved.erase.liveTickets, saved.erase.pending⟩⟩ : OwnerUseContexts.Entry)) ihRest
  | spent owner answer scope rest ih => exact ih

/-- Outer none means no selected offer. Some none denotes an exact builtin;
some (some contract) denotes the selected source operation's actual offer. -/
def selectedOffer (requested : Instance) (operation : Nat) :
    ProtectionContracts.Context → Option (Option ClauseContract)
  | [] => none
  | .barrier _ :: rest => selectedOffer requested operation rest
  | .builtin identity :: rest =>
      if requested = .cell identity then some none else selectedOffer requested operation rest
  | .handler effect _ table :: rest =>
      if requested = effect then (lookup operation table).map some else selectedOffer requested operation rest

def checkOwner (requested : Instance) (operation : Nat) (context : Context) : Bool :=
  match selectedOffer requested operation (layers context) with
  | none => false
  | some none => true
  | some (some offered) => OwnerUseContexts.check requested offered.dispose (owners context)

theorem offer_frame_miss (miss : frame.erase.target ≠ some requested) :
    selectedOffer requested operation (CallableProtectionFrames.pushContext tables frame rest) =
      selectedOffer requested operation rest := by
  cases frame <;> simp_all [selectedOffer, CallableProtectionFrames.pushContext, ExecFrame.erase,
    PlainData.erase, HandlerData.erase, ActionData.erase, closeFrame, CloseItem.frame, Frame.target, eq_comm]

theorem offer_cut (cut : HandlerCut requested whole capture tail handler) :
    selectedOffer requested operation (CallableProtectionFrames.contextOf tables whole) =
      (lookup operation (tables handler)).map some := by
  induction cut with
  | hit handler tail same => simp [CallableProtectionFrames.contextOf, CallableProtectionFrames.pushContext,
      selectedOffer, same]
  | push frame rest capture tail handler miss next ih =>
      simpa only [CallableProtectionFrames.contextOf, offer_frame_miss miss] using ih
  | live owner input answer saved scope rest capture tail handler next ih => exact ih
  | spent owner answer scope rest capture tail handler next ih => exact ih

/-- Reuse the ownership projection and exact-cut theorem. Table selection and
capture selection are now projections of the same ordered source context. -/
theorem check_cut (cut : HandlerCut requested whole capture tail handler) :
    checkOwner requested operation (ofStack tables whole) =
      CaptureOwnerChecks.checkSelected (tables handler) operation capture.erase := by
  simp only [checkOwner, layers_stack, offer_cut cut, CaptureOwnerChecks.checkSelected]
  cases found : lookup operation (tables handler) with
  | none => rfl
  | some offered =>
      simpa only [Option.map_some, owners_stack] using OwnerUseContexts.scoped_check (disposes := offered.dispose) cut

namespace Examples

def effect : Instance := .user 174 []
def waiting : Entry := ⟨.barrier false, ⟨[], [9]⟩⟩
def owner : Entry := ⟨.barrier false, ⟨[9], []⟩⟩
def resuming : Context := [waiting, ⟨.handler effect 0 [(0, ⟨false, some [], some []⟩)], ⟨[], []⟩⟩, owner]
def disposing : Context := [waiting, ⟨.handler effect 0 [(0, ⟨true, some [], none⟩)], ⟨[], []⟩⟩, owner]

theorem same_owner_projection : owners resuming = owners disposing := rfl

/-- The actual offer distinguishes contexts with identical ownership and
target projections. A separately chosen table must not decide this check. -/
theorem actual_offers_differ :
    checkOwner effect 0 resuming = true ∧ checkOwner effect 0 disposing = false := by decide

theorem missing_nearest_blocks_fallback :
    checkOwner effect 0 (⟨.handler effect 0 [], ⟨[], []⟩⟩ :: resuming) = false := by decide

end Examples
end Ash.OneShot.OwnerOfferContexts

#print axioms Ash.OneShot.OwnerOfferContexts.layers_stack
#print axioms Ash.OneShot.OwnerOfferContexts.owners_stack
#print axioms Ash.OneShot.OwnerOfferContexts.offer_frame_miss
#print axioms Ash.OneShot.OwnerOfferContexts.offer_cut
#print axioms Ash.OneShot.OwnerOfferContexts.check_cut
#print axioms Ash.OneShot.OwnerOfferContexts.Examples.same_owner_projection
#print axioms Ash.OneShot.OwnerOfferContexts.Examples.actual_offers_differ
#print axioms Ash.OneShot.OwnerOfferContexts.Examples.missing_nearest_blocks_fallback
