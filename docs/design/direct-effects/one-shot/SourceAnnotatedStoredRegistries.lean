import SourceAnnotatedStoredTyping
import SourceConsumingBoundInstallation

/-! Registering a fresh handler preserves the joint source/packet judgment at
all existing activations. Packet transport and source transport retain the same
recorded plans, including handlers inside dormant saved continuations. -/
namespace Ash.OneShot.SourceConsumingStoredBounds

/-- Transport a declaration judgment without choosing a different plan. -/
theorem HandlerBounds.registries_congr_evidence
    {families nextFamilies : SourceDependencyCapture.Families}
    {declarationEvidence : SourcePlannedFrames.DeclarationEvidence}
    (packet : HandlerBounds families handler)
    (same : families handler.erase = nextFamilies handler.erase)
    (checked : declarationEvidence needed packet.plans) :
    declarationEvidence needed (packet.registries_congr same).plans := by
  rcases packet with ⟨plans, bounds, route⟩
  change declarationEvidence needed plans at checked
  simp only [HandlerBounds.registries_congr]
  generalize oldFamily : families handler.erase = first at *
  generalize newFamily : nextFamilies handler.erase = second at *
  cases same
  exact checked

end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourceAnnotatedStoredTyping
open ScopedExpressions ScopedExecution
open SourceConsumingStoredBounds (HandlerBounds FrameBounds StackBounds)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

omit admission certification in
theorem PacketSource.registries_congr
    (source : PacketSource (entry := entry) operations policy contracts tables families required world evidence packet input output incoming outgoing)
    (tablesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → required handler = nextRequired handler) :
    PacketSource operations policy contracts nextTables nextFamilies nextRequired world evidence
      (FrameBounds.registries_congr (frame := entry) packet familiesAgree) input output incoming outgoing := by
  cases source with
  | @handler handler residual answer packet source checked =>
      have tableSame := tablesAgree handler.erase List.mem_cons_self
      have familySame := familiesAgree handler.erase List.mem_cons_self
      have requiredSame := requiredAgree handler.erase List.mem_cons_self
      have nextSource := packet.registries_congr_source familySame source
      rw [tableSame] at nextSource
      have nextChecked := packet.registries_congr_evidence familySame checked
      rw [requiredSame] at nextChecked
      exact .handler nextSource nextChecked
  | plain => exact .plain
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

theorem Frame.registries_congr
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing packet)
    (tablesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → required handler = nextRequired handler) :
    Frame (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing (packet.registries_congr familiesAgree) :=
  ⟨frame.forget.registries_congr tablesAgree familiesAgree requiredAgree,
    frame.packetSource.registries_congr tablesAgree familiesAgree requiredAgree⟩

theorem Segment.registries_congr
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing stored)
    (tablesAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → required handler = nextRequired handler) :
    Segment (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing (stored.registries_congr familiesAgree) := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      have nextTablesAgree := fun handler member => tablesAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr nextTablesAgree
      have changed := head.registries_congr
        (fun handler member => tablesAgree handler (List.mem_append_left _ member))
        (fun handler member => familiesAgree handler (List.mem_append_left _ member))
        (fun handler member => requiredAgree handler (List.mem_append_left _ member))
      simpa only [same, StackBounds.registries_congr] using Segment.push changed (ih nextTablesAgree
        (fun handler member => familiesAgree handler (List.mem_append_right _ member))
        (fun handler member => requiredAgree handler (List.mem_append_right _ member))) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held
        (ihSaved
          (fun handler member => tablesAgree handler (List.mem_append_left _ member))
          (fun handler member => familiesAgree handler (List.mem_append_left _ member))
          (fun handler member => requiredAgree handler (List.mem_append_left _ member))) savedBound
        (ihTail
          (fun handler member => tablesAgree handler (List.mem_append_right _ member))
          (fun handler member => familiesAgree handler (List.mem_append_right _ member))
          (fun handler member => requiredAgree handler (List.mem_append_right _ member))) resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent known annotation scope (ih tablesAgree familiesAgree requiredAgree) bound

end Ash.OneShot.SourceAnnotatedStoredTyping

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.PacketSource.registries_congr
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Frame.registries_congr
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.Segment.registries_congr

#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.registries_congr_evidence
