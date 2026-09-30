import DeclaredConnectedExecution

/-! One structural transport proof covers world extension, coherent contract
extension, independent action extension and handler-table agreement. Existing
source and port transports supply the frame components.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes

theorem Frame.transport
    (frame : Frame operations policy contracts tables world entry input output demand requirements incoming outgoing)
    (contractsExtend : contracts.Extends nextContracts)
    (larger : world ⊆ nextWorld)
    (agree : ∀ handler, handler.activation ∈ entry.erase.activation → tables handler = nextTables handler) :
    Frame operations policy nextContracts nextTables nextWorld entry input output demand requirements incoming outgoing := by
  have ports := Owners.port_contracts_extension contractsExtend
  cases frame with
  | plain context scope inputAnnotation outputAnnotation =>
      exact .plain (DeclaredSourceFrames.context_world_weaken
        (DeclaredSourceFrames.context_extension context contractsExtend) larger)
        (ScopedPorts.effect_scope_extension scope ports) inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact .handler (ScopedPorts.effect_scope_known_extension scope ports) annotation
        (ScopedPorts.clauses_world_weaken clauses larger) coverage unique
        (agree _ List.mem_cons_self ▸ DeclaredSourceTransport.declarations_world_weaken
          (DeclaredSourceTransport.declarations_extension declarations contractsExtend) larger)
        capabilities (agree _ List.mem_cons_self ▸ modes)
  | retained kind source interface =>
      exact .retained kind
        (DeclaredSourceFrames.frame_tables_congr (DeclaredSourceFrames.frame_world_weaken
          (DeclaredSourceFrames.frame_extension source contractsExtend) larger) agree)
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)

theorem Segment.transport
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (contractsExtend : contracts.Extends nextContracts)
    (actionsExtend : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler) :
    Segment operations policy nextContracts nextTables nextActions nextWorld
      stack input output demand requirements records incoming outgoing := by
  have ports := Owners.port_contracts_extension contractsExtend
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      have next := fun handler member => agree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr next
      have changed := head.transport contractsExtend larger
        (fun handler member => agree handler (List.mem_append_left _ member))
      simpa only [same] using Segment.push changed (ih next) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close bound ihSaved ihTail =>
      have inside := fun handler member => agree handler (List.mem_append_left _ member)
      have outside := fun handler member => agree handler (List.mem_append_right _ member)
      exact .live (contractsExtend _ _ known) (actionsExtend _ _ actionKnown)
        inputAnnotation answerAnnotation (ScopedPorts.effect_scope_known_extension scope ports) held
        (DeclaredSourceFrames.segment_tables_congr (DeclaredSourceFrames.segment_world_weaken
          (DeclaredSourceFrames.segment_extension saved contractsExtend) larger) inside)
        (fun permitted => ihSaved permitted inside) (ihTail outside) resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (contractsExtend _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports)
        (ih agree) bound

theorem Segment.input_weaken
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (smaller : nextIncoming ⊆ incoming) :
    Segment operations policy contracts tables actions world stack input output demand requirements records nextIncoming outgoing := by
  cases segment with
  | nil bound => exact .nil (smaller.trans bound)
  | push head tail bound => exact .push head tail (smaller.trans bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close (smaller.trans bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (smaller.trans bound)

theorem Segment.world_weaken
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (larger : world ⊆ nextWorld) :
    Segment operations policy contracts tables actions nextWorld stack input output demand requirements records incoming outgoing :=
  segment.transport (fun _ _ known => known) (fun _ _ known => known) larger (fun _ _ => rfl)

theorem Segment.action_extension
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (extension : Syntax.UsageExtension actions nextActions) :
    Segment operations policy contracts tables nextActions world stack input output demand requirements records incoming outgoing :=
  segment.transport (fun _ _ known => known) extension (List.Subset.refl _) (fun _ _ => rfl)

theorem Segment.contract_extension
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (extension : contracts.Extends nextContracts) :
    Segment operations policy nextContracts tables actions world stack input output demand requirements records incoming outgoing :=
  segment.transport extension (fun _ _ known => known) (List.Subset.refl _) (fun _ _ => rfl)

theorem Segment.tables_congr
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler) :
    Segment operations policy contracts nextTables actions world stack input output demand requirements records incoming outgoing :=
  segment.transport (fun _ _ known => known) (fun _ _ known => known) (List.Subset.refl _) agree

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.Frame.transport
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.transport
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.input_weaken
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.world_weaken
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.action_extension
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.contract_extension
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.tables_congr
