import CoreCaptureEntry
import CoreClosing

/-! Residual resource-only closing projection. Ordinary lexical frames and
nested owner scopes remain explicit even when Core has projected them away.
Retirement markers reuse the live capture’s static owner header. Dynamic ticket
provenance comes from initial construction and its subsequent transitions.
Callbacks are a later boundary; no armed/running cursor constructor is supplied. -/
namespace Ash.OneShot.CoreResourceProjection
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictFrames
  CoreEffectFrames CoreRequestFrames CoreCaptureEntry CoreCleanupFrames CoreResumeFrames

/-- Exact later-first completion ledger, including resources and retirement. -/
def completionOwners : Stack → List Owner
  | .nil => []
  | .push (.cell identity _ _ _) rest => completionOwners rest ++ [.resource identity]
  | .push (.retiring ticket) rest => completionOwners rest ++ [.ticket ticket]
  | .push _ rest => completionOwners rest
  | .live ticket _ _ saved _ rest => completionOwners rest ++ [.ticket ticket] ++ completionOwners saved
  | .spent _ _ _ rest => completionOwners rest

def weight : Stack → Nat
  | .nil => 0
  | .push _ rest => weight rest + 1
  | .live _ _ _ saved _ rest => weight saved + weight rest + 2
  | .spent _ _ _ rest => weight rest + 1

theorem weight_append (stack rest : Stack) : weight (stack.append rest) = weight stack + weight rest := by
  induction stack <;> simp_all [Stack.append,weight] <;> omega

/-- Physical resource frames are exact. Target-only retirement retains the
static header; that header does not authenticate a dynamic ticket or freshness.
Saved captures are recursively represented, never opaque. -/
inductive Cursor (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | nil : Cursor graph heap [] .nil
  | plain (frame : PushCarrier graph owners heap core (.plain plain))
      (next : Cursor graph heap physical target) :
      Cursor graph heap physical (.push (.plain plain) target)
  | handler (frame : BoundaryRel graph owners heap core (.handler data))
      (next : Cursor graph heap physical target) :
      Cursor graph heap physical (.push (.handler data) target)
  | cell (frame : BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload scope answer))
      (next : Cursor graph heap physical target) :
      Cursor graph heap (.resourceBoundary site key payload::physical) (.push (.cell key payload scope answer) target)
  | live (header : OwnerHeader graph owners heap handler owner occurrence data)
      (saved : Cursor graph heap savedPhysical savedTarget)
      (outside : Cursor graph heap outsidePhysical outsideTarget) :
      Cursor graph heap (savedPhysical ++ outsidePhysical)
        (.live ticket result data.answer savedTarget data.scope outsideTarget)
  | spent (header : OwnerHeader graph owners heap handler owner occurrence data)
      (next : Cursor graph heap physical target) :
      Cursor graph heap physical (.spent ticket data.answer data.scope target)
  | retiring (header : OwnerHeader graph owners heap handler owner occurrence data)
      (next : Cursor graph heap physical target) :
      Cursor graph heap physical (.push (.retiring ticket) target)

theorem Cursor.append (first : Cursor graph heap before target)
    (second : Cursor graph heap after tail) : Cursor graph heap (before++after) (target.append tail) := by
  induction first with
  | nil => exact second
  | plain frame next ih => exact .plain frame ih
  | handler frame next ih => exact .handler frame ih
  | cell frame next ih => exact .cell frame ih
  | live header saved outside ihSaved ihOutside =>
      simpa [Stack.append,List.append_assoc] using Cursor.live header saved ihOutside
  | spent header next ih => exact .spent header ih
  | retiring header next ih => exact .retiring header ih

private theorem push_weaken (frame : PushCarrier graph owners heap core target)
    (extension : HeapExtends heap larger) : PushCarrier graph owners larger core target := by
  cases frame with
  | ordinary frame => exact .ordinary (frame.heap_weaken extension)
  | initializer frame => exact .initializer (frame.heap_weaken extension)
  | request frame => exact .request (frame.heap_weaken extension)
  | resume frame => exact .resume (frame.heap_weaken extension)
  | cleanup frame => exact .cleanup (frame.heap_weaken extension)
  | boundary frame => exact .boundary (frame.heap_weaken extension)

theorem Cursor.heap_weaken (cursor : Cursor graph heap physical target)
    (extension : HeapExtends heap larger) : Cursor graph larger physical target := by
  induction cursor with
  | nil => exact .nil
  | plain frame next ih => exact .plain (push_weaken frame extension) ih
  | handler frame next ih => exact .handler (frame.heap_weaken extension) ih
  | cell frame next ih => exact .cell (frame.heap_weaken extension) ih
  | live header saved outside ihSaved ihOutside => exact .live (header.heap_weaken extension) ihSaved ihOutside
  | spent header next ih => exact .spent (header.heap_weaken extension) ih
  | retiring header next ih => exact .retiring (header.heap_weaken extension) ih

def ResourceOnly (frames : List CoreMachine.Frame) : Prop :=
  ∀ frame ∈ frames, ∃ site key payload, frame = .resourceBoundary site key payload

private theorem resource_tail (known : ResourceOnly (head::tail)) : ResourceOnly tail :=
  fun frame member => known frame (.tail _ member)

private theorem resource_append (known : ResourceOnly (left++right)) : ResourceOnly left ∧ ResourceOnly right :=
  ⟨fun frame member => known frame (List.mem_append_left _ member),
   fun frame member => known frame (List.mem_append_right _ member)⟩

private theorem plain_drop (frame : PlainFrameRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  change FrameRel graph owners heap core plain.context at frame
  generalize same : plain.context = context at frame
  cases frame <;> rfl

/-- Initial residual cursor comes from the same interpreted captured stack and
actual successful projection. Fuel and graph sites are not reconstructed. -/
theorem cursor_of_close (captured : PushedWithMaps graph heap maps target) :
    ∀ fuel closing consumed, CoreMachine.closeFuel fuel (framesOf maps) = .ok (closing,consumed) →
      ResourceOnly closing → Cursor graph heap closing target ∧
      consumed = (CoreClosing.consumed target.erase).map CoreMachine.Observation.nestedConsumed := by
  induction captured with
  | nil =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have same : closing = [] ∧ consumed = [] := by simpa [framesOf,CoreMachine.closeFuel] using projection.symm
          rcases same with ⟨rfl,rfl⟩; exact ⟨.nil,rfl⟩
  | cons frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,plain_drop frame] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
          exact ⟨.plain (.ordinary frame) cursor,order⟩
  | @initializer owners core plain maps target frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
          exact ⟨.plain (.initializer frame) cursor,order⟩
  | @request owners core plain maps target frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
          exact ⟨.plain (.request frame) cursor,order⟩
  | @resume owners core plain maps target frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
          exact ⟨.plain (.resume frame) cursor,order⟩
  | @boundary owners core effectFrame maps target frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame with
          | handler known kind translated header =>
              obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
              exact ⟨.handler (.handler known kind translated header) cursor,order⟩
          | @cell site node identity handle initializer body key payload scope answer known kind =>
              simp only [framesOf_cons,CoreMachine.closeFuel] at projection
              cases tail : CoreMachine.closeFuel fuel (framesOf maps) with
              | error error => simp [tail,Bind.bind,Except.bind] at projection
              | ok value =>
                  rcases value with ⟨rest,events⟩
                  have same : .resourceBoundary site key payload::rest = closing ∧ events = consumed := by
                    simpa [tail,Bind.bind,Except.bind,Pure.pure,Except.pure] using projection
                  rcases same with ⟨rfl,rfl⟩
                  obtain ⟨cursor,order⟩ := ih fuel rest events tail (resource_tail only)
                  exact ⟨.cell (.cell (owners := owners) known kind) cursor,order⟩
  | @cleanup owners core data maps target frame next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame
          rename_i site node callback action body environment parameter functionBody captured known kind shape delayed saved lookup value
          simp only [framesOf_cons,CoreMachine.closeFuel] at projection
          cases tail : CoreMachine.closeFuel fuel (framesOf maps) with
          | error error => simp [tail,Bind.bind,Except.bind] at projection
          | ok value =>
              rcases value with ⟨rest,events⟩
              have same : .cleanupBoundary action environment data.identity::rest = closing ∧ events = consumed := by
                simpa [tail,Bind.bind,Except.bind,Pure.pure,Except.pure] using projection
              obtain ⟨site,key,payload,impossible⟩ := only _ (same.1 ▸ List.mem_cons_self)
              cases impossible
  | spent header next ih =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection only
          exact ⟨.spent header cursor,order⟩
  | @live owners handler owner occurrence data capturedMaps capturedTarget outsideMaps outsideTarget ticket result header captured outside ihCaptured ihOutside =>
      intro fuel closing consumed projection only
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          simp only [framesOf_cons,CoreMachine.closeFuel] at projection
          cases child : CoreMachine.closeFuel fuel (framesOf capturedMaps) with
          | error error => simp [child,Bind.bind,Except.bind] at projection
          | ok value =>
              rcases value with ⟨savedClosing,savedConsumed⟩
              cases tail : CoreMachine.closeFuel fuel (framesOf outsideMaps) with
              | error error => simp [child,tail,Bind.bind,Except.bind] at projection
              | ok value =>
                  rcases value with ⟨tailClosing,tailConsumed⟩
                  have same : savedClosing++tailClosing = closing ∧
                    CoreMachine.Observation.nestedConsumed ticket::savedConsumed++tailConsumed = consumed := by
                    simpa [child,tail,Bind.bind,Except.bind,Pure.pure,Except.pure] using projection
                  have parts := resource_append (same.1 ▸ only)
                  obtain ⟨savedCursor,savedOrder⟩ := ihCaptured fuel _ _ child parts.1
                  obtain ⟨tailCursor,tailOrder⟩ := ihOutside fuel _ _ tail parts.2
                  refine ⟨same.1 ▸ Cursor.live header savedCursor tailCursor,?_⟩
                  rw [←same.2,savedOrder,tailOrder]
                  simp [CoreClosing.consumed,Stack.erase,List.map_append]

theorem Cursor.resource_only (cursor : Cursor graph heap physical target) : ResourceOnly physical := by
  induction cursor with
  | nil => intro frame member; cases member
  | plain frame next ih | handler frame next ih | spent header next ih | retiring header next ih => exact ih
  | cell frame next ih =>
      intro current member
      cases member with
      | head => exact ⟨_,_,_,rfl⟩
      | tail _ member => exact ih current member
  | live header saved outside ihSaved ihOutside =>
      intro frame member
      rcases List.mem_append.mp member with member | member
      · exact ihSaved frame member
      · exact ihOutside frame member

/-- Reuse the existing structural close traversal/accounting interfaces. -/
theorem pushed_ready (related : PushedWithMaps graph heap maps target) : CoreClosing.Ready target.erase := by
  induction related with
  | nil => exact .nil
  | cons frame next ih | initializer frame next ih | request frame next ih | resume frame next ih =>
      exact .push (by trivial) ih
  | boundary frame next ih => cases frame <;> exact .push (by trivial) ih
  | cleanup frame next ih => exact .push (by trivial) ih
  | live header captured outside ihCaptured ihOutside => exact .live ihCaptured ihOutside
  | spent header next ih => exact .spent ih

def resourceItems (physical : List CoreMachine.Frame) : List CloseItem :=
  physical.filterMap fun frame => match frame with
    | .resourceBoundary _ key _ => some (.release key)
    | _ => none

theorem Cursor.retained (cursor : Cursor graph heap physical target) :
    CoreClosing.retained target.erase = resourceItems physical := by
  induction cursor with
  | nil => rfl
  | plain frame next ih => simpa [Stack.erase,ExecFrame.erase,PlainData.erase,CoreClosing.retained,CoreClosing.keep] using ih
  | handler frame next ih => simpa [Stack.erase,ExecFrame.erase,HandlerData.erase,CoreClosing.retained,CoreClosing.keep] using ih
  | cell frame next ih => simpa [Stack.erase,ExecFrame.erase,CoreClosing.retained,CoreClosing.keep,resourceItems] using ih
  | live header saved outside ihSaved ihOutside => simp [Stack.erase,CoreClosing.retained,ihSaved,ihOutside,resourceItems,List.filterMap_append]
  | spent header next ih => exact ih
  | retiring header next ih => simpa [Stack.erase,ExecFrame.erase,CloseItem.frame,CoreClosing.retained,CoreClosing.keep] using ih

/-- The existing PopAppend output agrees with the actual projected resource
frames, rather than being used as a substitute evaluator. -/
theorem projected_traversal
    (captured : PushedWithMaps graph heap maps target)
    (projection : CoreMachine.closeFuel fuel (framesOf maps) = .ok (closing,consumed))
    (only : ResourceOnly closing) :
    CoreClosing.PopAppend (CoreClosing.vector target.erase).reverse
      (resourceItems closing) (CoreClosing.consumed target.erase) ∧
    consumed = (CoreClosing.consumed target.erase).map CoreMachine.Observation.nestedConsumed := by
  obtain ⟨cursor,order⟩ := cursor_of_close captured fuel closing consumed projection only
  have traversal := CoreClosing.ready_traversal (pushed_ready captured) CoreClosing.PopAppend.nil
  exact ⟨by simpa [cursor.retained] using traversal,order⟩

#print axioms projected_traversal
#print axioms Cursor.resource_only
#print axioms pushed_ready
#print axioms Cursor.retained
#print axioms Cursor.append
#print axioms Cursor.heap_weaken
#print axioms cursor_of_close
end Ash.OneShot.CoreResourceProjection
