import CoreResourceProjection

/-! General retained closing projection, including exact delayed cleanup
boundaries. Saved captures remain recursive; no callback success, dispatch,
world validity or dynamic-ticket freshness is inferred. -/
namespace Ash.OneShot.CoreCleanupProjection
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictFrames
  CoreEffectFrames CoreRequestFrames CoreCaptureEntry CoreCleanupFrames CoreResumeFrames

/-- Both retained frame kinds carry their exact current source evidence.
Static headers alone do not authenticate dynamic tickets or freshness. -/
inductive RetainedCursor (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | nil : RetainedCursor graph heap [] .nil
  | plain (frame : PushCarrier graph owners heap core (.plain plain))
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap physical (.push (.plain plain) target)
  | handler (frame : BoundaryRel graph owners heap core (.handler data))
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap physical (.push (.handler data) target)
  | cell (frame : BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload scope answer))
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap (.resourceBoundary site key payload::physical) (.push (.cell key payload scope answer) target)
  | armed (frame : CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data)
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap (.cleanupBoundary action environment data.identity::physical) (.push (.armed data) target)
  | live (header : OwnerHeader graph owners heap handler owner occurrence data)
      (saved : RetainedCursor graph heap savedPhysical savedTarget)
      (outside : RetainedCursor graph heap outsidePhysical outsideTarget) :
      RetainedCursor graph heap (savedPhysical ++ outsidePhysical)
        (.live ticket result data.answer savedTarget data.scope outsideTarget)
  | spent (header : OwnerHeader graph owners heap handler owner occurrence data)
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap physical (.spent ticket data.answer data.scope target)
  | retiring (header : OwnerHeader graph owners heap handler owner occurrence data)
      (next : RetainedCursor graph heap physical target) :
      RetainedCursor graph heap physical (.push (.retiring ticket) target)

theorem RetainedCursor.append (first : RetainedCursor graph heap before target)
    (second : RetainedCursor graph heap after tail) : RetainedCursor graph heap (before++after) (target.append tail) := by
  induction first with
  | nil => exact second
  | plain frame next ih => exact .plain frame ih
  | handler frame next ih => exact .handler frame ih
  | cell frame next ih => exact .cell frame ih
  | armed frame next ih => exact .armed frame ih
  | live header saved outside ihSaved ihOutside =>
      simpa [Stack.append,List.append_assoc] using RetainedCursor.live header saved ihOutside
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

theorem RetainedCursor.heap_weaken (cursor : RetainedCursor graph heap physical target)
    (extension : HeapExtends heap larger) : RetainedCursor graph larger physical target := by
  induction cursor with
  | nil => exact .nil
  | plain frame next ih => exact .plain (push_weaken frame extension) ih
  | handler frame next ih => exact .handler (frame.heap_weaken extension) ih
  | cell frame next ih => exact .cell (frame.heap_weaken extension) ih
  | armed frame next ih => exact .armed (frame.heap_weaken extension) ih
  | live header saved outside ihSaved ihOutside => exact .live (header.heap_weaken extension) ihSaved ihOutside
  | spent header next ih => exact .spent (header.heap_weaken extension) ih
  | retiring header next ih => exact .retiring (header.heap_weaken extension) ih

private theorem plain_drop (frame : PlainFrameRel graph owners heap core plain) :
    CoreMachine.closeFuel (fuel+1) (core::rest) = CoreMachine.closeFuel fuel rest := by
  change FrameRel graph owners heap core plain.context at frame
  generalize same : plain.context = context at frame
  cases frame <;> rfl

/-- Initial residual cursor comes from the same interpreted captured stack and
actual successful projection. Fuel and graph sites are not reconstructed. -/
theorem cursor_of_close (captured : PushedWithMaps graph heap maps target) :
    ∀ fuel closing consumed, CoreMachine.closeFuel fuel (framesOf maps) = .ok (closing,consumed) →
      RetainedCursor graph heap closing target ∧
      consumed = (CoreClosing.consumed target.erase).map CoreMachine.Observation.nestedConsumed := by
  induction captured with
  | nil =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have same : closing = [] ∧ consumed = [] := by simpa [framesOf,CoreMachine.closeFuel] using projection.symm
          rcases same with ⟨rfl,rfl⟩; exact ⟨.nil,rfl⟩
  | cons frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          rw [framesOf_cons,plain_drop frame] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
          exact ⟨.plain (.ordinary frame) cursor,order⟩
  | @initializer owners core plain maps target frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
          exact ⟨.plain (.initializer frame) cursor,order⟩
  | @request owners core plain maps target frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
          exact ⟨.plain (.request frame) cursor,order⟩
  | @resume owners core plain maps target frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          have dropped : CoreMachine.closeFuel (fuel+1) (core::framesOf maps) = CoreMachine.closeFuel fuel (framesOf maps) := by cases frame; rfl
          rw [framesOf_cons,dropped] at projection
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
          exact ⟨.plain (.resume frame) cursor,order⟩
  | @boundary owners core effectFrame maps target frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame with
          | handler known kind translated header =>
              obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
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
                  obtain ⟨cursor,order⟩ := ih fuel rest events tail
                  exact ⟨.cell (.cell (owners := owners) known kind) cursor,order⟩
  | @cleanup owners core data maps target frame next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          cases frame with
          | armed known kind shape delayed saved lookup relationValue =>
            rename_i site node callback action body environment parameter functionBody captured
            simp only [framesOf_cons,CoreMachine.closeFuel] at projection
            cases tail : CoreMachine.closeFuel fuel (framesOf maps) with
            | error error => simp [tail,Bind.bind,Except.bind] at projection
            | ok result =>
                rcases result with ⟨rest,events⟩
                have same : .cleanupBoundary action environment data.identity::rest = closing ∧ events = consumed := by
                  simpa [tail,Bind.bind,Except.bind,Pure.pure,Except.pure] using projection
                rcases same with ⟨rfl,rfl⟩
                obtain ⟨cursor,order⟩ := ih fuel rest events tail
                exact ⟨.armed (.armed known kind shape delayed saved lookup relationValue) cursor,order⟩
  | spent header next ih =>
      intro fuel closing consumed projection
      cases fuel with
      | zero => cases projection
      | succ fuel =>
          obtain ⟨cursor,order⟩ := ih fuel closing consumed projection
          exact ⟨.spent header cursor,order⟩
  | @live owners handler owner occurrence data capturedMaps capturedTarget outsideMaps outsideTarget ticket result header captured outside ihCaptured ihOutside =>
      intro fuel closing consumed projection
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
                  obtain ⟨savedRetainedCursor,savedOrder⟩ := ihCaptured fuel _ _ child
                  obtain ⟨tailRetainedCursor,tailOrder⟩ := ihOutside fuel _ _ tail
                  refine ⟨same.1 ▸ RetainedCursor.live header savedRetainedCursor tailRetainedCursor,?_⟩
                  rw [←same.2,savedOrder,tailOrder]
                  simp [CoreClosing.consumed,Stack.erase,List.map_append]

/-- The prior resource-only carrier embeds without changing its evidence. -/
theorem of_resource (cursor : CoreResourceProjection.Cursor graph heap physical target) :
    RetainedCursor graph heap physical target := by
  induction cursor with
  | nil => exact .nil
  | plain frame next ih => exact .plain frame ih
  | handler frame next ih => exact .handler frame ih
  | cell frame next ih => exact .cell frame ih
  | live header saved outside ihSaved ihOutside => exact .live header ihSaved ihOutside
  | spent header next ih => exact .spent header ih
  | retiring header next ih => exact .retiring header ih

#print axioms RetainedCursor.append
#print axioms RetainedCursor.heap_weaken
#print axioms cursor_of_close
#print axioms of_resource
end Ash.OneShot.CoreCleanupProjection
