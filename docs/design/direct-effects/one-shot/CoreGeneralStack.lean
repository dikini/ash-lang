import CoreCleanupRunFrames

/-! Physical and lexical continuation segments that survive capture and resume.
Completion atoms retain their existing authentication and can be split by a
handler cut. A retained projection is not a physical live clause owner.
This carrier alone supplies neither dispatch safety nor current admission. -/
namespace Ash.OneShot.CoreGeneralStack
set_option linter.unusedSimpArgs false
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack
  CoreCaptureEntry CoreCleanupFrames CoreCleanupProjection CoreCleanupRunFrames CoreRequestFrames

/-- A single protected completion, with its current saved return evidence.
Physical and lexical close labels are a local pair, not an identity claim. -/
inductive CompletionRel (graph : CoreSyntax.Graph) (heap : Heap) : CoreMachine.Frame → ExecFrame → Prop where
  | normal (delayed : CleanupRel graph cleanupOwners heap (.cleanupBoundary action environment data.identity) data)
      (saved : ValueRel graph callerOwners heap savedValue savedCode) :
      CompletionRel graph heap (.cleanupCompletion data.identity savedValue) (.running data savedCode saved.closed)
  | unwinding (delayed : CleanupRel graph cleanupOwners heap (.cleanupBoundary action environment data.identity) data) :
      CompletionRel graph heap (.cleanupCompletion data.identity .unit) (.unwinding data)
  | closing (coreIdentity targetIdentity : Nat) (callerScope : Scope) :
      CompletionRel graph heap (.closeCompletion coreIdentity) (.closing targetIdentity callerScope)

inductive GeneralSegment (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | ordinary (stack : PushedWithMaps graph heap maps target) :
      GeneralSegment graph heap (framesOf maps) target
  | retained (cursor : RetainedCursor graph heap physical lexical) :
      GeneralSegment graph heap physical lexical
  | push (frame : PushCarrier graph owners heap core target)
      (tail : GeneralSegment graph heap physical lexical) :
      GeneralSegment graph heap (core :: physical) (.push target lexical)
  | completion (atom : CompletionRel graph heap core target) :
      GeneralSegment graph heap [core] (.push target .nil)
  | live (header : OwnerHeader graph owners heap handler owner occurrence data)
      (saved : GeneralSegment graph heap savedPhysical savedTarget)
      (outside : GeneralSegment graph heap outsidePhysical outsideTarget) :
      GeneralSegment graph heap
        (.clauseBoundary handler owner occurrence ticket (some savedPhysical) :: outsidePhysical)
        (.live ticket result data.answer savedTarget data.scope outsideTarget)
  | spent (header : OwnerHeader graph owners heap handler owner occurrence data)
      (outside : GeneralSegment graph heap outsidePhysical outsideTarget) :
      GeneralSegment graph heap (.clauseBoundary handler owner occurrence ticket none :: outsidePhysical)
        (.spent ticket data.answer data.scope outsideTarget)
  | append (first : GeneralSegment graph heap firstPhysical firstTarget)
      (second : GeneralSegment graph heap secondPhysical secondTarget) :
      GeneralSegment graph heap (firstPhysical ++ secondPhysical) (firstTarget.append secondTarget)

theorem CompletionRel.heap_weaken (atom : CompletionRel graph heap core target)
    (extension : HeapExtends heap larger) : CompletionRel graph larger core target := by
  cases atom with
  | normal delayed saved => exact .normal (delayed.heap_weaken extension) (saved.heap_weaken extension)
  | unwinding delayed => exact .unwinding (delayed.heap_weaken extension)
  | closing core target scope => exact .closing core target scope

theorem CompletionRel.selector_miss (atom : CompletionRel graph heap core target) :
    target.erase.target ≠ some requested := by
  cases atom <;> simp [ExecFrame.erase, ActionData.erase, Frame.target, closeFrame]

theorem CompletionRel.protected (atom : CompletionRel graph heap core target) :
    ProtectionContexts.protectedMode (.push target rest : Stack).erase = true := by
  cases atom <;> rfl

theorem CompletionRel.handler_pass (atom : CompletionRel graph heap core target)
    (found : CoreMachine.findInterpreter graph effect rest = .ok (.handler inside site environment occurrence outside)) :
    CoreMachine.findInterpreter graph effect (core :: rest) =
      .ok (.handler (core :: inside) site environment occurrence outside) := by
  cases atom <;> simp [CoreMachine.findInterpreter, found, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem CompletionRel.owner_pass (atom : CompletionRel graph heap core target)
    (found : CoreMachine.findOwner handler owner rest = .ok cut) :
    CoreMachine.findOwner handler owner (core :: rest) = .ok {cut with inside := core :: cut.inside} := by
  cases atom <;> simp [CoreMachine.findOwner, found, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem GeneralSegment.heap_weaken (segment : GeneralSegment graph heap physical lexical)
    (extension : HeapExtends heap larger) : GeneralSegment graph larger physical lexical := by
  induction segment with
  | ordinary stack => exact .ordinary (stack.heap_weaken extension)
  | retained cursor => exact .retained (cursor.heap_weaken extension)
  | @push owners core target physical lexical frame tail ih =>
      have weakened : PushCarrier graph owners larger core target := by
        cases frame with
        | ordinary frame => exact .ordinary (frame.heap_weaken extension)
        | initializer frame => exact .initializer (frame.heap_weaken extension)
        | request frame => exact .request (frame.heap_weaken extension)
        | resume frame => exact .resume (frame.heap_weaken extension)
        | cleanup frame => exact .cleanup (frame.heap_weaken extension)
        | boundary frame => exact .boundary (frame.heap_weaken extension)
      exact .push weakened ih
  | completion atom => exact .completion (atom.heap_weaken extension)
  | live header saved outside ihSaved ihOutside => exact .live (header.heap_weaken extension) ihSaved ihOutside
  | spent header outside ih => exact .spent (header.heap_weaken extension) ih
  | append first second ihFirst ihSecond => exact .append ihFirst ihSecond

private theorem cursor_plain_tail (cursor : RetainedCursor graph heap physical target) :
    ∀ plain rest, target = .push (.plain plain) rest → RetainedCursor graph heap physical rest := by
  cases cursor with
  | plain frame next =>
      intro plain rest same
      exact (Stack.push.inj same).2 ▸ next
  | nil | live | spent => intro plain rest same; cases same
  | handler | cell | armed | retiring =>
      intro plain rest same
      cases (Stack.push.inj same).1

private theorem cursor_armed_tail (cursor : RetainedCursor graph heap physical target) :
    ∀ data rest action environment,
      target = .push (.armed data) rest →
      physical = .cleanupBoundary action environment data.identity :: remaining →
      RetainedCursor graph heap remaining rest := by
  cases cursor with
  | armed frame next =>
      intro data rest action environment same physicalEq
      have dataEq := ExecFrame.armed.inj (Stack.push.inj same).1
      cases dataEq
      have tailEq := (List.cons.inj physicalEq).2
      exact (Stack.push.inj same).2 ▸ (tailEq ▸ next)
  | nil | live | spent => intro data rest action environment same physicalEq; cases same
  | plain | handler | cell | retiring =>
      intro data rest action environment same physicalEq
      cases (Stack.push.inj same).1

/-- Existing running carriers embed with the same physical completion and
lexical stack. In particular the old projected close labels remain local. -/
theorem GeneralSegment.of_running (running : RunningTail graph heap physical lexical) :
    GeneralSegment graph heap physical lexical := by
  induction running with
  | normal delayed saved outside =>
      simpa [Stack.append] using GeneralSegment.append (.completion (.normal delayed saved)) (.ordinary outside)
  | @projected pendingOwners pending savedOwners action environment retainedMaps pendingPlain data retainedTarget
      outsideMaps outsideTarget closing closeIdentity closeScope captured delayed retained outside projection =>
      have cursor : RetainedCursor graph heap closing retainedTarget := by
        have projected := cursor_of_close captured _ _ _ projection
        have stripped := cursor_plain_tail projected.1 pendingPlain _ rfl
        exact cursor_armed_tail stripped data retainedTarget action environment rfl rfl
      simpa [Stack.append, List.append_assoc] using
        GeneralSegment.append (.completion (.unwinding delayed))
          (.append (.retained cursor) (.append (.completion (.closing closeIdentity closeIdentity closeScope)) (.ordinary outside)))
  | retainedProjected delayed residual outside =>
      simpa [Stack.append, List.append_assoc] using
        GeneralSegment.append (.completion (.unwinding delayed))
          (.append (.retained residual) (.append (.completion (.closing _ _ _)) (.ordinary outside)))
  | append first second ihFirst ihSecond => exact .append ihFirst ihSecond

/-- Saving a running completion transfers its protection into the saved
segment; it does not make the segment eligible for discard. -/
theorem normal_capture_protected (data : ActionData) (savedCode : Code) (closed : ClosedValue savedCode)
    (tail : Stack) :
    ProtectionContexts.protectedMode (.push (.running data savedCode closed) tail : Stack).erase = true := by
  rfl

theorem normal_capture_close_blocked (identity : Nat) (saved : CoreMachine.Value)
    (tail : List CoreMachine.Frame) (fuel : Nat) :
    CoreMachine.closeFuel (fuel + 1) (.cleanupCompletion identity saved :: tail) =
      .error .runningCloseBlocked := by rfl

/-- A protected obligation anywhere in the physical segment, including an
actual live owner's saved segment. Consumed projections add no live owner. -/
inductive ProtectedCapture : List CoreMachine.Frame → Prop where
  | cleanup : ProtectedCapture (.cleanupCompletion identity saved :: rest)
  | closing : ProtectedCapture (.closeCompletion identity :: rest)
  | tail (obligation : ProtectedCapture rest) : ProtectedCapture (frame :: rest)
  | saved (obligation : ProtectedCapture captured) :
      ProtectedCapture (.clauseBoundary handler owner occurrence ticket (some captured) :: rest)

theorem ProtectedCapture.prepend (obligation : ProtectedCapture captured) (front : List CoreMachine.Frame) :
    ProtectedCapture (front ++ captured) := by
  induction front with
  | nil => exact obligation
  | cons frame rest ih => exact .tail ih

theorem ProtectedCapture.append (obligation : ProtectedCapture captured) (outside : List CoreMachine.Frame) :
    ProtectedCapture (captured ++ outside) := by
  induction obligation with
  | cleanup => exact .cleanup
  | closing => exact .closing
  | tail _ ih => exact .tail ih
  | saved obligation _ => exact .saved obligation

theorem CompletionRel.physical_protected (atom : CompletionRel graph heap core target) :
    ProtectedCapture [core] := by
  cases atom with
  | normal _ _ => exact .cleanup
  | unwinding _ => exact .cleanup
  | closing _ _ _ => exact .closing

theorem ProtectedCapture.close_no_success (obligation : ProtectedCapture captured) (fuel : Nat) :
    ∀ remaining observations, CoreMachine.closeFuel fuel captured ≠ .ok (remaining, observations) := by
  induction obligation generalizing fuel with
  | cleanup => cases fuel <;> simp [CoreMachine.closeFuel]
  | closing => cases fuel <;> simp [CoreMachine.closeFuel]
  | @tail rest frame obligation ih =>
      cases fuel with
      | zero => simp [CoreMachine.closeFuel]
      | succ fuel =>
          cases frame with
          | clauseBoundary handler owner occurrence ticket capture =>
              cases capture with
              | none => exact ih fuel
              | some captured =>
                  simp only [CoreMachine.closeFuel]
                  cases h : CoreMachine.closeFuel fuel captured with
                  | error error => simp [Bind.bind, Except.bind]
                  | ok pair =>
                      cases pair with
                      | mk nested consumed =>
                          cases hrest : CoreMachine.closeFuel fuel rest with
                          | error error => simp [Bind.bind, Except.bind, Functor.map, Except.map]
                          | ok pair => exact False.elim (ih fuel pair.1 pair.2 hrest)
          | cleanupCompletion _ _ => simp [CoreMachine.closeFuel]
          | closeCompletion _ => simp [CoreMachine.closeFuel]
          | resourceBoundary _ _ _ =>
              simp only [CoreMachine.closeFuel]
              cases hrest : CoreMachine.closeFuel fuel rest with
              | error error => simp [Bind.bind, Except.bind, Functor.map, Except.map]
              | ok pair => exact False.elim (ih fuel pair.1 pair.2 hrest)
          | cleanupBoundary _ _ _ =>
              simp only [CoreMachine.closeFuel]
              cases hrest : CoreMachine.closeFuel fuel rest with
              | error error => simp [Bind.bind, Except.bind, Functor.map, Except.map]
              | ok pair => exact False.elim (ih fuel pair.1 pair.2 hrest)
          | _ => exact ih fuel
  | saved obligation ih =>
      cases fuel with
      | zero => simp [CoreMachine.closeFuel]
      | succ fuel =>
          simp only [CoreMachine.closeFuel]
          cases h : CoreMachine.closeFuel fuel _ with
          | error error => simp [Bind.bind, Except.bind]
          | ok pair => exact False.elim (ih fuel pair.1 pair.2 h)

/-- Successful physical handler selection through a consumed cursor comes
from its outside suffix. A retained live record contributes saved physical
resources and cleanups, never a live clause-boundary owner. -/
theorem RetainedCursor.handler_lookup_decompose
    (cursor : RetainedCursor graph heap physical lexical)
    (found : CoreMachine.findInterpreter graph effect (physical ++ rest) =
      .ok (.handler inside site environment occurrence outside)) :
    ∃ suffixInside, inside = physical ++ suffixInside ∧
      CoreMachine.findInterpreter graph effect rest =
        .ok (.handler suffixInside site environment occurrence outside) := by
  induction cursor generalizing rest inside with
  | nil => exact ⟨inside,rfl,found⟩
  | plain frame next ih | handler frame next ih | spent header next ih | retiring header next ih =>
      exact ih found
  | @cell owners site key payload scope answer physical target frame next ih =>
      simp only [List.cons_append, CoreMachine.findInterpreter] at found
      split at found
      · cases found
      · cases selected : CoreMachine.findInterpreter graph effect (physical ++ rest) with
        | error error => simp [selected,Bind.bind,Except.bind] at found
        | ok cut =>
            cases cut with
            | cell cut => simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
            | handler suffix selectedSite selectedEnvironment selectedOccurrence selectedOutside =>
                simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
                obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
                obtain ⟨suffixInside,shape,lookup⟩ := ih selected
                exact ⟨suffixInside,by simp [shape],lookup⟩
  | @armed owners action environment data physical target frame next ih =>
      simp only [List.cons_append,CoreMachine.findInterpreter] at found
      cases selected : CoreMachine.findInterpreter graph effect (physical ++ rest) with
      | error error => simp [selected,Bind.bind,Except.bind] at found
      | ok cut =>
          cases cut with
          | cell cut => simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
          | handler suffix selectedSite selectedEnvironment selectedOccurrence selectedOutside =>
              simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
              obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
              obtain ⟨suffixInside,shape,lookup⟩ := ih selected
              exact ⟨suffixInside,by simp [shape],lookup⟩
  | live header saved outside ihSaved ihOutside =>
      obtain ⟨middle,shape,selected⟩ := ihSaved (by simpa [List.append_assoc] using found)
      obtain ⟨suffixInside,secondShape,lookup⟩ := ihOutside selected
      exact ⟨suffixInside,by simp [shape,secondShape,List.append_assoc],lookup⟩

theorem RetainedCursor.owner_lookup_pass
    (cursor : RetainedCursor graph heap physical lexical)
    (found : CoreMachine.findOwner handler owner rest = .ok cut) :
    CoreMachine.findOwner handler owner (physical ++ rest) =
      .ok {cut with inside := physical ++ cut.inside} := by
  induction cursor generalizing rest cut with
  | nil => exact found
  | plain frame next ih | handler frame next ih | spent header next ih | retiring header next ih => exact ih found
  | cell frame next ih | armed frame next ih =>
      simp [CoreMachine.findOwner,ih found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | live header saved outside ihSaved ihOutside =>
      simpa [List.append_assoc] using ihSaved (ihOutside found)

theorem RetainedCursor.owner_lookup_decompose
    (cursor : RetainedCursor graph heap physical lexical)
    (found : CoreMachine.findOwner handler owner (physical ++ rest) =
      .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩) :
    ∃ suffixInside, inside = physical ++ suffixInside ∧
      CoreMachine.findOwner handler owner rest =
        .ok ⟨suffixInside,handler,owner,occurrence,ticket,captured,outside⟩ := by
  induction cursor generalizing rest inside with
  | nil => exact ⟨inside,rfl,found⟩
  | plain frame next ih | handler frame next ih | spent header next ih | retiring header next ih => exact ih found
  | @cell owners site key payload scope answer physical target frame next ih =>
      simp only [List.cons_append,CoreMachine.findOwner] at found
      cases selected : CoreMachine.findOwner handler owner (physical ++ rest) with
      | error error => simp [selected,Bind.bind,Except.bind] at found
      | ok cut =>
          cases cut with
          | mk suffix selectedHandler selectedOwner selectedOccurrence selectedTicket selectedCapture selectedOutside =>
              simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure,CoreMachine.OwnerCut.mk.injEq] at found
              obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := found
              obtain ⟨suffixInside,shape,lookup⟩ := ih selected
              exact ⟨suffixInside,by simp [shape],lookup⟩
  | @armed owners action environment data physical target frame next ih =>
      simp only [List.cons_append,CoreMachine.findOwner] at found
      cases selected : CoreMachine.findOwner handler owner (physical ++ rest) with
      | error error => simp [selected,Bind.bind,Except.bind] at found
      | ok cut =>
          cases cut with
          | mk suffix selectedHandler selectedOwner selectedOccurrence selectedTicket selectedCapture selectedOutside =>
              simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure,CoreMachine.OwnerCut.mk.injEq] at found
              obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := found
              obtain ⟨suffixInside,shape,lookup⟩ := ih selected
              exact ⟨suffixInside,by simp [shape],lookup⟩
  | live header saved outside ihSaved ihOutside =>
      obtain ⟨middle,shape,selected⟩ := ihSaved (by simpa [List.append_assoc] using found)
      obtain ⟨suffixInside,secondShape,lookup⟩ := ihOutside selected
      exact ⟨suffixInside,by simp [shape,secondShape,List.append_assoc],lookup⟩

#print axioms RetainedCursor.owner_lookup_decompose
#print axioms RetainedCursor.owner_lookup_pass
#print axioms RetainedCursor.handler_lookup_decompose
#print axioms ProtectedCapture.prepend
#print axioms ProtectedCapture.append
#print axioms CompletionRel.physical_protected
#print axioms ProtectedCapture.close_no_success
#print axioms CompletionRel.heap_weaken
#print axioms CompletionRel.selector_miss
#print axioms CompletionRel.protected
#print axioms CompletionRel.handler_pass
#print axioms CompletionRel.owner_pass
#print axioms GeneralSegment.heap_weaken
#print axioms GeneralSegment.of_running
#print axioms normal_capture_protected
#print axioms normal_capture_close_blocked
end Ash.OneShot.CoreGeneralStack
