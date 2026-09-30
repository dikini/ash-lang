import SourceAnnotatedRuntimeSegments

/-! Raw stack boundaries lift to the actual annotated prefix and suffix.
Dormant saved segments remain attached to their original live frames. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

/-- Recover a physical split without inventing annotations or choosing a
second source derivation. -/
theorem Stack.lift_append {whole : Stack}
    (same : whole.erase = first.append second) :
    ∃ front tail : Stack, whole = front.append tail ∧ front.erase = first ∧ tail.erase = second := by
  induction first generalizing whole with
  | nil => exact ⟨.nil, whole, rfl, rfl, same⟩
  | push frame rest ih =>
      cases whole <;> simp [ScopedExecution.Stack.append, Stack.erase] at same
      rcases same with ⟨rfl, same⟩
      obtain ⟨front, tail, rfl, rfl, rfl⟩ := ih same
      exact ⟨.push _ front, tail, rfl, rfl, rfl⟩
  | live owner input answer saved caller rest ihSaved ih =>
      cases whole <;> simp [ScopedExecution.Stack.append, Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, same⟩
      obtain ⟨front, tail, rfl, rfl, rfl⟩ := ih same
      exact ⟨.live _ _ _ _ _ front, tail, rfl, rfl, rfl⟩
  | spent owner answer caller rest ih =>
      cases whole <;> simp [ScopedExecution.Stack.append, Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, same⟩
      obtain ⟨front, tail, rfl, rfl, rfl⟩ := ih same
      exact ⟨.spent _ _ _ front, tail, rfl, rfl, rfl⟩

/-- Lift a selected live boundary with both the captured and waiting annotated
segments intact. This is structural decomposition, not admission. -/
theorem Stack.lift_live {whole : Stack}
    (same : whole.erase = front.append (.live owner input answer saved caller rest)) :
    ∃ first capture tail : Stack,
      whole = first.append (.live owner input answer capture caller tail) ∧
      first.erase = front ∧ capture.erase = saved ∧ tail.erase = rest := by
  obtain ⟨first, suffix, rfl, rfl, suffixSame⟩ := Stack.lift_append same
  cases suffix <;> simp [Stack.erase] at suffixSame
  rcases suffixSame with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨first, _, _, rfl, rfl, rfl, rfl⟩


open ScopedExecution (Scope)

inductive HandlerCut (requested : Instance) : Stack → Stack → Stack → Handler → Prop where
  | hit (handler : Handler) (tail : Stack) (same : handler.effectInst = requested) :
      HandlerCut requested (.push (.handler handler) tail)
        (.push (.handler handler) .nil) tail handler
  | push (frame : Frame) (rest cap tail : Stack) (handler : Handler)
      (miss : frame.erase.erase.target ≠ some requested)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.push frame rest) (.push frame cap) tail handler
  | live (ticket : Nat) (q a : Ty) (saved : Stack) (scope : Scope)
      (rest cap tail : Stack) (handler : Handler)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.live ticket q a saved scope rest)
        (.live ticket q a saved scope cap) tail handler
  | spent (ticket : Nat) (a : Ty) (scope : Scope) (rest cap tail : Stack) (handler : Handler)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.spent ticket a scope rest) (.spent ticket a scope cap) tail handler

theorem HandlerCut.erase (cut : HandlerCut requested whole capture tail handler) :
    ScopedExecution.HandlerCut requested whole.erase capture.erase tail.erase handler.erase := by
  induction cut with
  | hit handler tail same => exact .hit handler.erase tail.erase same
  | push frame rest capture tail handler miss next ih => exact .push frame.erase rest.erase capture.erase tail.erase handler.erase miss ih
  | live ticket input answer saved caller rest capture tail handler next ih =>
      exact .live ticket input answer saved.erase caller rest.erase capture.erase tail.erase handler.erase ih
  | spent ticket answer caller rest capture tail handler next ih =>
      exact .spent ticket answer caller rest.erase capture.erase tail.erase handler.erase ih

theorem HandlerCut.reconstructs (cut : HandlerCut requested whole capture tail handler) :
    whole = capture.append tail := by
  induction cut <;> simp_all [Stack.append]

/-- Exact raw interpretation selection recovers the original annotated capture,
suffix and selected handler, including saved captures crossed on the way. -/
theorem HandlerCut.of_raw
    (cut : ScopedExecution.HandlerCut requested whole.erase rawCapture rawTail rawHandler) :
    ∃ capture tail handler, HandlerCut requested whole capture tail handler ∧
      capture.erase = rawCapture ∧ tail.erase = rawTail ∧ handler.erase = rawHandler := by
  generalize same : whole.erase = rawWhole at cut
  induction cut generalizing whole with
  | hit handler tail effectSame =>
      cases whole <;> simp [Stack.erase] at same
      rename_i frame rest
      cases frame <;> simp [Frame.erase] at same
      rcases same with ⟨rfl, rfl⟩
      exact ⟨_, _, _, .hit _ _ effectSame, rfl, rfl, rfl⟩
  | push frame rest capture tail handler miss next ih =>
      cases whole <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl⟩
      obtain ⟨capture, tail, handler, selected, rfl, rfl, rfl⟩ := ih rfl
      exact ⟨_, _, _, .push _ _ _ _ _ miss selected, rfl, rfl, rfl⟩
  | live ticket input answer saved caller rest capture tail handler next ih =>
      cases whole <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨capture, tail, handler, selected, rfl, rfl, rfl⟩ := ih rfl
      exact ⟨_, _, _, .live _ _ _ _ _ _ _ _ _ selected, rfl, rfl, rfl⟩
  | spent ticket answer caller rest capture tail handler next ih =>
      cases whole <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨capture, tail, handler, selected, rfl, rfl, rfl⟩ := ih rfl
      exact ⟨_, _, _, .spent _ _ _ _ _ _ _ selected, rfl, rfl, rfl⟩

inductive ClauseAt (operation : Nat) : SourceAnnotatedCode.Clauses → Nat → Nat → SourceAnnotatedCode.Term → Prop where
  | hit : ClauseAt operation (.cons operation parameter binder body rest) parameter binder body
  | pass (different : operation ≠ other)
      (next : ClauseAt operation rest parameter binder body) :
      ClauseAt operation (.cons other otherParameter otherBinder otherBody rest) parameter binder body

theorem ClauseAt.erase (clause : ClauseAt operation clauses parameter binder body) :
    ScopedExecution.ClauseAt operation clauses.erase parameter binder body.erase := by
  induction clause with
  | hit => exact .hit
  | pass different next ih => exact .pass different ih

theorem ClauseAt.of_raw
    (clause : ScopedExecution.ClauseAt operation clauses.erase parameter binder rawBody) :
    ∃ body, ClauseAt operation clauses parameter binder body ∧ body.erase = rawBody := by
  generalize same : clauses.erase = rawClauses at clause
  induction clause generalizing clauses with
  | hit =>
      cases clauses <;> simp [SourceAnnotatedCode.Clauses.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨_, .hit, rfl⟩
  | pass different next ih =>
      cases clauses <;> simp [SourceAnnotatedCode.Clauses.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨body, selected, rfl⟩ := ih rfl
      exact ⟨body, .pass different selected, rfl⟩

end Ash.OneShot.SourceAnnotatedRuntime

#print axioms Ash.OneShot.SourceAnnotatedRuntime.Stack.lift_append
#print axioms Ash.OneShot.SourceAnnotatedRuntime.Stack.lift_live

#print axioms Ash.OneShot.SourceAnnotatedRuntime.HandlerCut.erase

#print axioms Ash.OneShot.SourceAnnotatedRuntime.HandlerCut.reconstructs

#print axioms Ash.OneShot.SourceAnnotatedRuntime.HandlerCut.of_raw

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ClauseAt.erase

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ClauseAt.of_raw
