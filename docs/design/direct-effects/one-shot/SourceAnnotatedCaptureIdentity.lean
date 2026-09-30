import SourceAnnotatedClosingRuntime
import SavedCaptureIdentity

/-! Retain exact annotated saved stacks at capture locations. The proofs reuse
existing raw owner membership and the established location/append argument;
no source typing or future execution is assumed by the location relation. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

inductive CapturedIn (owner : Nat) (capture : Stack) : Stack → Prop where
  | here : CapturedIn owner capture (.live owner input answer capture caller rest)
  | push (located : CapturedIn owner capture rest) : CapturedIn owner capture (.push frame rest)
  | saved (located : CapturedIn owner capture nested) : CapturedIn owner capture (.live other input answer nested caller rest)
  | tail (located : CapturedIn owner capture rest) : CapturedIn owner capture (.live other input answer nested caller rest)
  | spent (located : CapturedIn owner capture rest) : CapturedIn owner capture (.spent other answer caller rest)

theorem CapturedIn.erase (located : CapturedIn owner capture root) :
    SourceTemplates.CapturedIn owner capture.erase root.erase := by
  induction located with
  | here => exact .here
  | push located ih => exact .push ih
  | saved located ih => exact .saved ih
  | tail located ih => exact .tail ih
  | spent located ih => exact .spent ih

theorem CapturedIn.of_raw {root : Stack}
    (located : SourceTemplates.CapturedIn owner raw root.erase) :
    ∃ capture, CapturedIn owner capture root ∧ capture.erase = raw := by
  generalize same : root.erase = erased at located
  induction located generalizing root with
  | here =>
      cases root <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨_, .here, rfl⟩
  | push located ih =>
      cases root <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl⟩
      obtain ⟨capture, actual, rfl⟩ := ih rfl
      exact ⟨capture, .push actual, rfl⟩
  | saved located ih =>
      cases root <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨capture, actual, rfl⟩ := ih rfl
      exact ⟨capture, .saved actual, rfl⟩
  | tail located ih =>
      cases root <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨capture, actual, rfl⟩ := ih rfl
      exact ⟨capture, .tail actual, rfl⟩
  | spent located ih =>
      cases root <;> simp [Stack.erase] at same
      rcases same with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨capture, actual, rfl⟩ := ih rfl
      exact ⟨capture, .spent actual, rfl⟩

theorem located_below (front : Stack) (located : CapturedIn owner capture tail) :
    CapturedIn owner capture (front.append tail) := by
  induction front with
  | nil => exact located
  | push frame rest ih => exact .push ih
  | live boundary input answer saved scope rest ihSaved ih => exact .tail ih
  | spent boundary answer scope rest ih => exact .spent ih

theorem captured_in_unique (unique : (ScopedExecution.ownedTickets stack.erase).Nodup)
    (first : CapturedIn owner capture stack) (second : CapturedIn owner other stack) : capture = other := by
  induction stack generalizing capture other with
  | nil => cases first
  | push frame rest ih =>
      have restUnique : (ScopedExecution.ownedTickets rest.erase).Nodup := by cases frame <;> simp_all [Stack.erase, Frame.erase, ScopedExecution.ownedTickets]
      cases first with
      | push first => cases second with
          | push second => exact ih restUnique first second
  | live boundary input answer saved caller rest ihSaved ihRest =>
      have absent := (List.nodup_cons.mp unique).1
      have parts := List.nodup_append.mp (List.nodup_cons.mp unique).2
      cases first with
      | here => cases second with
          | here => rfl
          | saved second => exact False.elim (absent (List.mem_append_left _ (SourceTemplates.captured_in_owned second.erase)))
          | tail second => exact False.elim (absent (List.mem_append_right _ (SourceTemplates.captured_in_owned second.erase)))
      | saved first => cases second with
          | here => exact False.elim (absent (List.mem_append_left _ (SourceTemplates.captured_in_owned first.erase)))
          | saved second => exact ihSaved parts.1 first second
          | tail second => exact False.elim (parts.2.2 owner (SourceTemplates.captured_in_owned first.erase) owner (SourceTemplates.captured_in_owned second.erase) rfl)
      | tail first => cases second with
          | here => exact False.elim (absent (List.mem_append_right _ (SourceTemplates.captured_in_owned first.erase)))
          | saved second => exact False.elim (parts.2.2 owner (SourceTemplates.captured_in_owned second.erase) owner (SourceTemplates.captured_in_owned first.erase) rfl)
          | tail second => exact ihRest parts.2.1 first second
  | spent boundary answer caller rest ih =>
      cases first with
      | spent first => cases second with
          | spent second => exact ih unique first second

theorem located_append {first second : Stack} :
    CapturedIn owner capture (first.append second) ↔
      CapturedIn owner capture first ∨ CapturedIn owner capture second := by
  induction first with
  | nil =>
      constructor
      · exact Or.inr
      · intro located; rcases located with impossible | located
        · cases impossible
        · exact located
  | push frame rest ih =>
      constructor
      · intro located; cases located with
        | push located =>
            rcases ih.mp located with here | later
            · exact Or.inl (.push here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with | push here => exact .push (ih.mpr (Or.inl here))
        · exact located_below _ later
  | live boundary input answer saved scope rest ihSaved ihRest =>
      constructor
      · intro located; cases located with
        | here => exact Or.inl .here
        | saved located => exact Or.inl (.saved located)
        | tail located =>
            rcases ihRest.mp located with here | later
            · exact Or.inl (.tail here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with
          | here => exact .here
          | saved located => exact .saved located
          | tail located => exact .tail (ihRest.mpr (Or.inl located))
        · exact located_below _ later
  | spent boundary answer scope rest ih =>
      constructor
      · intro located; cases located with
        | spent located =>
            rcases ih.mp located with here | later
            · exact Or.inl (.spent here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with | spent here => exact .spent (ih.mpr (Or.inl here))
        · exact located_below _ later

theorem closing_has_no_capture (plan : List CloseEntry) :
    ¬ CapturedIn owner capture (closeControl scope plan) := by
  induction plan with
  | nil => intro located; cases located
  | cons entry rest ih => intro located; cases located with
      | push located => exact ih located


/-- Restoring one saved segment cannot change another saved continuation. -/
theorem resume_capture_origin {front capture tail : Stack}
    (located : CapturedIn other saved (capture.append (front.append (.spent owner answer caller tail)))) :
    CapturedIn other saved (front.append (.live owner input answer capture caller tail)) := by
  rcases located_append.mp located with inside | later
  · exact located_below front (.saved inside)
  · rcases located_append.mp later with earlier | later
    · exact located_append.mpr (Or.inl earlier)
    · cases later with | spent later => exact located_below front (.tail later)

/-- Closing creates no live captures; surviving locations come from the caller. -/
theorem discard_capture_origin {front capture tail : Stack}
    (located : CapturedIn other saved ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail))))) :
    CapturedIn other saved (front.append (.live owner input answer capture caller tail)) := by
  rcases located_append.mp located with closing | surviving
  · exact False.elim (closing_has_no_capture plan closing)
  · cases surviving with
    | push surviving =>
      rcases located_append.mp surviving with earlier | later
      · exact located_append.mpr (Or.inl earlier)
      · cases later with | spent later => exact located_below front (.tail later)

end Ash.OneShot.SourceAnnotatedRuntime

#print axioms Ash.OneShot.SourceAnnotatedRuntime.CapturedIn.erase
#print axioms Ash.OneShot.SourceAnnotatedRuntime.CapturedIn.of_raw
#print axioms Ash.OneShot.SourceAnnotatedRuntime.located_below
#print axioms Ash.OneShot.SourceAnnotatedRuntime.captured_in_unique
#print axioms Ash.OneShot.SourceAnnotatedRuntime.located_append
#print axioms Ash.OneShot.SourceAnnotatedRuntime.closing_has_no_capture
#print axioms Ash.OneShot.SourceAnnotatedRuntime.resume_capture_origin
#print axioms Ash.OneShot.SourceAnnotatedRuntime.discard_capture_origin
