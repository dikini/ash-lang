import SourcePlannedCaptureSubstitution

/-! Connect the actual runtime handler cut to the exact retained hints.
The structural cut follows existing dispatch and keeps dormant annotations and
both physical stack pieces, so capture cannot use an unrelated source split. -/
namespace Ash.OneShot.SourcePlannedRuntimeCuts
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Matches Compatible)
open SourceDependencyCapture (lookupDependencies)

theorem matched_cut {hints : Hints scope}
    (physical : HandlerCut effect whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (found : lookup operation (tables handler) = some contract)
    (declared : lookupDependencies operation (families handler) = some modes) :
    ∃ capturedScope tailScope, ∃ (saved : Hints capturedScope) (waiting : Hints tailScope),
      SourcePlannedCuts.Cut effect operation contract modes hints saved waiting ∧
      Matches tables families required saved captured ∧ Matches tables families required waiting tail ∧
      (Compatible hints .nil → SourceContextualHints.checkRequirements tailScope (required handler) = true) := by
  induction physical generalizing scope with
  | hit handler tail same => cases matched with
    | handler rest =>
        cases same
        refine ⟨_, _, _, _, .hit found declared, .handler .nil, rest, ?_⟩
        intro compatible
        cases compatible with
        | handler supplied tail =>
            apply SourceContextualRequirements.check_requirements_iff.mpr
            simpa only [SourceDependencyProjection.scope_append_nil] using supplied
  | push entry rest captured tail handler miss next ih => cases matched with
    | plain rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .plain cut, .plain saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | handler rest =>
        rename_i other
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        have different : effect ≠ other.effectInst := by
          intro same; apply miss
          simp [ExecFrame.erase, HandlerData.erase, Ash.OneShot.Frame.target, same]
        refine ⟨_, _, _, _, .handler different cut, .handler saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | cell rest =>
        rename_i identity payload caller answer
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        have different : effect ≠ .cell identity := by
          intro same; apply miss
          simp [ExecFrame.erase, Ash.OneShot.Frame.target, same]
        refine ⟨_, _, _, _, .cell different cut, .cell saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | cleanup rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .cleanup cut, .cleanup saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | running rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .running cut, .running saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | unwinding rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .running cut, .unwinding saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | closing rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .running cut, .closing saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
    | retiring rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .running cut, .retiring saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
  | live owner input answer dormant caller rest captured tail handler next ih => cases matched with
    | live dormant rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .live cut, .live dormant saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩
  | spent owner answer caller rest captured tail handler next ih => cases matched with
    | spent rest =>
        obtain ⟨_, _, _, _, cut, saved, waiting, supplied⟩ := ih rest found declared
        refine ⟨_, _, _, _, .spent cut, .spent saved, waiting, by intro compatible; cases compatible; exact supplied ‹_›⟩

end Ash.OneShot.SourcePlannedRuntimeCuts

#print axioms Ash.OneShot.SourcePlannedRuntimeCuts.matched_cut
