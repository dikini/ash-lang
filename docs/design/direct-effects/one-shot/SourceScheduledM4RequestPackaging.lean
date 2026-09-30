import SourceScheduledPreservation

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

theorem request_of_stable_at
    {operations : SourcePlannedTyping.Operations} {snapshot after : Snapshot operations}
    (shape : snapshot.run = beforeRun)
    (step : Stable.Step operations { snapshot with run := beforeRun } after) :
    Nonempty (Request snapshot) := by
  cases snapshot
  cases shape
  exact ⟨.stable after step⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.request_of_stable_at
