import SourceCodeRecordPositions
import SourceScheduledRetainedSplit
import SourceScheduledNormalizedRechecking
import SourceScheduledCaptureSource

/-! Reassemble exact capability source from positioned records, or reconstruct
canonical source by mutual induction on the original structural checks. The
latter also derives original capture/closing source; changed-receiver admission
remains independent. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)
open SourceScheduledChecks (Pending)
open SourceBoundSnapshots.Retained (ofCapability)

variable [DeclarationPolicy]
  [SourceScheduledChecks.DeclarationPolicy]
  [SourcePlannedChecks.DeclarationPolicy]

/-- Recover rich source at every actual bound position. This does not infer
code annotations from erased plans or from a successful schedule: every code
annotation comes from a concrete record at the matching receiver. -/
theorem Retained.Records.AtReceivers.source
    {hints : Hints scope} {forest : Forest hints} {bounds : Retained world forest}
    (records : bounds.Records (CodeRecord outward actions phases))
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (covered : AtReceivers outward actions phases records outside)
    (scheduled : Pending outward actions phases world forest outside) :
    ∃ source : SourceScheduledCapabilityAnnotations.Retained world forest outside,
      source.Valid outward actions phases ∧ ofCapability source = bounds := by
  induction records generalizing outsideScope with
  | nil => exact ⟨.operations .nil, rfl, rfl⟩
  | plain record tail ih =>
      cases covered with
      | plain located remaining =>
        cases scheduled with
        | plain _ scheduledTail =>
          obtain ⟨code, codeReady, codeOrigin⟩ := record.at_receiver located
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          refine ⟨.plain code source, ⟨codeReady, ready⟩, ?_⟩
          simp only [ofCapability, codeOrigin, origin]
  | handler tail ih =>
      cases covered with
      | handler remaining =>
        cases scheduled with
        | handler supplied scheduledTail =>
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          exact ⟨.handler source, ⟨supplied, ready⟩, congrArg _ origin⟩
  | cell tail ih =>
      cases covered with
      | cell remaining =>
        cases scheduled with
        | cell scheduledTail =>
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          exact ⟨.cell source, ready, congrArg _ origin⟩
  | cleanup record tail ih =>
      cases covered with
      | cleanup located remaining =>
        cases scheduled with
        | cleanup _ scheduledTail =>
          obtain ⟨code, codeReady, codeOrigin⟩ := record.at_receiver located
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          refine ⟨.cleanup code source, ⟨codeReady, ready⟩, ?_⟩
          simp only [ofCapability, codeOrigin, origin]
  | running tail ih =>
      cases covered with
      | running remaining =>
        cases scheduled with
        | running scheduledTail =>
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          exact ⟨.running source, ready, congrArg _ origin⟩
  | live saved tail ihSaved ihTail =>
      cases covered with
      | live inside remaining =>
        cases scheduled with
        | live scheduledSaved scheduledTail =>
          obtain ⟨insideSource, insideReady, insideOrigin⟩ := ihSaved inside scheduledSaved
          obtain ⟨source, ready, origin⟩ := ihTail remaining scheduledTail
          refine ⟨.live insideSource source, ⟨insideReady, ready⟩, ?_⟩
          simp only [ofCapability, insideOrigin, origin]
  | spent tail ih =>
      cases covered with
      | spent remaining =>
        cases scheduled with
        | spent scheduledTail =>
          obtain ⟨source, ready, origin⟩ := ih remaining scheduledTail
          exact ⟨.spent source, ready, congrArg _ origin⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.AtReceivers.source

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanBounds (Annotation ofCode)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceScheduledChecks (Local Pending)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

omit admission certification in
private theorem unspent {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world (.spent (owner := owner) forest) outside)
    (valid : source.Valid outward actions phases) :
    ∃ source : Retained world forest outside, source.Valid outward actions phases := by
  cases source with
  | operations interfaces => cases interfaces with | spent rest => exact ⟨.operations rest, valid⟩
  | spent rest => exact ⟨rest, valid⟩

omit admission certification in
private theorem unrunning {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world (.running forest) outside)
    (valid : source.Valid outward actions phases) :
    ∃ source : Retained world forest outside, source.Valid outward actions phases := by
  cases source with
  | operations interfaces => cases interfaces with | running rest => exact ⟨.operations rest, valid⟩
  | running rest => exact ⟨rest, valid⟩

/-- Reconstruct original capability source by mutual induction on the structural
checks. Metadata is canonicalized using the existing normalization; the plan,
forest, receiver, owner phases and declaration policy stay fixed. This derives
no changed-receiver check and assumes no future execution certificate. -/
theorem source_of_schedule_all (outward : List Instance) (actions : Syntax.UsageTickets)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    (∀ phases world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints),
      Local outward actions phases world plan forest → ∀ bounds : Annotation world plan,
      ∃ source : Code world plan forest,
        source.Valid outward actions phases ∧ ofCode source = bounds.normalize) ∧
    (∀ phases world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints),
      Pending outward actions phases world forest outside → ∀ bounds : SourceBoundSnapshots.Retained world forest,
      ∃ source : Retained world forest outside,
        source.Valid outward actions phases ∧ ofCapability source = bounds.normalize) := by
  constructor
  all_goals first
    | (intro phases world dependencies scope hints plan forest checked
       apply Local.rec
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           ∀ bounds : Annotation world plan, ∃ source : Code world plan forest,
             source.Valid outward actions phases ∧ ofCode source = bounds.normalize)
         (motive_2 := fun phases world {scope outsideScope hints outsideHints} forest outside _ =>
           ∀ bounds : SourceBoundSnapshots.Retained world forest, ∃ source : Retained world forest outside,
             source.Valid outward actions phases ∧ ofCapability source = bounds.normalize)
         (t := checked))
    | (intro phases world scope outsideScope hints outsideHints forest outside checked
       apply Pending.rec
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           ∀ bounds : Annotation world plan, ∃ source : Code world plan forest,
             source.Valid outward actions phases ∧ ofCode source = bounds.normalize)
         (motive_2 := fun phases world {scope outsideScope hints outsideHints} forest outside _ =>
           ∀ bounds : SourceBoundSnapshots.Retained world forest, ∃ source : Retained world forest outside,
             source.Valid outward actions phases ∧ ofCapability source = bounds.normalize)
         (t := checked))
  all_goals intros
  all_goals first
    | (rename_i bounds; guard_hyp bounds : Annotation _ .pure; cases bounds; exact ⟨.operations [] .pure .pure, rfl, rfl⟩)
    | (rename_i bounds; guard_hyp bounds : SourceBoundSnapshots.Retained _ .nil; cases bounds; exact ⟨.operations .nil, rfl, rfl⟩)
    | (rename_i first second ihFirst ihSecond bounds
       guard_hyp bounds : Annotation _ (.sequence _ _)
       cases bounds with
       | absent =>
         obtain ⟨a, ar, ab⟩ := ihFirst .absent
         obtain ⟨b, br, bb⟩ := ihSecond .absent
         exact ⟨.sequence a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩
       | sequence first second =>
         obtain ⟨a, ar, ab⟩ := ihFirst first
         obtain ⟨b, br, bb⟩ := ihSecond second
         exact ⟨.sequence a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩)
    | (rename_i first second ihFirst ihSecond bounds
       guard_hyp bounds : Annotation _ (.choice _ _)
       cases bounds with
       | absent =>
         obtain ⟨a, ar, ab⟩ := ihFirst .absent
         obtain ⟨b, br, bb⟩ := ihSecond .absent
         exact ⟨.choice a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩
       | choice first second =>
         obtain ⟨a, ar, ab⟩ := ihFirst first
         obtain ⟨b, br, bb⟩ := ihSecond second
         exact ⟨.choice a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩)
    | (rename_i recipes certified supplied body ih bounds
       guard_hyp bounds : Annotation _ (.handler _ _ _)
       cases bounds with
       | absent =>
         obtain ⟨a, ar, ab⟩ := ih .absent
         exact ⟨.handler (project recipes) a none, ⟨supplied, ar⟩, by simp only [ofCode, ab]; rfl⟩
       | handler recorded body =>
         obtain ⟨a, ar, ab⟩ := ih body
         exact ⟨.handler (project recipes) a recorded, ⟨supplied, ar⟩, by simp only [ofCode, ab]; rfl⟩)
    | (rename_i body callback ihBody ihCallback bounds
       guard_hyp bounds : Annotation _ (.cleanup _ _)
       cases bounds with
       | absent =>
         obtain ⟨a, ar, ab⟩ := ihBody .absent
         obtain ⟨b, br, bb⟩ := ihCallback .absent
         exact ⟨.cleanup a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩
       | cleanup body callback =>
         obtain ⟨a, ar, ab⟩ := ihBody body
         obtain ⟨b, br, bb⟩ := ihCallback callback
         exact ⟨.cleanup a b, ⟨ar, br⟩, by simp only [ofCode, ab, bb]; rfl⟩)
    | (rename_i body ih bounds
       guard_hyp bounds : Annotation _ (.resource _)
       cases bounds with
       | absent =>
         let a := fun identity fresh => Classical.choose (ih identity fresh .absent)
         refine ⟨.resource a, (fun identity fresh => (Classical.choose_spec (ih identity fresh .absent)).1), ?_⟩
         change Annotation.resource _ = Annotation.resource _
         congr 1
         funext identity fresh
         exact (Classical.choose_spec (ih identity fresh .absent)).2
       | resource bodies =>
         let a := fun identity fresh => Classical.choose (ih identity fresh (bodies identity fresh))
         refine ⟨.resource a, (fun identity fresh => (Classical.choose_spec (ih identity fresh (bodies identity fresh))).1), ?_⟩
         change Annotation.resource _ = Annotation.resource _
         congr 1
         funext identity fresh
         exact (Classical.choose_spec (ih identity fresh (bodies identity fresh))).2)
    | (rename_i code tail ihCode ihTail bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.plain _ _)
       cases bounds with
       | plain code tail =>
         obtain ⟨a, ar, ab⟩ := ihCode code
         obtain ⟨b, br, bb⟩ := ihTail tail
         exact ⟨.plain a b, ⟨ar, br⟩, by simp only [ofCapability, ab, bb]; rfl⟩)
    | (rename_i supplied tail ih bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.handler _)
       cases bounds with
       | handler tail =>
         obtain ⟨a, ar, ab⟩ := ih tail
         exact ⟨.handler a, ⟨supplied, ar⟩, by simp only [ofCapability, ab]; rfl⟩)
    | (rename_i tail ih bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.cell _)
       cases bounds with
       | cell tail =>
         obtain ⟨a, ar, ab⟩ := ih tail
         exact ⟨.cell a, ar, by simp only [ofCapability, ab]; rfl⟩)
    | (rename_i code tail ihCode ihTail bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.cleanup _ _)
       cases bounds with
       | cleanup code tail =>
         obtain ⟨a, ar, ab⟩ := ihCode code
         obtain ⟨b, br, bb⟩ := ihTail tail
         exact ⟨.cleanup a b, ⟨ar, br⟩, by simp only [ofCapability, ab, bb]; rfl⟩)
    | (rename_i tail ih bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.running _)
       cases bounds with
       | running tail =>
         obtain ⟨a, ar, ab⟩ := ih tail
         exact ⟨.running a, ar, by simp only [ofCapability, ab]; rfl⟩)
    | (rename_i saved tail ihSaved ihTail bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.live _ _)
       cases bounds with
       | live saved tail =>
         obtain ⟨a, ar, ab⟩ := ihSaved saved
         obtain ⟨b, br, bb⟩ := ihTail tail
         exact ⟨.live a b, ⟨ar, br⟩, by simp only [ofCapability, ab, bb]; rfl⟩)
    | (rename_i tail ih bounds
       guard_hyp bounds : SourceBoundSnapshots.Retained _ (.spent _)
       cases bounds with
       | spent tail =>
         obtain ⟨a, ar, ab⟩ := ih tail
         exact ⟨.spent a, ar, by simp only [ofCapability, ab]; rfl⟩)
    | (rename_i scope phases world effect operation hints forest checked scheduled ih bounds
       guard_hyp bounds : Annotation _ .request
       cases bounds
       have guarded := SourceDependencySchemes.checked_request checked
       cases SourceDependencyCapture.check_capture_iff.mp guarded with
       | builtin found =>
         refine ⟨.operations [(effect, operation)] .request .request, ?_, rfl⟩
         apply SourceContextualRequirements.check_requirements_iff.mpr
         intro request member
         cases List.mem_singleton.mp member
         exact .builtin found
       | handler found permission row body closing =>
         obtain ⟨savedHints, waitingHints, hintCut⟩ := SourcePlannedCuts.of_lookup hints found
         obtain ⟨saved, waiting, cut⟩ := SourceScheduledNeutral.of_cut hintCut forest
         let closingSource := fun disposes => Classical.choose
           (ih _ _ _ _ _ _ hintCut saved waiting cut.forest disposes (.absent saved.forClosing))
         refine ⟨.selected cut (SourceDependencySchemes.checked_request_owners checked found) closingSource,
           ⟨guarded, ?_⟩, rfl⟩
         intro disposes
         exact (Classical.choose_spec
           (ih _ _ _ _ _ _ hintCut saved waiting cut.forest disposes (.absent saved.forClosing))).1)
    | (rename_i scope owner phases world hints forest selected front saved tail found access same restored ih bounds
       guard_hyp access : SourceContextualInvocations.Resume _ _ _ _ _
       cases bounds
       obtain ⟨actualFront, actualSaved, actualTail, cut⟩ := SourceScheduledNeutral.of_owner forest found
       obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (same.symm.trans cut.forest))
       obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
       cases frontSame; cases savedSame; cases tailSame
       obtain ⟨source, valid, _⟩ := ih (.absent _)
       obtain ⟨inside, caller, insideReady, callerReady, _⟩ :=
         retained_split_retaining saved (front.append (.spent tail)) source valid
       obtain ⟨inside, insideReady, _⟩ :=
         (retained_receiver_nil_bounds (front.append (.spent tail)) _).mp ⟨inside, insideReady, rfl⟩
       obtain ⟨before, after, beforeReady, afterReady, _⟩ :=
         retained_split_retaining front (.spent tail) caller callerReady
       obtain ⟨before, beforeReady, _⟩ :=
         (retained_receiver_nil_bounds (.spent tail) _).mp ⟨before, beforeReady, rfl⟩
       obtain ⟨after, afterReady⟩ := unspent after afterReady
       refine ⟨.resume cut inside before after, ?_, rfl⟩
       have allowed : ∀ {after}, SourceDependencyCapture.ResumeChecked actions phases owner scope after →
           (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available := by
         intro after permitted
         cases permitted with
         | checked located known permission available => exact ⟨by simp [known, permission], available⟩
       generalize result : SourceContextualInvocationHints.Selection.resumed owner selected = output at access
       cases access with
       | checked located access compatible =>
         exact ⟨(allowed access).1, (allowed access).2, insideReady, beforeReady, afterReady⟩)
    | (rename_i scope owner phases world hints forest selected front saved tail found access same scheduled ih bounds
       guard_hyp access : SourceContextualInvocations.Dispose _ _ _ _ _ _
       cases bounds
       obtain ⟨actualFront, actualSaved, actualTail, cut⟩ := SourceScheduledNeutral.of_owner forest found
       obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (same.symm.trans cut.forest))
       obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
       cases frontSame; cases savedSame; cases tailSame
       obtain ⟨source, valid, _⟩ := ih (.absent _)
       obtain ⟨closing, caller, closingReady, callerReady, _⟩ :=
         retained_split_retaining saved.forClosing (.running (front.append (.spent tail))) source valid
       obtain ⟨closing, closingReady, _⟩ :=
         (retained_receiver_nil_bounds (.running (front.append (.spent tail))) _).mp ⟨closing, closingReady, rfl⟩
       obtain ⟨caller, callerReady⟩ := unrunning caller callerReady
       obtain ⟨before, after, beforeReady, afterReady, _⟩ :=
         retained_split_retaining front (.spent tail) caller callerReady
       obtain ⟨before, beforeReady, _⟩ :=
         (retained_receiver_nil_bounds (.spent tail) _).mp ⟨before, beforeReady, rfl⟩
       obtain ⟨after, afterReady⟩ := unspent after afterReady
       refine ⟨.dispose cut closing before after, ?_, rfl⟩
       have allowed : ∀ {after}, SourceDependencyCapture.DisposeChecked outward actions phases owner scope after →
           (actions owner).any (fun rights => rights.dispose) = true ∧ phases owner = .available ∧
           selected.scopes.captured.held = false ∧
           SourceDependencyCapture.checkClosing outward selected.scopes.captured.shape [] [] = true := by
         intro after permitted
         cases permitted with
         | checked located known permission available unprotected closingRoute =>
           cases Option.some.inj ((SourceContextualInvocationHints.selected_cut found).lookup.symm.trans located.lookup)
           exact ⟨by simp [known, permission], available, unprotected,
             SourceDependencyCapture.check_closing_iff.mpr closingRoute⟩
       generalize result : SourceContextualInvocationHints.Selection.disposed owner selected = output at access
       cases access with
       | checked located access compatible =>
         exact ⟨(allowed access).1, (allowed access).2.1, (allowed access).2.2.1,
           (allowed access).2.2.2, closingReady, beforeReady, afterReady⟩)
end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.source_of_schedule_all

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceBoundSnapshots.Retained (ofCapability)
variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The original request and pending checks supply capture source, including
canonical closing metadata. The existing cut split and normalization laws do
the reconstruction; selected-clause rechecking remains a separate obligation. -/
theorem CaptureSource.of_schedule
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (requested : SourceScheduledChecks.Local outward actions phases world
      (.request (effect := effect) (operation := operation)) whole)
    (pending : SourceScheduledChecks.Pending outward actions phases world whole .nil)
    (bounds : SourceBoundSnapshots.Retained world whole)
    (permits : rights.dispose = true → offered.dispose = true) :
    ∃ source : Retained world whole .nil,
      ofCapability source = bounds.normalize ∧
      Nonempty (CaptureSource outward actions phases cut source rights) := by
  cases cut.erase.reconstruct_scope
  cases cut.erase.hints
  have forestSame := eq_of_heq cut.forest
  cases forestSame
  obtain ⟨source, sourceReady, origin⟩ :=
    (source_of_schedule_all outward actions project).2 phases world _ _ pending bounds
  obtain ⟨inside, after, insideReady, afterReady, original⟩ :=
    retained_at_cut_retaining cut source sourceReady
  have normal : ((ofCapability inside).append (ofCapability after)).normalize =
      (ofCapability inside).append (ofCapability after) := by
    rw [eq_of_heq original, origin]
    exact SourceBoundSnapshots.Retained.normalize_idempotent
  have pieces := congrArg (fun bounds => bounds.splitAt saved waiting) normal
  simp only [SourceBoundSnapshots.Retained.normalize_append,
    SourceBoundSnapshots.Retained.splitAt_join, Prod.mk.injEq] at pieces
  cases requested with
  | request checked scheduled =>
    refine ⟨source, origin, ⟨⟨sourceReady,
      SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request checked),
      inside, after, insideReady, afterReady, original, ?_⟩⟩⟩
    intro permission
    obtain ⟨closing, ready, metadata⟩ :=
      (source_of_schedule_all outward actions project).2 phases world _ _
        (scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest (permits permission))
        (ofCapability inside).forClosing
    refine ⟨closing, ready, ?_⟩
    exact metadata.trans ((SourceBoundSnapshots.Retained.normalize_forClosing _).trans
      (congrArg SourceBoundSnapshots.Retained.forClosing pieces.1))
end Ash.OneShot.SourceScheduledCapabilityAnnotations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.of_schedule
