import SourceConsumingStructuralCapture
import SourceScheduledCaptureSource
import SourceConsumingCleanupAdmission
import SourceScheduledCaptureRetention
import SourceConsumingSelectedSource
import SourceAnnotatedStoredCertifiedCapture

/-! Generate a capture certificate from the current source and the exact
selected consuming declaration. Bounds are retained independently through the
actual cut. This replaces successful target-certificate validation at this
boundary with contextual structural admission; reachable admission remains open. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource Generated)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource DeclarationPolicy DeclarationLaws)
open SourceDependencyOwners (owners)
open SourcePlannedRecipeDeclarations (Selected)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]

/-- A capture has no caller frames before its newly introduced owner. -/
theorem Context.before_nil
    (context : Context world owner outward actions phases whole .nil saved waiting) :
    context.before = .nil := by
  cases context.before
  rfl

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Use the original source split and its checked canonical closing annotation. The
structural capture guard derives disposal protection and routing obligations.
The new context contains no selected clause code and assumes no validity of the
future clause annotation. -/
theorem Context.request_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (source : Retained world whole .nil)
    (rights : Syntax.OneShotRights)
    (captureSource : CaptureSource outward actions phases cut source rights)
    (permits : rights.dispose = true → offered.dispose = true)
    (fresh : actions owner = none) (absent : owner ∉ owners wholeScope) :
    ∃ context : Context world owner outward (actions.insert owner rights) (introduce phases owner)
      (.live (owner := owner) saved waiting) .nil saved waiting, ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
      HEq (savedBounds.append (SourceBoundSnapshots.Retained.ofCapability context.after))
        (SourceBoundSnapshots.Retained.ofCapability source) ∧
      (∀ permission, SourceBoundSnapshots.Retained.ofCapability (context.resumption permission).val = savedBounds) ∧
      ∀ permission, SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val = savedBounds.forClosing := by
  have disposal : rights.dispose = true → savedScope.held = false ∧
      SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true := by
    intro permission
    obtain ⟨unprotected, route, _⟩ := SourceDependencyCapture.disposing_capture
      (SourceDependencyCapture.check_capture_iff.mpr captureSource.guarded) cut.erase.lookup (permits permission)
    exact ⟨unprotected, SourceDependencyCapture.check_closing_iff.mpr route⟩
  have partsAbsent : owner ∉ owners (savedScope.append waitingScope) :=
    by simpa only [cut.erase.reconstruct_scope] using absent
  obtain ⟨context, resumed, closed, tail⟩ := Context.capture_canonical laws project
    captureSource.inside captureSource.after captureSource.insideReady captureSource.closing disposal
    captureSource.tailReady fresh partsAbsent
  refine ⟨context, SourceBoundSnapshots.Retained.ofCapability captureSource.inside, ?_, resumed, closed⟩
  exact (heq_of_eq (congrArg (fun after =>
    (SourceBoundSnapshots.Retained.ofCapability captureSource.inside).append after) tail)).trans captureSource.original

/-- Choose the context together with its exact saved/waiting metadata origin. -/
noncomputable def Context.of_request
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (source : Retained world whole .nil)
    (rights : Syntax.OneShotRights)
    (captureSource : CaptureSource outward actions phases cut source rights)
    (permits : rights.dispose = true → offered.dispose = true)
    (fresh : actions owner = none) (absent : owner ∉ owners wholeScope) :
    Context world owner outward (actions.insert owner rights) (introduce phases owner)
      (.live (owner := owner) saved waiting) .nil saved waiting :=
  Classical.choose (Context.request_bounds laws project cut source rights captureSource permits fresh absent)

/-- The context used for clause admission retains the actual source split.
This authenticates both resumption metadata and canonical closing metadata. -/
theorem Context.of_request_bounds
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (source : Retained world whole .nil)
    (rights : Syntax.OneShotRights)
    (captureSource : CaptureSource outward actions phases cut source rights)
    (permits : rights.dispose = true → offered.dispose = true)
    (fresh : actions owner = none) (absent : owner ∉ owners wholeScope) :
    let context := Context.of_request laws project cut source rights captureSource permits fresh absent
    ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
      HEq (savedBounds.append (SourceBoundSnapshots.Retained.ofCapability context.after))
        (SourceBoundSnapshots.Retained.ofCapability source) ∧
      (∀ permission, SourceBoundSnapshots.Retained.ofCapability (context.resumption permission).val = savedBounds) ∧
      ∀ permission, SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val = savedBounds.forClosing :=
  Classical.choose_spec (Context.request_bounds laws project cut source rights captureSource permits fresh absent)

/-- Runtime capture and the actual contextual source evidence use the same
saved/waiting metadata. Every permitted disposal uses the canonical closing. -/
theorem Context.of_request_snapshot
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotReady : snapshot.Admitted)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (source : Retained world snapshot.forest .nil)
    (rights : Syntax.OneShotRights)
    (captureSource : CaptureSource outward actions phases cut source rights)
    (permits : rights.dispose = true → offered.dispose = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (aligned : SourceBoundSnapshots.Retained.ofCapability source = snapshot.pending)
    {plan : Plan dependencies} (current : SourcePlanBounds.Annotation world plan) (currentReady : current.Admitted) :
    let context := Context.of_request laws project cut source rights captureSource permits fresh absent
    ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
      let captured : SourceBoundSnapshots.Snapshot world :=
        ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
          .live savedBounds (SourceBoundSnapshots.Retained.ofCapability context.after)⟩
      SourceBoundSnapshots.Captured owner snapshot captured ∧ captured.Admitted ∧
      (∀ permission, SourceBoundSnapshots.Retained.ofCapability (context.resumption permission).val = savedBounds) ∧
      ∀ permission,
        let closed := SourceBoundSnapshots.Snapshot.value
          ((SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val).append
            (.running (.spent (owner := owner) (SourceBoundSnapshots.Retained.ofCapability context.after))))
        SourceBoundSnapshots.Discarded owner captured closed ∧ closed.Admitted := by
  let context := Context.of_request laws project cut source rights captureSource permits fresh absent
  obtain ⟨savedBounds, kept, resumption, closing⟩ :=
    Context.of_request_bounds laws project cut source rights captureSource permits fresh absent
  have moved := SourceScheduledCapabilityAnnotations.capture_snapshot_from_parts (owner := owner)
    snapshot cut savedBounds (SourceBoundSnapshots.Retained.ofCapability context.after)
    (kept.trans (heq_of_eq aligned)) current
  have admitted := moved.admitted snapshotReady currentReady
  refine ⟨savedBounds, moved, admitted, resumption, ?_⟩
  intro permission
  have discarded := context.discarded_of_closing savedBounds permission (closing permission) current
  exact ⟨discarded, discarded.admitted admitted⟩

/-- Compile the selected stored source. The original request supplies its own
saved/closing evidence; the selected declaration supplies finite requirements
and nested bounds. The contextual premise is the structural source judgment,
not an already-valid target code or capture certificate. -/
theorem SelectedSource.capture_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (contextual : At laws project body
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent)) :
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation ∧
      (SourcePlanBounds.ofCode annotation).Admitted ∧
      SourceBoundSnapshots.CapturedBounds snapshot owner (bodies owner) (.live (owner := owner) saved waiting) ∧
      Generated (actions.insert owner code.requiredActions) (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent).continuationBounds body annotation := by
  obtain ⟨contract, needed, _, admitted, included, nested⟩ := selectedSource.admitted bounded
  have checked := admitted.at_capture (actions := actions.insert owner code.requiredActions)
    (phases := introduce phases owner) (captured := savedScope)
    (by simp [Syntax.UsageTickets.insert])
    (by simp [introduce]) (SourceContextualRequirements.check_requirements_subset included supplied)
  obtain ⟨annotation, ready, generated⟩ := contextual.generate_source (resumeRequired := contract.resume) (closeRequired := contract.close)
    (by simpa only [Context.before_nil] using checked)
  have kept := generated.current_bounds
  have boundsAdmitted := kept.symm ▸ nested.boundAnnotation_admitted
  obtain ⟨pending, moved⟩ := SourceBoundSnapshots.capture_snapshot snapshot cut (SourcePlanBounds.ofCode annotation)
  exact ⟨annotation, ready, kept, boundsAdmitted, ⟨_, pending, moved, moved.admitted snapshotAdmitted boundsAdmitted⟩, generated⟩

/-- Preserve the previous capture API as a projection of generated-source
correspondence; no independent clause compiler or proof is used. -/
theorem SelectedSource.capture_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (contextual : At laws project body
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent)) :
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation ∧
      (SourcePlanBounds.ofCode annotation).Admitted ∧
      SourceBoundSnapshots.CapturedBounds snapshot owner (bodies owner) (.live (owner := owner) saved waiting) := by
  obtain ⟨annotation, ready, kept, admitted, captured, _⟩ :=
    SelectedSource.capture_source laws project snapshot snapshotAdmitted bounded cut selected selectedSource
      source captureSource permits supplied fresh absent contextual
  exact ⟨annotation, ready, kept, admitted, captured⟩

/-- The emitted clause and the captured runtime snapshot share the actual
source split. The original source/snapshot alignment is explicit. Every permitted disposal of that context has canonical closing metadata and
an admitted runtime disposal snapshot. -/
theorem SelectedSource.capture_source_snapshot
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (contextual : At laws project body
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent))
    (aligned : SourceBoundSnapshots.Retained.ofCapability source = snapshot.pending) :
    let context := (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent)
    ∃ annotation : Code world (bodies owner) (.live (owner := owner) saved waiting),
      (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).Valid outward actions phases ∧
      Generated (actions.insert owner code.requiredActions) context.continuationBounds body annotation ∧
      ∃ savedBounds : SourceBoundSnapshots.Retained world saved,
        let captured : SourceBoundSnapshots.Snapshot world :=
          ⟨_, bodies owner, SourcePlanBounds.ofCode annotation, _, _, .live (owner := owner) saved waiting,
            .live savedBounds (SourceBoundSnapshots.Retained.ofCapability context.after)⟩
        SourceBoundSnapshots.Captured owner snapshot captured ∧ captured.Admitted ∧
        (∀ permission, context.continuationBounds.resumption permission = savedBounds) ∧
        ∀ permission,
          let closed := SourceBoundSnapshots.Snapshot.value
            ((SourceBoundSnapshots.Retained.ofCapability (context.closing permission).val).append
              (.running (.spent (owner := owner) (SourceBoundSnapshots.Retained.ofCapability context.after))))
          SourceBoundSnapshots.Discarded owner captured closed ∧ closed.Admitted := by
  obtain ⟨annotation, ready, _, boundsAdmitted, _, generated⟩ :=
    SelectedSource.capture_source laws project snapshot snapshotAdmitted bounded cut selected selectedSource
      source captureSource permits supplied fresh absent contextual
  obtain ⟨savedBounds, moved, admitted, kept, closing⟩ := Context.of_request_snapshot laws project snapshot snapshotAdmitted
    cut source code.requiredActions captureSource permits fresh absent aligned
    (SourcePlanBounds.ofCode annotation) boundsAdmitted
  exact ⟨annotation, ready, generated, savedBounds, moved, admitted, kept, closing⟩

/-- The result feeds the existing allocator's certificate boundary directly. -/
theorem SelectedSource.capture_certificate
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (contextual : At laws project body
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent)) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code snapshot.forest, certificate.Valid outward actions phases := by
  obtain ⟨annotation, ready, _⟩ := SelectedSource.capture_retaining laws project snapshot snapshotAdmitted bounded cut selected selectedSource
    source captureSource permits supplied fresh absent contextual
  exact ⟨.site cut selected annotation, ready⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.of_request
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_retaining
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_certificate

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.before_nil

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.request_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.of_request_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.of_request_snapshot

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_source_snapshot
