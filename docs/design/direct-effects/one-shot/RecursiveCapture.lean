import RecursiveContexts

/-!
Fresh capture from the actual selected handler cut. Saved and surviving source
segments determine the new resume template and retain every nested record.
Handler-clause admission and closing-template construction are separate joins.
-/

namespace Ash.OneShot.RecursiveCapture
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression Segment)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll)

theorem owned_registered
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (member : owner ∈ ownedTickets stack) : ∃ contract, contracts owner = some contract := by
  induction source with
  | nil => cases member
  | push head tail ih =>
      cases head with
      | plain | handler | cell | armed | running | closing => exact ih member
      | retiring known =>
          rcases List.mem_cons.mp member with same | member
          · subst_vars; exact ⟨_, known⟩
          · exact ih member
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | member
      · subst_vars; exact ⟨_, known⟩
      · rcases List.mem_append.mp member with inside | outside
        · exact ihSaved inside
        · exact ihTail outside
  | spent known answerAnnotation scopeKnown tail ih => exact ih member

theorem fresh_unowned
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (fresh : contracts owner = none) : owner ∉ ownedTickets stack := by
  intro member
  obtain ⟨contract, known⟩ := owned_registered source member
  rw [fresh] at known
  cases known

/-- The source segment judgment with structural evidence at every frame,
    including dormant saved segments. Erasure recovers the existing judgment. -/
inductive AnnotatedSegment (predicate : ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → Prop) (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → Prop where
  | nil : AnnotatedSegment predicate operations policy contracts tables world .nil result result [] (.request [] []) []
  | push (current : predicate entry input middle headDemand first) (head : SourceTemplates.Frame operations policy contracts world entry input middle headDemand first)
      (tail : AnnotatedSegment predicate operations policy contracts tables world rest middle output tailDemand second records) :
      AnnotatedSegment predicate operations policy contracts tables world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records
  | live (known : contracts owner = some contract)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : AnnotatedSegment predicate operations policy contracts tables world capture contract.input contract.answer contract.resumeDemand body nested)
      (tail : AnnotatedSegment predicate operations policy contracts tables world rest contract.answer output demand requirements remaining) :
      AnnotatedSegment predicate operations policy contracts tables world (.live owner inputType answerType capture caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining))
  | spent (known : contracts owner = some contract)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (tail : AnnotatedSegment predicate operations policy contracts tables world rest contract.answer output demand requirements records) :
      AnnotatedSegment predicate operations policy contracts tables world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records


theorem AnnotatedSegment.erase
    (source : AnnotatedSegment predicate operations policy contracts tables world stack input output demand requirements records) :
    Segment operations policy contracts tables world stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push current head tail ih => exact .push head ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih => exact .spent known answerAnnotation scopeKnown ih

theorem AnnotatedSegment.trivial
    (source : Segment operations policy contracts tables world stack input output demand requirements records) :
    AnnotatedSegment (fun _ _ _ _ _ => True) operations policy contracts tables world stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push True.intro head ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih => exact .spent known answerAnnotation scopeKnown ih

theorem AnnotatedSegment.extension
    (source : AnnotatedSegment predicate operations policy contracts tables world stack input output demand requirements records)
    (extension : contracts.Extends larger)
    (transfer : ∀ entry input output demand requirements, predicate entry input output demand requirements → nextPredicate entry input output demand requirements) :
    AnnotatedSegment nextPredicate operations policy larger tables world stack input output demand requirements records := by
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  induction source with
  | nil => exact .nil
  | push current head tail ih => exact .push (transfer _ _ _ _ _ current) (SourceTemplates.frame_extension head extension) ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live (extension _ _ known) inputAnnotation answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types) held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih =>
      exact .spent (extension _ _ known) answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types) ih

theorem AnnotatedSegment.world_weaken
    (source : AnnotatedSegment predicate operations policy contracts tables world stack input output demand requirements records)
    (larger : world ⊆ next)
    (transfer : ∀ entry input output demand requirements, predicate entry input output demand requirements → nextPredicate entry input output demand requirements) :
    AnnotatedSegment nextPredicate operations policy contracts tables next stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push current head tail ih => exact .push (transfer _ _ _ _ _ current) (SourceTemplates.frame_world_weaken head larger) ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih => exact .spent known answerAnnotation scopeKnown ih

theorem capture_segments_with_frames
    (cut : HandlerCut requested whole capture tail handler)
    (source : AnnotatedSegment predicate operations policy contracts tables world whole input output demand requirements records) :
    ∃ (answer : Value) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store),
      answer.port = ScopedPorts.eraseType handler.answer ∧ predicate (.handler handler) answer answer [] (.request [] []) ∧
      AnnotatedSegment predicate operations policy contracts tables world capture input answer capturedDemand capturedRequirements capturedRecords ∧
      AnnotatedSegment predicate operations policy contracts tables world tail answer output tailDemand tailRequirements tailRecords ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records with
  | hit handler tail same => cases source with
    | push current head rest => cases head with
      | handler typed annotation =>
          refine ⟨_, [], _, _, _, [], _, annotation, current, .push current (.handler typed annotation) .nil, rest, rfl, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current head rest =>
        obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, _, tailDemand, _, tailReq, capRecords, tailRecords, annotation, selected, .push current head saved, outside,
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known inputAnnotation answerAnnotation scopeKnown held historical rest =>
        obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, capDemand, tailDemand, _, tailReq, _, tailRecords, annotation, selected,
          .live known inputAnnotation answerAnnotation scopeKnown held historical saved, outside,
          sameDemand, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest =>
        obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, annotation, selected,
          .spent known answerAnnotation scopeKnown saved, outside, sameDemand, sameRecords, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]

theorem capture_segments
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records) :
    ∃ (answer : Value) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store),
      answer.port = ScopedPorts.eraseType handler.answer ∧
      Segment operations policy contracts tables world capture input answer capturedDemand capturedRequirements capturedRecords ∧
      Segment operations policy contracts tables world tail answer output tailDemand tailRequirements tailRecords ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ :=
    capture_segments_with_frames cut (AnnotatedSegment.trivial source)
  exact ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, saved.erase, outside.erase, sameDemand, sameRecords, evaluation⟩

theorem capture_segments_checked_with_frames
    (cut : HandlerCut requested whole capture tail handler)
    (source : AnnotatedSegment predicate operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked store receiving before requirements row) :
    ∃ (answer : Value) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedRow tailRow : Footprint),
      answer.port = ScopedPorts.eraseType handler.answer ∧ predicate (.handler handler) answer answer [] (.request [] []) ∧
      AnnotatedSegment predicate operations policy contracts tables world capture input answer capturedDemand capturedRequirements capturedRecords ∧
      AnnotatedSegment predicate operations policy contracts tables world tail answer output tailDemand tailRequirements tailRecords ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧ row = capturedRow ++ tailRow ∧
      Checked store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements capturedRow ∧
      Checked store receiving (spendAll before capturedDemand) tailRequirements tailRow := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := capture_segments_with_frames cut source
  have original := RecursiveRequirements.checked_complete checked
  rw [evaluation] at original
  obtain ⟨capturedRow, tailRow, inside, rest, sameRow⟩ := PhaseRechecking.merge_split original
  exact ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capturedRow, tailRow,
    annotation, selected, saved, outside, sameDemand, sameRecords, sameRow,
    RecursiveRequirements.evaluate_sound inside, RecursiveRequirements.evaluate_sound rest⟩

theorem capture_segments_checked
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked records receiving before requirements row) :
    ∃ (answer : Value) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedRow tailRow : Footprint),
      answer.port = ScopedPorts.eraseType handler.answer ∧
      Segment operations policy contracts tables world capture input answer capturedDemand capturedRequirements capturedRecords ∧
      Segment operations policy contracts tables world tail answer output tailDemand tailRequirements tailRecords ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧ row = capturedRow ++ tailRow ∧
      Checked records (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements capturedRow ∧
      Checked records receiving (spendAll before capturedDemand) tailRequirements tailRow := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, saved, outside, sameDemand, sameRecords, evaluation⟩ := capture_segments cut source
  have original := RecursiveRequirements.checked_complete checked
  rw [evaluation] at original
  obtain ⟨capturedRow, tailRow, inside, rest, sameRow⟩ := PhaseRechecking.merge_split original
  exact ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capturedRow, tailRow,
    annotation, saved, outside, sameDemand, sameRecords, sameRow,
    RecursiveRequirements.evaluate_sound inside, RecursiveRequirements.evaluate_sound rest⟩

theorem capture_owned
    (cut : HandlerCut requested whole capture tail handler) :
    ownedTickets (.live owner input handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  rw [handler_cut_reconstructs cut, owned_tickets_append]
  rfl

theorem capture_unique
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none) :
    (ownedTickets (.live owner inputType handler.answer capture handler.scope tail)).Nodup := by
  rw [capture_owned cut]
  exact List.nodup_cons.mpr ⟨fresh_unowned source fresh, unique⟩

theorem capture_phase_consumed
    (cut : HandlerCut requested whole capture tail handler)
    (absent : owner ∉ ownedTickets whole) :
    OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner input handler.answer capture handler.scope tail))) owner =
      OwnerPhaseTransitions.available (ownedTickets whole) := by
  rw [capture_owned cut]
  exact OwnerPhaseTransitions.spend_available_cons absent

theorem lookup_insert_other (different : key.owner ≠ owner) :
    RecursiveRequirements.lookup key ((⟨owner, mode⟩, body) :: records) = RecursiveRequirements.lookup key records := by
  have notKey : key ≠ ⟨owner, mode⟩ := fun same => different (congrArg RecursiveRequirements.Key.owner same)
  simp only [RecursiveRequirements.lookup, if_neg notKey]

theorem checked_insert_consumed
    (checked : Checked records receiving before requirements row) (consumed : before owner = .consumed) :
    Checked ((⟨owner, mode⟩, body) :: records) receiving before requirements row := by
  apply RecursiveTransport.checked_transport checked _ rfl
  intro key available
  have different : key.owner ≠ owner := by
    intro same
    rw [same, consumed] at available
    cases available
  exact (lookup_insert_other different).symm

theorem capture_record
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked records [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capRow, tailRow,
    annotation, saved, outside, sameDemand, sameRecords, sameRow, savedCheck, tailCheck⟩ := capture_segments_checked cut source checked
  let contract : Owners.Contract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
    capDemand, capRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  have extension := Owners.insert_extends (contract := contract) contracts fresh
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  have scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types handler.scope := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports source)
    cases handlerTyped with
    | handler known clauses coverage unique => exact known
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp only [OwnerPhaseTransitions.available, if_neg (fresh_unowned source fresh)]
  have consumedLater : spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  refine ⟨contract, capReq, tailDemand, tailReq, tailRow, rfl, annotation, rfl, rfl, rfl, rfl,
    sameDemand, sameRow, ?_, ?_, checked_insert_consumed tailCheck consumedLater, capture_unique cut source unique fresh,
    OwnerPhaseTransitions.capture_map cut⟩
  · rw [sameRecords]
    exact .live known (ScopedPorts.erase_embed_port input.port).symm annotation
      (ScopedPorts.scope_known_extension scopeKnown types) rfl
      (SourceTemplates.segment_extension saved extension) (SourceTemplates.segment_extension outside extension)
  · exact checked_insert_consumed (by simpa only [List.append_nil] using savedCheck) consumed

/-- The newly captured body supplies the check of an immediate resume clause.
    This joins the record with a concrete clause shape; arbitrary clauses still
    need their structural admission rule. -/
theorem fresh_resume_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (reply : SourceTemplates.ValueSummary operations policy contracts world Environment.empty allowed response contract.input)
    (permission : (policy binder).resume = true) (admitted : contract.resumeEffects ⊆ allowed)
    (formed : ScopedPorts.InWorld world contract.answer.port)
    (accepted : checkFootprint outside (contract.resumeRow ++ tailRow) = true) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside (.ticket binder owner)
      (.resume binder response) (.live owner inputType answerType capture caller tail) output
      (owner :: contract.resumeDemand ++ tailDemand) (contract.resumeRow ++ tailRow) := by
  let initial := OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))
  let callerContext := OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)
  change OwnerPhaseTransitions.spend initial owner = before at phases
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have selectedBody : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      callerContext before capturedRequirements contract.resumeRow := by
    apply RecursiveTransport.checked_transport savedCheck (fun _ _ => rfl)
    simp only [callerContext, OwnerPhases.ofStack, RecursiveTransport.normalize, consumed, if_true]
  have ready : initial owner = .available := by simp [initial, ownedTickets, OwnerPhaseTransitions.available]
  have trace : OwnerPhaseTransitions.Trace initial (owner :: contract.resumeDemand)
      (spendAll before contract.resumeDemand) := .cons ready (phases.symm ▸ RecursiveRequirements.checked_trace savedCheck)
  have invocation : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      callerContext initial (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow := by
    apply Checked.invoke (body := capturedRequirements) (by simp [RecursiveRequirements.lookup])
      (PhaseRechecking.check_owners_iff.mpr (by simpa only [spendAll, phases] using trace))
      (by simpa only [List.nil_append, callerContext, OwnerPhases.ofStack] using
        (OwnerPhases.Consumes.hit (owner := owner) (held := ProtectionContexts.protectedMode capture.erase)
          (rest := OwnerPhases.ofStack tables tail)))
    simpa only [List.nil_append, phases] using selectedBody
  have pending : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (spendAll initial (owner :: contract.resumeDemand)) (.sequence (.spent owner) tailRequirements) tailRow := by
    have afterOwner : spendAll before contract.resumeDemand owner = .consumed :=
      OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
    have combined := Checked.sequence (Checked.spent (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
      (receiving := []) afterOwner) tailCheck
    simpa only [spendAll, phases, List.nil_append] using combined
  have current : Expression operations policy contracts world allowed (.ticket binder owner) Environment.empty
      (.resume binder response) contract.answer (owner :: contract.resumeDemand)
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) :=
    .resume known (by simp [Execution.Scope.resolve]) permission (reply.expression _) admitted formed
  have currentCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) callerContext initial
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) contract.resumeRow := by
    have combined := Checked.sequence (Checked.request (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
      (before := initial) (receiving := callerContext) (nearer := []) (raw := []) (row := [])
      (by simp [OwnerSource.exportAt, residual_empty])) invocation
    simpa only [List.nil_append] using combined
  exact .checked (.checked current (.bound (Owners.ports_lookup known)) source) unique
    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)) pending) accepted

theorem request_operand
    (source : Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect requested) operation operand) result demand requirements)
    (isValue : operand.IsValue) :
    ∃ argument, operations requested operation = some (argument, result) ∧
      SourceTemplates.ValueSummary operations policy contracts world environment allowed operand argument ∧ demand = [] := by
  generalize encoded : Instantiation.freezeEffect requested = effect at source
  cases source with
  | stable summary => cases summary with
    | perform known admitted operand formed =>
        cases freeze_effect_injective encoded
        exact ⟨_, known, .stable (CoherentSourceTypes.value_row operand isValue ▸ operand), rfl⟩
  | callable summary => cases summary with
    | summaryPerform known admitted operand formed =>
        cases freeze_effect_injective encoded
        exact ⟨_, known, .callable (CallableSources.value_row operand isValue ▸ operand), rfl⟩
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      exact ⟨_, known, RecursiveRecomposition.value_summary operand isValue,
        SourceTemplates.expression_value_demand operand isValue⟩

/-- Complete capture preservation for clauses with a stable reply followed by
    their single resume. The reply is checked as source, including substitution
    of the actual request operand. This theorem does not cover disposal clauses
    or arbitrary effectful clause bodies. -/
theorem capture_immediate_resume
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder (.resume binder reply))
    (operationKnown : operations requested operation = some (argument, input))
    (replySource : Summary operations world (Environment.empty.extend parameter argument) allowed reply input [])
    (isValue : operand.IsValue) (fresh : contracts owner = none) (permission : (policy binder).resume = true)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance)
    (admitted : resumeEffects ⊆ allowed) :
    ∃ (contract : Owners.Contract) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
        ⟨.resume binder (reply.subst parameter operand), .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      SourceTemplates.CheckedConfiguration operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
        (.resume binder (reply.subst parameter operand))
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) output (owner :: demand) nextRow ∧
      nextRow.Sublist row ∧ contract.input = input ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨actualArgument, knownOperation, operandSummary, empty⟩ := request_operand current isValue
        obtain ⟨sameArgument, sameInput⟩ := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
        obtain ⟨contract, capReq, tailDemand, tailReq, tailRow, inputSame, annotation, closeDemandSame, closeRowSame,
          resumeEffectsSame, closeEffectsSame, sameDemand, capturedRow, boundary, capCheck, tailCheck, afterUnique, map⟩ :=
          capture_record cut pending pendingCheck unique fresh closeDemand closeRow resumeEffects closeEffects
        have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
        have closed : ClosedValue operand :=
          ScopedPorts.typed_value_closed (operandSummary.ports .none) isValue
        have replyAfter : SourceTemplates.ValueSummary operations policy (contracts.insert owner contract) world Environment.empty allowed
            (reply.subst parameter operand) _ :=
          (SourceTemplates.ValueSummary.callable (SourceCallableSubstitution.callable_substitution
            (CallableSources.from_legacy replySource (fun _ _ _ _ _ _ checked => .stable checked))
            (operandSummary.change_allowed isValue allowed) closed)).extension (Owners.insert_extends contracts fresh)
        obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports pending)
        have clauseReady : ClosedExcept parameter (.resume binder reply) ∧
            ScopedPorts.InWorld world (ScopedPorts.eraseType handler.answer) := by
          cases handlerTyped with
          | handler scopeKnown clauses coverage unique =>
              obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
              exact ⟨ScopedPorts.typed_suffix_ready bodyTyped, ScopedPorts.typed_result_in_world bodyTyped⟩
        have acceptedPending : checkFootprint outside (contract.resumeRow ++ tailRow) = true := by
          rw [← capturedRow]
          exact checked_footprint_subset (sameRow ▸ accepted) (List.sublist_append_right currentRow pendingRow).subset
        have after := fresh_resume_configuration known boundary capCheck tailCheck
          (capture_phase_consumed cut (fresh_unowned pending fresh)) afterUnique
          (inputSame.symm ▸ replyAfter) permission (resumeEffectsSame.symm ▸ admitted)
          (annotation.symm ▸ clauseReady.2) acceptedPending
        refine ⟨contract, contract.resumeRow ++ tailRow, .capture requested operation parameter binder owner operand (.resume binder reply) scope whole capture tail handler
          _ cut clause closed clauseReady.1, ?_, ?_, inputSame,
          closeDemandSame, closeRowSame, resumeEffectsSame, closeEffectsSame, capture_owned cut⟩
        · simpa only [sameDemand, List.nil_append, List.cons_append] using after
        · rw [← capturedRow, sameRow]
          exact List.sublist_append_right _ _

namespace Examples
open SharedSourceSegments.Examples (operations policy contracts tables handler plain capture effect operation_known handler_typed selected_cut)

def handlerRequirements : Requirements [] :=
  .sequence ((Requirements.request [] []).prepend []) (.request [] [])
def captureRequirements : Requirements [] :=
  .sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (.push (.handler handler) .nil))) handlerRequirements
def requestRequirements : Requirements [] := .emitAfter (.request [] []) [] [⟨effect, 0, false⟩]

theorem captured_source : Segment operations policy contracts tables [] capture .integer .boolean [] captureRequirements [] := by
  have context : SourceTemplates.Context operations policy contracts [] Environment.empty [] .none
      (.bind 8 (.boolean true)) .integer .boolean [] (.request [] []) := .bind (.stable .boolean)
  exact .push (.plain (plain := plain) context .none rfl rfl) (.push (.handler handler_typed rfl) .nil)

theorem captured_check : Checked [] receiving before captureRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp only [captureRequirements, handlerRequirements, RecursiveRequirements.evaluate_sequence,
    RecursiveRequirements.evaluate_prepend, RecursiveRecomposition.evaluate_empty, merge, List.nil_append]

theorem request_source : Expression operations policy contracts [] [effect] .none Environment.empty
    (.perform (Instantiation.freezeEffect effect) 0 .unit) .integer [] requestRequirements :=
  .perform operation_known List.mem_cons_self (.stable .unit) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem request_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] [] .none
    (.perform (Instantiation.freezeEffect effect) 0 .unit) capture .boolean [] [] := by
  have current : Checked [] (OwnerPhases.ofStack tables capture) (OwnerPhaseTransitions.available (ownedTickets capture))
      requestRequirements [] :=
    Checked.emitAfter (bodyRow := []) (requestRow := [])
      (Checked.request (raw := []) (nearer := []) (by simp [OwnerSource.exportAt, residual_empty])) (by decide)
  have currentPrefixed : Checked [] [] (OwnerPhaseTransitions.available (ownedTickets capture))
      (requestRequirements.prepend (OwnerPhases.ofStack tables capture)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using current)
  exact .checked (.checked request_source .none captured_source) (by decide)
    (.sequence currentPrefixed captured_check) (by decide)

theorem fresh_capture_preserved : ∃ contract : Owners.Contract,
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, capture⟩
      ⟨.resume 7 (.integer 17), .ticket 7 23, .live 23 .integer .boolean capture .none .nil⟩ [.ticket 23] [] ∧
    SourceTemplates.CheckedConfiguration operations policy (contracts.insert 23 contract) tables [] [] (.ticket 7 23)
      (.resume 7 (.integer 17)) (.live 23 .integer .boolean capture .none .nil) .boolean [23] [] := by
  obtain ⟨contract, nextRow, step, checked, included, input, closeDemand, closeRow, resumeEffects, closeEffects, owned⟩ :=
    capture_immediate_resume request_checked selected_cut (ClauseAt.hit (parameter := 2) (binder := 7)) operation_known
      (Summary.integer (environment := Environment.empty.extend 2 .unit) (allowed := [])) trivial (owner := 23) (by decide) rfl
      [] none [] [] (List.Subset.refl [])
  have empty := List.sublist_nil.mp included
  subst nextRow
  exact ⟨contract, step, checked⟩

theorem captured_then_resumed : ∃ (contract : Owners.Contract) (restored : Stack),
    RawStep ⟨.resume 7 (.integer 17), .ticket 7 23, .live 23 .integer .boolean capture .none .nil⟩
      ⟨.integer 17, .ticket 7 23, restored⟩ [] [.ticket 23] ∧
    SourceTemplates.CheckedConfiguration operations policy (contracts.insert 23 contract) tables [] [] (.ticket 7 23)
      (.integer 17) restored .boolean [] [] := by
  obtain ⟨contract, captureStep, captured⟩ := fresh_capture_preserved
  have closed : ClosedValue (.integer 17) := ⟨trivial, rfl, by intro dependency member; cases member⟩
  obtain ⟨owner, restored, remaining, step, checked, demand, trace⟩ := RecursiveRecomposition.resume_preserves captured closed
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj demand
  subst owner
  subst remaining
  exact ⟨contract, restored, step, checked⟩

end Examples

end Ash.OneShot.RecursiveCapture

#print axioms Ash.OneShot.RecursiveCapture.owned_registered
#print axioms Ash.OneShot.RecursiveCapture.fresh_unowned
#print axioms Ash.OneShot.RecursiveCapture.capture_segments
#print axioms Ash.OneShot.RecursiveCapture.capture_segments_checked
#print axioms Ash.OneShot.RecursiveCapture.capture_owned
#print axioms Ash.OneShot.RecursiveCapture.capture_unique
#print axioms Ash.OneShot.RecursiveCapture.capture_phase_consumed
#print axioms Ash.OneShot.RecursiveCapture.lookup_insert_other
#print axioms Ash.OneShot.RecursiveCapture.checked_insert_consumed
#print axioms Ash.OneShot.RecursiveCapture.capture_record
#print axioms Ash.OneShot.RecursiveCapture.fresh_resume_configuration
#print axioms Ash.OneShot.RecursiveCapture.request_operand
#print axioms Ash.OneShot.RecursiveCapture.capture_immediate_resume
#print axioms Ash.OneShot.RecursiveCapture.Examples.captured_source
#print axioms Ash.OneShot.RecursiveCapture.Examples.captured_check
#print axioms Ash.OneShot.RecursiveCapture.Examples.request_source
#print axioms Ash.OneShot.RecursiveCapture.Examples.request_checked
#print axioms Ash.OneShot.RecursiveCapture.Examples.fresh_capture_preserved
#print axioms Ash.OneShot.RecursiveCapture.Examples.captured_then_resumed

#print axioms Ash.OneShot.RecursiveCapture.AnnotatedSegment.erase
#print axioms Ash.OneShot.RecursiveCapture.AnnotatedSegment.trivial
#print axioms Ash.OneShot.RecursiveCapture.capture_segments_with_frames
#print axioms Ash.OneShot.RecursiveCapture.AnnotatedSegment.extension
#print axioms Ash.OneShot.RecursiveCapture.AnnotatedSegment.world_weaken
#print axioms Ash.OneShot.RecursiveCapture.capture_segments_checked_with_frames
