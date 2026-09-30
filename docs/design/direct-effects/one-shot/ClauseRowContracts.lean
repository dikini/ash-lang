import ContextualClauseChecks
import CoherentSourceTypes
import RecursiveRecords

/-! Parametric local row certificates for the existing requirement trees.
The interface authenticates continuation invocations at their actual context
and phase. It does not assume future execution or grant syntax permissions. -/
namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked Key)

/-- Additional static paths may be checked without replacing the source's
normal requirement tree. Alternatives share owner demand; recursive rules keep
the existing sequence, phase and interpretation structure. This relation alone
does not assert that an added alternative is the right lexical cleanup path. -/
inductive RowAnnotation : {demand : List Nat} → Requirements demand → Requirements demand → Prop where
  | original : RowAnnotation requirements requirements
  | alternatives {first annotated : Requirements demand} {extra : Requirements other}
      (normal : RowAnnotation first annotated) (same : demand.Perm other) :
      RowAnnotation first (.choice annotated extra same)
  | sequence (first : RowAnnotation a annotatedA) (second : RowAnnotation b annotatedB) :
      RowAnnotation (.sequence a b) (.sequence annotatedA annotatedB)
  | emitAfter (body : RowAnnotation requirements annotated) :
      RowAnnotation (.emitAfter requirements nearer raw) (.emitAfter annotated nearer raw)
  | choice (first : RowAnnotation a annotatedA) (second : RowAnnotation b annotatedB) :
      RowAnnotation (.choice a b same) (.choice annotatedA annotatedB same)

/-- Checking annotations and their exact normal source records retain the
same ordered keys and owner demands. Only requirement bodies gain alternatives;
this relation introduces no runtime store or evaluator operation. -/
inductive StoreAnnotation : Store → Store → Prop where
  | nil : StoreAnnotation [] []
  | cons {normal annotated : Requirements demand} (body : RowAnnotation normal annotated) (rest : StoreAnnotation normalRest annotatedRest) :
      StoreAnnotation ((key, ⟨demand, normal⟩) :: normalRest) ((key, ⟨demand, annotated⟩) :: annotatedRest)

theorem StoreAnnotation.lookup
    (annotation : StoreAnnotation normalStore annotatedStore)
    (found : RecursiveRequirements.lookup key annotatedStore = some ⟨demand, body⟩) :
    ∃ normal : Requirements demand,
      RecursiveRequirements.lookup key normalStore = some ⟨demand, normal⟩ ∧ RowAnnotation normal body := by
  induction annotation with
  | nil => cases found
  | cons bodyAnnotation rest ih =>
      simp only [RecursiveRequirements.lookup] at found ⊢
      rename_i demand normalRest annotatedRest key' normal annotated
      by_cases same : key = key'
      · subst key'
        rw [if_pos rfl] at found
        cases Option.some.inj found
        exact ⟨_, by rw [if_pos rfl], bodyAnnotation⟩
      · simp only [if_neg same] at found ⊢
        exact ih found

theorem StoreAnnotation.refl (store : Store) : StoreAnnotation store store := by
  induction store with
  | nil => exact .nil
  | cons entry rest ih =>
      obtain ⟨key, demand, body⟩ := entry
      exact .cons .original ih

end Ash.OneShot.SourceDependencyAnnotations

namespace Ash.OneShot.ClauseRowAdmission
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked Key)
open OwnerPhaseTransitions (Phases)
open ContextualClauseChecks (Derivation)
open SourceDependencyAnnotations (RowAnnotation StoreAnnotation)

/-- Invocation evidence is checked independently of the clause's literal
row proof and syntax-level continuation-use judgment. The closing budget is
the exported operation advertisement plus the saved resumption row; neither
continuation mode is assumed to bound the other. Closing evidence and its bound
are required only when the clause's independent disposal flag permits it.
The bound owner has no active alias in the receiving tail. -/
structure Interface (owner : Nat) (contract : Owners.Contract) (disposes : Bool)
    (store : Store) (tail : OwnerPhases.Context) (before : Phases) (requestRow : Footprint) : Prop where
  resume : Checked store (.live owner contract.held :: tail) before
    (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow
  closing : disposes = true → ∀ row, contract.closeRow = some row →
    Checked store (.live owner contract.held :: tail) before
      (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) row
  available : disposes = true → ∃ row, contract.closeRow = some row
  closingBound : disposes = true → ∀ row, contract.closeRow = some row → EffectBounds.Covers (requestRow ++ contract.resumeRow) row
  fresh : owner ∉ OwnerPhaseTransitions.liveNames tail

/-- A clause that forbids disposal needs only the resume interface, regardless
of any unused closing metadata retained in the historical contract. -/
theorem Interface.of_resume
    (resume : Checked store (.live owner contract.held :: tail) before
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow)
    (denied : disposes = false)
    (fresh : owner ∉ OwnerPhaseTransitions.liveNames tail) :
    Interface owner contract disposes store tail before requestRow := by
  subst disposes
  refine ⟨resume, ?_, ?_, ?_, fresh⟩ <;> intro impossible <;> cases impossible

structure Header where
  owner : Nat
  contract : Owners.Contract
  disposes : Bool
  advertised : Footprint

/-- Row-store source evidence retains ordinary typing and adds the actual
    lexical completion markers, with their distinct input/output ports. -/
inductive StoreFrame (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → Prop where
  | ordinary (source : SourceTemplates.Frame operations policy contracts world frame input output demand requirements) :
      StoreFrame operations policy contracts world frame input output demand requirements
  | unwinding (scope : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent))
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      StoreFrame operations policy contracts world (.unwinding action) .unit result [] (.request [] [])
  | closing (scope : ScopedPorts.ScopeKnown contracts.ports.types caller) :
      StoreFrame operations policy contracts world (.closing identity caller) input .unit [] (.request [] [])
  | retiring (known : contracts owner = some contract) :
      StoreFrame operations policy contracts world (.retiring owner) input input [owner] (.retire owner)

/-- The same source/requirement/store indices as SourceTemplates.Segment,
    with frame evidence that also represents lexical cleanup execution. -/
inductive StoreSegment (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → Prop where
  | nil : StoreSegment operations policy contracts tables world .nil result result [] (.request [] []) []
  | push (head : StoreFrame operations policy contracts world frame input middle headDemand first)
      (tail : StoreSegment operations policy contracts tables world rest middle output tailDemand second records) :
      StoreSegment operations policy contracts tables world (.push frame rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records
  | live (known : contracts owner = some contract)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : StoreSegment operations policy contracts tables world capture
        contract.input contract.answer contract.resumeDemand body nested)
      (tail : StoreSegment operations policy contracts tables world rest contract.answer output demand requirements remaining) :
      StoreSegment operations policy contracts tables world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining))
  | spent (known : contracts owner = some contract)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (tail : StoreSegment operations policy contracts tables world rest contract.answer output demand requirements records) :
      StoreSegment operations policy contracts tables world (.spent owner answerType caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements) records

theorem StoreSegment.of_legacy
    (source : SourceTemplates.Segment operations policy contracts tables world stack input output demand requirements records) :
    StoreSegment operations policy contracts tables world stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (.ordinary head) ih
  | live known inputAnnotation answerAnnotation scope held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scope held ihSaved ihTail
  | spent known annotation scope tail ih => exact .spent known annotation scope ih

/-- Each lexical closing callback has source typing under the same operation
    registry. Its stored requirement retains the real interpretation suffix. -/
inductive StoreClosingTemplate (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → (demand : List Nat) → Requirements demand → Prop where
  | nil : StoreClosingTemplate operations policy contracts tables world .nil [] (.request [] [])
  | plain (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.push (.plain data) rest) demand requirements
  | handler (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.push (.handler data) rest) demand requirements
  | cell (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.push (.cell identity payload scope answer) rest) demand requirements
  | cleanup (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent))
      (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.push (.armed action) rest) ([] ++ demand)
        (.sequence (.request (OwnerPhases.ofStack tables rest) (qualify true latent)) requirements)
  | live (saved : StoreClosingTemplate operations policy contracts tables world captured savedDemand savedRequirements)
      (tail : StoreClosingTemplate operations policy contracts tables world rest tailDemand tailRequirements) :
      StoreClosingTemplate operations policy contracts tables world (.live owner input answer captured caller rest)
        (savedDemand ++ ([owner] ++ tailDemand))
        (.sequence (savedRequirements.prepend (OwnerPhases.ofStack tables (.push (.retiring owner) rest)))
          (.sequence (.retire owner) tailRequirements))
  | spent (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.spent owner answer caller rest) ([] ++ demand)
        (.sequence (.spent owner) requirements)
  | retiring (tail : StoreClosingTemplate operations policy contracts tables world rest demand requirements) :
      StoreClosingTemplate operations policy contracts tables world (.push (.retiring owner) rest) ([owner] ++ demand)
        (.sequence (.retire owner) requirements)

/-- Authenticate either retained legacy evidence or structural lexical
    disposal records. This changes no runtime disposal rule. -/
inductive StoreClosingRecords (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) : Stack → Store → Prop where
  | legacy (source : RecursiveRecords.Records operations policy contracts tables world stack records) :
      StoreClosingRecords operations policy contracts tables world stack records
  | nil : StoreClosingRecords operations policy contracts tables world .nil []
  | push (tail : StoreClosingRecords operations policy contracts tables world rest records) :
      StoreClosingRecords operations policy contracts tables world (.push frame rest) records
  | blocked (held : ProtectionContexts.protectedMode capture.erase = true)
      (saved : StoreClosingRecords operations policy contracts tables world capture nested)
      (tail : StoreClosingRecords operations policy contracts tables world rest remaining) :
      StoreClosingRecords operations policy contracts tables world (.live owner input answer capture caller rest) (nested ++ remaining)
  | close (unprotected : ProtectionContexts.protectedMode capture.erase = false)
      (summary : StoreClosingTemplate operations policy contracts tables world capture demand requirements)
      (saved : StoreClosingRecords operations policy contracts tables world capture nested)
      (tail : StoreClosingRecords operations policy contracts tables world rest remaining) :
      StoreClosingRecords operations policy contracts tables world (.live owner input answer capture caller rest)
        ((⟨owner, .dispose⟩, ⟨demand, requirements⟩) :: (nested ++ remaining))
  | spent (tail : StoreClosingRecords operations policy contracts tables world rest records) :
      StoreClosingRecords operations policy contracts tables world (.spent owner answer caller rest) records

theorem StoreClosingRecords.record_mode
    (source : StoreClosingRecords operations policy contracts tables world stack records)
    (member : (key, body) ∈ records) : key.mode = .dispose := by
  induction source with
  | legacy source => exact RecursiveRecords.record_mode source member
  | nil => cases member
  | push tail ih | spent tail ih => exact ih member
  | blocked held saved tail ihSaved ihTail =>
      rcases List.mem_append.mp member with nested | remaining
      · exact ihSaved nested
      · exact ihTail remaining
  | close unprotected summary saved tail ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · cases same; rfl
      · rcases List.mem_append.mp later with nested | remaining
        · exact ihSaved nested
        · exact ihTail remaining

/-- Erased source for the actual entry/exit mode of a lexical frame. `none`
means unwinding, not an unknown value type. Ordinary evidence is reused. -/
inductive StoreModeFrame (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (world : List Nat) :
    ExecFrame → Option Value → Option Value → (demand : List Nat) → Requirements demand → Prop where
  | ordinary (source : StoreFrame operations policy contracts world frame input output demand requirements) :
      StoreModeFrame operations policy contracts world frame (some input) (some output) demand requirements
  | unwinding (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent)) :
      StoreModeFrame operations policy contracts world (.unwinding action) (some .unit) none [] (.request [] [])
  | closing (scope : ScopedPorts.ScopeKnown contracts.ports.types caller) :
      StoreModeFrame operations policy contracts world (.closing identity caller) input (some .unit) [] (.request [] [])
  | retiring : StoreModeFrame operations policy contracts world (.retiring owner) input input [owner] (.retire owner)
  | skipped : StoreModeFrame operations policy contracts world (.plain data) none none [] (.request [] [])
  | handler (source : StoreFrame operations policy contracts world (.handler data) answer answer [] (.request [] [])) :
      StoreModeFrame operations policy contracts world (.handler data) none none [] (.request [] [])
  | cell : StoreModeFrame operations policy contracts world (.cell identity payload caller answer) none none [] (.request [] [])
  | cleanup (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent)) :
      StoreModeFrame operations policy contracts world (.armed action) none none [] (.request [] (qualify true latent))

/-- Row admission retains the source of the actual requirement tree independently
of record collection. Existing ordinary certificates remain admitted; mixed
certificates additionally expose value and unwind boundaries. This is source
provenance, not a checked effect row or an assumption about future execution. -/
inductive StoreModeSource (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Option Value → Option Value → (demand : List Nat) → Requirements demand → Prop where
  | legacy (source : StoreSegment operations policy contracts tables world stack input output demand requirements records) :
      StoreModeSource operations policy contracts tables world stack (some input) (some output) demand requirements
  | nil : StoreModeSource operations policy contracts tables world .nil input input [] (.request [] [])
  | push (head : StoreModeFrame operations policy contracts world entry input middle headDemand first)
      (tail : StoreModeSource operations policy contracts tables world rest middle output tailDemand second) :
      StoreModeSource operations policy contracts tables world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second)
  | live (known : contracts owner = some contract)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (held : contract.held = ProtectionContexts.protectedMode captured.erase)
      (saved : StoreModeSource operations policy contracts tables world captured
        (some contract.input) boundary contract.resumeDemand body)
      (returns : boundary = some contract.answer ∨ boundary = none)
      (tail : StoreModeSource operations policy contracts tables world rest boundary output demand requirements) :
      StoreModeSource operations policy contracts tables world (.live owner inputType answerType captured caller rest)
        (some contract.answer) output demand (.sequence (.spent owner) requirements)
  | opening (saved : StoreModeSource operations policy contracts tables world captured none none savedDemand savedRequirements)
      (tail : StoreModeSource operations policy contracts tables world rest none output tailDemand tailRequirements) :
      StoreModeSource operations policy contracts tables world (.live owner input answer captured caller rest)
        none output (savedDemand ++ ([owner] ++ tailDemand))
        (.sequence (savedRequirements.prepend (OwnerPhases.ofStack tables (.push (.retiring owner) rest)))
          (.sequence (.retire owner) tailRequirements))
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (tail : StoreModeSource operations policy contracts tables world rest (some contract.answer) output demand requirements) :
      StoreModeSource operations policy contracts tables world (.spent owner answerType caller rest)
        (some contract.answer) output demand (.sequence (.spent owner) requirements)
  | skippedSpent (tail : StoreModeSource operations policy contracts tables world rest none output demand requirements) :
      StoreModeSource operations policy contracts tables world (.spent owner answerType caller rest)
        none output demand (.sequence (.spent owner) requirements)

inductive StoreCertified (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Owners.Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat)
    (root : Stack) : Key → RecursiveRequirements.Template → Prop where
  | resume (located : SourceTemplates.CapturedIn owner capture root) (known : contracts owner = some contract)
      (saved : StoreModeSource operations policy contracts tables world capture
        (some contract.input) boundary contract.resumeDemand requirements)
      (returns : boundary = some contract.answer ∨ boundary = none) :
      StoreCertified operations policy contracts tables world root ⟨owner, .resume⟩ ⟨contract.resumeDemand, requirements⟩

theorem StoreCertified.transport
    (source : StoreCertified operations policy contracts tables world first key body)
    (move : ∀ owner capture, SourceTemplates.CapturedIn owner capture first → SourceTemplates.CapturedIn owner capture second) :
    StoreCertified operations policy contracts tables world second key body := by
  cases source with
  | resume located known saved returns => exact .resume (move _ _ located) known saved returns

theorem StoreSegment.records_certified
    (source : StoreSegment operations policy contracts tables world stack input output demand requirements records)
    (member : (key, body) ∈ records) : StoreCertified operations policy contracts tables world stack key body := by
  induction source with
  | nil => cases member
  | push head tail ih => exact (ih member).transport (fun _ _ located => .push located)
  | live known inputAnnotation answerAnnotation scope held saved tail ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · cases same; exact .resume .here known (.legacy saved) (.inl rfl)
      · rcases List.mem_append.mp later with nested | remaining
        · exact (ihSaved nested).transport (fun _ _ located => .saved located)
        · exact (ihTail remaining).transport (fun _ _ located => .tail located)
  | spent known annotation scope tail ih => exact (ih member).transport (fun _ _ located => .spent located)

/-- A row contract ranges over structurally sourced resume and disposal
records under the same operation registry and exact owner contract. Each stored
normal resume body has a capture location, exact requirement tree and
value-or-unwind boundary. The checking store is structurally annotated over
these source records with the same keys and owner demands. Collection is
separate from active source, so resumed and abandoned suffixes need not pretend
to be ordinary source segments. No successful row evaluation, valid successor
or future execution is assumed. -/
def SourceStore (operations : Operations) (owner : Nat) (contract : Owners.Contract) (store : Store) : Prop :=
  ∃ policy contracts tables world stack input output demand,
    ∃ (requirements : Requirements demand), ∃ resumes disposals,
    StoreModeSource operations policy contracts tables world stack input output demand requirements ∧
    (∀ key body, (key, body) ∈ resumes → StoreCertified operations policy contracts tables world stack key body) ∧
    StoreClosingRecords operations policy contracts tables world stack disposals ∧
    contracts owner = some contract ∧ StoreAnnotation (resumes ++ disposals) store

theorem SourceStore.of_source
    (source : SourceTemplates.Segment operations policy contracts tables world stack input output demand requirements resumes)
    (closing : RecursiveRecords.Records operations policy contracts tables world stack disposals)
    (known : contracts owner = some contract) :
    SourceStore operations owner contract (resumes ++ disposals) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, .legacy (.of_legacy source),
    fun _ _ member => (StoreSegment.of_legacy source).records_certified member, .legacy closing, known, .refl _⟩

theorem SourceStore.resume_template
    (authenticated : SourceStore operations owner contract store)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ store = some template) :
    ∃ policy contracts tables world capture,
      ∃ (requirements annotated : Requirements contract.resumeDemand), ∃ boundary,
        template = ⟨contract.resumeDemand, annotated⟩ ∧
        StoreModeSource operations policy contracts tables world capture
          (some contract.input) boundary contract.resumeDemand requirements ∧
        RowAnnotation requirements annotated ∧
        (boundary = some contract.answer ∨ boundary = none) := by
  obtain ⟨policy, contracts, tables, world, stack, input, output, demand, requirements,
    resumes, disposals, source, records, closing, known, annotation⟩ := authenticated
  obtain ⟨storedDemand, annotated⟩ := template
  obtain ⟨normal, normalFound, bodyAnnotation⟩ := annotation.lookup found
  rcases List.mem_append.mp (SourceTemplates.lookup_member normalFound) with member | member
  · cases records _ _ member with
    | resume located actual saved returns =>
      cases Option.some.inj (actual.symm.trans known)
      exact ⟨_, _, _, _, _, _, _, _, rfl, saved, bodyAnnotation, returns⟩
  · have impossible := closing.record_mode member
    cases impossible


/-- A family of finite structural checks at a local continuation interface.
The row bound is explicit; the exact requirement tree is shared with source
typing by the enclosing declaration constructor. A source-relative certificate
quantifies only over stores carrying its template-source derivation. The
unrestricted default retains the earlier rule; instantiation of a relative
certificate requires evidence for the actual store, not a future execution. -/
def Rows (header : Header) {demand : List Nat} (requirements : Requirements demand)
    (templates : Store → Prop := fun _ => True) : Prop :=
  ∀ (store : { store : Store // templates store }) tail before requestRow,
    Interface header.owner header.contract header.disposes store tail before requestRow →
    OwnerSource.exportAt tail before header.advertised = some requestRow →
    ∃ row calls,
      Derivation (.live header.owner header.contract.held :: tail) before requirements row calls ∧
      (∀ call ∈ calls, call.Check store) ∧
      EffectBounds.Covers (requestRow ++ header.contract.resumeRow) row

theorem Rows.instantiate {templates : Store → Prop}
    (source : Rows header requirements templates)
    (interface : Interface header.owner header.contract header.disposes store tail before requestRow)
    (exported : OwnerSource.exportAt tail before header.advertised = some requestRow)
    (authenticated : templates store := by trivial) :
    ∃ row, Checked store (.live header.owner header.contract.held :: tail) before requirements row ∧
      EffectBounds.Covers (requestRow ++ header.contract.resumeRow) row := by
  obtain ⟨row, calls, derived, supplied, covered⟩ := source ⟨store, authenticated⟩ _ _ _ interface exported
  exact ⟨row, ContextualClauseChecks.close derived supplied, covered⟩

/-- The pure operand before resumption does not add an invocation or row. -/
theorem resume_rows {templates : Store → Prop} : Rows ⟨owner, contract, disposes, advertised⟩
    (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) templates := by
  intro store tail before requestRow interface exported
  have checked : Checked store (.live owner contract.held :: tail) before
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) contract.resumeRow :=
    Checked.sequence (a := .request [] []) (firstRow := []) (Checked.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) interface.resume
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨contract.resumeRow, calls, derived, supplied, List.subset_append_right _ _⟩

/-- Returning a value after the resume adds an empty requirement check at the
post-invocation phase. -/
theorem resume_then_value_rows {templates : Store → Prop} : Rows ⟨owner, contract, disposes, advertised⟩
    (.sequence (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
      (.request [] [])) templates := by
  intro store tail before requestRow interface exported
  have resumeCheck : Checked store (.live owner contract.held :: tail) before
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) contract.resumeRow :=
    Checked.sequence (a := .request [] []) (firstRow := []) (Checked.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) interface.resume
  have checked : Checked store (.live owner contract.held :: tail) before
      (.sequence (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) (.request [] []))
      (contract.resumeRow ++ []) :=
    Checked.sequence resumeCheck (Checked.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  refine ⟨_, calls, derived, supplied, ?_⟩
  simpa only [List.nil_append, List.append_nil] using (List.subset_append_right requestRow contract.resumeRow)

/-- With no additional owner demand, consuming the bound owner leaves the
receiving tail unchanged. An effectful cleanup can therefore export its
advertisement after resumption. Ownership freshness is needed independently
of the effect row and the resume permission. -/
theorem cleanup_resume_rows {templates : Store → Prop}
    (empty : contract.resumeDemand = []) : Rows ⟨owner, contract, disposes, advertised⟩
      (.emitAfter (.sequence (.request [] [])
        (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))) [] advertised) templates := by
  intro store tail before requestRow interface exported
  have operand : Checked store (.live owner contract.held :: tail) before (.request [] []) [] :=
    .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  have resumed := Checked.sequence operand interface.resume
  have body := Checked.sequence operand resumed
  have emitted : OwnerSource.exportAt ([] ++ .live owner contract.held :: tail)
      (OwnerPhaseTransitions.spendAll before ([] ++ ([] ++ owner :: contract.resumeDemand))) advertised = some requestRow := by
    simpa only [List.nil_append, empty, OwnerPhaseTransitions.spendAll, OwnerSource.exportAt,
      OwnerPhaseTransitions.project, OwnerPhaseTransitions.spend_self, reduceCtorEq, ↓reduceIte,
      OwnerPhaseTransitions.project_spend_absent_live interface.fresh] using exported
  have checked : Checked store (.live owner contract.held :: tail) before
      (.emitAfter (.sequence (.request [] [])
        (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))) [] advertised)
      (contract.resumeRow ++ requestRow) := .emitAfter body emitted
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  refine ⟨_, calls, derived, supplied, ?_⟩
  intro effect member
  rcases List.mem_append.mp member with first | second
  · exact List.mem_append_right _ first
  · exact List.mem_append_left _ second

/-- Disposal consumes the same one-shot authority. Its independent interface
supplies both the closing invocation and its effect budget. -/
theorem discard_rows {templates : Store → Prop} : Rows ⟨owner, contract, true, advertised⟩
    (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) templates := by
  intro store tail before requestRow interface exported
  obtain ⟨row, available⟩ := interface.available rfl
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked (interface.closing rfl row available)
  refine ⟨row, calls, derived, supplied, ?_⟩
  exact interface.closingBound rfl row available

#print axioms Ash.OneShot.ClauseRowAdmission.StoreSegment.of_legacy
#print axioms Ash.OneShot.ClauseRowAdmission.StoreClosingRecords.record_mode
#print axioms Ash.OneShot.ClauseRowAdmission.StoreCertified.transport
#print axioms Ash.OneShot.ClauseRowAdmission.StoreSegment.records_certified

end Ash.OneShot.ClauseRowAdmission

#print axioms Ash.OneShot.ClauseRowAdmission.Rows.instantiate
#print axioms Ash.OneShot.ClauseRowAdmission.resume_rows
#print axioms Ash.OneShot.ClauseRowAdmission.resume_then_value_rows
#print axioms Ash.OneShot.ClauseRowAdmission.discard_rows

#print axioms Ash.OneShot.ClauseRowAdmission.Interface.of_resume

#print axioms Ash.OneShot.ClauseRowAdmission.SourceStore.of_source

#print axioms Ash.OneShot.ClauseRowAdmission.SourceStore.resume_template

#print axioms Ash.OneShot.ClauseRowAdmission.cleanup_resume_rows

namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)

/-- A checked annotation supplies the normal source check at the same store,
receiving interpretations and owner phase, within its advertised effect row. -/
theorem RowAnnotation.checked
    (annotation : RowAnnotation normal annotated)
    (checked : Checked entries receiving before annotated row) :
    ∃ normalRow, Checked entries receiving before normal normalRow ∧ normalRow ⊆ row := by
  induction annotation generalizing receiving before row with
  | original => exact ⟨_, checked, List.Subset.refl _⟩
  | alternatives normal same ih => cases checked with
      | choice first second =>
          obtain ⟨normalRow, checkedNormal, bounded⟩ := ih first
          exact ⟨normalRow, checkedNormal, bounded.trans (List.subset_append_left _ _)⟩
  | sequence first second ihFirst ihSecond =>
          obtain ⟨leftRow, rightRow, left, right, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
          obtain ⟨a, checkedA, boundA⟩ := ihFirst left
          obtain ⟨b, checkedB, boundB⟩ := ihSecond right
          exact ⟨a ++ b, .sequence checkedA checkedB,
            List.append_subset.mpr ⟨boundA.trans (List.subset_append_left _ _), boundB.trans (List.subset_append_right _ _)⟩⟩
  | emitAfter body ih => cases checked with
      | emitAfter checked exported =>
          obtain ⟨row, normal, bounded⟩ := ih checked
          exact ⟨_, .emitAfter normal exported,
            List.append_subset.mpr ⟨bounded.trans (List.subset_append_left _ _), List.subset_append_right _ _⟩⟩
  | choice first second ihFirst ihSecond => cases checked with
      | choice left right =>
          obtain ⟨a, checkedA, boundA⟩ := ihFirst left
          obtain ⟨b, checkedB, boundB⟩ := ihSecond right
          exact ⟨a ++ b, .choice checkedA checkedB,
            List.append_subset.mpr ⟨boundA.trans (List.subset_append_left _ _), boundB.trans (List.subset_append_right _ _)⟩⟩

/-- Installed interpretations are prepended to both paths by the existing
requirement operation, preserving the annotation's source correspondence. -/
theorem RowAnnotation.prepend (annotation : RowAnnotation normal annotated) (nearer : OwnerPhases.Context) :
    RowAnnotation (normal.prepend nearer) (annotated.prepend nearer) := by
  induction annotation with
  | original => exact .original
  | alternatives normal same ih => exact .alternatives ih same
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | emitAfter body ih => exact .emitAfter ih
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond

/-- Hereditary row certificates may check extra static alternatives while
still supplying the normal source certificate. No source store is changed. -/
theorem RowAnnotation.rows
    (annotation : RowAnnotation normal annotated)
    (rows : ClauseRowAdmission.Rows header annotated templates) :
    ClauseRowAdmission.Rows header normal templates := by
  intro store tail before requestRow interface exported
  obtain ⟨row, checked, covered⟩ := rows.instantiate interface exported store.property
  obtain ⟨normalRow, normalCheck, within⟩ := annotation.checked checked
  obtain ⟨calls, derivation, supplied⟩ := ContextualClauseChecks.open_checked normalCheck
  exact ⟨normalRow, calls, derivation, supplied, within.trans covered⟩

end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.RowAnnotation.checked
#print axioms Ash.OneShot.SourceDependencyAnnotations.RowAnnotation.prepend
#print axioms Ash.OneShot.SourceDependencyAnnotations.RowAnnotation.rows

namespace Ash.OneShot.ClauseRowAdmission
open ScopedExpressions ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)

/-- Check both static alternatives against the same authenticated interface.
The common bound is reused; effect occurrences are not linear resources. -/
theorem Rows.alternatives
    (first : Rows header (normal : Requirements demand) templates)
    (second : Rows header (cleanup : Requirements otherDemand) templates)
    (same : demand.Perm otherDemand) :
    Rows header (.choice normal cleanup same) templates := by
  intro store tail before requestRow interface exported
  obtain ⟨normalRow, normalCheck, normalBound⟩ := first.instantiate interface exported store.property
  obtain ⟨cleanupRow, cleanupCheck, cleanupBound⟩ := second.instantiate interface exported store.property
  have checked : Checked store (.live header.owner header.contract.held :: tail) before
      (.choice normal cleanup same) (normalRow ++ cleanupRow) := .choice normalCheck cleanupCheck
  obtain ⟨calls, derivation, supplied⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨_, calls, derivation, supplied, List.append_subset.mpr ⟨normalBound, cleanupBound⟩⟩
end Ash.OneShot.ClauseRowAdmission
#print axioms Ash.OneShot.ClauseRowAdmission.Rows.alternatives


namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (spendAll)

/-- A structural position in a requirement tree. The prefix records precisely
which owners are consumed before the selected subtree. The whole tree remains
an index, including every surrounding alternative and its other branch. -/
inductive RequirementPath {selectedDemand : List Nat} (selected : Requirements selectedDemand) :
    {demand : List Nat} → Requirements demand → List Nat → Prop where
  | here : RequirementPath selected selected []
  | first (inside : RequirementPath selected a prior) :
      RequirementPath selected (.sequence a b) prior
  | second {a : Requirements firstDemand} (inside : RequirementPath selected b prior) :
      RequirementPath selected (.sequence a b) (firstDemand ++ prior)
  | body (inside : RequirementPath selected a prior) :
      RequirementPath selected (.emitAfter a nearer raw) prior
  | yes (inside : RequirementPath selected a prior) :
      RequirementPath selected (.choice a b same) prior
  | no (inside : RequirementPath selected b prior) :
      RequirementPath selected (.choice a b same) prior

/-- Read a checked subtree at its original phase. No surrounding branch is
removed from the root certificate. -/
theorem RequirementPath.checked
    (path : RequirementPath selected whole prior)
    (checked : Checked entries receiving before whole row) :
    ∃ selectedRow, Checked entries receiving (spendAll before prior) selected selectedRow ∧ selectedRow ⊆ row := by
  induction path generalizing before row with
  | here => exact ⟨_, checked, List.Subset.refl _⟩
  | first inside ih =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨selectedRow, selected, bounded⟩ := ih first
      exact ⟨selectedRow, selected, bounded.trans (List.subset_append_left _ _)⟩
  | second inside ih =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨selectedRow, selected, bounded⟩ := ih second
      exact ⟨selectedRow, by simpa only [PhaseRechecking.spendAll_append] using selected,
        bounded.trans (List.subset_append_right _ _)⟩
  | body inside ih => cases checked with
      | emitAfter body exported =>
          obtain ⟨selectedRow, selected, bounded⟩ := ih body
          exact ⟨selectedRow, selected, bounded.trans (List.subset_append_left _ _)⟩
  | yes inside ih => cases checked with
      | choice first second =>
          obtain ⟨selectedRow, selected, bounded⟩ := ih first
          exact ⟨selectedRow, selected, bounded.trans (List.subset_append_left _ _)⟩
  | no inside ih => cases checked with
      | choice first second =>
          obtain ⟨selectedRow, selected, bounded⟩ := ih second
          exact ⟨selectedRow, selected, bounded.trans (List.subset_append_right _ _)⟩

/-- Nested focus composes positions without discarding outer alternatives. -/
theorem RequirementPath.trans
    (outer : RequirementPath middle whole outerPrior)
    (inner : RequirementPath selected middle innerPrior) :
    RequirementPath selected whole (outerPrior ++ innerPrior) := by
  induction outer with
  | here => exact inner
  | first inside ih => exact .first ih
  | second inside ih => simpa only [List.append_assoc] using RequirementPath.second ih
  | body inside ih => exact .body ih
  | yes inside ih => exact .yes ih
  | no inside ih => exact .no ih

/-- Installed interpretations affect the selected subtree and its enclosing
annotation uniformly; the owner prefix does not change. -/
theorem RequirementPath.prepend
    (path : RequirementPath selected whole prior) (nearer : OwnerPhases.Context) :
    RequirementPath (selected.prepend nearer) (whole.prepend nearer) prior := by
  induction path with
  | here => exact .here
  | first inside ih => exact .first ih
  | second inside ih => exact .second ih
  | body inside ih => exact .body ih
  | yes inside ih => exact .yes ih
  | no inside ih => exact .no ih

private theorem sequence_path_cases
    {selected : Requirements selectedDemand} {whole : Requirements demand}
    (path : RequirementPath selected whole prior)
    {a : Requirements firstDemand} {b : Requirements secondDemand}
    (same : demand = firstDemand ++ secondDemand)
    (equation : HEq whole (Requirements.sequence a b)) :
    (selectedDemand = firstDemand ++ secondDemand ∧ HEq selected (Requirements.sequence a b) ∧ prior = []) ∨
    RequirementPath selected a prior ∨
    (∃ suffix, prior = firstDemand ++ suffix ∧ RequirementPath selected b suffix) := by
  cases path with
  | here => exact .inl ⟨same, equation, rfl⟩
  | first inside =>
      apply Requirements.sequence.noConfusion same equation
      intro firstSame secondSame leftSame rightSame
      cases firstSame
      cases secondSame
      cases eq_of_heq leftSame
      cases eq_of_heq rightSame
      exact .inr (.inl inside)
  | second inside =>
      apply Requirements.sequence.noConfusion same equation
      intro firstSame secondSame leftSame rightSame
      cases firstSame
      cases secondSame
      cases eq_of_heq leftSame
      cases eq_of_heq rightSame
      exact .inr (.inr ⟨_, rfl, inside⟩)
  | body | yes | no => exact Requirements.noConfusion same equation

/-- Locate the annotated subtree corresponding to a normal source position.
An enclosing added alternative is traversed on its normal side and remains in
the root tree; this is not a decomposition into independent annotations. -/
theorem RowAnnotation.focus
    (annotation : RowAnnotation normal annotated)
    {selected : Requirements selectedDemand}
    (path : RequirementPath selected normal prior) :
    ∃ focused : Requirements selectedDemand,
      RowAnnotation selected focused ∧ RequirementPath focused annotated prior := by
  induction annotation generalizing selectedDemand selected prior with
  | original => exact ⟨_, .original, path⟩
  | alternatives normal same ih =>
      obtain ⟨focused, annotation, position⟩ := ih path
      exact ⟨focused, annotation, .yes position⟩
  | sequence first second ihFirst ihSecond =>
      rcases sequence_path_cases path rfl HEq.rfl with ⟨same, sameTree, rfl⟩ | inside | ⟨suffix, rfl, inside⟩
      · cases same
        cases eq_of_heq sameTree
        exact ⟨_, .sequence first second, .here⟩
      · obtain ⟨focused, annotation, position⟩ := ihFirst inside
        exact ⟨focused, annotation, .first position⟩
      · obtain ⟨focused, annotation, position⟩ := ihSecond inside
        exact ⟨focused, annotation, .second position⟩
  | emitAfter body ih => cases path with
      | here => exact ⟨_, .emitAfter body, .here⟩
      | body inside =>
          obtain ⟨focused, annotation, position⟩ := ih inside
          exact ⟨focused, annotation, .body position⟩
  | choice first second ihFirst ihSecond => cases path with
      | here => exact ⟨_, .choice first second, .here⟩
      | yes inside =>
          obtain ⟨focused, annotation, position⟩ := ihFirst inside
          exact ⟨focused, annotation, .yes position⟩
      | no inside =>
          obtain ⟨focused, annotation, position⟩ := ihSecond inside
          exact ⟨focused, annotation, .no position⟩

end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.RequirementPath.checked
#print axioms Ash.OneShot.SourceDependencyAnnotations.RequirementPath.trans
#print axioms Ash.OneShot.SourceDependencyAnnotations.RequirementPath.prepend
#print axioms Ash.OneShot.SourceDependencyAnnotations.RowAnnotation.focus

namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked evaluate)

/-- Rebuild the normal syntax after a check-preserving administrative step,
retaining the complete earlier annotation as a checked alternative. Both paths
consume the same owners; they are checked separately, not executed in sequence.
The resulting effect bound is unchanged even if row entries are repeated. -/
theorem RowAnnotation.rebase_checked
    (annotation : RowAnnotation (normal : Requirements demand) annotated)
    (same : nextDemand.Perm demand)
    (evaluation : evaluate entries receiving before (next : Requirements nextDemand) =
      evaluate entries receiving before normal)
    (checked : Checked entries receiving before annotated row) :
    RowAnnotation next (.choice next annotated same) ∧
    RequirementPath annotated (.choice next annotated same) [] ∧
    ∃ nextRow, Checked entries receiving before (.choice next annotated same) nextRow ∧ nextRow ⊆ row := by
  obtain ⟨normalRow, normalCheck, within⟩ := annotation.checked checked
  have nextCheck : Checked entries receiving before next normalRow :=
    RecursiveRequirements.evaluate_sound (evaluation.trans (RecursiveRequirements.checked_complete normalCheck))
  exact ⟨.alternatives .original same, .no .here,
    normalRow ++ row, .choice nextCheck checked, List.append_subset.mpr ⟨within, List.Subset.refl _⟩⟩

end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.RowAnnotation.rebase_checked


namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (spendAll)

/-- Remove the portion before a selected subtree while retaining that subtree
and its following requirements. The remaining tree is checked at the phase
after the removed demand, within the original row bound. This is a structural
certificate transformation; it neither executes cleanup nor builds a runtime
unwind plan. Enclosing alternatives follow the selected path. -/
theorem RequirementPath.remainder
    {selected : Requirements selectedDemand} {whole : Requirements demand}
    (path : RequirementPath selected whole prior) :
    ∃ remainingDemand, ∃ remaining : Requirements remainingDemand,
      demand.Perm (prior ++ remainingDemand) ∧ RequirementPath selected remaining [] ∧
      ∀ entries receiving before row, Checked entries receiving before whole row →
        ∃ remainingRow, Checked entries receiving (spendAll before prior) remaining remainingRow ∧
          remainingRow ⊆ row := by
  induction path with
  | here =>
      exact ⟨_, _, .refl _, .here, fun _ _ _ _ checked => ⟨_, checked, List.Subset.refl _⟩⟩
  | @first firstDemand a prior secondDemand b inside ih =>
      obtain ⟨remainingDemand, remaining, same, retained, checkedRemaining⟩ := ih
      refine ⟨_, .sequence remaining b, ?_, .first retained, ?_⟩
      · simpa only [List.append_assoc] using same.append_right _
      · intro entries receiving before row checked
        obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        obtain ⟨remainingRow, rest, within⟩ := checkedRemaining _ _ _ _ first
        have phases := PhaseRechecking.spendAll_permutation (before := before) same
        rw [PhaseRechecking.spendAll_append] at phases
        rw [phases] at second
        exact ⟨_, .sequence rest second,
          List.append_subset.mpr ⟨within.trans (List.subset_append_left _ _), List.subset_append_right _ _⟩⟩
  | second inside ih =>
      obtain ⟨remainingDemand, remaining, same, retained, checkedRemaining⟩ := ih
      refine ⟨_, remaining, ?_, retained, ?_⟩
      · simpa only [List.append_assoc] using same.append_left _
      · intro entries receiving before row checked
        obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        obtain ⟨remainingRow, rest, within⟩ := checkedRemaining _ _ _ _ second
        exact ⟨_, by simpa only [PhaseRechecking.spendAll_append] using rest,
          within.trans (List.subset_append_right _ _)⟩
  | @body bodyDemand a prior nearer raw inside ih =>
      obtain ⟨remainingDemand, remaining, same, retained, checkedRemaining⟩ := ih
      refine ⟨_, .emitAfter remaining nearer raw, same, .body retained, ?_⟩
      intro entries receiving before row checked
      cases checked with
      | emitAfter body exported =>
          obtain ⟨remainingRow, rest, within⟩ := checkedRemaining _ _ _ _ body
          have phases := PhaseRechecking.spendAll_permutation (before := before) same
          rw [PhaseRechecking.spendAll_append] at phases
          rw [phases] at exported
          exact ⟨_, .emitAfter rest exported,
            List.append_subset.mpr ⟨within.trans (List.subset_append_left _ _), List.subset_append_right _ _⟩⟩
  | yes inside ih =>
      obtain ⟨remainingDemand, remaining, same, retained, checkedRemaining⟩ := ih
      refine ⟨_, remaining, same, retained, ?_⟩
      intro entries receiving before row checked
      cases checked with
      | choice first second =>
          obtain ⟨remainingRow, rest, within⟩ := checkedRemaining _ _ _ _ first
          exact ⟨_, rest, within.trans (List.subset_append_left _ _)⟩
  | no inside ih =>
      obtain ⟨remainingDemand, remaining, same, retained, checkedRemaining⟩ := ih
      refine ⟨_, remaining, ?_, retained, ?_⟩
      · exact List.Perm.trans ‹_› same
      · intro entries receiving before row checked
        cases checked with
        | choice first second =>
            obtain ⟨remainingRow, rest, within⟩ := checkedRemaining _ _ _ _ second
            exact ⟨_, rest, within.trans (List.subset_append_right _ _)⟩
end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.RequirementPath.remainder


namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked Key)

/-- Project all recursively invoked annotated bodies to their normal source
bodies. The owner phases and demanded owners are unchanged, and the normal row
stays within the annotated row. Reuse the existing tree-annotation projection
at each invocation. -/
theorem StoreAnnotation.checked
    (store : StoreAnnotation normalStore annotatedStore)
    (checked : Checked annotatedStore receiving before (requirements : Requirements demand) row) :
    ∃ normalRow, Checked normalStore receiving before requirements normalRow ∧ normalRow ⊆ row := by
  induction checked with
  | request exported => exact ⟨_, .request exported, List.Subset.refl _⟩
  | spent consumed => exact ⟨_, .spent consumed, List.Subset.refl _⟩
  | retire ready => exact ⟨_, .retire ready, List.Subset.refl _⟩
  | invoke known ready selection next ih =>
      obtain ⟨body, found, bodyAnnotation⟩ := store.lookup known
      obtain ⟨_, projected, within⟩ := ih
      obtain ⟨_, bodyCheck, bodyBound⟩ := bodyAnnotation.checked projected
      exact ⟨_, .invoke found ready selection bodyCheck, bodyBound.trans within⟩
  | sequence first second ihFirst ihSecond =>
      obtain ⟨a, left, leftBound⟩ := ihFirst
      obtain ⟨b, right, rightBound⟩ := ihSecond
      exact ⟨_, .sequence left right, List.append_subset.mpr
        ⟨leftBound.trans (List.subset_append_left _ _), rightBound.trans (List.subset_append_right _ _)⟩⟩
  | emitAfter body exported ih =>
      obtain ⟨row, check, within⟩ := ih
      exact ⟨_, .emitAfter check exported, List.append_subset.mpr
        ⟨within.trans (List.subset_append_left _ _), List.subset_append_right _ _⟩⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨a, left, leftBound⟩ := ihFirst
      obtain ⟨b, right, rightBound⟩ := ihSecond
      exact ⟨_, .choice left right, List.append_subset.mpr
        ⟨leftBound.trans (List.subset_append_left _ _), rightBound.trans (List.subset_append_right _ _)⟩⟩

theorem StoreAnnotation.lookup_annotated
    (annotation : StoreAnnotation normalStore annotatedStore)
    (found : RecursiveRequirements.lookup key normalStore = some ⟨demand, body⟩) :
    ∃ annotated : Requirements demand,
      RecursiveRequirements.lookup key annotatedStore = some ⟨demand, annotated⟩ ∧ RowAnnotation body annotated := by
  induction annotation with
  | nil => cases found
  | cons bodyAnnotation rest ih =>
      rename_i demand normalRest annotatedRest key' normal annotated
      simp only [RecursiveRequirements.lookup] at found ⊢
      by_cases same : key = key'
      · subst key'
        rw [if_pos rfl] at found
        cases Option.some.inj found
        exact ⟨_, by rw [if_pos rfl], bodyAnnotation⟩
      · simp only [if_neg same] at found ⊢
        exact ih found

theorem StoreAnnotation.remove_owner
    (annotation : StoreAnnotation normalStore annotatedStore) (owner : Nat) :
    StoreAnnotation (RecursiveTransport.removeOwner owner normalStore)
      (RecursiveTransport.removeOwner owner annotatedStore) := by
  induction annotation with
  | nil => exact .nil
  | cons body rest ih =>
      simp only [RecursiveTransport.removeOwner]
      split
      · exact ih
      · exact .cons body ih
end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.lookup
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.checked
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.refl
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.lookup_annotated
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.remove_owner


namespace Ash.OneShot.SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store)
/-- Preserve every existing body annotation when record collections are joined. -/
theorem StoreAnnotation.append
    (first : StoreAnnotation normalFirst annotatedFirst)
    (second : StoreAnnotation normalSecond annotatedSecond) :
    StoreAnnotation (normalFirst ++ normalSecond) (annotatedFirst ++ annotatedSecond) := by
  induction first with
  | nil => exact second
  | cons body rest ih => exact .cons body ih

/-- The structural relation preserves the resume/disposal partition, so fresh
closing records can be inserted without reinterpreting older bodies. -/
theorem StoreAnnotation.split
    (annotation : StoreAnnotation (normalFirst ++ normalSecond) annotated) :
    ∃ annotatedFirst annotatedSecond, annotated = annotatedFirst ++ annotatedSecond ∧
      StoreAnnotation normalFirst annotatedFirst ∧ StoreAnnotation normalSecond annotatedSecond := by
  induction normalFirst generalizing annotated with
  | nil => exact ⟨[], annotated, rfl, .nil, annotation⟩
  | cons entry rest ih =>
      obtain ⟨key, demand, body⟩ := entry
      cases annotation with
      | cons head tail =>
          obtain ⟨first, second, rfl, left, right⟩ := ih tail
          exact ⟨_, second, rfl, .cons head left, right⟩
end Ash.OneShot.SourceDependencyAnnotations
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.append
#print axioms Ash.OneShot.SourceDependencyAnnotations.StoreAnnotation.split


namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked)
/-- Add the real closing-boundary check at every disposal leaf of a finite
requirement tree, preserving owner demand and all existing alternatives. -/
def annotateDisposals : {demand : List Nat} → Requirements demand → Requirements demand
  | _, .request nearer raw => .request nearer raw
  | _, .retire owner => .retire owner
  | _, .spent owner => .spent owner
  | _, .invoke ⟨owner, .resume⟩ demand nearer => .invoke ⟨owner, .resume⟩ demand nearer
  | _, .invoke ⟨owner, .dispose⟩ demand nearer =>
      .choice (.invoke ⟨owner, .dispose⟩ demand nearer)
        (.invoke ⟨owner, .dispose⟩ demand (.ordinary (.barrier true) :: nearer)) (.refl _)
  | _, .sequence first second => .sequence (annotateDisposals first) (annotateDisposals second)
  | _, .emitAfter body nearer raw => .emitAfter (annotateDisposals body) nearer raw
  | _, .choice first second same => .choice (annotateDisposals first) (annotateDisposals second) same


/-- The ordinary clause interface and the extra finite check required by the
actual lexical closing boundary. Continuation permissions remain independent. -/
structure ProtectedClauseInterface (owner : Nat) (contract : CoherentSourceTypes.Owners.Contract) (disposes : Bool)
    (entries : Store) (tail : OwnerPhases.Context) (before : OwnerPhaseTransitions.Phases) (requestRow : Footprint) : Prop
    extends ClauseRowAdmission.Interface owner contract disposes entries tail before requestRow where
  protectedClosing : disposes = true → ∃ row,
    Checked entries (.live owner contract.held :: tail) before
      (.invoke ⟨owner, .dispose⟩ contract.closeDemand [.ordinary (.barrier true)]) row ∧
    row ⊆ requestRow ++ contract.resumeRow


/-- The generated disposal leaf is now checked using both finite interface
fields. Its two alternatives consume the same owner, not two executions. -/
theorem ProtectedClauseInterface.discard_checked
    (interface : ProtectedClauseInterface owner contract true entries tail before requestRow) :
    ∃ row, Checked entries (.live owner contract.held :: tail) before
      (annotateDisposals (.invoke ⟨owner, .dispose⟩ contract.closeDemand [])) row ∧
      row ⊆ requestRow ++ contract.resumeRow := by
  obtain ⟨ordinaryRow, available⟩ := interface.available rfl
  obtain ⟨protectedRow, protectedCheck, protectedBound⟩ := interface.protectedClosing rfl
  exact ⟨ordinaryRow ++ protectedRow, .choice (interface.closing rfl ordinaryRow available) protectedCheck,
    List.append_subset.mpr ⟨interface.closingBound rfl ordinaryRow available, protectedBound⟩⟩


end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.ProtectedClauseInterface.discard_checked


namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations (RowAnnotation RequirementPath)
open RecursiveRequirements (Requirements Store Checked)
open ContextualClauseChecks (Derivation Invocation)

/-- Reuse the existing open clause derivation. The only additional evidence is
one protected check for each disposal call, at that call's recorded context and
phase. Sequencing and choice preserve the same finite ownership demands. -/
theorem clause_disposals_checked
    (source : Derivation receiving before requirements row calls)
    (supplied : ∀ call ∈ calls, call.Check entries)
    (bounded : row ⊆ budget)
    (closing : ∀ call ∈ calls, call.key.mode = .dispose → ∃ closedRow,
      Checked entries call.receiving call.before
        (.invoke call.key call.demand [.ordinary (.barrier true)]) closedRow ∧
      closedRow ⊆ budget) :
    ∃ checkedRow, Checked entries receiving before (annotateDisposals requirements) checkedRow ∧
      checkedRow ⊆ budget := by
  induction source with
  | request exported => exact ⟨_, .request exported, bounded⟩
  | retire ready => exact ⟨[], .retire ready, by simp⟩
  | spent consumed => exact ⟨[], .spent consumed, by simp⟩
  | @invoke receiving before key demand nearer row =>
      have normal : Checked entries receiving before (.invoke key demand nearer) row :=
        ContextualClauseChecks.close .invoke supplied
      cases key with
      | mk owner mode => cases mode with
        | resume => exact ⟨row, normal, bounded⟩
        | dispose =>
          obtain ⟨closedRow, checked, within⟩ := closing _ List.mem_cons_self rfl
          have protectedCheck : Checked entries receiving before
              (.invoke ⟨owner, .dispose⟩ demand (.ordinary (.barrier true) :: nearer)) closedRow := by
            simpa only [Requirements.prepend, List.singleton_append] using
              (RecursiveRequirements.checked_prepend_iff.mpr checked :
                Checked entries receiving before
                  ((Requirements.invoke ⟨owner, .dispose⟩ demand [.ordinary (.barrier true)]).prepend nearer) closedRow)
          exact ⟨row ++ closedRow, .choice normal protectedCheck, List.append_subset.mpr ⟨bounded, within⟩⟩
  | sequence first second ihFirst ihSecond =>
      obtain ⟨firstBound, secondBound⟩ := List.append_subset.mp bounded
      obtain ⟨firstRow, firstChecked, firstWithin⟩ := ihFirst
        (fun call member => supplied call (List.mem_append_left _ member)) firstBound
        (fun call member => closing call (List.mem_append_left _ member))
      obtain ⟨secondRow, secondChecked, secondWithin⟩ := ihSecond
        (fun call member => supplied call (List.mem_append_right _ member)) secondBound
        (fun call member => closing call (List.mem_append_right _ member))
      exact ⟨firstRow ++ secondRow, .sequence firstChecked secondChecked,
        List.append_subset.mpr ⟨firstWithin, secondWithin⟩⟩
  | emitAfter source exported ih =>
      obtain ⟨bodyBound, requestBound⟩ := List.append_subset.mp bounded
      obtain ⟨bodyRow, checked, within⟩ := ih supplied bodyBound closing
      exact ⟨_, .emitAfter checked exported, List.append_subset.mpr ⟨within, requestBound⟩⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨firstBound, secondBound⟩ := List.append_subset.mp bounded
      obtain ⟨firstRow, firstChecked, firstWithin⟩ := ihFirst
        (fun call member => supplied call (List.mem_append_left _ member)) firstBound
        (fun call member => closing call (List.mem_append_left _ member))
      obtain ⟨secondRow, secondChecked, secondWithin⟩ := ihSecond
        (fun call member => supplied call (List.mem_append_right _ member)) secondBound
        (fun call member => closing call (List.mem_append_right _ member))
      exact ⟨firstRow ++ secondRow, .choice firstChecked secondChecked,
        List.append_subset.mpr ⟨firstWithin, secondWithin⟩⟩
end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.clause_disposals_checked

namespace Ash.OneShot.ClauseRowAdmission
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Checked)
open ContextualClauseChecks (Derivation)
open SourceScheduledCleanupInterfaces.Lexical.Recursive

/-- A hereditary clause certificate for the generated disposal alternatives.
It is checked at each local continuation interface, with the exact source
requirement tree, store, lexical receiver and phases. Its conclusion is an open
structural derivation and finite invocation evidence, never a successor state. -/
def ProtectedRows (header : Header) {demand : List Nat} (requirements : Requirements demand)
    (templates : Store → Prop := fun _ => True) : Prop :=
  ∀ (store : { store : Store // templates store }) tail before requestRow,
    ProtectedClauseInterface header.owner header.contract header.disposes store tail before requestRow →
    OwnerSource.exportAt tail before header.advertised = some requestRow →
    ∃ row calls,
      Derivation (.live header.owner header.contract.held :: tail) before
        (annotateDisposals requirements) row calls ∧
      (∀ call ∈ calls, call.Check store) ∧
      EffectBounds.Covers (requestRow ++ header.contract.resumeRow) row

theorem ProtectedRows.instantiate {templates : Store → Prop}
    (source : ProtectedRows header requirements templates)
    (interface : ProtectedClauseInterface header.owner header.contract header.disposes entries tail before requestRow)
    (exported : OwnerSource.exportAt tail before header.advertised = some requestRow)
    (authenticated : templates entries) :
    ∃ row, Checked entries (.live header.owner header.contract.held :: tail) before
      (annotateDisposals requirements) row ∧ row ⊆ requestRow ++ header.contract.resumeRow := by
  obtain ⟨row, calls, derived, supplied, covered⟩ := source ⟨entries, authenticated⟩ _ _ _ interface exported
  exact ⟨row, ContextualClauseChecks.close derived supplied, covered⟩

/-- Reuse an ordinary certificate when generation adds no disposal alternative. -/
theorem ProtectedRows.of_unchanged {templates : Store → Prop}
    (source : Rows header requirements templates)
    (unchanged : annotateDisposals requirements = requirements) :
    ProtectedRows header requirements templates := by
  intro store tail before requestRow interface exported
  rw [unchanged]
  exact source store tail before requestRow interface.toInterface exported

theorem protected_resume_rows {templates : Store → Prop} :
    ProtectedRows ⟨owner, contract, disposes, advertised⟩
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) templates :=
  .of_unchanged resume_rows rfl

theorem protected_discard_rows {templates : Store → Prop} :
    ProtectedRows ⟨owner, contract, true, advertised⟩
      (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) templates := by
  intro store tail before requestRow interface _exported
  obtain ⟨row, checked, bounded⟩ := interface.discard_checked
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨row, calls, derived, supplied, bounded⟩

/-- Construct the protected certificate by reusing an ordinary open derivation.
The extra checks refer to each call's actual receiver and phase, so nested
handlers do not inherit a check from a different lexical context. -/
theorem ProtectedRows.of_calls {templates : Store → Prop}
    (derive : ∀ (store : { store : Store // templates store }) tail before requestRow,
      ProtectedClauseInterface header.owner header.contract header.disposes store tail before requestRow →
      OwnerSource.exportAt tail before header.advertised = some requestRow →
      ∃ row calls, Derivation (.live header.owner header.contract.held :: tail) before requirements row calls ∧
        (∀ call ∈ calls, call.Check store) ∧ row ⊆ requestRow ++ header.contract.resumeRow ∧
        (∀ call ∈ calls, call.key.mode = .dispose → ∃ closedRow,
          Checked store call.receiving call.before (.invoke call.key call.demand [.ordinary (.barrier true)]) closedRow ∧
          closedRow ⊆ requestRow ++ header.contract.resumeRow)) :
    ProtectedRows header requirements templates := by
  intro store tail before requestRow interface exported
  obtain ⟨row, calls, derived, supplied, bounded, closing⟩ := derive store tail before requestRow interface exported
  obtain ⟨checkedRow, checked, within⟩ := clause_disposals_checked derived supplied bounded closing
  obtain ⟨checkedCalls, generated, allChecked⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨checkedRow, checkedCalls, generated, allChecked, within⟩
end Ash.OneShot.ClauseRowAdmission
#print axioms Ash.OneShot.ClauseRowAdmission.ProtectedRows.instantiate
#print axioms Ash.OneShot.ClauseRowAdmission.ProtectedRows.of_unchanged
#print axioms Ash.OneShot.ClauseRowAdmission.protected_resume_rows
#print axioms Ash.OneShot.ClauseRowAdmission.protected_discard_rows
#print axioms Ash.OneShot.ClauseRowAdmission.ProtectedRows.of_calls
