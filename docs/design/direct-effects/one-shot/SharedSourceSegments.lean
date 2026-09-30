import CaptureAuthentication

/-!
One annotation per pending value connects ordinary ports, source protection
and recursive saved-source authentication. Handler implementation admission,
closing contracts and dynamic phase transport remain separate obligations.
-/

namespace Ash.OneShot.SharedSourceSegments
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes
open OwnerPhaseTransitions (Phases Trace)
open CoherentSourceTypes.Owners (Contracts)

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) (world : List Nat) (environment : Environment)
    (allowed : List Instance) (scope : Execution.Scope) :
    ScopedExecution.Context → Phases → Value → Phases → Value → List Nat → Footprint → Prop where
  | pairLeft (right : Owners.Derives operations policy contracts inside world environment allowed scope middle code after output demand row) :
      Context operations policy contracts inside world environment allowed scope (.pairLeft code) middle input after (.pair input output) demand row
  | pairRight (left : Summary operations world environment allowed code input []) :
      Context operations policy contracts inside world environment allowed scope (.pairRight code) phases output phases (.pair input output) [] []
  | appFunction (argument : Owners.Derives operations policy contracts inside world environment allowed scope middle code after input demand argumentRow)
      (admitted : requests ⊆ allowed) (exported : OwnerSource.exportAt inside after latent = some invocationRow) :
      Context operations policy contracts inside world environment allowed scope (.appFunction code) middle (.function input output requests latent)
        after output demand (argumentRow ++ invocationRow)
  | appArgument (function : Summary operations world environment allowed code (.function input output requests latent) [])
      (admitted : requests ⊆ allowed) (exported : OwnerSource.exportAt inside phases latent = some row) :
      Context operations policy contracts inside world environment allowed scope (.appArgument code) phases input phases output [] row
  | bind (body : Owners.Derives operations policy contracts inside world (environment.extend parameter input) allowed scope middle code after output demand row) :
      Context operations policy contracts inside world environment allowed scope (.bind parameter code) middle input after output demand row
  | branch (yes : Owners.Derives operations policy contracts inside world environment allowed scope middle a after output yesDemand yesRow)
      (no : Owners.Derives operations policy contracts inside world environment allowed scope middle b after output noDemand noRow) :
      Context operations policy contracts inside world environment allowed scope (.branch a b) middle .boolean after output yesDemand (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.port)
      (exported : OwnerSource.exportAt inside phases [⟨effect, operation, false⟩] = some row) :
      Context operations policy contracts inside world environment allowed scope (.perform (Instantiation.freezeEffect effect) operation)
        phases input phases output [] row
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true) (transition : Trace before (owner :: contract.resumeDemand) after)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Context operations policy contracts inside world environment allowed scope (.resume binder)
        before contract.input after contract.answer (owner :: contract.resumeDemand) contract.resumeRow
  | cleanup (body : Owners.Derives operations policy contracts inside world environment allowed scope middle code after output demand bodyRow)
      (admitted : requests ⊆ allowed)
      (exported : ProtectionResiduals.residualize (.barrier true :: OwnerPhaseTransitions.project inside after) latent = some invocationRow) :
      Context operations policy contracts inside world environment allowed scope (.cleanup code) middle (.function .unit .unit requests latent)
        after output demand (bodyRow ++ invocationRow)
  | resource {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Summary operations (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw)
      (exported : OwnerSource.exportAt inside phases raw = some row) :
      Context operations policy contracts inside world environment allowed scope (.resource binder code) phases .integer phases output [] row

theorem context_source
    (context : Context operations policy contracts inside world environment allowed scope position before input after output demand row) :
    OwnerSource.ContextDerives operations.protection policy contracts.source inside environment.protection scope position
      before input.protection after output.protection demand row := by
  cases context with
  | pairLeft right => exact .pairLeft (Owners.owner_source right)
  | pairRight left => exact .pairRight (protection_summary left)
  | appFunction argument admitted exported => exact .appFunction (Owners.owner_source argument) exported
  | appArgument function admitted exported => exact .appArgument (protection_summary function) exported
  | bind body => exact .bind (by simpa only [protection_extend] using Owners.owner_source body)
  | branch yes no => exact .branch (Owners.owner_source yes) (Owners.owner_source no)
  | perform known admitted formed exported => exact .perform (protection_lookup known) exported
  | resume known resolved permission transition admitted formed => exact .resume (Owners.source_lookup known) resolved permission transition
  | cleanup body admitted exported => exact .cleanup (Owners.owner_source body) exported
  | resource body formed effectsBound admitted outward exported =>
      exact .resource (fun identity fresh => protection_summary (body identity fresh)) outward exported

theorem context_ports
    (context : Context operations policy contracts inside world environment allowed scope position before input after output demand row)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket) :
    ScopedPorts.ContextTyped operations.ports world environment.ports ticket allowed position input.port output.port := by
  cases context with
  | pairLeft right => exact .pairLeft (Owners.port_typing right scopeTyped)
  | pairRight left => exact .pairRight (port_typing left ticket)
  | appFunction argument admitted exported => exact .appFunction (Owners.port_typing argument scopeTyped) admitted
  | appArgument function admitted exported => exact .appArgument (port_typing function ticket) admitted
  | bind body => exact .bind (by simpa only [ports_extend] using Owners.port_typing body scopeTyped)
  | branch yes no => exact .branch (Owners.port_typing yes scopeTyped) (Owners.port_typing no scopeTyped)
  | perform known admitted formed exported => exact .perform (port_lookup known) admitted formed
  | resume known resolved permission transition admitted formed =>
      have same := Owners.scope_resolved scopeTyped known resolved
      subst ticket
      exact .resume admitted formed
  | cleanup body admitted exported => exact .cleanup (Owners.port_typing body scopeTyped) admitted
  | resource body formed effectsBound admitted outward exported =>
      exact .resource (fun identity fresh => port_typing (body identity fresh) ticket) formed effectsBound admitted

theorem context_plug
    (context : Context operations policy contracts inside world environment allowed scope position middle input after output restDemand restRow)
    (child : Owners.Derives operations policy contracts inside world environment allowed scope before code middle input demand row) :
    Owners.Derives operations policy contracts inside world environment allowed scope before (position.plug code) after output
      (demand ++ restDemand) (row ++ restRow) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left =>
      simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Owners.Derives.pair
        (Owners.Derives.stable (row := []) left (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) child
  | appFunction argument admitted exported =>
      simpa only [ScopedExecution.Context.plug, List.append_assoc] using Owners.Derives.app child argument admitted exported
  | appArgument function admitted exported =>
      simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Owners.Derives.app
        (Owners.Derives.stable (row := []) function (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) child admitted exported
  | bind body => exact .bind child body
  | branch yes no => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Owners.Derives.branch child yes no
  | perform known admitted formed exported =>
      simpa only [ScopedExecution.Context.plug, List.append_nil] using Owners.Derives.perform known admitted child formed exported
  | resume known resolved permission transition admitted formed => exact .resume known resolved permission child transition admitted formed
  | cleanup body admitted exported =>
      simpa only [ScopedExecution.Context.plug, List.append_assoc] using Owners.Derives.cleanup child body admitted exported
  | resource body formed effectsBound admitted outward exported =>
      simpa only [ScopedExecution.Context.plug, List.append_nil] using Owners.Derives.resource child body formed effectsBound admitted outward exported

theorem stable_context
    (context : ContextSummary operations world environment allowed position input output raw)
    (exported : OwnerSource.exportAt inside phases raw = some row) :
    Context operations policy contracts inside world environment allowed scope position phases input phases output [] row := by
  cases context with
  | pairLeft right => exact .pairLeft (.stable right exported)
  | pairRight left =>
      have empty : row = [] := by simpa [OwnerSource.exportAt, ProtectionResiduals.residual_empty] using exported.symm
      subst row
      exact .pairRight left
  | appFunction argument admitted =>
      obtain ⟨first, second, argRow, callRow, same⟩ := export_append_split exported
      subst row
      exact .appFunction (.stable argument argRow) admitted callRow
  | appArgument function admitted => exact .appArgument function admitted exported
  | bind body => exact .bind (.stable body exported)
  | branch yes no =>
      obtain ⟨first, second, yesRow, noRow, same⟩ := export_append_split exported
      subst row
      exact .branch (.stable yes yesRow) (.stable no noRow)
  | perform known admitted formed => exact .perform known admitted formed exported
  | resource body formed effectsBound admitted outward => exact .resource body formed effectsBound admitted outward exported
  | cleanup body admitted =>
      obtain ⟨first, second, bodyRow, callRow, same⟩ := export_append_split exported
      subst row
      apply Context.cleanup (.stable body bodyRow) admitted
      simpa only [OwnerSource.exportAt, ProtectionResiduals.residualize, DisposalProtection.through_barrier] using callRow

theorem focus_decompose
    (source : Owners.Derives operations policy contracts inside world environment allowed scope before whole after output demand row)
    (focus : Focus whole child position) :
    ∃ middle input childDemand restDemand childRow restRow,
      Owners.Derives operations policy contracts inside world environment allowed scope before child middle input childDemand childRow ∧
      Context operations policy contracts inside world environment allowed scope position middle input after output restDemand restRow ∧
      demand = childDemand ++ restDemand ∧ row = childRow ++ restRow := by
  cases source with
  | stable summary exported =>
      obtain ⟨input, childRaw, restRaw, childSource, context, same⟩ := CoherentSourceTypes.focus_decompose focus summary
      rw [same] at exported
      obtain ⟨childRow, restRow, childExport, restExport, same⟩ := export_append_split exported
      exact ⟨_, input, [], [], childRow, restRow, .stable childSource childExport, stable_context context restExport, rfl, same⟩
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, _, _, _, left, .pairLeft right, rfl, rfl⟩
      | pairRight isValue =>
          obtain ⟨summary, same, emptyDemand, emptyRow⟩ := Owners.value_summary left isValue
          subst_vars
          exact ⟨_, _, _, _, _, _, right, .pairRight summary, by simp, by simp⟩
  | app function argument admitted exported => cases focus with
      | appFunction => exact ⟨_, _, _, _, _, _, function, .appFunction argument admitted exported, rfl, List.append_assoc ..⟩
      | appArgument isValue =>
          obtain ⟨summary, same, emptyDemand, emptyRow⟩ := Owners.value_summary function isValue
          subst_vars
          exact ⟨_, _, _, _, _, _, argument, .appArgument summary admitted exported, by simp, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, _, _, _, initializer, .bind body, rfl, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, _, _, _, condition, .branch yes no, rfl, List.append_assoc ..⟩
  | perform known admitted operand formed exported => cases focus with
      | perform => exact ⟨_, _, _, [], _, _, operand, .perform known admitted formed exported, by simp, rfl⟩
  | resume known resolved permission operand transition admitted formed => cases focus with
      | resume => exact ⟨_, _, _, _, _, _, operand, .resume known resolved permission transition admitted formed, rfl, rfl⟩
  | discard => cases focus
  | cleanup callback body admitted exported => cases focus with
      | cleanup => exact ⟨_, _, _, _, _, _, callback, .cleanup body admitted exported, rfl, List.append_assoc ..⟩
  | resource initializer body formed effectsBound admitted outward exported => cases focus with
      | resource notValue => exact ⟨_, _, _, [], _, _, initializer, .resource body formed effectsBound admitted outward exported, by simp, rfl⟩

inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) (world : List Nat) :
    ExecFrame → Phases → Value → Phases → Value → List Nat → Footprint → Prop where
  | plain (source : Context operations policy contracts inside world Environment.empty allowed plain.scope plain.context before input after output demand row)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports plain.scope ticket)
      (inputAnnotation : input.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.port = ScopedPorts.eraseType plain.output) :
      Frame operations policy contracts inside world (.plain plain) before input after output demand row
  | handler (typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types world (.handler handler))
      (annotation : answer.port = ScopedPorts.eraseType handler.answer) :
      Frame operations policy contracts inside world (.handler handler) phases answer phases answer [] []
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.port = ScopedPorts.eraseType answer) :
      Frame operations policy contracts inside world (.cell identity payload scope answer) phases result phases result [] []
  | armed (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : Summary operations world Environment.empty [] action.action (.function .unit .unit action.requests latent) [])
      (annotation : result.port = ScopedPorts.eraseType action.answer)
      (exported : OwnerSource.exportAt inside phases (qualify true latent) = some row) :
      Frame operations policy contracts inside world (.armed action) phases result phases result [] row
  | running (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : Summary operations world Environment.empty [] action.action (.function .unit .unit action.requests latent) [])
      (saved : Summary operations world Environment.empty [] value result [])
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      Frame operations policy contracts inside world (.running action value closed) phases .unit phases result [] []
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
      Frame operations policy contracts inside world (.closing identity scope) phases .unit phases .unit [] []
  | retiring (known : contracts owner = some contract) (transition : Trace before [owner] after) :
      Frame operations policy contracts inside world (.retiring owner) before .unit after .unit [owner] []

theorem frame_source (frame : Frame operations policy contracts inside world entry before input after output demand row) :
    OwnerSource.FrameSource operations.protection policy contracts.source inside entry before input.protection after output.protection demand row := by
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation => exact .plain (context_source source)
  | handler => exact .handler
  | cell => exact .cell
  | armed scopeKnown callback annotation exported => exact .armed (protection_summary callback) exported
  | running scopeKnown callback saved annotation => exact .running (protection_summary saved)
  | closing => exact .closing
  | retiring known transition => exact .retiring transition

theorem frame_annotations (frame : Frame operations policy contracts inside world entry before input after output demand row) :
    input.port = ScopedPorts.eraseType entry.erase.input ∧ output.port = ScopedPorts.eraseType entry.erase.output := by
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation => exact ⟨inputAnnotation, outputAnnotation⟩
  | handler typed annotation | cell scopeKnown noEscape annotation | armed scopeKnown callback annotation exported => exact ⟨annotation, annotation⟩
  | running scopeKnown callback saved annotation => exact ⟨rfl, annotation⟩
  | closing | retiring => exact ⟨rfl, rfl⟩

theorem types_lookup {contracts : Contracts} (known : contracts owner = some contract) :
    contracts.ports.types owner = some (contract.input.port, contract.answer.port) := by
  simp [ScopedPorts.EffectTickets.types, Owners.ports_lookup known, Owners.Contract.ports]

theorem frame_ports (frame : Frame operations policy contracts inside world entry before input after output demand row) :
    ScopedPorts.FrameTyped operations.ports contracts.ports.types world entry := by
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      have typed := context_ports source scopeTyped
      rw [inputAnnotation, outputAnnotation] at typed
      exact .plain (ScopedPorts.effect_scope_has_types scopeTyped) typed
  | handler typed annotation => exact typed
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape
  | armed scopeKnown callback annotation exported => exact .armed scopeKnown (port_typing callback .none)
  | running scopeKnown callback saved annotation =>
      exact .running scopeKnown (port_typing callback .none) (annotation ▸ port_typing saved .none)
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known transition => exact .retiring (types_lookup known)

theorem context_extension
    (context : Context operations policy contracts inside world environment allowed scope position before input after output demand row)
    (extension : contracts.Extends larger) :
    Context operations policy larger inside world environment allowed scope position before input after output demand row := by
  cases context with
  | pairLeft right => exact .pairLeft (Owners.source_extension right extension)
  | pairRight left => exact .pairRight left
  | appFunction argument admitted exported => exact .appFunction (Owners.source_extension argument extension) admitted exported
  | appArgument function admitted exported => exact .appArgument function admitted exported
  | bind body => exact .bind (Owners.source_extension body extension)
  | branch yes no => exact .branch (Owners.source_extension yes extension) (Owners.source_extension no extension)
  | perform known admitted formed exported => exact .perform known admitted formed exported
  | resume known resolved permission transition admitted formed => exact .resume (extension _ _ known) resolved permission transition admitted formed
  | cleanup body admitted exported => exact .cleanup (Owners.source_extension body extension) admitted exported
  | resource body formed effectsBound admitted outward exported => exact .resource body formed effectsBound admitted outward exported

theorem frame_extension
    (frame : Frame operations policy contracts inside world entry before input after output demand row)
    (extension : contracts.Extends larger) :
    Frame operations policy larger inside world entry before input after output demand row := by
  have ports := Owners.port_contracts_extension extension
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      exact .plain (context_extension source extension) (ScopedPorts.effect_scope_extension scopeTyped ports) inputAnnotation outputAnnotation
  | handler typed annotation => exact .handler (ScopedPorts.frame_typed_extension typed types) annotation
  | cell scopeKnown noEscape annotation => exact .cell (ScopedPorts.scope_known_extension scopeKnown types) noEscape annotation
  | armed scopeKnown callback annotation exported => exact .armed (ScopedPorts.scope_known_extension scopeKnown types) callback annotation exported
  | running scopeKnown callback saved annotation => exact .running (ScopedPorts.scope_known_extension scopeKnown types) callback saved annotation
  | closing scopeKnown => exact .closing (ScopedPorts.scope_known_extension scopeKnown types)
  | retiring known transition => exact .retiring (extension _ _ known) transition

/-- Both branches of a live boundary are checked with shared annotations.
    Saved source retains its historical receiver and phase endpoints. -/
inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Stack → Phases → Value → Phases → Value → List Nat → Footprint → Prop where
  | nil : Segment operations policy contracts tables world fixed .nil phases value phases value [] []
  | push (head : Frame operations policy contracts (OwnerPhases.ofStack tables (rest.append fixed)) world
        frame before input middle intermediate headDemand headRow)
      (tail : Segment operations policy contracts tables world fixed rest middle intermediate after output tailDemand tailRow) :
      Segment operations policy contracts tables world fixed (.push frame rest) before input after output
        (headDemand ++ tailDemand) (headRow ++ tailRow)
  | live (known : contracts owner = some contract)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (consumed : phases owner = .consumed)
      (saved : Segment operations policy contracts tables world receiver capture savedBefore contract.input savedAfter contract.answer contract.resumeDemand savedRow)
      (covered : EffectBounds.Covers contract.resumeRow savedRow)
      (tail : Segment operations policy contracts tables world fixed rest phases contract.answer after output demand row) :
      Segment operations policy contracts tables world fixed (.live owner inputType answerType capture scope rest)
        phases contract.answer after output demand row
  | spent (known : contracts owner = some contract)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
      (consumed : phases owner = .consumed)
      (tail : Segment operations policy contracts tables world fixed rest phases contract.answer after output demand row) :
      Segment operations policy contracts tables world fixed (.spent owner answerType scope rest)
        phases contract.answer after output demand row

theorem segment_source (segment : Segment operations policy contracts tables world fixed stack before input after output demand row) :
    OwnerSource.Segment operations.protection policy contracts.source tables fixed stack before input.protection after output.protection demand row := by
  induction segment with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_source head) ih
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      exact .live (Owners.source_lookup known) held consumed ihTail
  | spent known answerAnnotation scopeKnown consumed tail ih => exact .spent (Owners.source_lookup known) consumed ih

theorem segment_ports (segment : Segment operations policy contracts tables world fixed stack before input after output demand row) :
    ScopedPorts.StackTyped operations.ports contracts.ports.types world stack input.port output.port := by
  induction segment with
  | nil => exact .nil
  | push head tail ih =>
      obtain ⟨inputAnnotation, outputAnnotation⟩ := frame_annotations head
      rw [outputAnnotation] at ih
      rw [inputAnnotation]
      exact .push (frame_ports head) ih
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      have signature := types_lookup known
      rw [inputAnnotation, answerAnnotation] at signature ihSaved
      rw [answerAnnotation] at ihTail ⊢
      exact .live signature scopeKnown ihSaved ihTail
  | spent known answerAnnotation scopeKnown consumed tail ih =>
      have signature := types_lookup known
      rw [answerAnnotation] at signature ih ⊢
      exact .spent signature scopeKnown ih

theorem segment_authenticated (segment : Segment operations policy contracts tables world fixed stack before input after output demand row) :
    CaptureAuthentication.Retained operations.protection policy contracts.source tables stack := by
  induction segment with
  | nil => exact .nil
  | push head tail ih => exact .push ih
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      exact .live (.saved (Owners.source_lookup known) ⟨_, segment_source saved, covered, held⟩) ihSaved ihTail
  | spent known answerAnnotation scopeKnown consumed tail ih => exact .spent ih

theorem segment_trace (segment : Segment operations policy contracts tables world fixed stack before input after output demand row) :
    Trace before demand after := OwnerSource.segment_trace (segment_source segment)

theorem segment_once (segment : Segment operations policy contracts tables world fixed stack before input after output demand row) :
    demand.Nodup := OwnerPhaseTransitions.trace_nodup (segment_trace segment)

theorem segment_extension
    (segment : Segment operations policy contracts tables world fixed stack before input after output demand row)
    (extension : contracts.Extends larger) :
    Segment operations policy larger tables world fixed stack before input after output demand row := by
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  induction segment with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_extension head extension) ih
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      exact .live (extension _ _ known) inputAnnotation answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types)
        held consumed ihSaved covered ihTail
  | spent known answerAnnotation scopeKnown consumed tail ih =>
      exact .spent (extension _ _ known) answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types) consumed ih

section Composition
variable {front middle fixed : Stack}

theorem segment_append
    (first : Segment operations policy contracts tables world (middle.append fixed) front before input between intermediate firstDemand firstRow)
    (second : Segment operations policy contracts tables world fixed middle between intermediate after output secondDemand secondRow) :
    Segment operations policy contracts tables world fixed (front.append middle) before input after output
      (firstDemand ++ secondDemand) (firstRow ++ secondRow) := by
  induction front generalizing before input firstDemand firstRow with
  | nil => cases first; exact second
  | push frame rest ih => cases first with
      | push head tail =>
          simpa only [Stack.append, List.append_assoc] using Segment.push
            (by simpa only [stack_append_assoc] using head) (ih tail)
  | live owner inputType answerType capture scope rest ihCapture ihRest => cases first with
      | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail =>
          exact .live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered (ihRest tail)
  | spent owner answer scope rest ih => cases first with
      | spent known answerAnnotation scopeKnown consumed tail => exact .spent known answerAnnotation scopeKnown consumed (ih tail)

theorem segment_decompose
    (segment : Segment operations policy contracts tables world fixed (front.append middle) before input after output demand row) :
    ∃ between intermediate firstDemand secondDemand firstRow secondRow,
      Segment operations policy contracts tables world (middle.append fixed) front before input between intermediate firstDemand firstRow ∧
      Segment operations policy contracts tables world fixed middle between intermediate after output secondDemand secondRow ∧
      demand = firstDemand ++ secondDemand ∧ row = firstRow ++ secondRow := by
  induction front generalizing before input demand row with
  | nil => exact ⟨_, _, [], demand, [], row, .nil, segment, rfl, rfl⟩
  | push frame rest ih => cases segment with
      | push head tail =>
          obtain ⟨between, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ih tail
          exact ⟨between, intermediate, _, secondDemand, _, secondRow,
            .push (by simpa only [stack_append_assoc] using head) first, second,
            by simp only [names, List.append_assoc], by simp only [effects, List.append_assoc]⟩
  | live owner inputType answerType capture scope rest ihCapture ihRest => cases segment with
      | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail =>
          obtain ⟨between, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ihRest tail
          exact ⟨between, intermediate, firstDemand, secondDemand, firstRow, secondRow,
            .live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered first, second, names, effects⟩
  | spent owner answer scope rest ih => cases segment with
      | spent known answerAnnotation scopeKnown consumed tail =>
          obtain ⟨between, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ih tail
          exact ⟨between, intermediate, firstDemand, secondDemand, firstRow, secondRow,
            .spent known answerAnnotation scopeKnown consumed first, second, names, effects⟩

theorem capture_segment (cut : HandlerCut requested whole capture tail handler)
    (segment : Segment operations policy contracts tables world fixed whole before input after output demand row) :
    ∃ between intermediate firstDemand secondDemand firstRow secondRow,
      Segment operations policy contracts tables world (tail.append fixed) capture before input between intermediate firstDemand firstRow ∧
      Segment operations policy contracts tables world fixed tail between intermediate after output secondDemand secondRow ∧
      demand = firstDemand ++ secondDemand ∧ row = firstRow ++ secondRow := by
  rw [handler_cut_reconstructs cut] at segment
  exact segment_decompose segment

theorem capture_answer (cut : HandlerCut requested whole capture tail handler)
    (segment : Segment operations policy contracts tables world fixed whole before input after output demand row) :
    ∃ between answer firstDemand secondDemand firstRow secondRow,
      answer.port = ScopedPorts.eraseType handler.answer ∧
      Segment operations policy contracts tables world (tail.append fixed) capture before input between answer firstDemand firstRow ∧
      Segment operations policy contracts tables world fixed tail between answer after output secondDemand secondRow ∧
      demand = firstDemand ++ secondDemand ∧ row = firstRow ++ secondRow := by
  induction cut generalizing before input demand row with
  | hit handler tail same => cases segment with
      | push head rest => cases head with
          | handler typed annotation => exact ⟨_, _, [], _, [], _, annotation, .push (.handler typed annotation) .nil, rest, rfl, rfl⟩
  | push entry rest cap tail handler miss next ih => cases segment with
      | push head rest =>
          obtain ⟨between, answer, firstDemand, secondDemand, firstRow, secondRow, annotation, saved, outside, names, effects⟩ := ih rest
          have moved := head
          rw [handler_cut_reconstructs next, stack_append_assoc] at moved
          exact ⟨between, answer, _, secondDemand, _, secondRow, annotation, .push moved saved, outside,
            by simp only [names, List.append_assoc], by simp only [effects, List.append_assoc]⟩
  | live owner inputType answerType saved scope rest cap tail handler next ih => cases segment with
      | live known inputAnnotation answerAnnotation scopeKnown held consumed historical covered rest =>
          obtain ⟨between, answer, firstDemand, secondDemand, firstRow, secondRow, annotation, saved, outside, names, effects⟩ := ih rest
          exact ⟨between, answer, firstDemand, secondDemand, firstRow, secondRow, annotation,
            .live known inputAnnotation answerAnnotation scopeKnown held consumed historical covered saved, outside, names, effects⟩
  | spent owner answer scope rest cap tail handler next ih => cases segment with
      | spent known answerAnnotation scopeKnown consumed rest =>
          obtain ⟨between, answer, firstDemand, secondDemand, firstRow, secondRow, annotation, saved, outside, names, effects⟩ := ih rest
          exact ⟨between, answer, firstDemand, secondDemand, firstRow, secondRow, annotation,
            .spent known answerAnnotation scopeKnown consumed saved, outside, names, effects⟩

/-- Construct the full shared input/answer annotation from the actual cut.
    Close fields and ordinary effect lists are still explicit annotations.
    The new owner's initial consumed phase is supplied by the caller. -/
theorem capture_record (cut : HandlerCut requested whole capture tail handler)
    (segment : Segment operations policy contracts tables world fixed whole before input after output demand row)
    (fresh : contracts owner = none) (consumed : before owner = .consumed)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance) :
    ∃ contract : Owners.Contract, ∃ between restDemand restRow,
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      Segment operations policy (contracts.insert owner contract) tables world fixed
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        between contract.answer after output restDemand restRow ∧
      demand = contract.resumeDemand ++ restDemand ∧ row = contract.resumeRow ++ restRow := by
  obtain ⟨between, answer, savedDemand, restDemand, savedRow, restRow, annotation, saved, rest, names, effects⟩ := capture_answer cut segment
  let contract : Owners.Contract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
    savedDemand, savedRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  have extension := Owners.insert_extends (contract := contract) contracts fresh
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have past : between owner = .consumed := OwnerPhaseTransitions.trace_monotone (segment_trace saved) consumed
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  have scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types handler.scope := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (segment_ports segment)
    cases handlerTyped with
    | handler known clauses coverage unique => exact known
  exact ⟨contract, between, restDemand, restRow, rfl, annotation, rfl, rfl, rfl, rfl,
    .live known (ScopedPorts.erase_embed_port input.port).symm annotation (ScopedPorts.scope_known_extension scopeKnown types)
      rfl past (segment_extension saved extension) (EffectBounds.covers_refl savedRow) (segment_extension rest extension), names, effects⟩

end Composition

inductive Source (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (fixed : Stack) (outside : ProtectionContracts.Context) :
    Execution.Scope → Code → Stack → Phases → Phases → Value → List Nat → Footprint → Prop where
  | checked (current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (stack.append fixed)) world
        Environment.empty allowed scope before code middle input currentDemand currentRow)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
      (pending : Segment operations policy contracts tables world fixed stack middle input after output pendingDemand pendingRow)
      (accepted : checkFootprint outside (currentRow ++ pendingRow) = true) :
      Source operations policy contracts tables world fixed outside scope code stack before after output
        (currentDemand ++ pendingDemand) (currentRow ++ pendingRow)

theorem source_owner (source : Source operations policy contracts tables world fixed outside scope code stack before after output demand row) :
    OwnerSource.Source operations.protection policy contracts.source tables fixed outside scope code stack before after output.protection demand row := by
  cases source with
  | checked current scopeTyped pending accepted => exact .checked (Owners.owner_source current) (segment_source pending) accepted

theorem source_ports (source : Source operations policy contracts tables world fixed outside scope code stack before after output demand row) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  cases source with
  | checked current scopeTyped pending accepted =>
      exact ⟨_, .checked (ScopedPorts.effect_scope_has_types scopeTyped) (Owners.port_typing current scopeTyped), segment_ports pending⟩

theorem source_authenticated (source : Source operations policy contracts tables world fixed outside scope code stack before after output demand row) :
    CaptureAuthentication.Retained operations.protection policy contracts.source tables stack := by
  cases source with
  | checked current scopeTyped pending accepted => exact segment_authenticated pending

theorem source_bind
    (source : Source operations policy contracts tables world fixed outside scope (.bind parameter value body) stack before after output demand row)
    (closed : ClosedValue value) :
    Source operations policy contracts tables world fixed outside scope (body.subst parameter value) stack before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted => exact .checked (Owners.bind_summary current closed) scopeTyped pending accepted

theorem source_beta
    (source : Source operations policy contracts tables world fixed outside scope (.app (.lambda parameter body) value) stack before after output demand row)
    (closed : ClosedValue value) :
    Source operations policy contracts tables world fixed outside .none (body.subst parameter value) stack before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted => exact .checked (Owners.beta_summary current closed) .none pending accepted

theorem request_result
    (source : Owners.Derives operations policy contracts inside world environment allowed scope before
      (.perform (Instantiation.freezeEffect effect) operation operand) after output demand row) :
    ∃ input, operations effect operation = some (input, output) := by
  generalize eq : Instantiation.freezeEffect effect = requested at source
  cases source with
  | stable summary exported => cases summary with
      | perform known admitted operand formed =>
          cases ScopedExecution.freeze_effect_injective eq
          exact ⟨_, known⟩
  | perform known admitted operand formed exported =>
      cases ScopedExecution.freeze_effect_injective eq
      exact ⟨_, known⟩

/-- Both full annotations come from the same request and selected stack.
    Ordinary ports, source protection and nested authentication are projections
    of that witness, rather than independently chosen derivations. -/
theorem capture_interface (cut : HandlerCut requested whole capture tail handler)
    (source : Source operations policy contracts tables world fixed outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole before after output demand row) :
    ∃ argument input answer start between savedDemand restDemand savedRow restRow,
      operations requested operation = some (argument, input) ∧
      answer.port = ScopedPorts.eraseType handler.answer ∧
      Segment operations policy contracts tables world (tail.append fixed) capture start input between answer savedDemand savedRow ∧
      Segment operations policy contracts tables world fixed tail between answer after output restDemand restRow ∧
      ScopedPorts.StackTyped operations.ports contracts.ports.types world capture input.port answer.port ∧
      OwnerSource.Segment operations.protection policy contracts.source tables (tail.append fixed) capture
        start input.protection between answer.protection savedDemand savedRow ∧
      CaptureAuthentication.Retained operations.protection policy contracts.source tables capture := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨argument, known⟩ := request_result current
      obtain ⟨between, answer, savedDemand, restDemand, savedRow, restRow, annotation, saved, rest, names, effects⟩ := capture_answer cut pending
      exact ⟨argument, _, answer, _, between, savedDemand, restDemand, savedRow, restRow,
        known, annotation, saved, rest, segment_ports saved, segment_source saved, segment_authenticated saved⟩

theorem capture_step_record (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (closed : ClosedValue operand) (environmentReady : ClosedExcept parameter body)
    (source : Source operations policy contracts tables world fixed outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole before after output demand row)
    (fresh : contracts owner = none) (consumed : before owner = .consumed)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance) :
    ∃ argument, ∃ contract : Owners.Contract, ∃ between restDemand restRow,
      operations requested operation = some (argument, contract.input) ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort contract.input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      Segment operations policy (contracts.insert owner contract) tables world fixed
        (.live owner (ScopedPorts.embedPort contract.input.port) handler.answer capture handler.scope tail)
        between contract.answer after output restDemand restRow := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨argument, known⟩ := request_result current
      obtain ⟨raw, summary, same, noDemand, exported⟩ := OwnerSource.request_summary (Owners.owner_source current) closed.1
      obtain ⟨contract, between, restDemand, restRow, inputSame, answerAnnotation, closeDemandSame, closeRowSame,
        resumeEffectsSame, closeEffectsSame, boundary, names, effects⟩ :=
        capture_record cut pending fresh (same ▸ consumed) closeDemand closeRow resumeEffects closeEffects
      rw [← inputSame] at known boundary
      exact ⟨argument, contract, between, restDemand, restRow, known,
        .capture requested operation parameter binder owner operand body scope whole capture tail handler
          (ScopedPorts.embedPort contract.input.port) cut clause closed environmentReady, boundary⟩

namespace Examples
open OwnerPhaseTransitions (empty)

def effect : Instance := .user 81 []
def operations : Operations := fun request operation =>
  if request = effect ∧ operation = 0 then some (.unit, .integer) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def contract : Owners.Contract := ⟨.integer, .boolean, false, [], [], [], none, [], []⟩
def contracts : Contracts := fun owner => if owner = 19 then some contract else none
def tables : CallableProtectionFrames.Tables := fun _ => [(0, ⟨false, some [], some []⟩)]
def handler : HandlerData := ⟨3, effect, .cons 0 2 7 (.resume 7 (.integer 17)) .nil, .none, .boolean, rfl⟩
def plain : PlainData := ⟨.bind 8 (.boolean true), .none, .integer, .boolean, [], rfl⟩
def capture : Stack := .push (.plain plain) (.push (.handler handler) .nil)
def nested : Stack := .live 19 .integer .boolean capture .none .nil

theorem operation_known : operations effect 0 = some (.unit, .integer) := by decide
theorem owner_known : contracts 19 = some contract := by decide

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  refine .handler (residual := []) ⟨.none, .none⟩ (.cons (port_lookup operation_known)
    (.resume .integer (by simp) (by simp [ScopedPorts.InWorld, handler, ScopedPorts.eraseType, ScopedPorts.Port.resources])) .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · subst operation
    simp [handler, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, handler] at known

theorem plain_shared : Frame operations policy contracts inside [] (.plain plain) empty .integer empty .boolean [] [] :=
  .plain (allowed := []) (.bind (.stable .boolean (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))) .none rfl rfl

theorem captured_shared : Segment operations policy contracts tables [] fixed capture empty .integer empty .boolean [] [] :=
  .push plain_shared (.push (.handler handler_typed rfl) .nil)

theorem selected_cut : HandlerCut effect capture capture .nil handler := by
  exact .push (.plain plain) (.push (.handler handler) .nil) (.push (.handler handler) .nil) .nil handler
    (by decide) (.hit handler .nil rfl)

theorem request_shared : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables capture) [] Environment.empty [effect] .none
    empty (.perform (Instantiation.freezeEffect effect) 0 .unit) empty .integer [] [] := by
  have operand : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables capture) [] Environment.empty [effect] .none
      empty .unit empty .unit [] [] := .stable .unit (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .perform operation_known List.mem_cons_self operand
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) (by decide)

theorem captured_configuration : Source operations policy contracts tables [] .nil [] .none
    (.perform (Instantiation.freezeEffect effect) 0 .unit) capture empty empty .boolean [] [] :=
  .checked request_shared .none (fixed := Stack.nil) captured_shared (by decide)

theorem fresh_capture_record :
    ∃ recorded : Owners.Contract, ∃ between remaining row,
      recorded.input = .integer ∧
      RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, capture⟩
        ⟨.resume 7 (.integer 17), .ticket 7 23, .live 23 .integer .boolean capture .none .nil⟩ [.ticket 23] [] ∧
      Segment operations policy (contracts.insert 23 recorded) tables [] .nil
        (.live 23 .integer .boolean capture .none .nil) between recorded.answer empty .boolean remaining row ∧
      (contracts.insert 23 recorded) 19 = some contract := by
  have clause : ClauseAt 0 handler.clauses 2 7 (.resume 7 (.integer 17)) := .hit
  obtain ⟨argument, recorded, between, remaining, row, known, step, boundary⟩ :=
    capture_step_record selected_cut clause CallableProtection.Examples.unit_closed
      (by intro name member; simp [Code.dependencies] at member) captured_configuration
      (owner := 23) (by decide) rfl [] none [] []
  have same : recorded.input = Value.integer := congrArg Prod.snd (Option.some.inj (known.symm.trans operation_known))
  refine ⟨recorded, between, remaining, row, same, ?_, ?_, ?_⟩
  · simpa only [same, Value.port, ScopedPorts.embedPort, Code.subst, handler] using step
  · simpa only [same, Value.port, ScopedPorts.embedPort, handler] using boundary
  · simpa only [Owners.Contracts.insert, if_neg (by decide : ¬ (19 = 23))] using owner_known

theorem different_atom_annotations :
    Compatible Value.integer.protection Value.boolean.port ∧ Value.integer.port ≠ Value.boolean.port :=
  ⟨rfl, by decide⟩

theorem capture_both_projections :
    ScopedPorts.StackTyped operations.ports contracts.ports.types [] capture .integer .boolean ∧
    OwnerSource.Segment operations.protection policy contracts.source tables .nil capture empty .scalar empty .scalar [] [] :=
  ⟨segment_ports (fixed := Stack.nil) captured_shared, segment_source (fixed := Stack.nil) captured_shared⟩

theorem nested_shared : Segment operations policy contracts tables [] .nil nested empty .boolean empty .boolean [] [] :=
  .live owner_known rfl rfl ⟨.none, .none⟩ rfl rfl (receiver := Stack.nil) captured_shared (EffectBounds.covers_refl []) .nil

theorem nested_authenticated : CaptureAuthentication.Retained operations.protection policy contracts.source tables nested :=
  segment_authenticated nested_shared

theorem wrong_plain_metadata_rejected :
    ¬ Frame operations policy contracts inside [] (.plain { plain with input := .unit }) empty .integer after output demand row := by
  intro frame
  have mismatch := (frame_annotations frame).1
  cases mismatch

theorem wrong_capture_metadata_rejected :
    ¬ Segment operations policy contracts tables [] fixed (.live 19 .boolean .boolean capture .none .nil)
      empty input after output demand row := by
  intro segment
  cases segment with
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail =>
      have same := Option.some.inj (known.symm.trans owner_known)
      subst_vars
      cases inputAnnotation

theorem owner_transition : Trace (OwnerPhaseTransitions.introduce empty 19) [19] empty := by
  apply Trace.cons (by simp [OwnerPhaseTransitions.introduce])
  rw [OwnerCaptureContracts.spend_introduced (by rfl)]
  exact .nil

def resumePlain : PlainData := ⟨.resume 7, .ticket 7 19, .integer, .boolean, [19], rfl⟩

theorem pending_resume_shared : Frame operations policy contracts inside [] (.plain resumePlain)
    (OwnerPhaseTransitions.introduce empty 19) .integer empty .boolean [19] [] := by
  have context : Context operations policy contracts inside [] Environment.empty [] (.ticket 7 19) (.resume 7)
      (OwnerPhaseTransitions.introduce empty 19) .integer empty .boolean [19] [] :=
    .resume owner_known rfl rfl owner_transition (by simp [contract])
      (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .plain context (.bound (Owners.ports_lookup owner_known)) rfl rfl

theorem resume_before : Source operations policy contracts tables [] .nil [] (.ticket 7 19) (.resume 7 (.integer 17))
    nested (OwnerPhaseTransitions.introduce empty 19) empty .boolean [19] [] := by
  have operand : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (nested.append .nil)) [] Environment.empty [] (.ticket 7 19)
      (OwnerPhaseTransitions.introduce empty 19) (.integer 17) (OwnerPhaseTransitions.introduce empty 19) .integer [] [] :=
    .stable .integer (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  have current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (nested.append .nil)) [] Environment.empty [] (.ticket 7 19)
      (OwnerPhaseTransitions.introduce empty 19) (.resume 7 (.integer 17)) empty .boolean [19] [] :=
    .resume owner_known rfl rfl operand owner_transition (by simp [contract])
      (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked current (.bound (Owners.ports_lookup owner_known)) nested_shared (by decide)

theorem resumed_segment : Segment operations policy contracts tables [] .nil
    (capture.append (.spent 19 .boolean .none .nil)) empty .integer empty .boolean [] [] :=
  segment_append captured_shared (.spent owner_known rfl ⟨.none, .none⟩ rfl .nil)

theorem resume_after : Source operations policy contracts tables [] .nil [] (.ticket 7 19) (.integer 17)
    (capture.append (.spent 19 .boolean .none .nil)) empty empty .boolean [] [] := by
  have current : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables ((capture.append (.spent 19 .boolean .none .nil)).append .nil)) [] Environment.empty [] (.ticket 7 19)
      empty (.integer 17) empty .integer [] [] :=
    .stable .integer (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked current (.bound (Owners.ports_lookup owner_known)) resumed_segment (by decide)

theorem resume_step :
    RawStep ⟨.resume 7 (.integer 17), .ticket 7 19, nested⟩
      ⟨.integer 17, .ticket 7 19, capture.append (.spent 19 .boolean .none .nil)⟩ [] [.ticket 19] ∧
    Source operations policy contracts tables [] .nil [] (.ticket 7 19) (.resume 7 (.integer 17))
      nested (OwnerPhaseTransitions.introduce empty 19) empty .boolean [19] [] ∧
    Source operations policy contracts tables [] .nil [] (.ticket 7 19) (.integer 17)
      (capture.append (.spent 19 .boolean .none .nil)) empty empty .boolean [] [] :=
  ⟨.resume 7 19 (.ticket 7 19) .none .integer .boolean .nil capture .nil (.integer 17)
    ⟨trivial, rfl, by intro dependency member; cases member⟩ rfl, resume_before, resume_after⟩

end Examples

end Ash.OneShot.SharedSourceSegments

#print axioms Ash.OneShot.SharedSourceSegments.context_source
#print axioms Ash.OneShot.SharedSourceSegments.context_ports
#print axioms Ash.OneShot.SharedSourceSegments.context_plug
#print axioms Ash.OneShot.SharedSourceSegments.stable_context
#print axioms Ash.OneShot.SharedSourceSegments.focus_decompose
#print axioms Ash.OneShot.SharedSourceSegments.frame_source
#print axioms Ash.OneShot.SharedSourceSegments.frame_annotations
#print axioms Ash.OneShot.SharedSourceSegments.types_lookup
#print axioms Ash.OneShot.SharedSourceSegments.frame_ports
#print axioms Ash.OneShot.SharedSourceSegments.context_extension
#print axioms Ash.OneShot.SharedSourceSegments.frame_extension
#print axioms Ash.OneShot.SharedSourceSegments.segment_source
#print axioms Ash.OneShot.SharedSourceSegments.segment_ports
#print axioms Ash.OneShot.SharedSourceSegments.segment_authenticated
#print axioms Ash.OneShot.SharedSourceSegments.segment_trace
#print axioms Ash.OneShot.SharedSourceSegments.segment_once
#print axioms Ash.OneShot.SharedSourceSegments.segment_extension
#print axioms Ash.OneShot.SharedSourceSegments.segment_append
#print axioms Ash.OneShot.SharedSourceSegments.segment_decompose
#print axioms Ash.OneShot.SharedSourceSegments.capture_segment
#print axioms Ash.OneShot.SharedSourceSegments.capture_answer
#print axioms Ash.OneShot.SharedSourceSegments.capture_record
#print axioms Ash.OneShot.SharedSourceSegments.source_owner
#print axioms Ash.OneShot.SharedSourceSegments.source_ports
#print axioms Ash.OneShot.SharedSourceSegments.source_authenticated
#print axioms Ash.OneShot.SharedSourceSegments.source_bind
#print axioms Ash.OneShot.SharedSourceSegments.source_beta
#print axioms Ash.OneShot.SharedSourceSegments.request_result
#print axioms Ash.OneShot.SharedSourceSegments.capture_interface
#print axioms Ash.OneShot.SharedSourceSegments.capture_step_record
#print axioms Ash.OneShot.SharedSourceSegments.Examples.operation_known
#print axioms Ash.OneShot.SharedSourceSegments.Examples.owner_known
#print axioms Ash.OneShot.SharedSourceSegments.Examples.handler_typed
#print axioms Ash.OneShot.SharedSourceSegments.Examples.plain_shared
#print axioms Ash.OneShot.SharedSourceSegments.Examples.captured_shared
#print axioms Ash.OneShot.SharedSourceSegments.Examples.selected_cut
#print axioms Ash.OneShot.SharedSourceSegments.Examples.request_shared
#print axioms Ash.OneShot.SharedSourceSegments.Examples.captured_configuration
#print axioms Ash.OneShot.SharedSourceSegments.Examples.fresh_capture_record
#print axioms Ash.OneShot.SharedSourceSegments.Examples.different_atom_annotations
#print axioms Ash.OneShot.SharedSourceSegments.Examples.capture_both_projections
#print axioms Ash.OneShot.SharedSourceSegments.Examples.nested_shared
#print axioms Ash.OneShot.SharedSourceSegments.Examples.nested_authenticated
#print axioms Ash.OneShot.SharedSourceSegments.Examples.wrong_plain_metadata_rejected
#print axioms Ash.OneShot.SharedSourceSegments.Examples.wrong_capture_metadata_rejected
#print axioms Ash.OneShot.SharedSourceSegments.Examples.owner_transition
#print axioms Ash.OneShot.SharedSourceSegments.Examples.pending_resume_shared
#print axioms Ash.OneShot.SharedSourceSegments.Examples.resume_before
#print axioms Ash.OneShot.SharedSourceSegments.Examples.resumed_segment
#print axioms Ash.OneShot.SharedSourceSegments.Examples.resume_after
#print axioms Ash.OneShot.SharedSourceSegments.Examples.resume_step
