import DeclaredSharedHandlers

/-! Store source and effect annotations in one structural pending-segment
derivation. Plain contexts share the same allowed row with their caller;
handler declarations share the installed handler's residual row. Dormant
captures require an executable interface only when their selected action bound
permits resumption. No rule assumes a future successor or successful execution.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)

/-- These frames already expose their callback or provider annotations in the
runtime data. Plain contexts and handlers use the explicit shared rules below. -/
inductive LocalFrame : ExecFrame → Prop where
  | cell : LocalFrame (.cell identity payload scope answer)
  | armed : LocalFrame (.armed action)
  | running : LocalFrame (.running action value closed)
  | closing : LocalFrame (.closing identity scope)
  | retiring : LocalFrame (.retiring owner)

inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → List Instance → List Instance → Prop where
  | plain
      (context : DeclaredSourceFrames.Context operations policy contracts world Environment.empty allowed
        plain.scope plain.context input output demand requirements)
      (scope : ScopedPorts.EffectScope contracts.ports plain.scope ticket)
      (inputAnnotation : input.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.port = ScopedPorts.eraseType plain.output) :
      Frame operations policy contracts tables world (.plain plain) input output demand requirements allowed allowed
  | handler
      (scope : ScopedPorts.EffectScopeKnown contracts.ports handler.scope)
      (annotation : answer.port = ScopedPorts.eraseType handler.answer)
      (clauses : ScopedPorts.ClausesTyped operations.ports world ScopedPorts.TypeEnv.empty
        handler.effectInst answer.port residual handler.clauses)
      (coverage : ScopedPorts.Covers operations.ports handler.effectInst handler.clauses)
      (unique : (ScopedTyping.clauseKeys handler.clauses).Nodup)
      (declarations : DeclaredSources.Declarations operations policy contracts world Environment.empty residual
        handler.effectInst answer handler.clauses (tables handler))
      (capabilities : ClausesUse policy handler.clauses)
      (modes : SourceTemplates.ClauseModes handler.clauses (tables handler)) :
      Frame operations policy contracts tables world (.handler handler) answer answer [] (.request [] [])
        (handler.effectInst :: residual) residual
  | retained (kind : LocalFrame entry)
      (source : DeclaredSourceFrames.Frame operations policy contracts tables world entry input output demand requirements)
      (interface : ScopedPorts.EffectFrame operations.ports contracts.ports world entry incoming outgoing) :
      Frame operations policy contracts tables world entry input output demand requirements incoming outgoing

theorem Frame.source
    (frame : Frame operations policy contracts tables world entry input output demand requirements incoming outgoing) :
    DeclaredSourceFrames.Frame operations policy contracts tables world entry input output demand requirements := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation => exact .plain context scope inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact .handler (.handler (ScopedPorts.effect_scope_known_has_types scope)
        (annotation ▸ clauses) coverage unique) annotation declarations capabilities modes
  | retained kind source interface => exact source

theorem Frame.interface
    (frame : Frame operations policy contracts tables world entry input output demand requirements incoming outgoing) :
    ScopedPorts.EffectFrame operations.ports contracts.ports world entry incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation =>
      have environmentSame : Environment.empty.ports = ScopedPorts.TypeEnv.empty := by funext name; rfl
      exact .plain scope (by
        simpa only [inputAnnotation, outputAnnotation, environmentSame] using
          SourceTemplates.context_ports (DeclaredSourceFrames.context_erase context) scope)
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact .handler scope (annotation ▸ clauses) coverage unique
  | retained kind source interface => exact interface

inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (actions : Syntax.UsageTickets) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → RecursiveRequirements.Store →
      List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment operations policy contracts tables actions world .nil result result [] (.request [] []) [] incoming outgoing
  | push (head : Frame operations policy contracts tables world entry input middle headDemand first inner outer)
      (tail : Segment operations policy contracts tables actions world rest middle output tailDemand second records outer outgoing)
      (bound : incoming ⊆ inner) :
      Segment operations policy contracts tables actions world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : DeclaredSourceFrames.Segment operations policy contracts tables world
        capture contract.input contract.answer contract.resumeDemand body nested)
      (savedInterface : rights.resume = true →
        Segment operations policy contracts tables actions world capture contract.input contract.answer
          contract.resumeDemand body nested [] contract.resumeEffects)
      (tail : Segment operations policy contracts tables actions world rest contract.answer output
        demand requirements remaining boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Segment operations policy contracts tables actions world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) incoming outgoing
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.ports caller)
      (tail : Segment operations policy contracts tables actions world rest contract.answer output
        demand requirements records boundary outgoing)
      (bound : incoming ⊆ boundary) :
      Segment operations policy contracts tables actions world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records incoming outgoing

theorem Segment.source
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing) :
    DeclaredSourceFrames.Segment operations policy contracts tables world stack input output demand requirements records := by
  induction segment with
  | nil bound => exact .nil
  | push head tail bound ih => exact DeclaredSourceFrames.push head.source ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close bound ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation (ScopedPorts.effect_scope_known_has_types scope) held saved ihTail
  | spent known annotation scope tail bound ih =>
      exact .spent known annotation (ScopedPorts.effect_scope_known_has_types scope) ih

theorem Segment.connected
    (segment : Segment operations policy contracts tables actions world stack input output demand requirements records incoming outgoing) :
    ScopedActionInterfaces.Connected operations.ports contracts.ports actions world stack incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.interface ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close bound ihSaved ihTail =>
      exact .live (Owners.ports_lookup known) actionKnown scope ihSaved ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent (Owners.ports_lookup known) scope ih bound

inductive State (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (actions : Syntax.UsageTickets) (world : List Nat)
    (outside : ProtectionContracts.Context) (scope : Execution.Scope) (code : Code) (stack : Stack)
    (output : Value) (demand : List Nat) (row : ProtectionContracts.Footprint) : Prop where
  | checked
      (current : DeclaredSources.Expression operations policy contracts world allowed scope Environment.empty
        code input currentDemand currentRequirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
      (pending : Segment operations policy contracts tables actions world stack input output
        pendingDemand pendingRequirements resumes allowed [])
      (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
      (accepted : ProtectionContracts.checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      State operations policy contracts tables actions world outside scope code stack output demand row

theorem State.shared
    (state : State operations policy contracts tables actions world outside scope code stack output demand row) :
    DeclaredSourceInterfaces.State operations policy contracts tables actions world outside scope code stack output demand row := by
  cases state with
  | checked current scope pending closing unique evaluated accepted accounting =>
      exact .checked current scope pending.source closing unique evaluated accepted accounting pending.connected

theorem initial
    (current : DeclaredSources.Expression operations policy contracts world [] .none Environment.empty code output demand requirements)
    (empty : demand = [])
    (evaluated : Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint outside row = true) :
    State operations policy contracts tables actions world outside .none code .nil output demand row := by
  subst demand
  have currentCheck : Checked [] [] (OwnerPhaseTransitions.available []) (requirements.prepend []) row :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.nil_append] using evaluated)
  have pendingCheck : Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := .request rfl
  simpa only [List.append_nil] using
    (State.checked (tables := tables) current .none (.nil (List.Subset.refl [])) .nil (by decide)
      (Checked.sequence currentCheck pendingCheck) (by simpa only [List.append_nil] using accepted) rfl)

theorem focus
    (state : State operations policy contracts tables actions world outside scope whole stack output demand row)
    (position : Focus whole child context) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      State operations policy contracts tables actions world outside scope child
        (.push (.plain plain) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting =>
      obtain ⟨input, childDemand, restDemand, currentReq, restReq, childSource, sourceContext, sameDemand, evaluation⟩ :=
        DeclaredSourceContexts.focus_decompose current position
      obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ :=
        RecursiveContexts.prepare_plain (DeclaredSources.expression_erase current) position scopeTyped input
      have frame : Frame operations policy contracts tables world (.plain plain) input _ restDemand restReq _ _ :=
        .plain (by simpa only [contextSame, scopeSame] using sourceContext)
          (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
      refine ⟨plain, contextSame, scopeSame, ?_, ?_⟩
      · simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using position) stack
      · refine .checked childSource scopeTyped (.push frame pending (List.Subset.refl _)) (.push closing)
          unique ?_ accepted ?_
        · apply RecursiveRequirements.evaluate_sound
          have oldEvaluation := RecursiveRequirements.checked_complete checked
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveContexts.plain_context, RecursiveContexts.plain_owners, List.cons_append,
            RecursiveContexts.evaluate_plain]
          simpa only [sameDemand, PhaseRechecking.spendAll_append, ProtectionResiduals.merge_assoc] using oldEvaluation
        · simpa only [sameDemand, List.append_assoc] using accounting

theorem plug
    (state : State operations policy contracts tables actions world outside scope value
      (.push (.plain plain) tail) output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables actions world outside plain.scope (plain.context.plug value)
      tail output demand row := by
  cases state with
  | checked current scope pending closing unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase current) closed.1
      subst_vars
      cases closing with
      | push closing => cases pending with
      | push frame pending bound => cases frame with
          | retained kind source interface => cases kind
          | plain context frameScope inputAnnotation outputAnnotation =>
              obtain ⟨combined, combinedSource, evaluation⟩ := DeclaredSourceContexts.context_plug context
                (DeclaredSourceValues.expression
                  (DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary current closed.1) closed.1 _) _)
              refine .checked combinedSource frameScope pending closing unique ?_ accepted rfl
              apply RecursiveRequirements.evaluate_sound
              have oldEvaluation := RecursiveRequirements.checked_complete checked
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase current) closed.1,
                RecursiveRecomposition.merge_empty_left, OwnerPhaseTransitions.spendAll,
                RecursiveContexts.plain_owners] at oldEvaluation
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
                RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, OwnerPhaseTransitions.spendAll]
              exact oldEvaluation

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.Frame.source
#print axioms Ash.OneShot.DeclaredConnectedSources.Frame.interface
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.source
#print axioms Ash.OneShot.DeclaredConnectedSources.Segment.connected
#print axioms Ash.OneShot.DeclaredConnectedSources.State.shared
#print axioms Ash.OneShot.DeclaredConnectedSources.initial
#print axioms Ash.OneShot.DeclaredConnectedSources.focus
#print axioms Ash.OneShot.DeclaredConnectedSources.plug
