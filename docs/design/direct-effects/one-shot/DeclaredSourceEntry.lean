import DeclaredSourceTransport
import SourceClauseCapture

/-! Source-derived handler entry retains hereditary clause declarations.
    This connects the stronger executable expression to the existing entry,
    requirement and ownership proofs. General executable-frame transport and
    upper effect-bound admission are still separate obligations. -/
namespace Ash.OneShot.DeclaredSourceEntry
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open RecursiveCapture (AnnotatedSegment)
open DeclaredSources (Expression Declarations)

def FrameDeclarations (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) : ExecFrame → Value → Value → Prop
  | .handler handler, answer, _ => ∃ allowed,
      Declarations operations policy contracts world Environment.empty allowed handler.effectInst answer handler.clauses (tables handler)
  | _, _, _ => True

/-- Handler declarations are hereditary. Other saved frame expressions still
    use SourceTemplates.Frame; this is not yet full executable-frame admission. -/
abbrev HandlerSegment operations policy contracts tables world :=
  AnnotatedSegment (fun entry input output _ _ => FrameDeclarations operations policy contracts tables world entry input output) operations policy contracts tables world

theorem FrameDeclarations.erase
    (source : FrameDeclarations operations policy contracts tables world entry input output) :
    SourceClauseCapture.FrameSource operations policy contracts tables world entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, clauses.erase⟩

theorem segment_erase
    (source : HandlerSegment operations policy contracts tables world stack input output demand requirements records) :
    SourceClauseCapture.DeclaredSegment operations policy contracts tables world stack input output demand requirements records :=
  source.extension (fun _ _ known => known) (fun _ _ _ _ _ current => current.erase)

theorem FrameDeclarations.world_weaken
    (source : FrameDeclarations operations policy contracts tables world entry input output)
    (larger : world ⊆ next) :
    FrameDeclarations operations policy contracts tables next entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, DeclaredSourceTransport.declarations_world_weaken clauses larger⟩

theorem segment_world_weaken
    (source : HandlerSegment operations policy contracts tables world stack input output demand requirements records)
    (larger : world ⊆ next) :
    HandlerSegment operations policy contracts tables next stack input output demand requirements records :=
  source.world_weaken larger (fun _ _ _ _ _ current => current.world_weaken larger)

theorem FrameDeclarations.extension
    (source : FrameDeclarations operations policy contracts tables world entry input output)
    (grows : contracts.Extends next) :
    FrameDeclarations operations policy next tables world entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, DeclaredSourceTransport.declarations_extension clauses grows⟩

theorem segment_extension
    (source : HandlerSegment operations policy contracts tables world stack input output demand requirements records)
    (grows : contracts.Extends next) :
    HandlerSegment operations policy next tables world stack input output demand requirements records :=
  source.extension grows (fun _ _ _ _ _ current => current.extension grows)

theorem FrameDeclarations.tables_congr
    (source : FrameDeclarations operations policy contracts first world entry input output)
    (agree : ∀ handler, handler.activation ∈ entry.erase.activation → first handler = second handler) :
    FrameDeclarations operations policy contracts second world entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, agree handler List.mem_cons_self ▸ clauses⟩

theorem segment_tables_congr
    (source : HandlerSegment operations policy contracts first world stack input output demand requirements records)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    HandlerSegment operations policy contracts second world stack input output demand requirements records :=
  RecursiveHandlerTables.annotated_segment_congr source
    (fun _ _ _ _ _ agreed current => current.tables_congr agreed) agree

/-- The executable source rule supplies the declaration. The successor retains
    the stronger current body and handler annotations as well as the existing
    checked-state and exact ownership results. No successor check is assumed. -/
theorem handler_entry
    (current : Expression operations policy contracts world allowed scope Environment.empty
      (.handle requested code clauses) answer bodyDemand requirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : HandlerSegment operations policy contracts tables world stack answer output tailDemand tailRequirements resumes)
    (closing : RecursiveRecords.Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) tailRequirements) row)
    (accepted : checkFootprint outside row = true)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, ∃ table activeAllowed, ∃ bodyRequirements : Requirements bodyDemand,
      handler.activation ∉ history ∧
      RecursiveHandlerTables.register tables handler.activation table handler = table ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      Expression operations policy contracts world activeAllowed scope Environment.empty code answer bodyDemand bodyRequirements ∧
      FrameDeclarations operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        world (.handler handler) answer answer ∧
      HandlerSegment operations policy contracts (RecursiveHandlerTables.register tables handler.activation table) world
        (.push (.handler handler) stack) answer output tailDemand
        (.sequence ((Requirements.request [] []).prepend
          (OwnerPhases.ofStack (RecursiveHandlerTables.register tables handler.activation table) stack)) tailRequirements) resumes ∧
      RecursiveRecords.CheckedState operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        world outside scope code (.push (.handler handler) stack) output (bodyDemand ++ tailDemand) row ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack := by
  obtain ⟨effect, residual, table, bodyRequirements, rfl, rfl, body, clausesTyped, capabilities,
    coverage, clauseUnique, admitted, modes, declarations⟩ := DeclaredSources.handler_parts current
  obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
  have bodyCheck := RecursiveRequirements.checked_prepend_iff.mp
    (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
  simp only [List.append_nil, List.cons_append, List.nil_append] at bodyCheck
  obtain ⟨handler, fresh, installed, step, successor, owners, clausesSame, effectSame, frame⟩ :=
    RecursiveHandlerTables.handler_entry_with_frame (DeclaredSources.expression_erase body) scopeTyped clausesTyped
      coverage clauseUnique pending.erase closing unique bodyCheck tailCheck (sameRow ▸ accepted) retained
  have after := segment_tables_congr pending
    (RecursiveHandlerTables.register_agrees (clauses := table) (fun member => fresh (retained member)))
  have annotation : FrameDeclarations operations policy contracts
      (RecursiveHandlerTables.register tables handler.activation table) world (.handler handler) answer answer := by
    refine ⟨residual, ?_⟩
    simpa only [effectSame, clausesSame, installed] using declarations
  exact ⟨handler, table, effect :: residual, bodyRequirements, fresh, installed, step, body,
    annotation, .push annotation frame after, sameRow.symm ▸ successor, owners⟩

namespace Examples
open SourceCallableExamples (operations policy contracts body bodyRequirements)

def tables : CallableProtectionFrames.Tables := fun _ => []

theorem executable_handler_entry :
    ∃ handler : HandlerData, ∃ table activeAllowed, ∃ requirements : Requirements [],
      RawStep ⟨body, .none, .nil⟩
        ⟨.perform (Instantiation.freezeEffect SourceCallableExamples.effect) 0 .unit,
          .none, .push (.handler handler) .nil⟩ [] [] ∧
      Expression operations policy contracts [] activeAllowed .none Environment.empty
        (.perform (Instantiation.freezeEffect SourceCallableExamples.effect) 0 .unit) .unit [] requirements ∧
      FrameDeclarations operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        [] (.handler handler) .unit .unit ∧
      RecursiveRecords.CheckedState operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        [] [] .none (.perform (Instantiation.freezeEffect SourceCallableExamples.effect) 0 .unit)
        (.push (.handler handler) .nil) .unit [] [] := by
  have current := DeclaredSources.Examples.body_source contracts Environment.empty
  have checked : Checked [] [] (OwnerPhaseTransitions.available [])
      (.sequence (bodyRequirements.prepend []) (.request [] [])) [] := by
    apply Checked.sequence (firstRow := []) (secondRow := [])
    · apply RecursiveRequirements.checked_prepend_iff.mpr
      apply RecursiveRequirements.evaluate_sound
      rw [RecursiveOutward.evaluation SourceCallableExamples.body_outward]
      rfl
    · exact .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  obtain ⟨handler, table, activeAllowed, requirements, fresh, installed, step, bodySource, declaration, pending, successor, owners⟩ :=
    handler_entry (tables := tables) (history := []) current .none .nil .nil (by simp [ownedTickets])
      checked (by rfl) (by intro activation member; cases member)
  exact ⟨handler, table, activeAllowed, requirements, step, bodySource, declaration, successor⟩

end Examples
end Ash.OneShot.DeclaredSourceEntry
#print axioms Ash.OneShot.DeclaredSourceEntry.FrameDeclarations.erase
#print axioms Ash.OneShot.DeclaredSourceEntry.segment_erase
#print axioms Ash.OneShot.DeclaredSourceEntry.FrameDeclarations.world_weaken
#print axioms Ash.OneShot.DeclaredSourceEntry.segment_world_weaken
#print axioms Ash.OneShot.DeclaredSourceEntry.FrameDeclarations.extension
#print axioms Ash.OneShot.DeclaredSourceEntry.segment_extension
#print axioms Ash.OneShot.DeclaredSourceEntry.FrameDeclarations.tables_congr
#print axioms Ash.OneShot.DeclaredSourceEntry.segment_tables_congr
#print axioms Ash.OneShot.DeclaredSourceEntry.handler_entry
#print axioms Ash.OneShot.DeclaredSourceEntry.Examples.executable_handler_entry
