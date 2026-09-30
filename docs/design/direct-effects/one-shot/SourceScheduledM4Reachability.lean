import SourceScheduledPreservation

/-! Finite reachable traces for the source-constructed one-shot interface.

Requests and realizations remain the data-only M3 relations. A reachable
endpoint is represented by `ValidSnapshot`; its proof is supplied by M3's
constructive preservation theorem, rather than being a premise of a request
or a realization. This file proves finite reachable-state safety only. It
does not select an applicable request at a nonterminal state and therefore does
not claim progress or termination. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Reachability

open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open Preservation

structure ValidSnapshot
    (operations : Operations) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (ambient : List Nat) (budget : Footprint) (ports : OperationRows operations)
    (emptyRows : EnvironmentRows (fun _ => none)) (output : Value)
    (outputRows : ValueRows output) where
  snapshot : Snapshot operations
  valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot

abbrev Admitted (operations : Operations) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (ambient : List Nat) (budget : Footprint)
    (ports : OperationRows operations) (emptyRows : EnvironmentRows (fun _ => none))
    (output : Value) (outputRows : ValueRows output) : Type :=
  ValidSnapshot operations policy outward ambient budget ports emptyRows output outputRows

structure ChosenStep
    (operations : Operations) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (ambient : List Nat) (budget : Footprint) (ports : OperationRows operations)
    (emptyRows : EnvironmentRows (fun _ => none)) (output : Value)
    (outputRows : ValueRows output)
    (before after : Admitted operations policy outward ambient budget ports emptyRows output outputRows) where
  request : Request before.snapshot
  event : LexicalUnwind.Event before.snapshot.run.execution after.snapshot.run.execution
  realizes : Realizes request after.snapshot

inductive Trace
    (operations : Operations) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (ambient : List Nat) (budget : Footprint) (ports : OperationRows operations)
    (emptyRows : EnvironmentRows (fun _ => none)) (output : Value)
    (outputRows : ValueRows output)
    (initial : Admitted operations policy outward ambient budget ports emptyRows output outputRows) :
    Admitted operations policy outward ambient budget ports emptyRows output outputRows → Prop where
  | refl : Trace operations policy outward ambient budget ports emptyRows output outputRows initial initial
  | step {before after : Admitted operations policy outward ambient budget ports emptyRows output outputRows}
      (pre : Trace operations policy outward ambient budget ports emptyRows output outputRows initial before)
      (chosen : ChosenStep operations policy outward ambient budget ports emptyRows output outputRows before after) :
      Trace operations policy outward ambient budget ports emptyRows output outputRows initial after

namespace Trace

theorem endpoint_valid
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {initial final : Admitted operations policy outward ambient budget ports emptyRows output outputRows}
    (_trace : Trace operations policy outward ambient budget ports emptyRows output outputRows initial final) :
    Valid policy outward ambient budget ports emptyRows output outputRows final.snapshot :=
  final.valid

/-- M3 supplies a valid endpoint and the corresponding event and realization
for every applicable request. -/
theorem preserving_step
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {initial before : Admitted operations policy outward ambient budget ports emptyRows output outputRows}
    (pre : Trace operations policy outward ambient budget ports emptyRows output outputRows initial before)
    (request : Request before.snapshot) :
    ∃ after : Admitted operations policy outward ambient budget ports emptyRows output outputRows,
      LexicalUnwind.Event before.snapshot.run.execution after.snapshot.run.execution ∧
      Realizes request after.snapshot ∧
      Trace operations policy outward ambient budget ports emptyRows output outputRows initial after := by
  obtain ⟨after, event, realizes, valid⟩ := Preservation.preservation before.valid request
  let next : Admitted operations policy outward ambient budget ports emptyRows output outputRows :=
    ⟨after, valid⟩
  exact ⟨next, event, realizes, .step pre ⟨request, event, realizes⟩⟩

theorem chosen_event
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {before after : Admitted operations policy outward ambient budget ports emptyRows output outputRows}
    (chosen : ChosenStep operations policy outward ambient budget ports emptyRows output outputRows before after) :
    LexicalUnwind.Event before.snapshot.run.execution after.snapshot.run.execution :=
  chosen.event

end Trace

theorem one_step
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    (initial : Admitted operations policy outward ambient budget ports emptyRows output outputRows)
    (request : Request initial.snapshot) :
    ∃ after : Admitted operations policy outward ambient budget ports emptyRows output outputRows,
      LexicalUnwind.Event initial.snapshot.run.execution after.snapshot.run.execution ∧
      Realizes request after.snapshot ∧
      Trace operations policy outward ambient budget ports emptyRows output outputRows initial after :=
  Trace.preserving_step .refl request

/-- Package an existing M2 complete state as a reachable-trace seed. -/
def initial_of_state
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {contracts : Contracts} {tables : CallableProtectionFrames.Tables}
    {families : SourceDependencyFrames.Families} {required : SourceContextualRechecking.Required}
    {annotations : Nat → Option SourceDependencyCapture.Scope} {world history : List Nat}
    {resumes disposals annotatedStore : RecursiveRequirements.Store}
    {owners : ContractRows contracts} {run : LexicalUnwind.UseRunState}
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient
      history resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    Admitted operations policy outward ambient budget ports emptyRows output outputRows :=
  ⟨Snapshot.ofState state, valid_ofState state⟩

theorem initial_of_state_valid
    {operations : Operations} {policy : Syntax.TicketPolicy} {outward : List Instance}
    {ambient : List Nat} {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)} {output : Value}
    {outputRows : ValueRows output}
    {contracts : Contracts} {tables : CallableProtectionFrames.Tables}
    {families : SourceDependencyFrames.Families} {required : SourceContextualRechecking.Required}
    {annotations : Nat → Option SourceDependencyCapture.Scope} {world history : List Nat}
    {resumes disposals annotatedStore : RecursiveRequirements.Store}
    {owners : ContractRows contracts} {run : LexicalUnwind.UseRunState}
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient
      history resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    Valid policy outward ambient budget ports emptyRows output outputRows
      (initial_of_state state).snapshot :=
  (initial_of_state state).valid

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Reachability

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Reachability.Trace.preserving_step
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Reachability.Trace.endpoint_valid
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Reachability.initial_of_state
