import CoreCallableGeneratedBindProducers
import CoreCallableInitialChronology
namespace Ash.OneShot.CoreCallableGeneratedBindConsumers
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedChronology CoreCallableInitialChronology CoreCallableGeneratedBindProducers

noncomputable def bind_from_initial {graph : Graph} {code : Code}
    {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged)
    (ready : BindReady current) : BindInput current :=
  bind_from_current_origins (checkShape_postorder graph input.shape) run.site_origins run.scope_origins ready

noncomputable def bind_from_generated {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (ready : BindReady current) : BindInput current :=
  bind_from_current_origins ordered (run.current_site_origins ordered) run.current_evaluating_scope ready

noncomputable def bind_initial_next {graph : Graph} {code : Code}
    {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) (ready : BindReady current) :
    InitialChronology input (bind_result (bind_from_initial run ready)).after (count+1) (created++[]) ([]++discharged) :=
  .next run (.bind (bind_from_initial run ready))

noncomputable def bind_generated_next {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (ready : BindReady current) :
    Generated start (bind_result (bind_from_generated ordered run ready)).after (count+1) (created++[]) ([]++discharged) :=
  .next run (.bind (bind_from_generated ordered run ready))

theorem bind_initial_actual {graph : Graph} {code : Code}
    {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) (ready : BindReady current) :
    CoreMachine.next graph current.state = .stepped (bind_result (bind_from_initial run ready)).after.state ∧
    Matching graph current (bind_result (bind_from_initial run ready)).after [] [] :=
  Operation.actual (.bind (bind_from_initial run ready))

theorem bind_generated_actual {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (ready : BindReady current) :
    CoreMachine.next graph current.state = .stepped (bind_result (bind_from_generated ordered run ready)).after.state ∧
    Matching graph current (bind_result (bind_from_generated ordered run ready)).after [] [] :=
  Operation.actual (.bind (bind_from_generated ordered run ready))

#print axioms bind_from_initial
#print axioms bind_from_generated
#print axioms bind_initial_next
#print axioms bind_generated_next
#print axioms bind_initial_actual
#print axioms bind_generated_actual
end Ash.OneShot.CoreCallableGeneratedBindConsumers
