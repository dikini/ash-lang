import CoreCallableGeneratedBindConsumers
namespace Ash.OneShot.CoreCallableGeneratedBindProducerInterfaces
open CoreSyntax CoreMachine CoreTranslationFuel ScopedExpressions ScopedExecution
open CoreCallableGeneratedChronology CoreCallableInitialChronology CoreCallableRunningOccurrence
open CoreCallableGeneratedBindProducers CoreCallableGeneratedBindConsumers

/-- Generic actual-initial consumer: the new bind joins the same causal Core
prefix and target trace, with no separately supplied saved receipt or endpoint. -/
theorem initial_prefix_extended {graph : Graph} {code : Code}
    {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) (ready : BindReady current) :
    CoreAllocationHistory.Steps graph (count+1) (initial_endpoint input).state
      (bind_result (bind_from_initial run ready)).after.state ∧
    CoreUnwindRelation.Trace (initial_endpoint input).point.machine
      (bind_result (bind_from_initial run ready)).after.point.machine (created++[]) ([]++discharged) :=
  ⟨(bind_initial_next run ready).actual_steps,(bind_initial_next run ready).target_trace⟩

theorem generated_prefix_extended {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (ready : BindReady current) :
    CoreAllocationHistory.Steps graph (count+1) (started start).state
      (bind_result (bind_from_generated ordered run ready)).after.state ∧
    CoreUnwindRelation.Trace (started start).point.machine
      (bind_result (bind_from_generated ordered run ready)).after.point.machine (created++[]) ([]++discharged) :=
  ⟨(bind_generated_next ordered run ready).core_steps,(bind_generated_next ordered run ready).target_trace⟩

theorem initial_positive {graph : Graph} {code : Code}
    {input : InitialInput graph code} {current : Endpoint graph}
    (run : InitialChronology input current count created discharged) (ready : BindReady current) :
    CoreUnwindRelation.Positive current.point.machine (bind_result (bind_from_initial run ready)).after.point.machine [] [] :=
  produced_positive (checkShape_postorder graph input.shape) run.site_origins run.scope_origins ready

theorem generated_positive {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (ready : BindReady current) :
    CoreUnwindRelation.Positive current.point.machine (bind_result (bind_from_generated ordered run ready)).after.point.machine [] [] :=
  produced_positive ordered (run.current_site_origins ordered) run.current_evaluating_scope ready

/-- Returned controls cannot be certified as current evaluate bind readiness. -/
theorem returned_control_excluded {graph : Graph} {current : Endpoint graph}
    (ready : BindReady current) (actual : current.state.control = .returned value) : False := by
  have impossible := ready.control
  rw [actual] at impossible
  cases impossible

/-- A literal value initializer fails the existing strict bind premise. -/
theorem literal_unit_excluded {graph : Graph} {current : Endpoint graph}
    (ready : BindReady current) (literal : ready.initializerCode = .unit) : False := by
  apply ready.notValue
  rw [literal]
  trivial

#print axioms initial_prefix_extended
#print axioms generated_prefix_extended
#print axioms initial_positive
#print axioms generated_positive
#print axioms returned_control_excluded
#print axioms literal_unit_excluded
end Ash.OneShot.CoreCallableGeneratedBindProducerInterfaces
