import CoreCallableComposedRuntimeBindings
import CoreCallableGeneratedCurrentScopeOrigins
namespace Ash.OneShot.CoreCallableComposedRuntimeCurrent
open ScopedExpressions ScopedExecution CoreSyntax CoreMachine CoreValueRelation CoreStrictStack
open CoreCallableComposedResourceEntry CoreCallableComposedRuntimeBindings
open CoreCallableGeneratedChronology CoreCallableReachableResume CoreCallableSiteLineage
variable {graph : Graph} {s : Selection graph}

/-- Projection of the computed installed endpoint; no new initial history. -/
noncomputable def current (r : ReaderSelection s) : Endpoint graph where
  state := r.s12
  focus := ⟨r.suffix.subst r.binder.id r.initializer,.none,.nil⟩
  owners := []
  maps := []
  physical := r.s12.frames
  lexical := .push (.cell s.s8.nextActivation s.payload .none .integer) .nil
  history := installed_history s r
  frames := rfl

theorem current_point (r : ReaderSelection s) :
    (current r).point.state = r.p12.state ∧
    (current r).point.machine = .eval r.p12.target := ⟨rfl,rfl⟩

theorem current_empty (r : ReaderSelection s) :
    EmptyFocus (current r) (r.suffix.subst r.binder.id r.initializer) .none := ⟨rfl,rfl⟩

theorem current_sites (r : ReaderSelection s) : SiteOrigins (current r) := by
  refine ⟨.empty graph,?_,?_,?_⟩
  · intro mapped member; cases member
  · exact SiteLineage.inactive (.empty graph)
  · intro mapped member; cases member

theorem current_scopes (r : ReaderSelection s) : EvaluatedScopeOrigins (current r) := by
  refine ⟨CurrentScopeOrigin.inactive (.empty graph),?_⟩
  intro mapped member; cases member

theorem current_ticket_bound (r : ReaderSelection s) : TicketBound r.s12 (current r).lexical := by
  intro ticket
  simp [current,Stack.erase,ExecFrame.erase,Control.ticketNames]

theorem current_initial_steps (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    CoreAllocationHistory.Steps graph 12 (CoreMachine.initial graph) (current r).state :=
  installed_steps s r input checked

theorem current_closing (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    EnvCloses graph [] [] r.installedEnvironment r.rawTail (current r).focus.expression :=
  (reader_chain s r input checked).2

theorem current_old_maps (r : ReaderSelection s) :
    PushedWithMaps graph [] r.p12.annotations r.p12.target.stack :=
  .boundary (.cell s.resourceKnown s.resourceKind) .nil

theorem current_general (r : ReaderSelection s) :
    CoreGeneralStack.GeneralSegment graph (current r).state.heap (current r).physical (current r).lexical :=
  (current r).history.related

theorem current_old_related (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    CoreInitialPrefix.Related graph r.p12 := by
  refine ⟨rfl,r.suffix.subst r.binder.id r.initializer,.none,?_,?_⟩
  · exact .evaluate r.tailTranslated (current_closing r input checked)
  · exact CoreStrictStack.pushed_mapped (current_old_maps r)

#print axioms current_old_related

#print axioms current_general

#print axioms current_old_maps

#print axioms current_point
#print axioms current_empty
#print axioms current_sites
#print axioms current_scopes
#print axioms current_ticket_bound
#print axioms current_initial_steps
#print axioms current_closing
end Ash.OneShot.CoreCallableComposedRuntimeCurrent
