import CoreCallbackRequestRoutes
import CoreGraphAdmission

/-! Construct the source and authentication of the same closed callback from
an existing Core graph derivation. Shape validation does not construct that
derivation, and graph rows do not yet construct declaration certification. -/
namespace Ash.OneShot.CoreCallbackAdmissionProducer
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission

/-- The source-owned part of StoredCallback. Declaration certification is a
separate missing producer, rather than an assumed field in this annotation. -/
structure CallbackAnnotation (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (ports : OperationRows operations) (owners : ContractRows contracts)
    (emptyRows : EnvironmentRows (fun _ => none)) (world : List Nat) (action : ActionData)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (latent : Footprint) where
  callback : SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) [] action.action
    (.function .unit .unit action.requests latent (signature plan))
  authenticated : Auth operations policy ports owners emptyRows callback (.function .unit .unit rows) .pure

/-- The supplied signature indices are preserved; this weaker endpoint does
not identify a literal private plan by signature equality. Both output layers
are constructed from the same graph proof and actual
stored closed value. Translation and resource instantiation are retained. -/
theorem callback_annotation
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      (fun _ => none) emptyRows fuel index action.action
      (.function .unit .unit action.requests latent (signature callbackPlan))
      demand requirements expressionPlan (.function .unit .unit callbackRows) expressionRows effects) :
    ∃ raw, CoreTranslation.translateFuel graph fuel ownerMap index = .ok raw ∧
      raw.instantiate resources = action.action ∧
      Nonempty (CallbackAnnotation operations policy contracts ports owners emptyRows world action callbackPlan callbackRows latent) := by
  obtain ⟨raw, translated, instantiated, source, authenticated⟩ := checked.compiled
  exact ⟨raw, translated, instantiated, ⟨{
    callback := SourcePlannedSources.Values.change_allowed (SourcePlannedSources.Values.summary source action.closed.1) action.closed.1 []
    authenticated := (authenticated.value_summary action.closed.1).value_context action.closed.1 [] .none }⟩⟩

/-- A literal callable's declared Core type and request row come from the same
actual node, preserving its full private body signature and rows. -/
theorem callback_node_metadata
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      environment environmentRows fuel index (.lambda parameter body)
      value demand requirements expressionPlan valueRows expressionRows effects) :
    ∃ node, graph.node index = some node ∧ Metadata resources node value [] := by
  cases checked with
  | lambda known kind inputType body bodyBound outward captured formed latentBound metadata =>
    exact ⟨_, known, metadata⟩

/-- Instantiated declared effects agree with the same callable request list;
this does not authenticate those effects independently of Checked. -/
theorem callback_declared_requests
    (metadata : Metadata resources node (.function .unit .unit requests latent checking) effects) :
    ∃ input output declared, node.type = .function input output declared ∧
      EffectsSame (declared.map (fun effect => effect.instantiate resources)) (allowanceEffects requests) := by
  cases node with
  | mk originalId nodeType nodeEffects source kind =>
    cases metadata.type with
    | function input output same latentBound => exact ⟨_, _, _, rfl, same⟩

theorem callback_node_requests
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      environment environmentRows fuel index (.lambda parameter body)
      (.function .unit .unit requests latent checking)
      demand requirements expressionPlan valueRows expressionRows effects) :
    ∃ node input output declared, graph.node index = some node ∧
      node.type = .function input output declared ∧
      EffectsSame (declared.map (fun effect => effect.instantiate resources)) (allowanceEffects requests) := by
  obtain ⟨node, known, metadata⟩ := callback_node_metadata checked
  obtain ⟨input, output, declared, shape, same⟩ := callback_declared_requests metadata
  exact ⟨node, input, output, declared, known, shape, same⟩

/-- The initial application is also constructed without a requested current
source or a future callback invariant. -/
theorem CallbackAnnotation.initial_source
    (annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action plan rows latent) :
    SourcePlannedSources.Expression operations policy contracts world action.requests .none (fun _ => none)
      (.app action.action .unit) .unit []
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
      (signature (.sequence .pure (.sequence .pure plan))) :=
  .app (SourcePlannedSources.Values.change_context annotation.callback action.closed.1 action.requests .none)
    .unit (List.Subset.refl _)

theorem CallbackAnnotation.initial_auth
    (annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action plan rows latent) :
    Auth operations policy ports owners emptyRows annotation.initial_source .unit
      (by simpa only [signature] using Rows.sequence Rows.pure (Rows.sequence Rows.pure rows)) :=
  .app (annotation.authenticated.value_context action.closed.1 action.requests .none) .unit
    (admitted := List.Subset.refl _)

theorem CallbackAnnotation.initial_ports
    (annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action plan rows latent) :
    ScopedPorts.Typed operations.erase.erase.ports world ScopedPorts.TypeEnv.empty .none action.requests
      (.app action.action .unit) .unit := by
  exact SourceTemplates.expression_ports
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
      (SourcePlannedSources.expression_erase annotation.initial_source))) .none

/-- The constructed application supplies the ordinary current typing seed.
No execution or desired request membership is assumed. -/
theorem CallbackAnnotation.initial_configuration
    (annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action plan rows latent) :
    ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports contracts.erase.erase.ports world
      ⟨.app action.action .unit, .none, .nil⟩ .unit action.requests := by
  exact ⟨.unit, action.requests, .checked .none annotation.initial_ports, .nil, .nil (List.Subset.refl _)⟩

/-- The same graph derivation constructs the stored source annotation and
its actual initial application typing together. The absent private declaration
certificate is not concealed in an input. -/
theorem callback_initial
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      (fun _ => none) emptyRows fuel index action.action
      (.function .unit .unit action.requests latent (signature callbackPlan))
      demand requirements expressionPlan (.function .unit .unit callbackRows) expressionRows effects) :
    ∃ _annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action callbackPlan callbackRows latent,
      (∃ raw, CoreTranslation.translateFuel graph fuel ownerMap index = .ok raw ∧ raw.instantiate resources = action.action) ∧
      ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports contracts.erase.erase.ports world
        ⟨.app action.action .unit, .none, .nil⟩ .unit action.requests := by
  obtain ⟨raw, translated, instantiated, ⟨annotation⟩⟩ := callback_annotation checked
  exact ⟨annotation, ⟨raw, translated, instantiated⟩, annotation.initial_configuration⟩

/-- Invert the actual lambda constructor before choosing its private plan.
The caller supplies the callable signature, not a candidate literal body plan. -/
theorem callback_private_annotation
    (sameAction : action.action = .lambda parameter bodyCode)
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      (fun _ => none) emptyRows fuel index (.lambda parameter bodyCode)
      (.function .unit .unit action.requests latent checking)
      demand requirements expressionPlan (.function .unit .unit suppliedRows) expressionRows effects) :
    ∃ (dependencies : Dependencies) (privatePlan : Plan dependencies) (privateRows : Rows (signature privatePlan)),
      HEq (signature privatePlan) checking ∧ HEq privateRows suppliedRows ∧
      Nonempty (CallbackAnnotation operations policy contracts ports owners emptyRows world action privatePlan privateRows latent) := by
  cases action with
  | mk identity actionCode closed actionScope answer requests =>
    dsimp only at sameAction
    subst actionCode
    cases checked with
    | lambda known kind inputType body bodyBound outward captured formed latentBound metadata =>
      obtain ⟨source, authenticated⟩ := body.sourceAuth
      refine ⟨_, _, _, HEq.rfl, HEq.rfl, ⟨{ callback := ?_, authenticated := ?_ }⟩⟩
      · exact .lambda source outward formed latentBound
      · exact .lambda authenticated captured (outward := outward) (formed := formed) (latentBound := latentBound)

/-- Recover the constructor's actual private plan and complete rows, then
construct the same stored callback's initial application and translation link. -/
theorem callback_private_initial
    (sameAction : action.action = .lambda parameter bodyCode)
    (checked : Checked graph operations policy ports resources contracts owners world ownerMap allowed scope
      (fun _ => none) emptyRows fuel index (.lambda parameter bodyCode)
      (.function .unit .unit action.requests latent checking)
      demand requirements expressionPlan (.function .unit .unit suppliedRows) expressionRows effects) :
    ∃ (dependencies : Dependencies) (privatePlan : Plan dependencies) (privateRows : Rows (signature privatePlan))
      (_annotation : CallbackAnnotation operations policy contracts ports owners emptyRows world action privatePlan privateRows latent),
      HEq (signature privatePlan) checking ∧ HEq privateRows suppliedRows ∧
      (∃ raw, CoreTranslation.translateFuel graph fuel ownerMap index = .ok raw ∧ raw.instantiate resources = action.action) ∧
      ScopedPorts.EffectConfigurationTyped operations.erase.erase.ports contracts.erase.erase.ports world
        ⟨.app action.action .unit, .none, .nil⟩ .unit action.requests := by
  obtain ⟨dependencies, privatePlan, privateRows, sameSignature, sameRows, ⟨annotation⟩⟩ :=
    callback_private_annotation sameAction checked
  obtain ⟨raw, translated, instantiated⟩ := checked.translation
  exact ⟨dependencies, privatePlan, privateRows, annotation, sameSignature, sameRows,
    ⟨raw, translated, instantiated.trans sameAction.symm⟩, annotation.initial_configuration⟩

end Ash.OneShot.CoreCallbackAdmissionProducer
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_annotation
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_node_metadata
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.CallbackAnnotation.initial_source
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.CallbackAnnotation.initial_auth
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_declared_requests
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.CallbackAnnotation.initial_ports
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.CallbackAnnotation.initial_configuration
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_node_requests
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_initial
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_private_annotation
#print axioms Ash.OneShot.CoreCallbackAdmissionProducer.callback_private_initial
