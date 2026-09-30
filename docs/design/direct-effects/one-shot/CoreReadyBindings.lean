import CoreInitialPrefix

/-! Current lexical evidence for value-ready lambda bindings over arbitrary
mapped tails. The composition reuses the existing ranked Core traversal and
value transport, followed by the ordinary bind reduction. -/
namespace Ash.OneShot.CoreReadyBindings
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreStrictPotential CoreAdministrativeTransport CoreOrdinaryCompletion CoreInitialPrefix

/-- Three actual Core transitions for one ready lambda bind. All maps and the
complete target tail are explicit; no successor interpretation is supplied. -/
theorem lambda_binding_mapped {base : CoreMachine.State}
    {site initializer body fnBody fuel fnFuel : Nat}
    {bindNode functionNode : CoreSyntax.Node} {binder parameter : CoreSyntax.Binder}
    {environment : CoreMachine.Environment} {rawInitializer rawBody rawFunction initializerCode suffix : Code}
    (ordered : Postorder graph) (known : graph.node site = some bindNode)
    (kind : bindNode.kind = .bind binder initializer body)
    (fnKnown : graph.node initializer = some functionNode)
    (fnKind : functionNode.kind = .function parameter fnBody)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (ft : CoreTranslation.translateFuel graph fnFuel owners fnBody = .ok rawFunction)
    (fnRaw : rawInitializer = .lambda parameter.id rawFunction)
    (certificate : CallableCertificate graph parameter.id fnBody rawFunction)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (closed : ClosedValue initializerCode) (ready : ClosedExcept binder.id suffix)
    (plain : PlainData) (context : plain.context = .bind binder.id suffix)
    (tail : PushedWithMaps graph base.heap annotations target) :
    let entered := { base with
      control := .evaluate initializer environment
      frames := .bind binder.id body environment :: framesOf annotations
      observations := base.observations ++ [.entered site] }
    let returned := { entered with
      control := .returned (.closure parameter.id fnBody environment)
      observations := entered.observations ++ [.entered initializer] }
    let completed := { returned with
      control := .evaluate body (.binding binder.id (.closure parameter.id fnBody environment) environment)
      frames := framesOf annotations }
    let before : Point := ⟨{ base with control := .evaluate site environment, frames := framesOf annotations },
      ⟨.bind binder.id initializerCode suffix, plain.scope, target⟩, owners, annotations⟩
    let middle : Point := ⟨entered, before.target, owners, (owners, .bind binder.id body environment) :: annotations⟩
    let lastValue : Point := ⟨returned, before.target, owners, middle.annotations⟩
    let after : Point := ⟨completed, ⟨suffix.subst binder.id initializerCode, plain.scope, target⟩, owners, annotations⟩
    Chain graph before [middle, lastValue, after] after ∧
    EnvCloses graph owners base.heap (.binding binder.id (.closure parameter.id fnBody environment) environment)
      rawBody (suffix.subst binder.id initializerCode) ∧
    RawStep before.target after.target [] [] := by
  dsimp only
  obtain ⟨initSaved, bodySaved⟩ := bind_components current
  have entry := bind_entry_same_target ordered known kind it bt current closed ready plain context tail
  rw [fnRaw] at initSaved
  obtain ⟨valueWitness, _translated⟩ := CoreAdministrativeSteps.lambda_evaluate
    (base := { base with observations := base.observations ++ [.entered site] })
    fnKnown fnKind ft certificate initSaved closed (.bind binder.id body environment :: framesOf annotations)
  have frame : PlainFrameRel graph owners base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]
    exact .bind bt bodySaved ready
  have stack := prepend_mapped frame closed (pushed_mapped tail) plain.scope
  simp only [context, Context.plug] at stack
  have transport := value_entry_mapped valueWitness rfl rfl stack
  obtain ⟨value, equal, related⟩ := valueWitness.returned
  have valueEqual : value = .closure parameter.id fnBody environment := CoreMachine.Control.returned.inj equal.symm
  cases valueEqual
  obtain ⟨_beforeReturn, next, _plug, bind, afterReturn⟩ := bind_return_mapped
    (base := { base with observations := base.observations ++ [.entered site] ++ [.entered initializer] })
    bt bodySaved ready related plain context tail plain.scope
  exact ⟨.next (.traversal entry) (.next (.value transport)
    (.last (.positive transport.successor next (.one bind) afterReturn))), bodySaved.beta_argument related, bind⟩

/-- A handler boundary prevents an ordinary flattened prefix from hiding the
current expression, scope or pushed tail. -/
theorem handler_head_pushed {graph : CoreSyntax.Graph}
    (related : OrdinaryWithMaps graph heap ((owners, .handlerBoundary site saved activation) :: rest)
      code scope result resultScope target) :
    code = result ∧ scope = resultScope ∧
      PushedWithMaps graph heap ((owners, .handlerBoundary site saved activation) :: rest) target := by
  obtain ⟨_flatPrefix, _suffix, split, flat, pushed⟩ := related
  cases flat with
  | nil => exact ⟨rfl, rfl, split.symm ▸ pushed⟩
  | @cons frameOwners core plain cores code scope result resultScope frame ready tail =>
    have same : core = .handlerBoundary site saved activation := by
      have head := congrArg (fun xs => xs.head?.map Prod.snd) split
      simpa using head.symm
    cases same
    cases frame
  | @initializer frameOwners core plain cores code scope result resultScope frame ready tail =>
    have same : core = .handlerBoundary site saved activation := by
      have head := congrArg (fun xs => xs.head?.map Prod.snd) split
      simpa using head.symm
    cases same
    cases frame
  | @request frameOwners core plain cores code scope result resultScope frame ready tail =>
    have same : core = .handlerBoundary site saved activation := by
      have head := congrArg (fun xs => xs.head?.map Prod.snd) split
      simpa using head.symm
    cases same
    cases frame
  | @resume frameOwners core plain cores code scope result resultScope frame ready tail =>
    have same : core = .handlerBoundary site saved activation := by
      have head := congrArg (fun xs => xs.head?.map Prod.snd) split
      simpa using head.symm
    cases same
    cases frame

end Ash.OneShot.CoreReadyBindings
#print axioms Ash.OneShot.CoreReadyBindings.lambda_binding_mapped
#print axioms Ash.OneShot.CoreReadyBindings.handler_head_pushed
