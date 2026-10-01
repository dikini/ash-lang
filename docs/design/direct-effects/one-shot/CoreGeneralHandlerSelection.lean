import CoreCallableGeneralHistory
set_option linter.unusedSimpArgs false
namespace Ash.OneShot.CoreGeneralHandlerSelection
open CoreSyntax CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreEffectFrames CoreGeneralStack CoreGeneralCaptureResume
open CoreCallableGeneralHistory CoreRequestFrames
structure Key where
  inside : List CoreMachine.Frame
  site : Nat
  environment : CoreMachine.Environment
  occurrence : Nat
  outside : List CoreMachine.Frame

def Key.prepend (leading : List CoreMachine.Frame) (key : Key) : Key :=
  {key with inside := leading ++ key.inside}
def Key.suffix (key : Key) (suffix : List CoreMachine.Frame) : Key :=
  {key with outside := key.outside ++ suffix}
def physical_handlers : List CoreMachine.Frame → List Key
  | [] => []
  | frame :: rest =>
    let tail := (physical_handlers rest).map (Key.prepend [frame])
    match frame with
    | .handlerBoundary site environment occurrence => ⟨[],site,environment,occurrence,rest⟩ :: tail
    | _ => tail

def HandlerLocation.key (location : HandlerLocation graph heap physical target) : Key :=
  ⟨location.inside,location.site,location.environment,location.data.activation,location.outside⟩

private theorem keys_append (first second : List CoreMachine.Frame) :
    physical_handlers (first ++ second) =
      (physical_handlers first).map (fun key => key.suffix second) ++
      (physical_handlers second).map (Key.prepend first) := by
  induction first with
  | nil =>
    change physical_handlers second = (physical_handlers second).map id
    simp
  | cons frame rest ih =>
    cases frame <;> simp [physical_handlers,ih,List.map_append,List.map_map,Key.prepend,Key.suffix,List.append_assoc,Function.comp_def]

private theorem retained_keys (history : RetainedHistory graph heap physical target) :
    physical_handlers physical = [] := by
  induction history with
  | nil => rfl
  | plain frame tail ih | handler installation header tail ih | spent installation header tail ih | retiring installation header tail ih => exact ih
  | cell frame tail ih | armed installed tail ih => simp [physical_handlers,ih]
  | live installation header saved tail ihSaved ihTail => simp [keys_append,ihSaved,ihTail]

theorem inventory_keys (history : GeneralHistory graph heap physical target) :
    (handler_locations history).map HandlerLocation.key = physical_handlers physical := by
  induction history with
  | nil => rfl
  | retained history => exact (retained_keys history).symm
  | @push owners core frameTarget physical lexical frame ordinary tail ih =>
    have shape : physical_handlers (core :: physical) = (physical_handlers physical).map (Key.prepend [core]) := by
      cases core <;> try rfl
      cases ordinary
    rw [shape,← ih]
    change ((handler_locations tail).map (fun location => location.prepend (.push frame ordinary .nil))).map HandlerLocation.key =
      ((handler_locations tail).map HandlerLocation.key).map (Key.prepend [core])
    simp only [List.map_map]
    rfl
  | @handler owners site environment data physical lexical installation header tail ih =>
    simp only [physical_handlers]; rw [← ih]
    change HandlerLocation.key _ :: ((handler_locations tail).map (fun location => location.prepend (.handler installation header .nil))).map HandlerLocation.key =
      _ :: ((handler_locations tail).map HandlerLocation.key).map (Key.prepend [.handlerBoundary site environment data.activation])
    simp only [List.map_map]
    rfl
  | running receipt | unwinding installed | closing core target scope => rfl
  | @live owners handler owner occurrence dynamicTicket capturedPhysical data savedTarget physical target result installation header saved tail ihSaved ihTail =>
    simp only [physical_handlers]; rw [← ihTail]
    change ((handler_locations tail).map (fun location => location.prepend (.live installation header saved .nil))).map HandlerLocation.key =
      ((handler_locations tail).map HandlerLocation.key).map (Key.prepend [.clauseBoundary handler owner occurrence dynamicTicket (some capturedPhysical)])
    simp only [List.map_map]
    rfl
  | @spent owners handler owner occurrence dynamicTicket capturedPhysical data physical target installation header tail ihTail =>
    simp only [physical_handlers]; rw [← ihTail]
    change ((handler_locations tail).map (fun location => location.prepend (.spent installation header .nil))).map HandlerLocation.key =
      ((handler_locations tail).map HandlerLocation.key).map (Key.prepend [.clauseBoundary handler owner occurrence dynamicTicket none])
    simp only [List.map_map]
    rfl
  | append first second ihFirst ihSecond =>
    rw [keys_append,← ihFirst,← ihSecond]
    dsimp only [handler_locations]; simp only [List.map_append,List.map_map]; rfl

private theorem lookup_key
    (found : CoreMachine.findInterpreter graph effect physical =
      .ok (.handler inside site environment occurrence outside)) :
    Key.mk inside site environment occurrence outside ∈ physical_handlers physical ∧
    ∃ node handler handled body clauses, graph.node site = some node ∧
      node.kind = .handler handler handled body clauses ∧ effect = handled.instantiate environment.instantiation := by
  induction physical generalizing inside outside with
  | nil => simp [CoreMachine.findInterpreter] at found
  | cons frame rest ih =>
    have pass (found : ((do
        match ← CoreMachine.findInterpreter graph effect rest with
        | .cell cut => pure (.cell {cut with inside := frame :: cut.inside})
        | .handler front selected env activation tail => pure (.handler (frame :: front) selected env activation tail)) : Except CoreMachine.Error CoreMachine.InterpreterCut) =
        Except.ok (.handler inside site environment occurrence outside)) :
        Key.mk inside site environment occurrence outside ∈ (physical_handlers rest).map (Key.prepend [frame]) ∧
        ∃ node handler handled body clauses, graph.node site = some node ∧
          node.kind = .handler handler handled body clauses ∧ effect = handled.instantiate environment.instantiation := by
      cases selected : CoreMachine.findInterpreter graph effect rest with
      | error error => simp [selected,Bind.bind,Except.bind] at found
      | ok cut =>
        cases cut with
        | cell cut => simp [selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
        | handler front selected env activation tail =>
          simp only [selected,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq,CoreMachine.InterpreterCut.handler.injEq] at found
          obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
          obtain ⟨member,actual⟩ := ih selected
          exact ⟨List.mem_map.mpr ⟨_,member,rfl⟩,actual⟩
    cases frame with
    | resourceBoundary node key payload =>
      simp only [CoreMachine.findInterpreter] at found
      split at found
      · cases found
      · exact pass found
    | handlerBoundary selected env activation =>
      simp only [CoreMachine.findInterpreter] at found
      cases known : graph.node selected with
      | none => simp [known,Bind.bind,Except.bind] at found
      | some node =>
        cases kind : node.kind <;> simp [known,kind] at found
        rename_i handler handled body clauses
        split at found
        · simp only [Pure.pure,Except.pure,Except.ok.injEq,CoreMachine.InterpreterCut.handler.injEq] at found
          obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
          rename_i same
          exact ⟨by simp [physical_handlers],node,handler,handled,body,clauses,known,kind,same⟩
        · obtain ⟨member,actual⟩ := pass found
          exact ⟨by simp [physical_handlers,member],actual⟩
    | _ => exact pass found

private theorem boundary_effect
    (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
    (known : graph.node site = some node) (kind : node.kind = .handler handler handled body clauses)
    (matching : Instantiation.freezeEffect requested = handled.instantiate environment.instantiation) :
    data.effectInst = requested := by
  generalize coreEq : CoreMachine.Frame.handlerBoundary site environment data.activation = core at header
  generalize targetEq : ExecFrame.handler data = frame at header
  cases header with
  | handler headerKnown headerKind translated closing =>
    have dataEq := ExecFrame.handler.inj targetEq
    cases dataEq
    obtain ⟨rfl,rfl,_⟩ := CoreMachine.Frame.handlerBoundary.inj coreEq
    have nodeSame := Option.some.inj (headerKnown.symm.trans known)
    subst node
    have kindSame := CoreSyntax.Kind.handler.inj (headerKind.symm.trans kind)
    obtain ⟨rfl,rfl,rfl,rfl⟩ := kindSame
    have actual := handle_effect_at closing _ _ _ _ _ _ rfl rfl
    have same : Instantiation.freezeEffect requested = Instantiation.freezeEffect data.effectInst := matching.trans actual
    exact (Instantiation.effect_realization_unique
      (same ▸ Instantiation.frozen_effect_realizes Instantiation.Environment.empty requested)
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty data.effectInst)).symm
  | cell headerKnown headerKind => cases coreEq

/-- Recover the inventory index and effect from the actual lookup, keeping the
same inventory entry's original installation and full header together. -/
theorem handler_selection (history : GeneralHistory graph heap physical target)
    (found : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler inside site environment occurrence outside)) :
    ∃ index : Fin (handler_locations history).length,
      let location := (handler_locations history)[index]
      location.inside = inside ∧ location.site = site ∧ location.environment = environment ∧
      location.data.activation = occurrence ∧ location.outside = outside ∧ location.data.effectInst = requested := by
  obtain ⟨member,node,handler,handled,body,clauses,known,kind,matching⟩ := lookup_key found
  rw [← inventory_keys history] at member
  obtain ⟨location,inInventory,keySame⟩ := List.mem_map.mp member
  have insideSame := congrArg Key.inside keySame
  have siteSame := congrArg Key.site keySame
  have envSame := congrArg Key.environment keySame
  have activationSame := congrArg Key.occurrence keySame
  have outsideSame := congrArg Key.outside keySame
  change location.inside = inside at insideSame
  change location.site = site at siteSame
  change location.environment = environment at envSame
  change location.data.activation = occurrence at activationSame
  change location.outside = outside at outsideSame
  have effectSame := boundary_effect location.header (siteSame ▸ known) kind (envSame ▸ matching)
  obtain ⟨i,bounded,indexSame⟩ := List.getElem_of_mem inInventory
  refine ⟨⟨i,bounded⟩,?_⟩
  dsimp only
  rw [show (handler_locations history)[(⟨i,bounded⟩ : Fin (handler_locations history).length)] = location from indexSame]
  exact ⟨insideSame,siteSame,envSame,activationSame,outsideSame,effectSame⟩

/-- Actual capture consumes the index/effect constructed from the SAME current physical lookup.
Only existing current source route/scope and operation/value carriers remain inputs. -/
theorem capture_from_lookup {base : CoreMachine.State}
    (history : GeneralHistory graph base.heap physical target)
    (found : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler inside site environment occurrence outside)) :
    ∃ index : Fin (handler_locations history).length,
    let location := (handler_locations history)[index]
    location.inside = inside ∧ location.site = site ∧ location.environment = environment ∧
    location.data.activation = occurrence ∧ location.outside = outside ∧
    ∀ (prefixScope : SourceRecursiveRoutes.Scope context location.front.erase)
      (route : SourceResourceRoutes.Route outward context requested none)
      (selected : location.installation.clauses.find? (fun clause => clause.operation == operation) = some selectedClause)
      (operand : ValueRel graph operandOwners base.heap value operandCode)
      (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
        (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
      (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
      (ready : ∀ parameter binder body, ClauseAt operation location.data.clauses parameter binder body → ClosedExcept parameter body)
      (operationResult : Ty) (runtimeScope : Execution.Scope),
    ∃ (fuel : Nat) (argument : Binder) (rawBody body : Code),
      selectedClause.argument = .binder argument ∧
      ClauseAt operation location.data.clauses argument.id (CoreTranslation.ticket graph selectedClause.owner) body ∧
      translateFuel graph fuel
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        selectedClause.body = .ok rawBody ∧
      EnvCloses graph
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        base.heap (.binding argument.id value location.environment) rawBody (body.subst argument.id operandCode) ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment physical,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base selectedClause argument.id value location.installation.handler location.data.activation
          location.site location.environment location.inside location.outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph selectedClause.owner) base.nextOwner,
            .live base.nextOwner operationResult location.data.answer
              (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail⟩,
          ⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners,[]⟩
          [.ticket base.nextOwner] [] ∧
      ∃ (installation : GeneralClausePast graph location.owners location.installation.handler selectedClause.owner
            location.data.activation base.nextOwner
            (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation]) location.data)
        (header : OwnerHeader graph location.owners base.heap location.installation.handler selectedClause.owner location.data.activation location.data)
        (successor : GeneralHistory graph base.heap
          (.clauseBoundary location.installation.handler selectedClause.owner location.data.activation base.nextOwner
            (some (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation])) :: location.outside)
          (.live base.nextOwner operationResult location.data.answer
            (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail)),
        installation.site = location.site ∧ installation.environment = location.environment ∧
        HEq installation.installation location.installation ∧ installation.selected = selectedClause ∧
        installation.originalInside = location.inside ∧ installation.originalOutside = location.outside ∧
        successor = .live installation header
          (.append location.before (.handler location.installation location.header .nil)) location.after := by
  obtain ⟨index,insideSame,siteSame,envSame,activationSame,outsideSame,same⟩ := handler_selection history found
  refine ⟨index,insideSame,siteSame,envSame,activationSame,outsideSame,?_⟩
  intro prefixScope route selected operand requestCarrier plain context ready operationResult runtimeScope
  have lookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler ((handler_locations history)[index]).inside ((handler_locations history)[index]).site
        ((handler_locations history)[index]).environment ((handler_locations history)[index]).data.activation
        ((handler_locations history)[index]).outside) := by
    simpa only [insideSame,siteSame,envSame,activationSame,outsideSame] using found
  exact capture_history history index same prefixScope route lookup selected operand requestCarrier plain context ready operationResult runtimeScope

#print axioms inventory_keys
#print axioms handler_selection
#print axioms capture_from_lookup
end Ash.OneShot.CoreGeneralHandlerSelection
