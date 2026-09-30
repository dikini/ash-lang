import CoreEffectFrames

/-! Request operands and selected-clause lexical carriers. These relations retain
one current closing derivation. They do not authenticate scope annotations,
freshness or reachable owner maps. -/
namespace Ash.OneShot.CoreRequestFrames
open ScopedExpressions ScopedExecution CoreValueRelation CoreEffectFrames Instantiation

private theorem argument_empty (argument : Argument) :
    argument.instantiate Instantiation.Environment.empty = argument := by
  induction argument with
  | nominal => rfl
  | resource name => cases name <;> rfl
  | apply left right ihLeft ihRight => simp only [Argument.instantiate, ihLeft, ihRight]

private theorem effect_empty (effect : Effect) :
    effect.instantiate Instantiation.Environment.empty = effect := by
  cases effect with
  | cell name => cases name <;> rfl
  | user family arguments =>
    simp only [Effect.instantiate]
    congr 1
    have same := List.map_congr_left (l := arguments) (f := Argument.instantiate Instantiation.Environment.empty) (g := id)
      (fun argument member => argument_empty argument)
    simpa only [List.map_id_fun, id_eq] using same

theorem perform_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ effect operation rawOperand closedEffect operand,
      source = .perform effect operation rawOperand → target = .perform closedEffect operation operand →
      effect.instantiate environment.instantiation = closedEffect ∧
      EnvCloses graph owners heap environment rawOperand operand := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro effect operation raw ce operand sourceEq targetEq
      have same : effect = ce ∧ raw = operand := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩
      exact ⟨effect_empty effect, .empty⟩
  | @binding owners heap value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      obtain ⟨effectEq, child⟩ := ihTail effect operation (raw.subst binder valueCode) ce operand
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨effectEq, .binding replacement child⟩
  | @resource owners heap rest output binder key code tail ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      obtain ⟨effectEq, child⟩ := ihTail
        (effect.instantiate (Instantiation.Environment.empty.bind binder key)) operation
        (raw.instantiate (Instantiation.Environment.empty.bind binder key)) ce operand
        (by simp only [sourceEq, Code.instantiate]) targetEq
      rw [effect_single] at effectEq
      have instantiation : (CoreMachine.Environment.resource binder key rest).instantiation =
          rest.instantiation.bind binder key := by
        funext name
        simp [CoreMachine.Environment.instantiation, CoreMachine.Environment.resourceKey, Instantiation.Environment.bind]
      exact ⟨by rw [instantiation]; exact effectEq, .resource child⟩
  | @templateUnused binder owners heap rest code output parameter body absent tail ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      obtain ⟨effectEq, child⟩ := ihTail effect operation raw ce operand sourceEq targetEq
      have absentChild : Syntax.Dependency.variable binder ∉ raw.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right _ member
      exact ⟨effectEq, .templateUnused absentChild child⟩
  | @templateExpand fuel body bodyCode parameter binder heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      obtain ⟨effectEq, child⟩ := ihTail effect operation (raw.subst binder valueCode) ce operand
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨effectEq, .templateExpand translated callable nonrecursive replacement closed child⟩

theorem perform_header_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ effect operation rawOperand closedEffect operand,
      source = .perform effect operation rawOperand → target = .perform closedEffect operation operand →
      EnvCloses graph owners heap environment (.perform effect operation .unit) (.perform closedEffect operation .unit) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro effect operation raw ce operand sourceEq targetEq
      have same : effect = ce ∧ raw = operand := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩
      exact .empty
  | @binding owners heap value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      have header := ihTail effect operation (raw.subst binder valueCode) ce operand
        (by simp only [sourceEq, Code.subst]) targetEq
      exact .binding replacement header
  | @resource owners heap rest output binder key code tail ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      have header := ihTail
        (effect.instantiate (Instantiation.Environment.empty.bind binder key)) operation
        (raw.instantiate (Instantiation.Environment.empty.bind binder key)) ce operand
        (by simp only [sourceEq, Code.instantiate]) targetEq
      exact .resource (by simpa only [Code.instantiate] using header)
  | @templateUnused binder owners heap rest code output parameter body absent tail ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      have header := ihTail effect operation raw ce operand sourceEq targetEq
      have absentHeader : Syntax.Dependency.variable binder ∉ (Code.perform effect operation .unit).dependencies := by
        simp [Code.dependencies, List.mem_map]
      exact .templateUnused absentHeader header
  | @templateExpand fuel body bodyCode parameter binder heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro effect operation raw ce operand sourceEq targetEq
      have header := ihTail effect operation (raw.subst binder valueCode) ce operand
        (by simp only [sourceEq, Code.subst]) targetEq
      exact .templateExpand translated callable nonrecursive replacement closed header

theorem perform_components
    (related : EnvCloses graph owners heap environment (.perform effect operation rawOperand)
      (.perform closedEffect operation operand)) :
    effect.instantiate environment.instantiation = closedEffect ∧
      EnvCloses graph owners heap environment rawOperand operand :=
  perform_components_at related _ _ _ _ _ rfl rfl

/-- Clause substitution masks exactly its own argument, as a lambda carrier
would. This includes an older binding with the same name. -/
theorem ClauseAt.subst_carrier
    (selected : ClauseAt operation clauses parameter binder body) (name : Nat) (value : Code) :
    ClauseAt operation (clauses.subst name value) parameter binder
      (if name = parameter then body else body.subst name value) := by
  induction selected with
  | hit => exact .hit
  | pass different next ih => exact .pass different ih

theorem ClauseAt.instantiate_carrier
    (selected : ClauseAt operation clauses parameter binder body) (environment : Instantiation.Environment) :
    ClauseAt operation (clauses.instantiate environment) parameter binder (body.instantiate environment) := by
  induction selected with
  | hit => exact .hit
  | pass different next ih => exact .pass different ih

private theorem ClauseAt.variable_member
    (selected : ClauseAt operation clauses parameter binder body)
    (member : Syntax.Dependency.variable name ∈ (Code.lambda parameter body).dependencies) :
    Syntax.Dependency.variable name ∈ clauses.dependencies := by
  induction selected with
  | hit =>
      apply List.mem_append_left
      simpa [Code.dependencies, Clauses.dependencies, Syntax.without, List.mem_filter] using member
  | pass different next ih =>
      exact List.mem_append_right _ (ih member)

/-- Project the selected clause through ONE handler-header closing derivation.
The output is a lambda carrier, so earlier same-name lexical bindings remain
masked instead of being substituted into the raw selected body. -/
theorem selected_clause_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ effect rawClauses closedEffect clauses operation parameter binder rawBody,
      source = .handle effect .unit rawClauses → target = .handle closedEffect .unit clauses →
      ClauseAt operation rawClauses parameter binder rawBody →
      ∃ body, ClauseAt operation clauses parameter binder body ∧
        EnvCloses graph owners heap environment (.lambda parameter rawBody) (.lambda parameter body) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro effect rc ce c op parameter binder raw sourceEq targetEq selected
      have same : effect = ce ∧ rc = c := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩
      exact ⟨raw, selected, .empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro effect rc ce c op parameter binder raw sourceEq targetEq selected
      obtain ⟨body, clause, carrier⟩ := ihTail effect (rc.subst name valueCode) ce c op parameter binder
        (if name = parameter then raw else raw.subst name valueCode)
        (by simp only [sourceEq, Code.subst]) targetEq (ClauseAt.subst_carrier selected name valueCode)
      exact ⟨body, clause, .binding replacement (by simpa only [Code.subst] using carrier)⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro effect rc ce c op parameter binder raw sourceEq targetEq selected
      let inst := Instantiation.Environment.empty.bind name key
      obtain ⟨body, clause, carrier⟩ := ihTail (effect.instantiate inst) (rc.instantiate inst) ce c op parameter binder
        (raw.instantiate inst) (by simp only [sourceEq, Code.instantiate, inst]) targetEq
        (ClauseAt.instantiate_carrier selected inst)
      exact ⟨body, clause, .resource (by simpa only [Code.instantiate] using carrier)⟩
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro effect rc ce c op argument binder raw sourceEq targetEq selected
      obtain ⟨body, clause, carrier⟩ := ihTail effect rc ce c op argument binder raw sourceEq targetEq selected
      have carrierAbsent : Syntax.Dependency.variable name ∉ (Code.lambda argument raw).dependencies := by
        intro member
        apply absent
        simpa only [sourceEq, Code.dependencies, List.append_nil] using
          List.mem_append_right ((effectAtoms effect).map Syntax.Dependency.resource)
            (ClauseAt.variable_member selected member)
      exact ⟨body, clause, .templateUnused carrierAbsent carrier⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro effect rc ce c op argument binder raw sourceEq targetEq selected
      obtain ⟨body, clause, carrier⟩ := ihTail effect (rc.subst name valueCode) ce c op argument binder
        (if name = argument then raw else raw.subst name valueCode)
        (by simp only [sourceEq, Code.subst]) targetEq (ClauseAt.subst_carrier selected name valueCode)
      exact ⟨body, clause, .templateExpand translated callable nonrecursive replacement closed
        (by simpa only [Code.subst] using carrier)⟩

/-- The saved request effect is instantiated by its exact saved environment.
PlainData scope and type fields remain supplied annotations. -/
inductive RequestRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → PlainData → Prop where
  | operand (carrier : EnvCloses graph owners heap environment (.perform effect operation .unit)
        (.perform (freezeEffect requested) operation .unit))
      (context : plain.context = .perform (freezeEffect requested) operation) :
      RequestRel graph owners heap (.request effect operation environment) plain

theorem RequestRel.heap_weaken (related : RequestRel graph owners heap core plain)
    (extension : HeapExtends heap larger) : RequestRel graph owners larger core plain := by
  cases related with
  | operand carrier context => exact .operand (carrier.heap_weaken extension) context

/-- Named normalization of the existing handler RHS; this is not an
alternative syntax translator. Every result below follows from translateFuel. -/
private def clauseEntry (graph : CoreSyntax.Graph) (fuel : Nat) (owners : CoreTranslation.OwnerMap)
    (handler site : Nat) (clause : CoreSyntax.Clause) : Except CoreSyntax.Error (Nat × Nat × Nat × Code) := do
  if owners.any (fun binding => binding.owner == clause.owner) then throw (.duplicateOwner site clause.owner)
  match clause.argument with
  | .binder argument =>
      let mapped := CoreTranslation.ticket graph clause.owner
      let translated ← CoreTranslation.translateFuel graph fuel (⟨handler, clause.owner, mapped⟩ :: owners) clause.body
      pure (clause.operation, argument.id, mapped, translated)
  | _ => throw (.unsupportedClausePattern site clause.operation)

private def pack (entries : List (Nat × Nat × Nat × Code)) : Clauses :=
  entries.foldr (fun (operation, parameter, binder, body) rest => .cons operation parameter binder body rest) .nil

set_option linter.unusedSimpArgs false in
private theorem entries_selected {clauses : List CoreSyntax.Clause} {clause : CoreSyntax.Clause}
    (translated : clauses.mapM (clauseEntry graph fuel owners handler site) = .ok entries)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause) :
    ∃ argument rawBody, clause.argument = .binder argument ∧
      CoreTranslation.translateFuel graph fuel
        (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: owners) clause.body = .ok rawBody ∧
      ClauseAt operation (pack entries) argument.id (CoreTranslation.ticket graph clause.owner) rawBody := by
  induction clauses generalizing entries with
  | nil => simp at selected
  | cons head rest ih =>
      cases entry : clauseEntry graph fuel owners handler site head with
      | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, List.mapM_cons, entry] at translated
      | ok value =>
          cases tail : rest.mapM (clauseEntry graph fuel owners handler site) with
          | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, List.mapM_cons, entry, tail] at translated
          | ok values =>
              have entriesEq : entries = value :: values := by
                simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, List.mapM_cons, entry, tail] using translated.symm
              subst entries
              unfold clauseEntry at entry
              cases duplicate : owners.any (fun binding => binding.owner == head.owner) <;>
                simp only [duplicate, Bool.false_eq_true, if_false, if_true] at entry
              case true => cases entry
              case false =>
                cases argumentEq : head.argument <;> simp only [argumentEq] at entry
                all_goals try (cases entry)
                rename_i argument
                cases bodyEq : CoreTranslation.translateFuel graph fuel
                    (⟨handler, head.owner, CoreTranslation.ticket graph head.owner⟩ :: owners) head.body with
                | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, bodyEq] at entry
                | ok rawBody =>
                    have valueEq : value = (head.operation, argument.id, CoreTranslation.ticket graph head.owner, rawBody) := by
                      simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, bodyEq] using entry.symm
                    subst value
                    by_cases same : head.operation = operation
                    · have clauseEq : head = clause := by simpa [List.find?, same] using selected
                      subst clause
                      exact ⟨argument, rawBody, argumentEq, bodyEq, same ▸ .hit⟩
                    · have test : (head.operation == operation) = false := beq_eq_false_iff_ne.mpr same
                      have restSelected : rest.find? (fun clause => clause.operation == operation) = some clause := by
                        simpa [List.find?, test] using selected
                      obtain ⟨parameter, body, shape, translation, selection⟩ := ih tail restSelected
                      exact ⟨parameter, body, shape, translation, .pass (Ne.symm same) selection⟩

set_option linter.unusedSimpArgs false in
/-- Extract the actual first selected Core clause and its translation from the
saved handler's successful site translation. No independently translated
future body is assumed. -/
theorem handler_selected_translation
    (known : graph.node site = some node)
    (kind : node.kind = .handler handler effect body clauses)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause) :
    ∃ clauseFuel argument code, clause.argument = .binder argument ∧
      CoreTranslation.translateFuel graph clauseFuel
        (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: owners) clause.body = .ok code ∧
      ClauseAt operation rawClauses argument.id (CoreTranslation.ticket graph clause.owner) code := by
  cases fuel with
  | zero => simp [CoreTranslation.translateFuel] at translated
  | succ fuel =>
      cases node with
      | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known] at translated
        change (do
          CoreSyntax.checkClauseShapes site clauses
          let translatedBody ← CoreTranslation.translateFuel graph fuel owners body
          let translatedClauses ← clauses.mapM (clauseEntry graph fuel owners handler site)
          pure (Code.handle effect translatedBody (pack translatedClauses))) = _ at translated
        cases shape : CoreSyntax.checkClauseShapes site clauses with
        | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, shape] at translated
        | ok valid =>
          cases bodyTranslation : CoreTranslation.translateFuel graph fuel owners body with
          | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, shape, bodyTranslation] at translated
          | ok bodyCode =>
            cases entriesTranslation : clauses.mapM (clauseEntry graph fuel owners handler site) with
            | error error => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, shape, bodyTranslation, entriesTranslation] at translated
            | ok entries =>
              have clausesEq : pack entries = rawClauses := by
                have equal : bodyCode = rawBody ∧ pack entries = rawClauses := by
                  simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, shape, bodyTranslation, entriesTranslation] using translated
                exact equal.2
              obtain ⟨argument, code, pattern, translation, selection⟩ := entries_selected entriesTranslation selected
              exact ⟨fuel, argument, code, pattern, translation, clausesEq ▸ selection⟩

/-- Static owner identity is tied to an actual clause of the saved handler.
Its supplied answer and scope come from that same handler carrier. -/
inductive OwnerHeader (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    Nat → Nat → Nat → HandlerData → Prop where
  | selected (known : graph.node site = some node)
      (kind : node.kind = .handler handler effect body clauses)
      (member : clause ∈ clauses) (owned : clause.owner = owner)
      (boundary : BoundaryRel graph owners heap (.handlerBoundary site environment occurrence) (.handler data))
      (activation : data.activation = occurrence)
      (selection : ClauseAt clause.operation data.clauses parameter (CoreTranslation.ticket graph owner) clauseBody) :
      OwnerHeader graph owners heap handler owner occurrence data

theorem OwnerHeader.heap_weaken (related : OwnerHeader graph owners heap handler owner occurrence data)
    (extension : HeapExtends heap larger) : OwnerHeader graph owners larger handler owner occurrence data := by
  cases related with
  | selected known kind member owned boundary activation selection =>
      exact .selected known kind member owned (boundary.heap_weaken extension) activation selection

#print axioms handler_selected_translation
#print axioms selected_clause_at
#print axioms perform_components
#print axioms RequestRel.heap_weaken
#print axioms OwnerHeader.heap_weaken
end Ash.OneShot.CoreRequestFrames
