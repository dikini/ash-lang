import CoreStrictFrames
import ScopedDependencies

/-! Exact handler/cell boundary components. This reuses EnvCloses rather than
introducing a clause interpreter. Supplied scopes, answers and ticket barriers
remain static authentication obligations; activation freshness/world validity,
owner states and cleanup are not inferred. -/
namespace Ash.OneShot.CoreEffectFrames
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames Instantiation

private theorem name_single (name : ResourceName) (outer : Instantiation.Environment) (binder key : Nat) :
    (name.instantiate (Instantiation.Environment.empty.bind binder key)).instantiate outer =
      name.instantiate (outer.bind binder key) := by
  cases name with
  | activation => rfl
  | bound name =>
    by_cases same : name = binder <;>
      simp [ResourceName.instantiate, Instantiation.Environment.bind, Instantiation.Environment.empty, same]

private theorem argument_single (argument : Argument) (outer : Instantiation.Environment) (binder key : Nat) :
    (argument.instantiate (Instantiation.Environment.empty.bind binder key)).instantiate outer =
      argument.instantiate (outer.bind binder key) := by
  induction argument with
  | nominal => rfl
  | resource name => exact congrArg Argument.resource (name_single name outer binder key)
  | apply left right ihLeft ihRight => simp only [Argument.instantiate, ihLeft, ihRight]

/-- The nearest resource entry freezes its activation before the finite tail.
This is lexical composition, not a runtime world or freshness assumption. -/
theorem effect_single (effect : Effect) (outer : Instantiation.Environment) (binder key : Nat) :
    (effect.instantiate (Instantiation.Environment.empty.bind binder key)).instantiate outer =
      effect.instantiate (outer.bind binder key) := by
  cases effect with
  | cell name => exact congrArg Effect.cell (name_single name outer binder key)
  | user family arguments =>
    simp only [Effect.instantiate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro argument member
    exact argument_single argument outer binder key

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

/-- Recover the runtime effect instantiation from the same current lexical
closing derivation. Ordinary value replacements cannot alter the effect header. -/
theorem handle_effect_at
    (related : EnvCloses graph owners heap environment source output) :
    ∀ effect rawBody rawClauses closedEffect body clauses,
      source = .handle effect rawBody rawClauses → output = .handle closedEffect body clauses →
      effect.instantiate environment.instantiation = closedEffect := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro effect rb rc ce b c sourceEq outputEq
      have parts : effect = ce ∧ rb = b ∧ rc = c := by simpa [sourceEq] using outputEq
      have equal := parts.1
      rw [← equal]; exact effect_empty effect
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      exact ihTail effect (rb.subst name valueCode) (rc.subst name valueCode) ce b c
        (by simp only [sourceEq, Code.subst]) outputEq
  | @resource owners heap rest output name key code tail ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      have result := ihTail (effect.instantiate (Instantiation.Environment.empty.bind name key))
        (rb.instantiate (Instantiation.Environment.empty.bind name key))
        (rc.instantiate (Instantiation.Environment.empty.bind name key)) ce b c
        (by simp only [sourceEq, Code.instantiate]) outputEq
      rw [effect_single] at result
      have instantiation : (CoreMachine.Environment.resource name key rest).instantiation =
          rest.instantiation.bind name key := by
        funext binder
        simp [CoreMachine.Environment.instantiation, CoreMachine.Environment.resourceKey, Instantiation.Environment.bind]
      rw [instantiation]; exact result
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      exact ihTail effect rb rc ce b c sourceEq outputEq
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      exact ihTail effect (rb.subst name valueCode) (rc.subst name valueCode) ce b c
        (by simp only [sourceEq, Code.subst]) outputEq

private theorem header_member (member : dependency ∈ (Code.handle effect .unit clauses).dependencies) :
    dependency ∈ (Code.handle effect body clauses).dependencies := by
  simp only [Code.dependencies, List.mem_append, List.not_mem_nil, or_false] at member ⊢
  rcases member with effect | clause
  · exact Or.inl (Or.inl effect)
  · exact Or.inr clause

/-- Extract body and header carrier from ONE closing derivation, retaining the
exact lexical replacements, resource identities and finite template witnesses. -/
theorem handle_components_at
    (related : EnvCloses graph owners heap environment source output) :
    ∀ effect rawBody rawClauses closedEffect body clauses,
      source = .handle effect rawBody rawClauses → output = .handle closedEffect body clauses →
      EnvCloses graph owners heap environment rawBody body ∧
      EnvCloses graph owners heap environment (.handle effect .unit rawClauses)
        (.handle closedEffect .unit clauses) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro effect rb rc ce b c sourceEq outputEq
      have equal : effect = ce ∧ rb = b ∧ rc = c := by simpa [sourceEq] using outputEq
      rcases equal with ⟨rfl, rfl, rfl⟩; exact ⟨.empty, .empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      obtain ⟨body, header⟩ := ihTail effect (rb.subst name valueCode) (rc.subst name valueCode) ce b c
        (by simp only [sourceEq, Code.subst]) outputEq
      exact ⟨.binding replacement body, .binding replacement (by simpa only [Code.subst] using header)⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      obtain ⟨body, header⟩ := ihTail (effect.instantiate (Instantiation.Environment.empty.bind name key))
        (rb.instantiate (Instantiation.Environment.empty.bind name key))
        (rc.instantiate (Instantiation.Environment.empty.bind name key)) ce b c
        (by simp only [sourceEq, Code.instantiate]) outputEq
      exact ⟨.resource body, .resource (by simpa only [Code.instantiate] using header)⟩
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      obtain ⟨body, header⟩ := ihTail effect rb rc ce b c sourceEq outputEq
      have bodyAbsent : Syntax.Dependency.variable name ∉ rb.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using
          List.mem_append_left rc.dependencies (List.mem_append_right _ member)
      have headerAbsent : Syntax.Dependency.variable name ∉ (Code.handle effect .unit rc).dependencies := by
        intro member; apply absent
        simpa only [sourceEq] using (header_member (body := rb) member)
      exact ⟨.templateUnused bodyAbsent body, .templateUnused headerAbsent header⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro effect rb rc ce b c sourceEq outputEq
      obtain ⟨body, header⟩ := ihTail effect (rb.subst name valueCode) (rc.subst name valueCode) ce b c
        (by simp only [sourceEq, Code.subst]) outputEq
      exact ⟨.templateExpand translated callable nonrecursive replacement closed body,
        .templateExpand translated callable nonrecursive replacement closed (by simpa only [Code.subst] using header)⟩

theorem handle_components
    (current : EnvCloses graph owners heap environment (.handle effect rawBody rawClauses)
      (.handle closedEffect body clauses)) :
    EnvCloses graph owners heap environment rawBody body ∧
    EnvCloses graph owners heap environment (.handle effect .unit rawClauses) (.handle closedEffect .unit clauses) :=
  handle_components_at current _ _ _ _ _ _ rfl rfl

private def merge (first second : Instantiation.Environment) : Instantiation.Environment :=
  fun name => match first name with | some key => some key | none => second name

private theorem merge_mask (first second : Instantiation.Environment) (binder : Nat) :
    merge (first.mask binder) (second.mask binder) = (merge first second).mask binder := by
  funext name
  by_cases same : name = binder <;> simp [merge, Instantiation.Environment.mask, same]

private theorem name_merge (name : ResourceName) (first second : Instantiation.Environment) :
    (name.instantiate first).instantiate second = name.instantiate (merge first second) := by
  cases name with
  | activation => rfl
  | bound name =>
      cases known : first name <;> simp [ResourceName.instantiate, merge, known]

private theorem argument_merge (argument : Argument) (first second : Instantiation.Environment) :
    (argument.instantiate first).instantiate second = argument.instantiate (merge first second) := by
  induction argument with
  | nominal => rfl
  | resource name => exact congrArg Argument.resource (name_merge name first second)
  | apply left right ihLeft ihRight => simp only [Argument.instantiate, ihLeft, ihRight]

private theorem effect_merge (effect : Effect) (first second : Instantiation.Environment) :
    (effect.instantiate first).instantiate second = effect.instantiate (merge first second) := by
  cases effect with
  | cell name => exact congrArg Effect.cell (name_merge name first second)
  | user family arguments =>
      simp only [Effect.instantiate, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => argument_merge argument first second

mutual
private theorem code_merge (code : Code) (first second : Instantiation.Environment) :
    (code.instantiate first).instantiate second = code.instantiate (merge first second) := by
  cases code with
  | unit | boolean | integer | «variable» | discard => rfl
  | resourceRef name => exact congrArg Code.resourceRef (name_merge name first second)
  | pair left right | app left right | cleanup left right =>
      simp only [Code.instantiate, code_merge left first second, code_merge right first second]
  | lambda parameter body => simp only [Code.instantiate, code_merge body first second]
  | bind binder initializer body =>
      simp only [Code.instantiate, code_merge initializer first second, code_merge body first second]
  | branch condition yes no =>
      simp only [Code.instantiate, code_merge condition first second, code_merge yes first second, code_merge no first second]
  | perform effect operation operand =>
      simp only [Code.instantiate, effect_merge effect first second, code_merge operand first second]
  | handle effect body clauses =>
      simp only [Code.instantiate, effect_merge effect first second, code_merge body first second, clauses_merge clauses first second]
  | resume ticket operand => simp only [Code.instantiate, code_merge operand first second]
  | resource binder initializer body =>
      simp only [Code.instantiate, code_merge initializer first second,
        code_merge body (first.mask binder) (second.mask binder), merge_mask]

private theorem clauses_merge (clauses : Clauses) (first second : Instantiation.Environment) :
    (clauses.instantiate first).instantiate second = clauses.instantiate (merge first second) := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [Clauses.instantiate, code_merge body first second, clauses_merge rest first second]
end

/-- Opening the declaration's own identity commutes with lexical tail closure
under its mask, including nested same-name resource declarations. -/
theorem resource_open_commute (code : Code) (outer : Instantiation.Environment) (identity key : Nat) :
    (code.instantiate (outer.mask identity)).instantiate (Instantiation.Environment.empty.bind identity key) =
      (code.instantiate (Instantiation.Environment.empty.bind identity key)).instantiate outer := by
  rw [code_merge, code_merge]
  congr 1
  funext name
  by_cases same : name = identity <;>
    simp [merge, Instantiation.Environment.mask, Instantiation.Environment.bind,
      Instantiation.Environment.empty, same]
  cases outer name <;> rfl

/-- Open the body's resource barrier using ONE current resource derivation.
This constructs the actual extended Core environment relation. -/
theorem resource_body_at
    (related : EnvCloses graph owners heap environment source output) :
    ∀ identity rawInitializer rawBody initializer body key,
      source = .resource identity rawInitializer rawBody → output = .resource identity initializer body →
      EnvCloses graph owners heap environment rawInitializer initializer ∧
      EnvCloses graph owners heap (.resource identity key environment) rawBody
        (body.instantiate (Instantiation.Environment.empty.bind identity key)) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro identity ri rb i b key sourceEq outputEq
      have equal : ri = i ∧ rb = b := by simpa [sourceEq] using outputEq
      rcases equal with ⟨rfl, rfl⟩; exact ⟨.empty, .resource .empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro identity ri rb i b key sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity (ri.subst name valueCode) (rb.subst name valueCode) i b key
        (by simp only [sourceEq, Code.subst]) outputEq
      cases body with
      | resource opened =>
        rw [Code.instantiation_subst rb name valueCode _ replacement.closed.2.1] at opened
        exact ⟨.binding replacement init, .resource (.binding replacement opened)⟩
  | @resource owners heap rest output name oldKey code tail ihTail =>
      intro identity ri rb i b key sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity
        (ri.instantiate (Instantiation.Environment.empty.bind name oldKey))
        (rb.instantiate ((Instantiation.Environment.empty.bind name oldKey).mask identity)) i b key
        (by simp only [sourceEq, Code.instantiate]) outputEq
      cases body with
      | resource opened =>
        rw [resource_open_commute] at opened
        exact ⟨.resource init, .resource (.resource opened)⟩
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro identity ri rb i b key sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity ri rb i b key sourceEq outputEq
      have initAbsent : Syntax.Dependency.variable name ∉ ri.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_left rb.dependencies member
      have bodyAbsent : Syntax.Dependency.variable name ∉ rb.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right ri.dependencies member
      have openedAbsent : Syntax.Dependency.variable name ∉
          (rb.instantiate (Instantiation.Environment.empty.bind identity key)).dependencies := by
        intro member
        have bounded := acquisition_dependency_bound identity key rb member
        rcases List.mem_append.mp bounded with old | fresh
        · exact bodyAbsent old
        · simp at fresh
      cases body with
      | resource opened => exact ⟨.templateUnused initAbsent init, .resource (.templateUnused openedAbsent opened)⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro identity ri rb i b key sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity (ri.subst name valueCode) (rb.subst name valueCode) i b key
        (by simp only [sourceEq, Code.subst]) outputEq
      cases body with
      | resource opened =>
        rw [Code.instantiation_subst rb name valueCode _ closed.2.1] at opened
        exact ⟨.templateExpand translated callable nonrecursive replacement closed init,
          .resource (.templateExpand translated callable nonrecursive replacement closed opened)⟩

theorem resource_body
    (current : EnvCloses graph owners heap environment (.resource identity rawInitializer rawBody)
      (.resource identity initializer body)) (key : Nat) :
    EnvCloses graph owners heap environment rawInitializer initializer ∧
    EnvCloses graph owners heap (.resource identity key environment) rawBody
      (body.instantiate (Instantiation.Environment.empty.bind identity key)) :=
  resource_body_at current _ _ _ _ _ key rfl rfl

#print axioms resource_open_commute
#print axioms resource_body

/-- Keep the resource body's lexical barrier while replacing only its current
initializer by Unit. This carrier is derived, never supplied as a successor. -/
theorem resource_components_at
    (related : EnvCloses graph owners heap environment source output) :
    ∀ identity rawInitializer rawBody initializer body,
      source = .resource identity rawInitializer rawBody → output = .resource identity initializer body →
      EnvCloses graph owners heap environment rawInitializer initializer ∧
      EnvCloses graph owners heap environment (.resource identity .unit rawBody) (.resource identity .unit body) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro identity ri rb i b sourceEq outputEq
      have equal : ri = i ∧ rb = b := by simpa [sourceEq] using outputEq
      rcases equal with ⟨rfl, rfl⟩; exact ⟨.empty, .empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro identity ri rb i b sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity (ri.subst name valueCode) (rb.subst name valueCode) i b
        (by simp only [sourceEq, Code.subst]) outputEq
      exact ⟨.binding replacement init, .binding replacement (by simpa only [Code.subst] using body)⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro identity ri rb i b sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity
        (ri.instantiate (Instantiation.Environment.empty.bind name key))
        (rb.instantiate ((Instantiation.Environment.empty.bind name key).mask identity)) i b
        (by simp only [sourceEq, Code.instantiate]) outputEq
      exact ⟨.resource init, .resource (by simpa only [Code.instantiate] using body)⟩
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro identity ri rb i b sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity ri rb i b sourceEq outputEq
      have initAbsent : Syntax.Dependency.variable name ∉ ri.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_left rb.dependencies member
      have bodyAbsent : Syntax.Dependency.variable name ∉ (Code.resource identity .unit rb).dependencies := by
        intro member; apply absent
        simp only [Code.dependencies, List.nil_append] at member
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right ri.dependencies member
      exact ⟨.templateUnused initAbsent init, .templateUnused bodyAbsent body⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro identity ri rb i b sourceEq outputEq
      obtain ⟨init, body⟩ := ihTail identity (ri.subst name valueCode) (rb.subst name valueCode) i b
        (by simp only [sourceEq, Code.subst]) outputEq
      exact ⟨.templateExpand translated callable nonrecursive replacement closed init,
        .templateExpand translated callable nonrecursive replacement closed (by simpa only [Code.subst] using body)⟩

theorem resource_components
    (current : EnvCloses graph owners heap environment (.resource identity rawInitializer rawBody)
      (.resource identity initializer body)) :
    EnvCloses graph owners heap environment rawInitializer initializer ∧
    EnvCloses graph owners heap environment (.resource identity .unit rawBody) (.resource identity .unit body) :=
  resource_components_at current _ _ _ _ _ rfl rfl

/-- The resource initializer's strict plain context, with its exact saved
resource-body carrier. PlainData annotations remain supplied obligations. -/
inductive InitializerRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → PlainData → Prop where
  | resource (known : graph.node site = some node)
      (kind : node.kind = .resource identity handle initializer body)
      (translated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
      (saved : EnvCloses graph owners heap environment
        (.resource identity .unit (.bind handle.id (.resourceRef (.bound identity)) rawBody))
        (.resource identity .unit suffix))
      (context : plain.context = .resource identity suffix) :
      InitializerRel graph owners heap (.resourceInitializer site identity handle body environment) plain

theorem InitializerRel.heap_weaken (related : InitializerRel graph owners heap core plain)
    (extension : HeapExtends heap larger) : InitializerRel graph owners larger core plain := by
  cases related with
  | resource known kind translated saved context => exact .resource known kind translated (saved.heap_weaken extension) context

#print axioms resource_components
#print axioms InitializerRel.heap_weaken

inductive BoundaryRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → ExecFrame → Prop where
  | handler (known : graph.node site = some node)
      (kind : node.kind = .handler handlerId effect body clauses)
      (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
      (header : EnvCloses graph owners heap environment (.handle effect .unit rawClauses)
        (.handle (freezeEffect data.effectInst) .unit data.clauses)) :
      BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data)
  | cell (known : graph.node site = some node)
      (kind : node.kind = .resource identity handle initializer body) :
      BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload scope answer)

theorem BoundaryRel.heap_weaken (related : BoundaryRel graph owners heap core target)
    (extension : HeapExtends heap larger) : BoundaryRel graph owners larger core target := by
  cases related with
  | handler known kind translated header => exact .handler known kind translated (header.heap_weaken extension)
  | cell known kind => exact .cell known kind

#print axioms effect_single
#print axioms handle_effect_at
#print axioms handle_components
#print axioms BoundaryRel.heap_weaken
end Ash.OneShot.CoreEffectFrames
