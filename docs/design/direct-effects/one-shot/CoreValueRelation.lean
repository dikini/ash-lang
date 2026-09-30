import CoreMachine
import CoreTranslation
import ScopedSubstitution
import CoreMachineExamples

/-! Finite Core value/environment/heap correspondence for TASK-0032.
This relation uses the existing graph translation and lexical Code.subst and
Code.instantiate operations. It takes no calculus evaluation, admission,
future invariant or desired successor as an input.

Closedness is evidence at each translated closure boundary, not a claim that
validated Rust input already supplies that evidence. Function templates expand
used references over their finite tail. Their self binding is erased only where
its absence is proved. Finite derivations reject raw cyclic heap references;
this file does not yet prove every reachable Core heap has such a derivation.
OwnerMap authentication and dynamic ticket correspondence remain separate. -/
namespace Ash.OneShot.CoreValueRelation
open ScopedExpressions
open Syntax (Dependency)

abbrev MValue := CoreMachine.Value
abbrev MEnv := CoreMachine.Environment
abbrev Heap := CoreMachine.Heap

/-- Successful old lookups remain valid; append-only tuple allocation supplies
    this condition without requiring a heap equality or an execution premise. -/
def HeapExtends (before after : Heap) : Prop :=
  ∀ (index : Nat) (cell : CoreMachine.HeapCell), before[index]? = some cell → after[index]? = some cell

theorem heap_append (heap suffix : Heap) : HeapExtends heap (heap ++ suffix) := by
  intro index cell known
  have bounded : index < heap.length := List.getElem?_eq_some_iff.mp known |>.1
  rw [List.getElem?_append_left bounded]
  exact known

mutual
inductive ValueRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : MValue → Code → Prop where
  | unit : ValueRel graph owners heap .unit .unit
  | boolean : ValueRel graph owners heap (.boolean value) (.boolean value)
  | integer : ValueRel graph owners heap (.integer value) (.integer value)
  | handle : ValueRel graph owners heap (.handle key) (.resourceRef (.activation key))
  | location (known : heap[index]? = some (.pair left right))
      (leftRelated : ValueRel graph owners heap left leftCode)
      (rightRelated : ValueRel graph owners heap right rightCode) :
      ValueRel graph owners heap (.location index) (.pair leftCode rightCode)
  | closure (translated : CoreTranslation.translateFuel graph fuel owners body = .ok bodyCode)
      (environment : EnvCloses graph owners heap saved (.lambda parameter bodyCode) closed)
      (closedValue : ClosedValue closed) :
      ValueRel graph owners heap (.closure parameter body saved) closed

/-- Interpret the nearest lexical entry first. Inserted values are related
    closed values, so later outer substitutions cannot capture their names and
    outer resource instantiation cannot replace existing activation atoms.
    Arbitrary pending Code need not itself be a closed value. -/
inductive EnvCloses (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : MEnv → Code → Code → Prop where
  | empty : EnvCloses graph owners heap .empty code code
  | binding (related : ValueRel graph owners heap value valueCode)
      (tail : EnvCloses graph owners heap rest (code.subst binder valueCode) closed) :
      EnvCloses graph owners heap (.binding binder value rest) code closed
  | resource (tail : EnvCloses graph owners heap rest
      (code.instantiate (Instantiation.Environment.empty.bind binder key)) closed) :
      EnvCloses graph owners heap (.resource binder key rest) code closed
  | templateUnused (absent : Dependency.variable binder ∉ code.dependencies)
      (tail : EnvCloses graph owners heap rest code closed) :
      EnvCloses graph owners heap (.functionTemplate binder parameter body rest) code closed
  | templateExpand
      (translated : CoreTranslation.translateFuel graph fuel owners body = .ok bodyCode)
      (nonrecursive : Dependency.variable binder ∉ (Code.lambda parameter bodyCode).dependencies)
      (replacement : EnvCloses graph owners heap rest (.lambda parameter bodyCode) valueCode)
      (closedValue : ClosedValue valueCode)
      (tail : EnvCloses graph owners heap rest (code.subst binder valueCode) closed) :
      EnvCloses graph owners heap (.functionTemplate binder parameter body rest) code closed
end

theorem ValueRel.closed (related : ValueRel graph owners heap value code) : ClosedValue code := by
  cases related with
  | unit | boolean | integer | handle =>
      simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Instantiation.ResourceName.freeNames, Code.dependencies]
  | location known left right =>
      obtain ⟨leftValue, leftResources, leftDependencies⟩ := left.closed
      obtain ⟨rightValue, rightResources, rightDependencies⟩ := right.closed
      refine ⟨⟨leftValue, rightValue⟩, ?_, ?_⟩
      · simp [Code.ResourceClosed, Code.freeNames, Code.ResourceClosed] at leftResources rightResources ⊢
        simp [leftResources, rightResources]
      · intro dependency member
        rcases List.mem_append.mp member with here | there
        · exact leftDependencies dependency here
        · exact rightDependencies dependency there
  | closure translated environment closedValue => exact closedValue

/-- Later ordinary and resource bindings leave an inserted closed value intact. -/
theorem EnvCloses.closed_identity (related : EnvCloses graph owners heap environment code output) :
    ClosedValue code → output = code := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => intro closed; rfl
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro closed
      have unchanged := ScopedTyping.subst_absent code binder valueCode
        (ScopedTyping.closedValue_no_variable closed)
      exact (ihTail (unchanged.symm ▸ closed)).trans unchanged
  | @resource rest output binder key code tail ihTail =>
      intro closed
      have unchanged := Code.closed_instantiation_identity code (Instantiation.Environment.empty.bind binder key) closed.2.1
      exact (ihTail (unchanged.symm ▸ closed)).trans unchanged
  | templateUnused absent tail ihTail => exact ihTail
  | @templateExpand fuel body bodyCode parameter binder rest valueCode output code translated nonrecursive replacement valueClosed tail ihReplacement ihTail =>
      intro closed
      have unchanged := ScopedTyping.subst_absent code binder valueCode
        (ScopedTyping.closedValue_no_variable closed)
      exact (ihTail (unchanged.symm ▸ closed)).trans unchanged

/-- Stable tuple locations allow weakening through any successful heap extension. -/
theorem ValueRel.heap_weaken (related : ValueRel graph owners heap value code)
    (larger : HeapExtends heap next) : ValueRel graph owners next value code := by
  induction related using ValueRel.rec
      (motive_2 := fun environment code output _ => EnvCloses graph owners next environment code output) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | handle => exact .handle
  | location known left right ihLeft ihRight => exact .location (larger _ _ known) ihLeft ihRight
  | closure translated environment closed ihEnvironment => exact .closure translated ihEnvironment closed
  | empty => exact .empty
  | binding replacement tail ihReplacement ihTail => exact .binding ihReplacement ihTail
  | resource tail ihTail => exact .resource ihTail
  | templateUnused absent tail ihTail => exact .templateUnused absent ihTail
  | templateExpand translated nonrecursive replacement closed tail ihReplacement ihTail =>
      exact .templateExpand translated nonrecursive ihReplacement closed ihTail

theorem EnvCloses.heap_weaken (related : EnvCloses graph owners heap environment code output)
    (larger : HeapExtends heap next) : EnvCloses graph owners next environment code output := by
  induction related using EnvCloses.rec
      (motive_1 := fun value code _ => ValueRel graph owners next value code) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | handle => exact .handle
  | location known left right ihLeft ihRight => exact .location (larger _ _ known) ihLeft ihRight
  | closure translated environment closed ihEnvironment => exact .closure translated ihEnvironment closed
  | empty => exact .empty
  | binding replacement tail ihReplacement ihTail => exact .binding ihReplacement ihTail
  | resource tail ihTail => exact .resource ihTail
  | templateUnused absent tail ihTail => exact .templateUnused absent ihTail
  | templateExpand translated nonrecursive replacement closed tail ihReplacement ihTail =>
      exact .templateExpand translated nonrecursive ihReplacement closed ihTail

/-- Reuse the established lexical substitution/instantiation commutation law. -/
theorem binding_instantiation (related : ValueRel graph owners heap value replacement)
    (code : Code) (name : Nat) (environment : Instantiation.Environment) :
    (code.subst name replacement).instantiate environment =
      (code.instantiate environment).subst name replacement :=
  code.instantiation_subst name replacement environment related.closed.2.1

/-- Applying an environment to a closed variable result supplies the actual
    Core lookup value. Used templates produce closures capturing their complete
    finite suffix, but their proved absent self binding does not expand again. -/
theorem EnvCloses.lookup_at
    (related : EnvCloses graph owners heap environment code output)
    : ∀ name, code = .variable name → ClosedValue output →
      ∃ value, environment.lookup name = some value ∧ ValueRel graph owners heap value output := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => intro name same closed; rw [same] at closed; cases closed.1
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro name same closed
      by_cases equal : binder = name
      · have substituted : code.subst binder valueCode = valueCode := by simp [same, Code.subst, equal]
        have result := tail.closed_identity (substituted.symm ▸ replacement.closed)
        have resultEqual : output = valueCode := result.trans substituted
        exact ⟨value, by simp [CoreMachine.Environment.lookup, equal], resultEqual ▸ replacement⟩
      · have pending : code.subst binder valueCode = .variable name := by simp [same, Code.subst, equal]
        obtain ⟨found, known, valueRelated⟩ := ihTail name pending closed
        exact ⟨found, by simpa [CoreMachine.Environment.lookup, equal, Ne.symm equal] using known, valueRelated⟩
  | @resource rest output binder key code tail ihTail =>
      intro name same closed
      have pending : code.instantiate (Instantiation.Environment.empty.bind binder key) = .variable name := by
        simp [same, Code.instantiate]
      obtain ⟨found, known, valueRelated⟩ := ihTail name pending closed
      exact ⟨found, known, valueRelated⟩
  | @templateUnused binder rest code output parameter body absent tail ihTail =>
      intro name same closed
      have different : binder ≠ name := by
        intro equal
        subst binder
        rw [same] at absent
        exact absent List.mem_cons_self
      obtain ⟨found, known, valueRelated⟩ := ihTail name same closed
      exact ⟨found, by simpa [CoreMachine.Environment.lookup, different, Ne.symm different] using known, valueRelated⟩
  | @templateExpand fuel body bodyCode parameter binder rest valueCode output code translated nonrecursive replacement valueClosed tail ihReplacement ihTail =>
      intro name same closed
      by_cases equal : binder = name
      · have substituted : code.subst binder valueCode = valueCode := by simp [same, Code.subst, equal]
        have result := tail.closed_identity (substituted.symm ▸ valueClosed)
        have resultEqual : output = valueCode := result.trans substituted
        refine ⟨.closure parameter body (.functionTemplate binder parameter body rest), ?_, ?_⟩
        · simp [CoreMachine.Environment.lookup, equal]
        · rw [resultEqual]
          exact .closure translated (.templateUnused nonrecursive replacement) valueClosed
      · have pending : code.subst binder valueCode = .variable name := by simp [same, Code.subst, equal]
        obtain ⟨found, known, valueRelated⟩ := ihTail name pending closed
        exact ⟨found, by simpa [CoreMachine.Environment.lookup, equal, Ne.symm equal] using known, valueRelated⟩

theorem EnvCloses.lookup (related : EnvCloses graph owners heap environment (.variable name) output)
    (closed : ClosedValue output) :
    ∃ value, environment.lookup name = some value ∧ ValueRel graph owners heap value output :=
  related.lookup_at name rfl closed

/-- Closing a lambda preserves its parameter and lambda shape. Closed-value
    insertion preserves lexical binding; it does not substitute under the same
    ordinary parameter name. -/
theorem EnvCloses.lambda_shape_at
    (related : EnvCloses graph owners heap environment code output) :
    ∀ parameter body, code = .lambda parameter body → ∃ result, output = .lambda parameter result := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => intro parameter body same; exact ⟨body, same⟩
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro parameter body same
      exact ihTail parameter (if binder = parameter then body else body.subst binder valueCode)
        (by simp only [same, Code.subst])
  | @resource rest output binder key code tail ihTail =>
      intro parameter body same
      exact ihTail parameter (body.instantiate (Instantiation.Environment.empty.bind binder key))
        (by simp only [same, Code.instantiate])
  | templateUnused absent tail ihTail => exact ihTail
  | @templateExpand fuel functionBody bodyCode functionParameter binder rest valueCode output code translated nonrecursive replacement closed tail ihReplacement ihTail =>
      intro parameter body same
      exact ihTail parameter (if binder = parameter then body else body.subst binder valueCode)
        (by simp only [same, Code.subst])

theorem ValueRel.closure_shape
    (related : ValueRel graph owners heap (.closure parameter body environment) code) :
    ∃ result, code = .lambda parameter result := by
  cases related with
  | closure translated saved closed => exact saved.lambda_shape_at _ _ rfl

/-- A lambda's own parameter masks a same-name saved ordinary binding. -/
theorem EnvCloses.parameter_shadow
    (related : ValueRel graph owners heap value valueCode)
    (tail : EnvCloses graph owners heap rest (.lambda parameter body) output) :
    EnvCloses graph owners heap (.binding parameter value rest) (.lambda parameter body) output := by
  apply EnvCloses.binding related
  simpa only [Code.subst, ↓reduceIte] using tail

/-- Scalar correspondence cannot change the returned observation. -/
theorem ValueRel.integer_iff : ValueRel graph owners heap (.integer value) code ↔ code = .integer value := by
  constructor
  · intro related; cases related; rfl
  · intro equal; subst code; exact .integer

theorem ValueRel.handle_iff : ValueRel graph owners heap (.handle key) code ↔
    code = .resourceRef (.activation key) := by
  constructor
  · intro related; cases related; rfl
  · intro equal; subst code; exact .handle

theorem ValueRel.location_view (related : ValueRel graph owners heap (.location index) code) :
    ∃ left right leftCode rightCode, heap[index]? = some (.pair left right) ∧
      code = .pair leftCode rightCode ∧ ValueRel graph owners heap left leftCode ∧
      ValueRel graph owners heap right rightCode := by
  cases related with
  | location known left right => exact ⟨_, _, _, _, known, rfl, left, right⟩

/-- Closing a bound resource name agrees with the Core environment's nearest
    resource-key lookup. Ordinary bindings and templates do not shadow resources. -/
theorem EnvCloses.resource_lookup_at
    (related : EnvCloses graph owners heap environment code output) :
    ∀ name, code = .resourceRef (.bound name) → ClosedValue output →
      ∃ key, environment.resourceKey name = some key ∧ output = .resourceRef (.activation key) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => intro name same closed; rw [same] at closed; cases closed.1
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro name same closed
      have pending : code.subst binder valueCode = .resourceRef (.bound name) := by simp [same, Code.subst]
      obtain ⟨key, known, equal⟩ := ihTail name pending closed
      exact ⟨key, known, equal⟩
  | @resource rest output binder key code tail ihTail =>
      intro name same closed
      by_cases equal : binder = name
      · have instantiated : code.instantiate (Instantiation.Environment.empty.bind binder key) =
            .resourceRef (.activation key) := by
          simp [same, Code.instantiate, Instantiation.ResourceName.instantiate,
            Instantiation.Environment.bind, equal]
        have valueClosed : ClosedValue (.resourceRef (.activation key)) := (ValueRel.handle (graph := graph)
          (owners := owners) (heap := heap) (key := key)).closed
        have outputEqual := (tail.closed_identity (instantiated.symm ▸ valueClosed)).trans instantiated
        exact ⟨key, by simp [CoreMachine.Environment.resourceKey, equal], outputEqual⟩
      · have pending : code.instantiate (Instantiation.Environment.empty.bind binder key) =
            .resourceRef (.bound name) := by
          simp [same, Code.instantiate, Instantiation.ResourceName.instantiate,
            Instantiation.Environment.empty, Instantiation.Environment.bind, Ne.symm equal]
        obtain ⟨found, known, outputEqual⟩ := ihTail name pending closed
        exact ⟨found, by simpa [CoreMachine.Environment.resourceKey, equal, Ne.symm equal] using known, outputEqual⟩
  | templateUnused absent tail ihTail =>
      intro name same closed
      obtain ⟨key, known, equal⟩ := ihTail name same closed
      exact ⟨key, known, equal⟩
  | @templateExpand fuel body bodyCode parameter binder rest valueCode output code translated nonrecursive replacement valueClosed tail ihReplacement ihTail =>
      intro name same closed
      have pending : code.subst binder valueCode = .resourceRef (.bound name) := by simp [same, Code.subst]
      obtain ⟨key, known, equal⟩ := ihTail name pending closed
      exact ⟨key, known, equal⟩

theorem EnvCloses.resource_lookup
    (related : EnvCloses graph owners heap environment (.resourceRef (.bound name)) output)
    (closed : ClosedValue output) :
    ∃ key, environment.resourceKey name = some key ∧ output = .resourceRef (.activation key) :=
  related.resource_lookup_at name rfl closed

/-- Closed values are unchanged by ordinary substitution. -/
theorem closed_subst (closed : ClosedValue code) (name : Nat) (replacement : Code) :
    code.subst name replacement = code :=
  ScopedTyping.subst_absent code name replacement (ScopedTyping.closedValue_no_variable closed)

mutual
/-- Distinct lexical substitutions commute when both inserted values are closed.
    This joins the existing single-substitution operations; it is not a new
    source translator or an evaluation assumption. -/
theorem subst_commute (code : Code) (first second : Nat) (left right : Code)
    (leftClosed : ClosedValue left) (rightClosed : ClosedValue right)
    (different : first ≠ second) :
    (code.subst first left).subst second right = (code.subst second right).subst first left := by
  cases code with
  | unit | boolean | integer | resourceRef | discard => rfl
  | «variable» name =>
      by_cases a : first = name <;> by_cases b : second = name
      · exact False.elim (different (a.trans b.symm))
      · simp [Code.subst, a, b, closed_subst leftClosed]
      · simp [Code.subst, a, b, closed_subst rightClosed]
      · simp [Code.subst, a, b]
  | pair a b | app a b | cleanup a b | resource _ a b =>
      simp only [Code.subst, subst_commute a first second left right leftClosed rightClosed different,
        subst_commute b first second left right leftClosed rightClosed different]
  | lambda parameter body =>
      by_cases a : first = parameter <;> by_cases b : second = parameter <;>
        simp [Code.subst, a, b, subst_commute body first second left right leftClosed rightClosed different]
  | bind parameter initializer body =>
      simp only [Code.subst, subst_commute initializer first second left right leftClosed rightClosed different]
      by_cases a : first = parameter <;> by_cases b : second = parameter <;>
        simp [a, b,
          subst_commute body first second left right leftClosed rightClosed different]
  | branch condition yes no =>
      simp only [Code.subst, subst_commute condition first second left right leftClosed rightClosed different,
        subst_commute yes first second left right leftClosed rightClosed different,
        subst_commute no first second left right leftClosed rightClosed different]
  | perform effect operation operand | resume operation operand =>
      simp only [Code.subst, subst_commute operand first second left right leftClosed rightClosed different]
  | handle effect body clauses =>
      simp only [Code.subst, subst_commute body first second left right leftClosed rightClosed different,
        clauses_subst_commute clauses first second left right leftClosed rightClosed different]

theorem clauses_subst_commute (clauses : Clauses) (first second : Nat) (left right : Code)
    (leftClosed : ClosedValue left) (rightClosed : ClosedValue right)
    (different : first ≠ second) :
    (clauses.subst first left).subst second right = (clauses.subst second right).subst first left := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [Clauses.subst, clauses_subst_commute rest first second left right leftClosed rightClosed different]
      by_cases a : first = parameter <;> by_cases b : second = parameter <;>
        simp [a, b,
          subst_commute body first second left right leftClosed rightClosed different]
end

/-- Closing a lambda and then supplying a closed argument agrees with closing
    its raw body after parameter substitution, through every lexical entry. -/
theorem EnvCloses.lambda_argument_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ parameter body result argument, source = .lambda parameter body → target = .lambda parameter result →
      ClosedValue argument → EnvCloses graph owners heap environment
        (body.subst parameter argument) (result.subst parameter argument) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro parameter body result argument sourceEq targetEq closed
      have same : body = result := by simpa [sourceEq] using targetEq
      subst result
      exact .empty
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro parameter body result argument sourceEq targetEq closed
      apply EnvCloses.binding replacement
      by_cases same : binder = parameter
      · have unchanged : (body.subst parameter argument).subst binder valueCode = body.subst parameter argument := by
          rw [same]
          exact ScopedTyping.subst_absent _ _ _ (body.subst_removes_variable _ _
            (ScopedTyping.closedValue_no_variable closed))
        rw [unchanged]
        exact ihTail parameter body result argument (by simp [sourceEq, Code.subst, same]) targetEq closed
      · rw [subst_commute body parameter binder argument valueCode closed replacement.closed (Ne.symm same)]
        exact ihTail parameter (body.subst binder valueCode) result argument
          (by simp [sourceEq, Code.subst, same]) targetEq closed
  | @resource rest output binder key code tail ihTail =>
      intro parameter body result argument sourceEq targetEq closed
      apply EnvCloses.resource
      rw [Code.instantiation_subst _ _ _ _ closed.2.1]
      exact ihTail parameter (body.instantiate (Instantiation.Environment.empty.bind binder key)) result argument
        (by simp only [sourceEq, Code.instantiate]) targetEq closed
  | @templateUnused binder rest code output functionParameter functionBody absent tail ihTail =>
      intro parameter body result argument sourceEq targetEq closed
      have stillAbsent : Dependency.variable binder ∉ (body.subst parameter argument).dependencies := by
        intro member
        rcases List.mem_append.mp (ScopedTyping.substitution_bound_for_closed_value body parameter closed member) with old | inserted
        · apply absent
          simpa only [sourceEq, Code.dependencies] using old
        · exact ScopedTyping.closedValue_no_variable closed inserted
      exact .templateUnused stillAbsent (ihTail parameter body result argument sourceEq targetEq closed)
  | @templateExpand fuel functionBody bodyCode functionParameter binder rest valueCode output code translated nonrecursive replacement valueClosed tail ihReplacement ihTail =>
      intro parameter body result argument sourceEq targetEq closed
      apply EnvCloses.templateExpand translated nonrecursive replacement valueClosed
      by_cases same : binder = parameter
      · have unchanged : (body.subst parameter argument).subst binder valueCode = body.subst parameter argument := by
          rw [same]
          exact ScopedTyping.subst_absent _ _ _ (body.subst_removes_variable _ _
            (ScopedTyping.closedValue_no_variable closed))
        rw [unchanged]
        exact ihTail parameter body result argument (by simp [sourceEq, Code.subst, same]) targetEq closed
      · rw [subst_commute body parameter binder argument valueCode closed valueClosed (Ne.symm same)]
        exact ihTail parameter (body.subst binder valueCode) result argument
          (by simp [sourceEq, Code.subst, same]) targetEq closed

theorem EnvCloses.beta_argument
    (environment : EnvCloses graph owners heap saved (.lambda parameter body) (.lambda parameter result))
    (argument : ValueRel graph owners heap value argumentCode) :
    EnvCloses graph owners heap (.binding parameter value saved) body (result.subst parameter argumentCode) :=
  .binding argument (environment.lambda_argument_at _ _ _ _ rfl rfl argument.closed)

theorem ValueRel.closure_view
    (related : ValueRel graph owners heap (.closure parameter body saved) (.lambda parameter result)) :
    ∃ fuel rawBody, CoreTranslation.translateFuel graph fuel owners body = .ok rawBody ∧
      EnvCloses graph owners heap saved (.lambda parameter rawBody) (.lambda parameter result) ∧
      ClosedValue (.lambda parameter result) := by
  cases related with
  | closure translated environment closed => exact ⟨_, _, translated, environment, closed⟩

/-- Decompose one closing derivation, retaining its exact lexical replacements. -/
theorem EnvCloses.app_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ rawFunction rawArgument function argument,
      source = .app rawFunction rawArgument → target = .app function argument →
      EnvCloses graph owners heap environment rawFunction function ∧
      EnvCloses graph owners heap environment rawArgument argument := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro rf ra f a sourceEq targetEq
      have same : rf = f ∧ ra = a := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩
      exact ⟨.empty, .empty⟩
  | @binding value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail (rf.subst binder valueCode) (ra.subst binder valueCode) f a
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.binding replacement left, .binding replacement right⟩
  | @resource rest output binder key code tail ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail
        (rf.instantiate (Instantiation.Environment.empty.bind binder key))
        (ra.instantiate (Instantiation.Environment.empty.bind binder key)) f a
        (by simp only [sourceEq, Code.instantiate]) targetEq
      exact ⟨.resource left, .resource right⟩
  | @templateUnused binder rest code output parameter body absent tail ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail rf ra f a sourceEq targetEq
      have absentLeft : Dependency.variable binder ∉ rf.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_left ra.dependencies member
      have absentRight : Dependency.variable binder ∉ ra.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right rf.dependencies member
      exact ⟨.templateUnused absentLeft left, .templateUnused absentRight right⟩
  | @templateExpand fuel body bodyCode parameter binder rest valueCode output code translated nonrecursive replacement closed tail ihReplacement ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail (rf.subst binder valueCode) (ra.subst binder valueCode) f a
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.templateExpand translated nonrecursive replacement closed left,
        .templateExpand translated nonrecursive replacement closed right⟩

theorem EnvCloses.app_components
    (related : EnvCloses graph owners heap environment (.app rawFunction rawArgument) (.app function argument)) :
    EnvCloses graph owners heap environment rawFunction function ∧
      EnvCloses graph owners heap environment rawArgument argument :=
  related.app_components_at _ _ _ _ rfl rfl

#print axioms EnvCloses.app_components

namespace Examples
open CoreMachineExamples

/-- The existing lexical-closure graph's function reads 17 from its saved
    environment even when the caller shadows binder 1 with 99. -/
theorem lexical_closure : ValueRel lexicalClosure [] []
    (.closure 2 1 (.binding 1 (.integer 17) .empty)) (.lambda 2 (.integer 17)) := by
  refine .closure (fuel := 1) (bodyCode := .variable 1) rfl ?_ ?_
  · exact .binding .integer (by simpa [Code.subst] using (EnvCloses.empty
      (graph := lexicalClosure) (owners := []) (heap := []) (code := .lambda 2 (.integer 17))))
  · simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]

theorem lexical_lookup : EnvCloses lexicalClosure [] []
    (.binding 1 (.integer 99)
      (.binding 3 (.closure 2 1 (.binding 1 (.integer 17) .empty))
        (.binding 1 (.integer 17) .empty)))
    (.variable 3) (.lambda 2 (.integer 17)) := by
  apply EnvCloses.binding ValueRel.integer
  simp only [Code.subst, if_neg (show ¬ (1 : Nat) = 3 by decide)]
  apply EnvCloses.binding lexical_closure
  simp only [Code.subst, ↓reduceIte]
  apply EnvCloses.binding ValueRel.integer
  simpa [Code.subst] using (EnvCloses.empty (graph := lexicalClosure)
    (owners := []) (heap := []) (code := .lambda 2 (.integer 17)))

theorem lexical_lookup_value : ∃ value,
    CoreMachine.Environment.lookup
      (.binding 1 (.integer 99)
        (.binding 3 (.closure 2 1 (.binding 1 (.integer 17) .empty))
          (.binding 1 (.integer 17) .empty))) 3 = some value ∧
    ValueRel lexicalClosure [] [] value (.lambda 2 (.integer 17)) :=
  lexical_lookup.lookup lexical_closure.closed

theorem parameter_shadow : EnvCloses lexicalClosure [] []
    (.binding 1 (.integer 99) .empty) (.lambda 1 (.variable 1)) (.lambda 1 (.variable 1)) :=
  EnvCloses.parameter_shadow .integer .empty

/-- Shadowed ordinary names use the nearest entry; older 17 cannot replace 99. -/
theorem ordinary_shadow : EnvCloses lexicalClosure [] []
    (.binding 1 (.integer 99) (.binding 1 (.integer 17) .empty))
    (.variable 1) (.integer 99) := by
  apply EnvCloses.binding ValueRel.integer
  simp only [Code.subst, ↓reduceIte]
  exact .binding .integer .empty

/-- The actual singleton main wrapper has a used template. Its replacement
    closes over the finite tail; lookup's closure still retains the self suffix. -/
theorem main_template : EnvCloses entryWrapper [] []
    (.functionTemplate 5 8 0 .empty) (.variable 5) (.lambda 8 (.integer 17)) := by
  refine .templateExpand (fuel := 1) (bodyCode := .integer 17) rfl ?_ .empty ?_ ?_
  · simp [Code.dependencies, Syntax.without]
  · simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]
  · simpa [Code.subst] using (EnvCloses.empty (graph := entryWrapper)
      (owners := []) (heap := []) (code := .lambda 8 (.integer 17)))

theorem main_lookup_value : ValueRel entryWrapper [] []
    (.closure 8 0 (.functionTemplate 5 8 0 .empty)) (.lambda 8 (.integer 17)) := by
  obtain ⟨value, known, related⟩ := main_template.lookup
    (by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without])
  have same : value = .closure 8 0 (.functionTemplate 5 8 0 .empty) := by
    simpa [CoreMachine.Environment.lookup] using known.symm
  exact same ▸ related

/-- An unused template needs no recursive interpretation of its self suffix. -/
theorem unused_template : EnvCloses entryWrapper [] []
    (.functionTemplate 5 8 0 .empty) (.integer 99) (.integer 99) :=
  .templateUnused (by simp [Code.dependencies]) .empty

/-- The nearest resource activation wins, and a previously closed handle stays
    on activation 7 under an unrelated later same-name binding to activation 11. -/
theorem resource_shadow : EnvCloses cellGraph [] []
    (.resource 3 7 (.resource 3 11 .empty)) (.resourceRef (.bound 3)) (.resourceRef (.activation 7)) := by
  apply EnvCloses.resource
  simp only [Code.instantiate, Instantiation.ResourceName.instantiate,
    Instantiation.Environment.bind, ↓reduceIte]
  exact .resource .empty

theorem resource_lookup : ∃ key,
    CoreMachine.Environment.resourceKey (.resource 3 7 (.resource 3 11 .empty)) 3 = some key ∧
      Code.resourceRef (.activation 7) = .resourceRef (.activation key) :=
  resource_shadow.resource_lookup (ValueRel.handle (graph := cellGraph)
    (owners := []) (heap := []) (key := 7)).closed

/-- Binary tuple storage preserves the scalar observation under fresh allocation. -/
theorem tuple_value : ValueRel tupleGraph [] [.pair (.integer 17) (.boolean true)]
    (.location 0) (.pair (.integer 17) (.boolean true)) :=
  .location rfl .integer .boolean

theorem tuple_allocation : ValueRel tupleGraph []
    [.pair (.integer 17) (.boolean true), .pair .unit .unit]
    (.location 0) (.pair (.integer 17) (.boolean true)) :=
  tuple_value.heap_weaken (heap_append _ [.pair .unit .unit])

/-- Malformed raw data receives no successful representation witness. -/
theorem missing_tuple_rejected : ¬ ValueRel tupleGraph [] [] (.location 0) code := by
  intro related
  obtain ⟨left, right, leftCode, rightCode, known, rest⟩ := related.location_view
  cases known

theorem changed_integer_rejected : ¬ ValueRel lexicalClosure [] [] (.integer 17) (.integer 99) := by
  intro related
  have impossible := ValueRel.integer_iff.mp related
  cases impossible

end Examples

#print axioms subst_commute
#print axioms EnvCloses.beta_argument
#print axioms ValueRel.closure_view
#print axioms ValueRel.closed
#print axioms ValueRel.heap_weaken
#print axioms EnvCloses.heap_weaken
#print axioms EnvCloses.closed_identity
#print axioms EnvCloses.lookup
#print axioms ValueRel.closure_shape
#print axioms EnvCloses.parameter_shadow
#print axioms EnvCloses.resource_lookup
#print axioms binding_instantiation
#print axioms Examples.lexical_lookup_value
#print axioms Examples.main_lookup_value
#print axioms Examples.tuple_allocation

end Ash.OneShot.CoreValueRelation
