import CoreRequestFrames

/-! Exact resume operand carriers. Static resolution uses the current code's
owner map; dynamic scope coherence is separate and supplied at completion.
These lemmas reuse one existing lexical closing derivation. -/
namespace Ash.OneShot.CoreResumeFrames
open ScopedExpressions ScopedExecution CoreValueRelation CoreRequestFrames

/-- Resume binders are unchanged by ordinary closure or resource instantiation.
Both child and marker carrier come from the same current derivation. -/
theorem resume_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ rawBinder rawOperand binder operand,
      source = .resume rawBinder rawOperand → target = .resume binder operand →
      rawBinder = binder ∧ EnvCloses graph owners heap environment rawOperand operand ∧
        EnvCloses graph owners heap environment (.resume binder .unit) (.resume binder .unit) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro rb raw binder operand sourceEq targetEq
      have same : rb = binder ∧ raw = operand := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl,rfl⟩
      exact ⟨rfl,.empty,.empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro rb raw binder operand sourceEq targetEq
      obtain ⟨same,child,header⟩ := ihTail rb (raw.subst name valueCode) binder operand
        (by simp only [sourceEq,Code.subst]) targetEq
      exact ⟨same,.binding replacement child,.binding replacement header⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro rb raw binder operand sourceEq targetEq
      obtain ⟨same,child,header⟩ := ihTail rb (raw.instantiate (Instantiation.Environment.empty.bind name key)) binder operand
        (by simp only [sourceEq,Code.instantiate]) targetEq
      exact ⟨same,.resource child,.resource header⟩
  | @templateUnused name owners heap rest code output parameter body absent tail ihTail =>
      intro rb raw binder operand sourceEq targetEq
      obtain ⟨same,child,header⟩ := ihTail rb raw binder operand sourceEq targetEq
      have absentChild : Syntax.Dependency.variable name ∉ raw.dependencies := by
        intro member; apply absent
        simpa only [sourceEq,Code.dependencies,List.mem_cons] using Or.inr member
      have absentHeader : Syntax.Dependency.variable name ∉ (Code.resume binder .unit).dependencies := by
        simp [Code.dependencies]
      exact ⟨same,.templateUnused absentChild child,.templateUnused absentHeader header⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro rb raw binder operand sourceEq targetEq
      obtain ⟨same,child,header⟩ := ihTail rb (raw.subst name valueCode) binder operand
        (by simp only [sourceEq,Code.subst]) targetEq
      exact ⟨same,.templateExpand translated callable nonrecursive replacement closed child,
        .templateExpand translated callable nonrecursive replacement closed header⟩

theorem resume_components
    (related : EnvCloses graph owners heap environment (.resume rawBinder rawOperand) (.resume binder operand)) :
    rawBinder = binder ∧ EnvCloses graph owners heap environment rawOperand operand ∧
      EnvCloses graph owners heap environment (.resume binder .unit) (.resume binder .unit) :=
  resume_components_at related _ _ _ _ rfl rfl

set_option linter.unusedSimpArgs false in
/-- Projection of the existing translator's resume RHS. Static owner resolution
and operand translation are derived from actual successful site translation. -/
theorem resume_translation_parts
    (known : graph.node site = some node) (kind : node.kind = .resume handler owner post operand)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.resume binder code)) :
    ∃ operandFuel, CoreTranslation.resolveOwner owners site handler owner = .ok binder ∧
      CoreTranslation.translateFuel graph operandFuel owners operand = .ok code := by
  cases fuel with
  | zero => simp [CoreTranslation.translateFuel] at translated
  | succ fuel =>
      cases node with
      | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,known] at translated
        cases resolved : CoreTranslation.resolveOwner owners site handler owner with
        | error error => simp [Bind.bind,Except.bind,resolved] at translated
        | ok mapped =>
          cases child : CoreTranslation.translateFuel graph fuel owners operand with
          | error error => simp [Bind.bind,Except.bind,resolved,child] at translated
          | ok raw =>
            have same : mapped = binder ∧ raw = code := by
              simpa [Bind.bind,Except.bind,Pure.pure,Except.pure,resolved,child] using translated
            rcases same with ⟨rfl,rfl⟩
            exact ⟨fuel,rfl,child⟩

/-- Recover all Boolean branch children from the same clause derivation. -/
theorem branch_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ rawCondition rawYes rawNo condition yes no,
      source = .branch rawCondition rawYes rawNo → target = .branch condition yes no →
      EnvCloses graph owners heap environment rawCondition condition ∧
      EnvCloses graph owners heap environment rawYes yes ∧ EnvCloses graph owners heap environment rawNo no := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro rc ry rn c y n sourceEq targetEq
      have same : rc = c ∧ ry = y ∧ rn = n := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl,rfl,rfl⟩
      exact ⟨.empty,.empty,.empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro rc ry rn c y n sourceEq targetEq
      obtain ⟨condition,yes,no⟩ := ihTail (rc.subst name valueCode) (ry.subst name valueCode) (rn.subst name valueCode) c y n
        (by simp only [sourceEq,Code.subst]) targetEq
      exact ⟨.binding replacement condition,.binding replacement yes,.binding replacement no⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro rc ry rn c y n sourceEq targetEq
      let inst := Instantiation.Environment.empty.bind name key
      obtain ⟨condition,yes,no⟩ := ihTail (rc.instantiate inst) (ry.instantiate inst) (rn.instantiate inst) c y n
        (by simp only [sourceEq,Code.instantiate,inst]) targetEq
      exact ⟨.resource condition,.resource yes,.resource no⟩
  | @templateUnused name owners heap rest code output parameter body absent tail ihTail =>
      intro rc ry rn c y n sourceEq targetEq
      obtain ⟨condition,yes,no⟩ := ihTail rc ry rn c y n sourceEq targetEq
      have conditionAbsent : Syntax.Dependency.variable name ∉ rc.dependencies := by
        intro member; apply absent
        simpa only [sourceEq,Code.dependencies] using
          List.mem_append_left rn.dependencies (List.mem_append_left ry.dependencies member)
      have yesAbsent : Syntax.Dependency.variable name ∉ ry.dependencies := by
        intro member; apply absent
        simpa only [sourceEq,Code.dependencies] using
          List.mem_append_left rn.dependencies (List.mem_append_right rc.dependencies member)
      have noAbsent : Syntax.Dependency.variable name ∉ rn.dependencies := by
        intro member; apply absent
        simpa only [sourceEq,Code.dependencies] using List.mem_append_right (rc.dependencies ++ ry.dependencies) member
      exact ⟨.templateUnused conditionAbsent condition,.templateUnused yesAbsent yes,.templateUnused noAbsent no⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro rc ry rn c y n sourceEq targetEq
      obtain ⟨condition,yes,no⟩ := ihTail (rc.subst name valueCode) (ry.subst name valueCode) (rn.subst name valueCode) c y n
        (by simp only [sourceEq,Code.subst]) targetEq
      exact ⟨.templateExpand translated callable nonrecursive replacement closed condition,
        .templateExpand translated callable nonrecursive replacement closed yes,
        .templateExpand translated callable nonrecursive replacement closed no⟩

theorem branch_components
    (related : EnvCloses graph owners heap environment (.branch rawCondition rawYes rawNo) (.branch condition yes no)) :
    EnvCloses graph owners heap environment rawCondition condition ∧
      EnvCloses graph owners heap environment rawYes yes ∧ EnvCloses graph owners heap environment rawNo no :=
  branch_components_at related _ _ _ _ _ _ rfl rfl

#print axioms branch_components

/-- The frame retains the exact static resume site and map interpretation.
Scope resolution to a dynamic live ticket is required separately at completion. -/
inductive ResumeRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → PlainData → Prop where
  | operand (known : graph.node site = some node)
      (kind : node.kind = .resume handler owner post operand)
      (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.resume binder raw))
      (resolved : CoreTranslation.resolveOwner owners site handler owner = .ok binder)
      (marker : EnvCloses graph owners heap environment (.resume binder .unit) (.resume binder .unit))
      (context : plain.context = .resume binder) :
      ResumeRel graph owners heap (.resume handler owner) plain

theorem ResumeRel.heap_weaken (related : ResumeRel graph owners heap core plain)
    (extension : HeapExtends heap larger) : ResumeRel graph owners larger core plain := by
  cases related with
  | operand known kind translated resolved marker context =>
      exact .operand known kind translated resolved (marker.heap_weaken extension) context

#print axioms resume_components
#print axioms resume_translation_parts
#print axioms ResumeRel.heap_weaken
end Ash.OneShot.CoreResumeFrames
