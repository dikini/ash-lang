import CoreCallableAuthenticatedOwners
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution Syntax
open CoreCallableReceiverRefinement (LexicalBounds)
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
private theorem closed_variables (closed : ScopedExpressions.ClosedValue value) :
    ∀ n, Dependency.variable n ∉ value.dependencies := fun _ => ScopedTyping.closedValue_no_variable closed
private theorem closed_tickets (closed : ScopedExpressions.ClosedValue value) :
    ∀ n, Dependency.ticket n ∉ value.dependencies := fun _ => ScopedTyping.closedValue_no_ticket closed

theorem substitution_dependencies_exact {value : Code}
    (expression : Code) (name : Nat) (closed : ScopedExpressions.ClosedValue value) (dependency : Dependency) :
    dependency ∈ (expression.subst name value).dependencies ↔
      (dependency ∈ expression.dependencies ∧ dependency ≠ .variable name) ∨
      (.variable name ∈ expression.dependencies ∧ dependency ∈ value.dependencies) := by
  have noVariables := closed_variables closed
  have noTickets := closed_tickets closed
  induction expression using Code.rec
    (motive_2 := fun clauses => ∀ dependency,
      dependency ∈ (clauses.subst name value).dependencies ↔
      (dependency ∈ clauses.dependencies ∧ dependency ≠ .variable name) ∨
      (.variable name ∈ clauses.dependencies ∧ dependency ∈ value.dependencies))
    generalizing dependency with
  | unit | boolean | integer => simp [Code.subst, Code.dependencies]
  | resourceRef ref => cases ref <;> simp [Code.subst, Code.dependencies] <;> grind
  | «variable» other =>
      by_cases same : name = other
      · subst other; simp_all [Code.subst, Code.dependencies]
      · simp [Code.subst, Code.dependencies, same] <;> grind
  | lambda parameter body ih =>
      by_cases same : name = parameter
      · subst parameter; simp_all [Code.subst, Code.dependencies, Syntax.mem_without]
      · simp_all [Code.subst, Code.dependencies, Syntax.mem_without] <;> grind
  | bind parameter initial body ihI ihB =>
      by_cases same : name = parameter
      · subst parameter; simp_all [Code.subst, Code.dependencies, Syntax.mem_without] <;> grind
      · simp_all [Code.subst, Code.dependencies, Syntax.mem_without] <;> grind
  | cons operation parameter ticket body rest ihB ihR =>
      by_cases same : name = parameter
      · subst parameter; simp_all [ScopedExpressions.Clauses.subst, ScopedExpressions.Clauses.dependencies, Syntax.mem_without] <;> grind
      · simp_all [ScopedExpressions.Clauses.subst, ScopedExpressions.Clauses.dependencies, Syntax.mem_without] <;> grind
  | nil => simp [ScopedExpressions.Clauses.subst, ScopedExpressions.Clauses.dependencies]
  | _ => simp_all [Code.subst, Code.dependencies] <;> grind
theorem substitution_support_reverse {value : Code}
    (expression : Code) (name : Nat) (closed : ScopedExpressions.ClosedValue value) :
    ScopedPorts.Support.evaluate
      (ScopedPorts.Support.extend environment name (resourceDependencies value.dependencies)) expression.dependencies ⊆
      ScopedPorts.Support.evaluate environment (expression.subst name value).dependencies := by
  intro identity retained
  obtain ⟨dependency, member, head⟩ := List.mem_flatMap.mp retained
  cases dependency with
  | resource resource =>
      exact List.mem_flatMap.mpr ⟨.resource resource,
        (substitution_dependencies_exact expression name closed _).mpr (.inl ⟨member, by simp⟩), head⟩
  | ticket ticket => simp at head
  | «variable» other =>
      by_cases same : other = name
      · subst other
        have actual : identity ∈ resourceDependencies value.dependencies := by
          simpa [ScopedPorts.Support.extend] using head
        exact List.mem_flatMap.mpr ⟨.resource identity,
          (substitution_dependencies_exact expression name closed _).mpr
            (.inr ⟨member, Syntax.mem_resourceDependencies.mp actual⟩), by simp⟩
      · exact List.mem_flatMap.mpr ⟨.variable other,
          (substitution_dependencies_exact expression name closed _).mpr (.inl ⟨member, by simpa using same⟩),
          by simpa [ScopedPorts.Support.extend, same] using head⟩

@[simp] theorem lexical_lookup_extend {lexical : LexicalBounds} :
    (lexical.extend name resources).lookup other = if other = name then some resources else lexical.lookup other := rfl

theorem known_substitution_restore {value expression : Code}
    (known : LexicalBounds.Known lexical (expression.subst name value).dependencies)
    (closed : ScopedExpressions.ClosedValue value) :
    LexicalBounds.Known (lexical.extend name (resourceDependencies value.dependencies)) expression.dependencies := by
  intro other member
  by_cases same : other = name
  · subst other; exact ⟨resourceDependencies value.dependencies, by simp⟩
  · obtain ⟨resources, found⟩ := known other
      ((substitution_dependencies_exact expression name closed _).mpr (.inl ⟨member, by simpa using same⟩))
    exact ⟨resources, by simpa [same] using found⟩

theorem known_substitution_remove {value expression : Code}
    (known : LexicalBounds.Known (lexical.extend name resources) expression.dependencies)
    (closed : ScopedExpressions.ClosedValue value) :
    LexicalBounds.Known lexical (expression.subst name value).dependencies := by
  intro other member
  have original := (substitution_dependencies_exact expression name closed _).mp member
  rcases original with ⟨member, different⟩ | ⟨_, inserted⟩
  · have unequal : other ≠ name := by simpa using different
    obtain ⟨resources, found⟩ := known other member
    exact ⟨resources, by simpa [unequal] using found⟩
  · exact False.elim (ScopedTyping.closedValue_no_variable closed inserted)

end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.substitution_dependencies_exact

#print axioms Ash.OneShot.CoreCallableContractAdmission.substitution_support_reverse
#print axioms Ash.OneShot.CoreCallableContractAdmission.known_substitution_restore
#print axioms Ash.OneShot.CoreCallableContractAdmission.known_substitution_remove
