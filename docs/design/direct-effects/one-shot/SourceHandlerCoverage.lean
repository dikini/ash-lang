import SourceContextualRequirements

/-! Finite operation coverage for replacing the nearest interpretation with a
resumptive handler. This checks operation availability and control capabilities,
not callback scheduling or whole-clause admission. Builtin coverage is limited
to the two operations authenticated by the existing cell signature. -/
namespace Ash.OneShot.SourceHandlerCoverage
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture
open SourceContextualHints (checkCapability)

/-- Stop at the nearest matching interpreter, including an incomplete handler.
Dormant captures are not on the current lookup path. -/
def operationDomain (effect : Instance) : Scope → List Nat
  | .nil => []
  | .handler requested table _ rest =>
      if effect = requested then table.map Prod.fst else operationDomain effect rest
  | .cell identity rest =>
      if effect = .cell identity then [0, 1] else operationDomain effect rest
  | .plain _ rest | .cleanup _ _ rest | .running rest | .spent _ rest => operationDomain effect rest
  | .live _ _ rest => operationDomain effect rest

/-- Raw source lookup intentionally abstracts over builtin operation typing.
The coverage theorem separately requires that typing fact for cell operations. -/
def BuiltinTyped (operation : Nat) : Selection → Prop
  | .builtin _ => operation = 0 ∨ operation = 1
  | .handler _ _ _ _ => True

private theorem lookup_key (found : lookup operation table = some contract) : operation ∈ table.map Prod.fst := by
  induction table with
  | nil => cases found
  | cons item rest ih =>
      obtain ⟨key, value⟩ := item
      by_cases same : operation = key
      · simp [same]
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

private theorem prepend_typed (frame : Scope → Scope) (selected : Selection) :
    BuiltinTyped operation (selected.prepend frame) = BuiltinTyped operation selected := by
  cases selected <;> rfl

/-- Every selected, typed operation belongs to the finite nearest-provider
interface. This includes same-effect shadowing and builtin blockers. -/
theorem selected_in_domain
    (found : select effect operation scope = some selected)
    (typed : BuiltinTyped operation selected) : operation ∈ operationDomain effect scope := by
  induction scope generalizing selected with
  | nil => cases found
  | handler requested table families rest ih =>
      by_cases same : effect = requested
      · simp only [select, if_pos same] at found
        cases entry : lookup operation table with
        | none => simp [entry] at found
        | some contract =>
            simpa only [operationDomain, if_pos same] using lookup_key entry
      · simp only [select, if_neg same] at found
        obtain ⟨original, looked, rfl⟩ := Option.map_eq_some_iff.mp found
        simpa only [operationDomain, if_neg same] using ih looked (by simpa only [prepend_typed] using typed)
  | cell identity rest ih =>
      by_cases same : effect = .cell identity
      · simp only [select, if_pos same, Option.some.injEq] at found
        subst selected
        simpa [operationDomain, same, BuiltinTyped] using typed
      · simp only [select, if_neg same] at found
        obtain ⟨original, looked, rfl⟩ := Option.map_eq_some_iff.mp found
        simpa only [operationDomain, if_neg same] using ih looked (by simpa only [prepend_typed] using typed)
  | plain dependencies rest ih | cleanup needs callback rest ih | running rest ih | spent owner rest ih =>
      obtain ⟨original, looked, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ih looked (by simpa only [prepend_typed] using typed)
  | live owner saved rest ihSaved ihRest =>
      obtain ⟨original, looked, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ihRest looked (by simpa only [prepend_typed] using typed)

/-- Cell typing discharges the operation-domain premise; it is not a new
restriction on typed cell programs. -/
theorem builtin_typed_of_signature
    (known : ScopedPorts.withCellSignatures users (.cell identity) operation = some ports) :
    BuiltinTyped operation (.builtin identity) := by
  cases operation with
  | zero => exact Or.inl rfl
  | succ operation => cases operation with
    | zero => exact Or.inr rfl
    | succ operation => cases known

private theorem prepend_builtin {selected : Selection}
    (same : selected.prepend frame = .builtin identity) : selected = .builtin identity := by
  cases selected with
  | builtin actual => exact same
  | handler captured tail contract modes => cases same

/-- A builtin result authenticates the requested resource instance even below
arbitrary intervening scopes. Saved captures are not searched. -/
theorem selected_builtin_effect
    (found : select effect operation scope = some (.builtin identity)) : effect = .cell identity := by
  induction scope with
  | nil => cases found
  | handler requested table families rest ih =>
      by_cases same : effect = requested
      · simp only [select, if_pos same] at found
        cases entry : lookup operation table <;> cases modes : lookupDependencies operation families <;>
          simp [entry, modes] at found
      · simp only [select, if_neg same] at found
        obtain ⟨original, looked, equal⟩ := Option.map_eq_some_iff.mp found
        exact ih (prepend_builtin equal ▸ looked)
  | cell actual rest ih =>
      by_cases same : effect = .cell actual
      · simp only [select, if_pos same, Option.some.injEq] at found
        cases found
        exact same
      · simp only [select, if_neg same] at found
        obtain ⟨original, looked, equal⟩ := Option.map_eq_some_iff.mp found
        exact ih (prepend_builtin equal ▸ looked)
  | plain dependencies rest ih | cleanup needs callback rest ih | running rest ih | spent owner rest ih =>
      obtain ⟨original, looked, equal⟩ := Option.map_eq_some_iff.mp found
      exact ih (prepend_builtin equal ▸ looked)
  | live owner saved rest ihSaved ihRest =>
      obtain ⟨original, looked, equal⟩ := Option.map_eq_some_iff.mp found
      exact ihRest (prepend_builtin equal ▸ looked)

/-- Typing the requested operation supplies the coverage bound for whichever
interpreter exact lookup selected. No builtin-specific premise is needed. -/
theorem selected_typed_of_signature
    (known : ScopedPorts.withCellSignatures users effect operation = some ports)
    (found : select effect operation scope = some selected) : BuiltinTyped operation selected := by
  cases selected with
  | builtin identity =>
      have same := selected_builtin_effect found
      exact builtin_typed_of_signature (same ▸ known)
  | handler captured tail contract modes => trivial

def check (effect : Instance) (table : List (Nat × ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (before : Scope) : Bool :=
  (operationDomain effect before).all
    (fun operation => checkCapability (.handler effect table families .nil) effect operation)

private theorem installed_capability (tail : Scope) :
    checkCapability (.handler effect table families tail) effect operation =
      checkCapability (.handler effect table families .nil) effect operation := by
  simp only [checkCapability, select]
  cases lookup operation table <;> cases lookupDependencies operation families <;> rfl

/-- The finite test checks the existing capability judgment at every key in
that nearest interface. Repeated keys do not create use-count obligations. -/
theorem check_iff : check effect table families before = true ↔
    ∀ operation ∈ operationDomain effect before,
      SourceContextualClauses.RequestCapability effect operation (.handler effect table families tail) := by
  simp only [check, List.all_eq_true, ← SourceContextualRequirements.check_capability_iff, installed_capability]

/-- A checked replacement supplies every previously selectable typed operation
with the existing independent resumptive capability in both protection modes.
No equality of provider implementations or change to lookup order is assumed. -/
theorem selected_capability
    (covered : check effect table families before = true)
    (found : select effect operation before = some selected)
    (typed : BuiltinTyped operation selected) :
    SourceContextualClauses.RequestCapability effect operation (.handler effect table families tail) := by
  exact check_iff.mp covered operation (selected_in_domain found typed)

namespace Examples
open SourceDependencyCapture.Examples

theorem same_effect_covered : check effectE resumeTable resumeDependencies (handlerE .nil) = true := by decide

theorem missing_operation_rejected : check effectE [] [] (handlerE .nil) = false := by decide

theorem incomplete_nearest_stops :
    operationDomain effectE (.handler effectE [] [] (handlerE .nil)) = [] := rfl

theorem missing_protected_mode_rejected :
    check effectE resumeTable [(0, some resumeFamily, none)] (handlerE .nil) = false := by decide

def cellTable : List (Nat × ClauseContract) :=
  [(0, ⟨false, some [], some []⟩), (1, ⟨false, some [], some []⟩)]
def cellFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some resumeFamily, some resumeFamily), (1, some resumeFamily, some resumeFamily)]

theorem cell_covered : check (.cell 4) cellTable cellFamilies (.cell 4 .nil) = true := by decide

theorem read_only_does_not_cover_cell : check (.cell 4) resumeTable resumeDependencies (.cell 4 .nil) = false := by decide

end Examples
end Ash.OneShot.SourceHandlerCoverage

#print axioms Ash.OneShot.SourceHandlerCoverage.selected_in_domain
#print axioms Ash.OneShot.SourceHandlerCoverage.builtin_typed_of_signature
#print axioms Ash.OneShot.SourceHandlerCoverage.selected_builtin_effect
#print axioms Ash.OneShot.SourceHandlerCoverage.selected_typed_of_signature
#print axioms Ash.OneShot.SourceHandlerCoverage.check_iff
#print axioms Ash.OneShot.SourceHandlerCoverage.selected_capability
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.same_effect_covered
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.missing_operation_rejected
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.incomplete_nearest_stops
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.missing_protected_mode_rejected
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.cell_covered
#print axioms Ash.OneShot.SourceHandlerCoverage.Examples.read_only_does_not_cover_cell
