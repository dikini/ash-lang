import SourceDependencyHandlerGap

/-! Clause certificates retain the exact receiving interpretation scope.
Captured continuations and fresh owners remain universally quantified. These
lemmas are a contextual replacement interface for uniform schemes; source
handler entry and the runtime stored-forest integration remain separate. -/
namespace Ash.OneShot.SourceContextualClauses
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture
open SourceDependencyChecks (Local)
open SourceDependencySchemes (Checked Retained CaptureSource ClauseFamily)
abbrev Receiving := SourceDependencyCapture.Scope

inductive FamilyAt (outward : List Instance) (rights : Syntax.OneShotRights)
    (family : Nat → Dependencies) (tail : Receiving) : Prop where
  | checked (body : ∀ actions phases world owner captured,
      actions owner = some rights → phases owner = .available →
      CaptureSource outward actions phases world owner rights captured tail →
      Checked outward actions phases world (family owner) (.live owner captured tail)) :
      FamilyAt outward rights family tail

theorem FamilyAt.instantiate (scheme : FamilyAt outward rights family tail)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : CaptureSource outward actions phases world owner rights captured tail) :
    Checked outward actions phases world (family owner) (.live owner captured tail) := by
  cases scheme with | checked body => exact body actions phases world owner captured known available source

/-- Uniform proofs retain their original generality and require no new
continuation, substitution or recomposition proof. -/
theorem FamilyAt.of_uniform (scheme : ClauseFamily outward rights family) :
    FamilyAt outward rights family tail :=
  .checked (fun _ _ _ _ _ known available source => scheme.instantiate known available source)

theorem FamilyAt.silent_prefix (scheme : FamilyAt outward rights family tail)
    (silent : dependencies.Silent) :
    FamilyAt outward rights (fun owner => .sequence dependencies (family owner)) tail :=
  .checked (fun _ _ _ _ _ known available source =>
    .sequence (.silent silent) (scheme.instantiate known available source))

theorem FamilyAt.choice (left : FamilyAt outward rights first tail)
    (right : FamilyAt outward rights second tail) :
    FamilyAt outward rights (fun owner => .choice (first owner) (second owner)) tail :=
  .checked (fun _ _ _ _ _ known available source =>
    .choice (left.instantiate known available source) (right.instantiate known available source))

/-- Spent-marker projection may change the representation of the receiving
tail without changing its interpretation or restoring a consumed permission.
This does not allow arbitrary caller insertion or handler exchange. -/
theorem FamilyAt.project_tail (scheme : FamilyAt outward rights family tail)
    (same : SourceDependencyProjection.project tail = SourceDependencyProjection.project nextTail) :
    FamilyAt outward rights family nextTail := by
  constructor
  intro actions phases world owner captured known available source
  have original : CaptureSource outward actions phases world owner rights captured tail := by
    refine ⟨?_, ?_, ?_⟩
    · intro permission
      simpa only [Retained, same] using source.saved permission
    · simpa only [Retained, same] using source.waiting
    · intro permission
      obtain ⟨unprotected, closes, scheduled⟩ := source.disposal permission
      exact ⟨unprotected, closes, by
        simpa only [Retained, SourceDependencyProjection.project, same] using scheduled⟩
  simpa only [Checked, SourceDependencyProjection.project, same] using
    scheme.instantiate known available original

/-- An operation capability is authenticated by exact nearest lookup. The
source-handler case provides both modes and excludes disposal of the new
capture. This capability can be reused for repeated requests; it is not a
continuation-use permission or a counted effect occurrence. -/
inductive RequestCapability (effect : Instance) (operation : Nat) (tail : Receiving) : Prop where
  | builtin (found : select effect operation tail = some (.builtin identity)) :
      RequestCapability effect operation tail
  | handler (found : select effect operation tail = some (.handler captured outside contract modes))
      (resumesOnly : contract.dispose = false)
      (rows : ∀ held, ∃ row, contract.row held = some row)
      (bodies : ∀ held, ∃ family, modeDependencies held modes = some family) :
      RequestCapability effect operation tail

/-- Pending sequencing and the live clause owner preserve nearest lookup.
No property of the saved continuation is assumed by this request lemma. -/
theorem RequestCapability.request (capability : RequestCapability effect operation tail) :
    Checked outward actions phases world (.request effect operation)
      (.plain suffix (.live owner captured tail)) := by
  cases capability with
  | builtin found =>
      rename_i identity
      have actual : select effect operation
          (SourceDependencyProjection.project (.plain suffix (.live owner captured tail))) = some (.builtin identity) := by
        rw [SourceDependencyProjection.project_select]
        simp only [select, found, Option.map_some, Selection.prepend]
        rfl
      apply Local.request (.builtin actual)
      · intro saved outside contract modes selected
        rw [actual] at selected
        cases selected
      · intro saved outside contract modes selected
        rw [actual] at selected
        cases selected
  | handler found resumesOnly rows bodies =>
      rename_i saved outside contract modes
      have actual : select effect operation
          (SourceDependencyProjection.project (.plain suffix (.live owner captured tail))) =
          some (.handler (SourceDependencyProjection.project (.plain suffix (.live owner captured saved)))
            (SourceDependencyProjection.project outside) contract modes) := by
        rw [SourceDependencyProjection.project_select]
        simp only [select, found, Option.map_some, Selection.prepend]
        rfl
      apply Local.request_selected actual
      · apply check_capture_iff.mpr
        obtain ⟨row, rowFound⟩ := rows _
        obtain ⟨family, bodyFound⟩ := bodies _
        exact .handler actual (by simp [modeCheck, resumesOnly]) rowFound bodyFound
          (by intro impossible; simp [resumesOnly] at impossible)
      · intro impossible; simp [resumesOnly] at impossible
      · intro impossible; simp [resumesOnly] at impossible

/-- A literal operation followed by a certified suffix uses the same direct
sequencing rule. The retained context supplies the operation independently of
the suffix's continuation capabilities. -/
theorem FamilyAt.request_prefix (scheme : FamilyAt outward rights family tail)
    (capability : RequestCapability effect operation tail) :
    FamilyAt outward rights
      (fun owner => .sequence (.sequence .pure (.request effect operation)) (family owner)) tail := by
  constructor
  intro actions phases world owner captured known available source
  exact .sequence (.sequence .pure capability.request) (scheme.instantiate known available source)

inductive ModeAt (outward : List Instance) (rights : Syntax.OneShotRights) (tail : Receiving) :
    Option (Nat → Dependencies) → Prop where
  | unavailable : ModeAt outward rights tail none
  | available (scheme : FamilyAt outward rights family tail) : ModeAt outward rights tail (some family)

inductive DeclarationsAt (outward : List Instance) (tail : Receiving) :
    Clauses → SourceDependencyAnnotations.ClauseDependencies → Prop where
  | nil : DeclarationsAt outward tail .nil []
  | cons (ordinary : ModeAt outward body.requiredActions tail ordinaryFamily)
      (protectedMode : ModeAt outward body.requiredActions tail protectedFamily)
      (rest : DeclarationsAt outward tail clauses families) :
      DeclarationsAt outward tail (.cons operation parameter binder body clauses)
        ((operation, ordinaryFamily, protectedFamily) :: families)

theorem ModeAt.of_uniform (scheme : SourceDependencySchemes.ModeScheme outward rights family) :
    ModeAt outward rights tail family := by
  cases scheme with
  | unavailable => exact .unavailable
  | available checked => exact .available (.of_uniform checked)

theorem DeclarationsAt.of_uniform (schemes : SourceDependencySchemes.DeclarationSchemes outward clauses families) :
    DeclarationsAt outward tail clauses families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons (.of_uniform ordinary) (.of_uniform protectedMode) ih

theorem ModeAt.selected (scheme : ModeAt outward rights tail offeredFamily)
    (found : offeredFamily = some family) : FamilyAt outward rights family tail := by
  subst offeredFamily
  cases scheme with | available checked => exact checked

/-- The contextual certificate follows the existing first-match declaration
lookup and uses the exact selected source body's continuation permissions. -/
theorem DeclarationsAt.selected (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (lookupDependencies operation families).bind (modeDependencies held) = some family) :
    FamilyAt outward code.requiredActions family tail := by
  induction selected generalizing families with
  | hit => cases schemes with
      | cons ordinary protectedMode rest =>
          simp only [lookupDependencies, if_true, Option.bind_some] at found
          cases held with
          | false => exact ordinary.selected found
          | true => exact protectedMode.selected found
  | pass different next ih => cases schemes with
      | cons ordinary protectedMode rest =>
          exact ih rest (by simpa only [lookupDependencies, if_neg different] using found)

/-- Reuse capture-source construction and pending recomposition on the actual
cut. The receiving tail supplied to the certificate is exactly the cut's tail;
no fresh-owner or captured-source proof is assumed by the certificate itself. -/
theorem allocate_checked_clause
    (scheme : FamilyAt outward rights family tail)
    (checked : Checked outward actions phases world (.request effect operation) (captured.append tail))
    (retained : Retained outward actions phases world (captured.append tail) .nil)
    (found : select effect operation (captured.append tail) = some (.handler captured tail contract modes))
    (disposalPermission : rights.dispose = true → contract.dispose = true)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    Checked outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (family owner) (.live owner captured tail) ∧
    Retained outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (.live owner captured tail) .nil := by
  have source := SourceDependencySchemes.capture_source_from_request checked retained found disposalPermission fresh consumed
  constructor
  · exact scheme.instantiate (by simp [Syntax.UsageTickets.insert])
      (by simp [OwnerPhaseTransitions.introduce]) source
  · exact SourceDependencySchemes.pending_transport (SourceDependencySchemes.retained_capture retained)
      SourceDependencySchemes.introduce_extends (Syntax.fresh_usage_insert_extends fresh) (List.Subset.refl _)

/-- Selection joins the contextual certificate to the existing hereditary
source offer. The fresh contract and dependency family are the same witnesses
returned by the established rich declaration-selection theorem. -/
theorem selected_checked_body
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies held) = some family ∧
      FamilyAt outward code.requiredActions family tail ∧
      ∀ owner (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, body⟩ :=
    selected_body source selected found available
  exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located,
    schemes.selected selected located, body⟩

/-- Capture joins the exact contextual declaration with its typed payload and
fresh continuation interface. This reuses the earlier selected-mode and
capture-source construction; runtime stored-certificate transport is separate. -/
theorem allocate_declared_clause
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (modes : SourceTemplates.ClauseModes clauses table)
    (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (selection : select requested operation (captured.append tail) = chosen operation table families captured tail)
    (checked : Checked outward actions phases world (.request requested operation) (captured.append tail))
    (retained : Retained outward actions phases world (captured.append tail) .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies captured.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner captured tail) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner captured tail) .nil ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, scheme, body⟩ :=
    selected_checked_body source schemes selected found available
  obtain ⟨contract, actual, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected modes
  cases Option.some.inj (found.symm.trans actual)
  cases familyFound : lookupDependencies operation families with
  | none => simp [familyFound] at located
  | some alternatives =>
      have exactSelection : select requested operation (captured.append tail) =
          some (.handler captured tail offered alternatives) := by
        simpa only [chosen, found, familyFound] using selection
      obtain ⟨clauseChecked, liveRetained⟩ := allocate_checked_clause scheme checked retained exactSelection disposalPermission fresh consumed
      exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, by simpa only [familyFound] using located,
        clauseChecked, liveRetained, body owner⟩


namespace Examples
open SourceDependencyHandlerGap (effect rights family outside)

theorem outer_capability : RequestCapability effect 0 outside :=
  .handler rfl rfl (fun held => by cases held <;> exact ⟨[], rfl⟩)
    (fun held => by cases held <;> exact ⟨_, rfl⟩)

/-- Unlike the old single fixture, this certificate checks the failing
clause for every captured source and fresh owner under the retained outer
interpretation. Resume is the previously established proof. -/
theorem contextual_family : FamilyAt outward rights family outside :=
  ((FamilyAt.of_uniform (SourceDependencySchemes.resume_family (rights := rights) rfl)).silent_prefix .pure).request_prefix
    outer_capability

theorem contextual_declarations : DeclarationsAt outward outside
    SourceDependencyHandlerGap.clauses SourceDependencyHandlerGap.dependencies :=
  .cons (.available contextual_family) .unavailable .nil

theorem spent_tail_family : FamilyAt outward rights family (.spent retired outside) :=
  contextual_family.project_tail rfl

/-- One reusable operation capability supports two sequential requests.
The continuation suffix is checked once by the existing one-shot scheme. -/
theorem repeated_request_family : FamilyAt outward rights
    (fun owner => .sequence (.sequence .pure (.request effect 0)) (family owner)) outside :=
  contextual_family.request_prefix outer_capability

/-- A nearest handler without the operation blocks the outer capability.
It is not permissible to reinterpret the effect list by skipping that handler. -/
theorem shadowed_capability_rejected :
    ¬ RequestCapability effect 0 (.handler effect [] [] outside) := by
  intro capability
  cases capability with
  | builtin found | handler found => change none = some _ at found; cases found

/-- The new certificate has not turned an effect name into an ambient
implementation: absence of the required interpretation still rejects it. -/
theorem absent_rejected : ¬ FamilyAt outward rights family .nil := by
  intro scheme
  have checked := scheme.instantiate rfl rfl (SourceDependencyHandlerGap.empty_capture_source outward)
  have request := (Local.sequence_iff.mp (Local.sequence_iff.mp checked).1).2
  have guarded := Local.request_guard request
  change false = true at guarded
  cases guarded

end Examples
end Ash.OneShot.SourceContextualClauses

#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.instantiate
#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.of_uniform
#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.silent_prefix
#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.choice
#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.project_tail
#print axioms Ash.OneShot.SourceContextualClauses.RequestCapability.request
#print axioms Ash.OneShot.SourceContextualClauses.FamilyAt.request_prefix
#print axioms Ash.OneShot.SourceContextualClauses.ModeAt.of_uniform
#print axioms Ash.OneShot.SourceContextualClauses.DeclarationsAt.of_uniform
#print axioms Ash.OneShot.SourceContextualClauses.ModeAt.selected
#print axioms Ash.OneShot.SourceContextualClauses.DeclarationsAt.selected
#print axioms Ash.OneShot.SourceContextualClauses.allocate_checked_clause
#print axioms Ash.OneShot.SourceContextualClauses.selected_checked_body
#print axioms Ash.OneShot.SourceContextualClauses.Examples.outer_capability
#print axioms Ash.OneShot.SourceContextualClauses.Examples.contextual_family
#print axioms Ash.OneShot.SourceContextualClauses.Examples.contextual_declarations
#print axioms Ash.OneShot.SourceContextualClauses.Examples.spent_tail_family
#print axioms Ash.OneShot.SourceContextualClauses.Examples.repeated_request_family
#print axioms Ash.OneShot.SourceContextualClauses.Examples.shadowed_capability_rejected
#print axioms Ash.OneShot.SourceContextualClauses.Examples.absent_rejected

#print axioms Ash.OneShot.SourceContextualClauses.allocate_declared_clause


namespace Ash.OneShot.SourceContextualClauses.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture
open SourceDependencyChecks.Lexical (Local Pending)
open SourceDependencySchemes.Lexical (CaptureSource ClauseFamily)
abbrev Receiving := SourceDependencyCapture.Scope
inductive FamilyAt (outward : List Instance) (rights : Syntax.OneShotRights)
    (family : Nat → Dependencies) (tail : Receiving) : Prop where
  | checked (body : ∀ actions phases world owner captured,
      actions owner = some rights → phases owner = .available →
      CaptureSource outward actions phases world owner rights captured tail →
      Local outward actions phases world (family owner) (.live owner captured tail)) :
      FamilyAt outward rights family tail

theorem FamilyAt.instantiate (scheme : FamilyAt outward rights family tail)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : CaptureSource outward actions phases world owner rights captured tail) :
    Local outward actions phases world (family owner) (.live owner captured tail) := by
  cases scheme with | checked body => exact body actions phases world owner captured known available source

/-- Uniform proofs retain their original generality and require no new
continuation, substitution or recomposition proof. -/
theorem FamilyAt.of_uniform (scheme : ClauseFamily outward rights family) :
    FamilyAt outward rights family tail :=
  .checked (fun _ _ _ _ _ known available source => scheme.instantiate known available source)

theorem FamilyAt.silent_prefix (scheme : FamilyAt outward rights family tail)
    (silent : dependencies.Silent) :
    FamilyAt outward rights (fun owner => .sequence dependencies (family owner)) tail :=
  .checked (fun _ _ _ _ _ known available source =>
    .sequence (.silent silent) (scheme.instantiate known available source))

theorem FamilyAt.choice (left : FamilyAt outward rights first tail)
    (right : FamilyAt outward rights second tail) :
    FamilyAt outward rights (fun owner => .choice (first owner) (second owner)) tail :=
  .checked (fun _ _ _ _ _ known available source =>
    .choice (left.instantiate known available source) (right.instantiate known available source))


/-- The existing exact-tail request capability supplies the lexical request
    guard; its nondisposing handler modes need no abandoned callback traversal. -/
theorem request_capability (capability : RequestCapability effect operation tail) :
    Local outward actions phases world (.request effect operation) (.plain suffix (.live owner captured tail)) := by
  cases capability with
  | builtin found =>
    rename_i identity
    have actual : select effect operation (.plain suffix (.live owner captured tail)) = some (.builtin identity) := by
      simp only [select, found, Option.map_some, Selection.prepend]
    apply Local.request (.builtin actual)
    all_goals
      intro saved outside contract modes selected disposes
      cases Option.some.inj (actual.symm.trans selected)
  | handler found resumesOnly rows bodies =>
    rename_i saved outside contract modes
    have actual : select effect operation (.plain suffix (.live owner captured tail)) =
        some (.handler (.plain suffix (.live owner captured saved)) outside contract modes) := by
      simp only [select, found, Option.map_some, Selection.prepend]
    obtain ⟨row, rowFound⟩ := rows (SourceDependencyCapture.Scope.held (.plain suffix (.live owner captured saved)))
    obtain ⟨family, bodyFound⟩ := bodies (SourceDependencyCapture.Scope.held (.plain suffix (.live owner captured saved)))
    apply Local.request (.handler actual (by simp [modeCheck, resumesOnly]) rowFound bodyFound)
    all_goals
      intro saved outside contract modes selected disposes
      cases Option.some.inj (actual.symm.trans selected)
      simp [resumesOnly] at disposes

/-- A literal operation followed by a certified suffix uses the same direct
sequencing rule. The retained context supplies the operation independently of
the suffix's continuation capabilities. -/
theorem FamilyAt.request_prefix (scheme : FamilyAt outward rights family tail)
    (capability : RequestCapability effect operation tail) :
    FamilyAt outward rights
      (fun owner => .sequence (.sequence .pure (.request effect operation)) (family owner)) tail := by
  constructor
  intro actions phases world owner captured known available source
  exact .sequence (.sequence .pure (request_capability capability)) (scheme.instantiate known available source)

inductive ModeAt (outward : List Instance) (rights : Syntax.OneShotRights) (tail : Receiving) :
    Option (Nat → Dependencies) → Prop where
  | unavailable : ModeAt outward rights tail none
  | available (scheme : FamilyAt outward rights family tail) : ModeAt outward rights tail (some family)

inductive DeclarationsAt (outward : List Instance) (tail : Receiving) :
    Clauses → SourceDependencyAnnotations.ClauseDependencies → Prop where
  | nil : DeclarationsAt outward tail .nil []
  | cons (ordinary : ModeAt outward body.requiredActions tail ordinaryFamily)
      (protectedMode : ModeAt outward body.requiredActions tail protectedFamily)
      (rest : DeclarationsAt outward tail clauses families) :
      DeclarationsAt outward tail (.cons operation parameter binder body clauses)
        ((operation, ordinaryFamily, protectedFamily) :: families)

/-- Value substitution preserves the same certified families and their
permission indices. Ordinary source substitution separately authenticates the
unchanged dependency annotations. Both clause binders still shadow the name. -/
theorem DeclarationsAt.substitution (schemes : DeclarationsAt outward tail clauses families)
    (value : replacement.IsValue) (name : Nat) :
    DeclarationsAt outward tail (clauses.subst name replacement) families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      simp only [Clauses.subst]
      split
      · exact .cons ordinary protectedMode ih
      · exact .cons
          (by simpa only [Code.substitution_required_actions _ name value] using ordinary)
          (by simpa only [Code.substitution_required_actions _ name value] using protectedMode) ih

/-- Name instantiation preserves certification of the supplied dependency
families because required continuation actions are unchanged. This theorem
alone does not authenticate those families as source annotations of the
instantiated code; resource bodies must supply their hereditary source proof. -/
theorem DeclarationsAt.instantiation (schemes : DeclarationsAt outward tail clauses families)
    (environment : Instantiation.Environment) :
    DeclarationsAt outward tail (clauses.instantiate environment) families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons
        (by simpa only [Code.instantiation_required_actions] using ordinary)
        (by simpa only [Code.instantiation_required_actions] using protectedMode) ih

theorem ModeAt.selected (scheme : ModeAt outward rights tail offeredFamily)
    (found : offeredFamily = some family) : FamilyAt outward rights family tail := by
  subst offeredFamily
  cases scheme with | available checked => exact checked

/-- The contextual certificate follows the existing first-match declaration
lookup and uses the exact selected source body's continuation permissions. -/
theorem DeclarationsAt.selected (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (lookupDependencies operation families).bind (modeDependencies held) = some family) :
    FamilyAt outward code.requiredActions family tail := by
  induction selected generalizing families with
  | hit => cases schemes with
      | cons ordinary protectedMode rest =>
          simp only [lookupDependencies, if_true, Option.bind_some] at found
          cases held with
          | false => exact ordinary.selected found
          | true => exact protectedMode.selected found
  | pass different next ih => cases schemes with
      | cons ordinary protectedMode rest =>
          exact ih rest (by simpa only [lookupDependencies, if_neg different] using found)

/-- Reuse capture-source construction and pending recomposition on the actual
cut. The receiving tail supplied to the certificate is exactly the cut's tail;
no fresh-owner or captured-source proof is assumed by the certificate itself. -/
theorem allocate_checked_clause
    (scheme : FamilyAt outward rights family tail)
    (checked : Local outward actions phases world (.request effect operation) (captured.append tail))
    (retained : Pending outward actions phases world (captured.append tail) .nil)
    (found : select effect operation (captured.append tail) = some (.handler captured tail contract modes))
    (disposalPermission : rights.dispose = true → contract.dispose = true)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    Local outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (family owner) (.live owner captured tail) ∧
    Pending outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (.live owner captured tail) .nil := by
  have source := SourceDependencySchemes.Lexical.capture_source_from_request checked retained found disposalPermission fresh consumed
  constructor
  · exact scheme.instantiate (by simp [Syntax.UsageTickets.insert])
      (by simp [OwnerPhaseTransitions.introduce]) source
  · exact SourceDependencySchemes.Lexical.pending_transport (Pending.capture retained)
      SourceDependencySchemes.introduce_extends (Syntax.fresh_usage_insert_extends fresh) (List.Subset.refl _)

/-- Selection joins the contextual certificate to the existing hereditary
source offer. The fresh contract and dependency family are the same witnesses
returned by the established rich declaration-selection theorem. -/
theorem selected_checked_body
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies held) = some family ∧
      FamilyAt outward code.requiredActions family tail ∧
      ∀ owner (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, body⟩ :=
    selected_body source selected found available
  exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located,
    schemes.selected selected located, body⟩

/-- Capture joins the exact contextual declaration with its typed payload and
fresh continuation interface. This reuses the earlier selected-mode and
capture-source construction; runtime stored-certificate transport is separate. -/
theorem allocate_declared_clause
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (modes : SourceTemplates.ClauseModes clauses table)
    (schemes : DeclarationsAt outward tail clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (selection : select requested operation (captured.append tail) = chosen operation table families captured tail)
    (checked : Local outward actions phases world (.request requested operation) (captured.append tail))
    (retained : Pending outward actions phases world (captured.append tail) .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies captured.held) = some family ∧
      Local outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner captured tail) ∧
      Pending outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner captured tail) .nil ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, scheme, body⟩ :=
    selected_checked_body source schemes selected found available
  obtain ⟨contract, actual, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected modes
  cases Option.some.inj (found.symm.trans actual)
  cases familyFound : lookupDependencies operation families with
  | none => simp [familyFound] at located
  | some alternatives =>
      have exactSelection : select requested operation (captured.append tail) =
          some (.handler captured tail offered alternatives) := by
        simpa only [chosen, found, familyFound] using selection
      obtain ⟨clauseChecked, liveRetained⟩ := allocate_checked_clause scheme checked retained exactSelection disposalPermission fresh consumed
      exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, by simpa only [familyFound] using located,
        clauseChecked, liveRetained, body owner⟩



namespace Examples
open SourceDependencyHandlerGap (effect rights family outside)
theorem contextual_family : FamilyAt outward rights family outside :=
  ((FamilyAt.of_uniform (SourceDependencySchemes.Lexical.resume_family (rights := rights) rfl)).silent_prefix .pure).request_prefix
    SourceContextualClauses.Examples.outer_capability

theorem contextual_declarations : DeclarationsAt outward outside
    SourceDependencyHandlerGap.clauses SourceDependencyHandlerGap.dependencies :=
  .cons (.available contextual_family) .unavailable .nil

theorem repeated_request_family : FamilyAt outward rights
    (fun owner => .sequence (.sequence .pure (.request effect 0)) (family owner)) outside :=
  contextual_family.request_prefix SourceContextualClauses.Examples.outer_capability

theorem absent_rejected : ¬ FamilyAt outward rights family .nil := by
  intro scheme
  have source : CaptureSource outward SourceDependencyHandlerGap.actions SourceDependencyHandlerGap.phases [] 19 rights .nil .nil :=
    ⟨fun _ => .nil, .nil, by intro impossible; cases impossible⟩
  have checked := scheme.instantiate rfl rfl source
  have request := (Local.sequence_iff.mp (Local.sequence_iff.mp checked).1).2
  cases request.request_guard with
  | builtin found | handler found => cases found
end Examples
end Ash.OneShot.SourceContextualClauses.Lexical

#print axioms Ash.OneShot.SourceContextualClauses.Lexical.FamilyAt.instantiate
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.FamilyAt.of_uniform
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.FamilyAt.silent_prefix
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.FamilyAt.choice
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.request_capability
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.FamilyAt.request_prefix
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.ModeAt.selected
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.DeclarationsAt.selected
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.allocate_checked_clause
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.selected_checked_body
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.allocate_declared_clause
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.Examples.contextual_family
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.Examples.contextual_declarations
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.Examples.repeated_request_family
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.Examples.absent_rejected
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.DeclarationsAt.substitution
#print axioms Ash.OneShot.SourceContextualClauses.Lexical.DeclarationsAt.instantiation
