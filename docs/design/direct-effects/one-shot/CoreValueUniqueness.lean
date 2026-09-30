import CoreValueRelation
import CoreTranslationFuel

/-! Uniqueness of finite value and environment closing derivations for the
same physical inputs. This concerns Code, not selectable port/row annotations. -/
namespace Ash.OneShot.CoreValueRelation
open ScopedExpressions
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem translated_unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok code)
    (second : CoreTranslation.translateFuel graph other owners index = .ok otherCode) : code = otherCode := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel other) owners index code (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph other (max fuel other) owners index otherCode (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

/-- A finite physical value has one related Code at fixed graph/map/heap. -/
theorem ValueRel.unique (first : ValueRel graph owners heap value code)
    (second : ValueRel graph owners heap value other) : code = other := by
  induction first using ValueRel.rec
    (motive_2 := fun owners heap environment code output _ =>
      ∀ other, EnvCloses graph owners heap environment code other → output = other) generalizing other with
  | unit => cases second; rfl
  | boolean => cases second; rfl
  | integer => cases second; rfl
  | handle => cases second; rfl
  | location known left right ihLeft ihRight =>
    cases second with
    | location otherKnown otherLeft otherRight =>
      have same := Option.some.inj (known.symm.trans otherKnown)
      obtain ⟨rfl,rfl⟩ := CoreMachine.HeapCell.pair.inj same
      rw [ihLeft otherLeft,ihRight otherRight]
  | closure translated callable environment closed ihEnvironment =>
    cases second with
    | closure otherTranslated otherCallable otherEnvironment otherClosed =>
      have same := translated_unique translated otherTranslated
      cases same
      exact ihEnvironment _ otherEnvironment

  | empty =>
    rename_i other second
    cases second; rfl
  | binding replacement tail ihReplacement ihTail =>
    rename_i other second
    cases second with
    | binding otherReplacement otherTail =>
      have same := ihReplacement otherReplacement
      cases same
      exact ihTail _ otherTail
  | resource tail ihTail =>
    rename_i other second
    cases second with
    | resource otherTail => exact ihTail _ otherTail
  | templateUnused absent tail ihTail =>
    rename_i other second
    cases second with
    | templateUnused otherAbsent otherTail => exact ihTail _ otherTail
    | templateExpand translated callable nonrecursive replacement closed otherTail =>
      have unchanged := fun value => ScopedTyping.subst_absent _ _ value absent
      simp only [unchanged] at otherTail
      exact ihTail _ otherTail
  | templateExpand translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
    rename_i other second
    cases second with
    | templateUnused absent otherTail =>
      have unchanged := fun value => ScopedTyping.subst_absent _ _ value absent
      simp only [unchanged] at ihTail
      exact ihTail _ otherTail
    | templateExpand otherTranslated otherCallable otherNonrecursive otherReplacement otherClosed otherTail =>
      have same := translated_unique translated otherTranslated
      cases same
      have replacementEq := ihReplacement _ otherReplacement
      cases replacementEq
      exact ihTail _ otherTail
/-- The same finite lexical substitution closes one source Code uniquely. -/
theorem EnvCloses.unique (first : EnvCloses graph owners heap environment code output)
    (second : EnvCloses graph owners heap environment code other) : output = other := by
  induction first using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) generalizing other with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => cases second; rfl
  | binding replacement tail ihReplacement ihTail =>
    cases second with
    | binding otherReplacement otherTail =>
      have same := ValueRel.unique replacement otherReplacement
      cases same
      exact ihTail otherTail
  | resource tail ihTail =>
    cases second with
    | resource otherTail => exact ihTail otherTail
  | templateUnused absent tail ihTail =>
    cases second with
    | templateUnused otherAbsent otherTail => exact ihTail otherTail
    | templateExpand translated callable nonrecursive replacement closed otherTail =>
      have unchanged := fun value => ScopedTyping.subst_absent _ _ value absent
      simp only [unchanged] at otherTail
      exact ihTail otherTail
  | templateExpand translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
    cases second with
    | templateUnused absent otherTail =>
      have unchanged := fun value => ScopedTyping.subst_absent _ _ value absent
      simp only [unchanged] at ihTail
      exact ihTail otherTail
    | templateExpand otherTranslated otherCallable otherNonrecursive otherReplacement otherClosed otherTail =>
      have same := translated_unique translated otherTranslated
      cases same
      have replacementEq := ihReplacement otherReplacement
      cases replacementEq
      exact ihTail otherTail
end Ash.OneShot.CoreValueRelation
#print axioms Ash.OneShot.CoreValueRelation.ValueRel.unique
#print axioms Ash.OneShot.CoreValueRelation.EnvCloses.unique
