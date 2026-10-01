import CoreCallableStorageRecipes

namespace Ash.OneShot.CoreCallableCapturedRecipes
open ScopedExpressions ScopedExecution
open CoreCallableReturnStorageProducer
open CallableContracts (Contract AgreeOn)

/-- Finite transport of the actual callee annotation. Capture hits install the
already specialized caller tree; bind and lambda shadowing follow Code.subst. -/
def substitute (code : Code) (annotation : Annotation) (name : Nat) (frozen : Annotation) : Annotation :=
  match code, annotation with
  | .variable other, _ => if name = other then frozen else annotation
  | .pair left right, .node template [a,b] => .node template [substitute left a name frozen,substitute right b name frozen]
  | .lambda parameter body, .node template [a] => .node template [if name = parameter then a else substitute body a name frozen]
  | .app function argument, .node template [a,b] => .node template [substitute function a name frozen,substitute argument b name frozen]
  | .bind parameter initial body, .node template [a,b] => .node template [substitute initial a name frozen,if name = parameter then b else substitute body b name frozen]
  | .branch condition yes no, .node template [a,b,c] => .node template [substitute condition a name frozen,substitute yes b name frozen,substitute no c name frozen]
  | .resource _ initial body, .node template [a,b] => .node template [substitute initial a name frozen,substitute body b name frozen]
  | .cleanup action body, .node template [a,b] => .node template [substitute action a name frozen,substitute body b name frozen]
  | _, _ => annotation
termination_by code.nodes
decreasing_by all_goals simp only [Code.nodes]; all_goals omega

theorem captureCheck_complete (captured : CallableContracts.Captures (environment bindings) bound deps) :
    captureCheck bindings bound deps = true := by
  apply List.all_eq_true.mpr
  intro dep member
  cases CallableContracts.captures_iff.mp captured dep member with
  | resource received => simpa [atomCheck] using received
  | «variable» known received => simp [atomCheck,environment] at known ⊢; rw [known]; simpa using received

theorem captureCheck_congr (accepted : captureCheck bindings bound deps = true)
    (agree : AgreeOn (environment bindings) (environment next) deps) :
    captureCheck next bound deps = true :=
  captureCheck_complete (CallableContracts.captures_environment (captureCheck_sound accepted) agree)

theorem captureCheck_substitute {code : Code}
    (accepted : captureCheck (extend bindings name input) bound code.dependencies = true)
    (closed : ClosedValue value) (received : Syntax.resourceDependencies value.dependencies ⊆ input.storageOf) :
    captureCheck bindings bound (code.subst name value).dependencies = true := by
  apply captureCheck_complete
  exact CallableContracts.captures_substitution (captureCheck_sound accepted) closed received

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- The SAME finite tree checks identically when its actual free-variable
storage lookups agree. Local parameter contracts are preserved exactly. -/
theorem check_environment_congr {code : Code}
    (accepted : check bindings code annotation = some result)
    (agree : AgreeOn (environment bindings) (environment next) code.dependencies) :
    check next code annotation = some result := by
  induction code using Code.rec (motive_2 := fun _ => True) generalizing bindings next annotation result with
  | unit | boolean flag | integer value | resourceRef resource =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next template =>
          cases template <;> try simp [check] at accepted ⊢
          next bound =>
            first
            | simpa [check,Code.dependencies,captureCheck] using accepted
            | cases resource <;> simp [check,Code.dependencies,captureCheck,atomCheck] at accepted ⊢; assumption
  | «variable» name =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        have same := agree name (by simp [Code.dependencies])
        exact same.symm.trans accepted
  | pair left right ihL ihR =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next first rest =>
          cases rest <;> try simp [check] at accepted ⊢
          next second rest =>
            cases rest <;> try simp [check] at accepted ⊢
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨a,ha,b,hb,same⟩ := accepted
            have la := ihL ha (CallableContracts.agree_left agree)
            have rb := ihR hb (CallableContracts.agree_right agree)
            simpa only [check,la,rb,Option.bind_some] using same
  | lambda parameter body ih =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next template bodyAnn rest =>
          cases rest <;> cases template <;> try simp [check] at accepted ⊢
          next captures input output =>
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨actual,bodyChecked,accepted⟩ := accepted
            split at accepted
            next same =>
              cases Option.some.inj accepted
              have nextBody := ih (next := extend next parameter input) bodyChecked (by simpa only [environment_extend] using CallableContracts.agree_extend (input := input) agree)
              have nextCapture := captureCheck_congr same.2 agree
              simp only [nextBody,Option.bind_some]
              exact if_pos ⟨same.1,nextCapture⟩
            next => contradiction
  | app function argument ihF ihA =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next first rest =>
          cases rest <;> try simp [check] at accepted ⊢
          next second rest =>
            cases rest <;> try simp [check] at accepted ⊢
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨functionContract,functionChecked,accepted⟩ := accepted
            cases functionContract
            · contradiction
            · contradiction
            next captures input output =>
              cases argumentChecked : check bindings argument second with
              | none => simp [argumentChecked] at accepted
              | some actual =>
                have nextFn := ihF functionChecked (CallableContracts.agree_left agree)
                have nextArg := ihA argumentChecked (CallableContracts.agree_right agree)
                simp only [argumentChecked,Option.bind_some] at accepted
                simpa only [check,nextFn,nextArg,Option.bind_some] using accepted
  | bind parameter initial body ihI ihB =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next first rest =>
          cases rest <;> try simp [check] at accepted ⊢
          next second rest =>
            cases rest <;> try simp [check] at accepted ⊢
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨input,initialChecked,bodyChecked⟩ := accepted
            have nextInitial := ihI initialChecked (CallableContracts.agree_left agree)
            have nextBody := ihB (next := extend next parameter input) bodyChecked (by simpa only [environment_extend] using CallableContracts.agree_extend (input := input) (CallableContracts.agree_right agree))
            simpa only [check,nextInitial,Option.bind_some] using nextBody
  | branch condition yes no ihC ihY ihN =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next first rest =>
          cases rest <;> try simp [check] at accepted ⊢
          next second rest =>
            cases rest <;> try simp [check] at accepted ⊢
            next third rest =>
              cases rest <;> try simp [check] at accepted ⊢
              simp only [Option.bind_eq_some_iff] at accepted
              obtain ⟨cc,hc,a,ha,b,hb,accepted⟩ := accepted
              have nc := ihC hc (CallableContracts.agree_left (CallableContracts.agree_left agree))
              have ny := ihY ha (CallableContracts.agree_right (CallableContracts.agree_left agree))
              have nn := ihN hb (CallableContracts.agree_right agree)
              simpa only [check,nc,ny,nn,Option.bind_some] using accepted
  | perform | handle | resume | discard | resource | cleanup => cases annotation <;> simp [check] at accepted
  | nil | cons => trivial

theorem check_closed_environment {value : Code}
    (accepted : check bindings value annotation = some result) (closed : ClosedValue value) :
    check next value annotation = some result :=
  check_environment_congr accepted (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem check_environment_equal
    (accepted : check bindings code annotation = some result)
    (same : environment bindings = environment next) : check next code annotation = some result :=
  check_environment_congr accepted (fun name _ => congrFun same name)

theorem checked_value_support {value : Code}
    (accepted : check bindings value annotation = some input) (closed : ClosedValue value) :
    Syntax.resourceDependencies value.dependencies ⊆ input.storageOf :=
  CallableContracts.value_support (check_sound (declarations := fun _ => none) (world := []) (ticket := .none) accepted) closed.1

/-- Generic exact finite storage transport. The replacement is the frozen
caller tree at the SAME full captured slot contract; results are not widened. -/
theorem check_substitute {code value : Code}
    (accepted : check (extend bindings name input) code annotation = some result)
    (replacement : check callerBindings value frozen = some input) (closed : ClosedValue value) :
    check bindings (code.subst name value) (substitute code annotation name frozen) = some result := by
  induction code using Code.rec (motive_2 := fun _ => True) generalizing bindings name input annotation result with
  | unit | boolean flag | integer val | resourceRef resource =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted ⊢
        next template =>
          cases template <;> try simp [check] at accepted ⊢
          next bound =>
            first
            | simpa [Code.subst,substitute,check,Code.dependencies,captureCheck] using accepted
            | cases resource <;> simp [check,Code.subst,substitute,Code.dependencies,captureCheck,atomCheck] at accepted ⊢; assumption
  | «variable» other =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        by_cases same : name = other
        · subst other
          simp only [lookup,extend,↓reduceIte] at accepted
          cases Option.some.inj accepted
          simpa only [Code.subst,substitute,↓reduceIte] using check_closed_environment (next := bindings) replacement closed
        · simpa only [Code.subst,substitute,if_neg same,check,lookup,extend,if_neg (Ne.symm same)] using accepted
  | pair left right ihL ihR =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨a,ha,b,hb,same⟩ := accepted
            have la := ihL ha replacement
            have rb := ihR hb replacement
            simpa only [Code.subst,substitute,check,la,rb,bind,pure,Option.bind_some] using same
  | lambda parameter body ih =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next template bodyAnn rest =>
          cases rest <;> cases template <;> try simp [check] at accepted
          next captures domain output =>
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨actual,bodyChecked,accepted⟩ := accepted
            split at accepted
            next shape =>
              cases Option.some.inj accepted
              have nextCapture := captureCheck_substitute shape.2 closed (checked_value_support replacement closed)
              by_cases same : name = parameter
              · subst parameter
                have nextBody := check_environment_equal (next := extend bindings name domain) bodyChecked (by simp only [environment_extend,CallableContracts.Environment.extend_shadow])
                simp only [Code.subst,substitute,↓reduceIte,check,nextBody]
                exact if_pos ⟨shape.1,by simpa only [Code.subst,↓reduceIte] using nextCapture⟩
              · have reordered : check (extend (extend bindings parameter domain) name input) body bodyAnn = some actual :=
                  check_environment_equal bodyChecked (by simpa only [environment_extend] using CallableContracts.Environment.extend_commute (environment bindings) name parameter input domain same)
                have nextBody := ih reordered replacement
                simp only [Code.subst,substitute,if_neg same,check,nextBody]
                exact if_pos ⟨shape.1,by simpa only [Code.subst,if_neg same] using nextCapture⟩
            next => contradiction
  | app function argument ihF ihA =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨fn,fnChecked,accepted⟩ := accepted
            cases fn
            · contradiction
            · contradiction
            next captures domain output =>
              cases argChecked : check (extend bindings name input) argument second with
              | none => simp [argChecked] at accepted
              | some actual =>
                have nextFn := ihF fnChecked replacement
                have nextArg := ihA argChecked replacement
                simp only [argChecked,Option.bind_some] at accepted
                simpa only [Code.subst,substitute,check,nextFn,nextArg,bind,pure,Option.bind_some] using accepted
  | bind parameter initial body ihI ihB =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨domain,initialChecked,bodyChecked⟩ := accepted
            have nextInitial := ihI initialChecked replacement
            by_cases same : name = parameter
            · subst parameter
              have nextBody := check_environment_equal (next := extend bindings name domain) bodyChecked (by simp only [environment_extend,CallableContracts.Environment.extend_shadow])
              simpa only [Code.subst,substitute,↓reduceIte,check,nextInitial,bind,pure,Option.bind_some] using nextBody
            · have reordered : check (extend (extend bindings parameter domain) name input) body second = some result :=
                check_environment_equal bodyChecked (by simpa only [environment_extend] using CallableContracts.Environment.extend_commute (environment bindings) name parameter input domain same)
              have nextBody := ihB reordered replacement
              simpa only [Code.subst,substitute,if_neg same,check,nextInitial,bind,pure,Option.bind_some] using nextBody
  | branch condition yes no ihC ihY ihN =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            next third rest =>
              cases rest <;> try simp [check] at accepted
              simp only [Option.bind_eq_some_iff] at accepted
              obtain ⟨cc,hc,a,ha,b,hb,accepted⟩ := accepted
              have nc := ihC hc replacement
              have ny := ihY ha replacement
              have nn := ihN hb replacement
              simpa only [Code.subst,substitute,check,nc,ny,nn,bind,pure,Option.bind_some] using accepted
  | perform | handle | resume | discard | resource | cleanup => cases annotation <;> simp [check] at accepted
  | nil | cons => trivial

/-- Compute the callee tree in its original environment/map and the replacement
in its own caller environment/map before inserting that frozen tree. -/
def specialize_substitution (bindings : Bindings) (calleeInst : Instantiation.Environment)
    (code : Code) (originalRecipe : CoreCallableStorageRecipes.Recipe)
    (name : Nat) (input : Contract) (callerBindings : Bindings)
    (callerInst : Instantiation.Environment) (callerRecipe : CoreCallableStorageRecipes.Recipe) :
    Option (Annotation × Annotation × Annotation) := do
  let original ← CoreCallableStorageRecipes.specialize (extend bindings name input) calleeInst originalRecipe
  let frozen ← CoreCallableStorageRecipes.specialize callerBindings callerInst callerRecipe
  return (original,frozen,substitute code original name frozen)

/-- Successful ORIGINAL recipe/slot checks produce the exact transformed
finite checker result. Neither callee nor caller template is reinterpreted. -/
theorem recipe_check_substitute {code value : Code}
    (accepted : CoreCallableStorageRecipes.check (extend bindings name input) calleeInst code originalRecipe = some result)
    (replacement : CoreCallableStorageRecipes.check callerBindings callerInst value callerRecipe = some input)
    (closed : ClosedValue value) :
    ∃ original frozen next : Annotation,
      CoreCallableStorageRecipes.specialize (extend bindings name input) calleeInst originalRecipe = some original ∧
      CoreCallableStorageRecipes.specialize callerBindings callerInst callerRecipe = some frozen ∧
      check (extend bindings name input) code original = some result ∧
      check callerBindings value frozen = some input ∧
      next = substitute code original name frozen ∧
      specialize_substitution bindings calleeInst code originalRecipe name input callerBindings callerInst callerRecipe = some (original,frozen,next) ∧
      check bindings (code.subst name value) next = some result := by
  cases originalEq : CoreCallableStorageRecipes.specialize (extend bindings name input) calleeInst originalRecipe with
  | none => simp [CoreCallableStorageRecipes.check,originalEq] at accepted
  | some original =>
      simp only [CoreCallableStorageRecipes.check,originalEq] at accepted
      cases callerEq : CoreCallableStorageRecipes.specialize callerBindings callerInst callerRecipe with
      | none => simp [CoreCallableStorageRecipes.check,callerEq] at replacement
      | some frozen =>
          simp only [CoreCallableStorageRecipes.check,callerEq] at replacement
          exact ⟨original,frozen,substitute code original name frozen,rfl,rfl,accepted,replacement,rfl,
            by simp [specialize_substitution,originalEq,callerEq],check_substitute accepted replacement closed⟩

/-- The returned full contract and receiver guard are inherited from the
original check. Future checker/storage evidence is constructed, never assumed. -/
theorem recipe_check_substitute_bound {code value : Code}
    (accepted : CoreCallableStorageRecipes.check (extend bindings name input) calleeInst code originalRecipe = some result)
    (replacement : CoreCallableStorageRecipes.check callerBindings callerInst value callerRecipe = some input)
    (closed : ClosedValue value) (received : result.storageOf ⊆ receiver) (issued : receiver ⊆ world) :
    ∃ original frozen next : Annotation,
      CoreCallableStorageRecipes.specialize (extend bindings name input) calleeInst originalRecipe = some original ∧
      CoreCallableStorageRecipes.specialize callerBindings callerInst callerRecipe = some frozen ∧
      next = substitute code original name frozen ∧
      check bindings (code.subst name value) next = some result ∧
      CallableContracts.Derives declarations (environment bindings) world ticket (code.subst name value) result ∧
      result.storageOf ⊆ receiver ∧ result.storageOf ⊆ world := by
  obtain ⟨original,frozen,next,oeq,feq,_,_,computed,_,nextCheck⟩ := recipe_check_substitute accepted replacement closed
  exact ⟨original,frozen,next,oeq,feq,computed,nextCheck,check_sound nextCheck,received,received.trans issued⟩

/-- Resource binders are a separate namespace: substitution descends through
both children even when the numeric names coincide. This mirrors Code.subst. -/
theorem resource_binder_substitute (binder name : Nat) (initial body : Code)
    (template : Option Contract) (a b frozen : Annotation) :
    substitute (.resource binder initial body) (.node template [a,b]) name frozen =
      .node template [substitute initial a name frozen,substitute body b name frozen] := by simp only [substitute]

#print axioms substitute
#print axioms captureCheck_complete
#print axioms captureCheck_congr
#print axioms captureCheck_substitute
#print axioms check_environment_congr
#print axioms check_closed_environment
#print axioms check_environment_equal
#print axioms checked_value_support
#print axioms check_substitute
#print axioms specialize_substitution
#print axioms recipe_check_substitute
#print axioms recipe_check_substitute_bound
#print axioms resource_binder_substitute
end Ash.OneShot.CoreCallableCapturedRecipes
