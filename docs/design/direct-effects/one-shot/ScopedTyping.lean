import DeclaredSignatures

/-!
Scoped expression typing with generative resource bodies. The world records
resource names unavailable for fresh allocation, not live access or ownership.
A resource body checks for every fresh opening; no fixed source slot is treated
as a runtime owner. Signatures, usage and source admission remain separate.
-/

namespace Ash.OneShot.ScopedTyping
open Instantiation ScopedExpressions
open Typing (TypeEnv Signature TicketType retainedSupport)
open Syntax (Dependency without resourceDependencies)

abbrev World := List Nat

def InWorld (world : World) (type : Ty) : Prop := type.resources ⊆ world

def resourceWorld (issued : List Owner) : World := issued.filterMap fun owner =>
  match owner with | .resource key => some key | _ => none

theorem mem_resource_world : key ∈ resourceWorld issued ↔ Owner.resource key ∈ issued := by
  simp only [resourceWorld, List.mem_filterMap]
  constructor
  · rintro ⟨owner, member, selected⟩
    cases owner <;> simp_all
  · intro member
    exact ⟨.resource key, member, rfl⟩

theorem resource_world_append (left right : List Owner) :
    resourceWorld (left ++ right) = resourceWorld left ++ resourceWorld right := by
  simp [resourceWorld]

def clauseKeys : Clauses → List Nat
  | .nil => []
  | .cons operation _ _ _ rest => operation :: clauseKeys rest

def Covers (signature : Signature) (effect : Instance) (clauses : Clauses) : Prop :=
  ∀ operation input output, signature effect operation = some (input, output) → operation ∈ clauseKeys clauses

mutual
inductive Typed (signature : Signature) : World → TypeEnv → TicketType → List Instance → Code → Ty → Prop where
  | unit : Typed signature world environment ticket allowed .unit .unit
  | boolean : Typed signature world environment ticket allowed (.boolean value) .boolean
  | integer : Typed signature world environment ticket allowed (.integer value) .integer
  | «variable» (known : environment name = some type) (formed : InWorld world type) :
      Typed signature world environment ticket allowed (.variable name) type
  | reference (issued : identity ∈ world) :
      Typed signature world environment ticket allowed (.resourceRef (.activation identity)) (.reference identity)
  | pair : Typed signature world environment ticket allowed left leftType →
      Typed signature world environment ticket allowed right rightType →
      Typed signature world environment ticket allowed (.pair left right) (.product leftType rightType)
  | lambda : Typed signature world (environment.extend parameter input) .none latent body output →
      retainedSupport environment (without (.variable parameter) body.dependencies) ⊆ retained →
      InWorld world (.function input output latent retained) →
      Typed signature world environment ticket allowed (.lambda parameter body) (.function input output latent retained)
  | app : Typed signature world environment ticket allowed function (.function input output latent retained) →
      Typed signature world environment ticket allowed argument input → latent ⊆ allowed →
      Typed signature world environment ticket allowed (.app function argument) output
  | bind : Typed signature world environment ticket allowed initializer input →
      Typed signature world (environment.extend parameter input) ticket allowed suffix output →
      Typed signature world environment ticket allowed (.bind parameter initializer suffix) output
  | branch : Typed signature world environment ticket allowed condition .boolean →
      Typed signature world environment ticket allowed yes type → Typed signature world environment ticket allowed no type →
      Typed signature world environment ticket allowed (.branch condition yes no) type
  | perform : signature effect operation = some (input, output) → effect ∈ allowed →
      Typed signature world environment ticket allowed operand input → InWorld world output →
      Typed signature world environment ticket allowed (.perform (freezeEffect effect) operation operand) output
  | handle : Typed signature world environment ticket (effect :: residual) body answer →
      ClausesTyped signature world environment effect answer residual clauses → Covers signature effect clauses →
      (clauseKeys clauses).Nodup → residual ⊆ allowed →
      Typed signature world environment ticket allowed (.handle (freezeEffect effect) body clauses) answer
  | resume : Typed signature world environment (.bound binder input answer residual closing) allowed operand input →
      residual ⊆ allowed → InWorld world answer →
      Typed signature world environment (.bound binder input answer residual closing) allowed (.resume binder operand) answer
  | discard : closing ⊆ allowed →
      Typed signature world environment (.bound binder input answer residual closing) allowed (.discard binder) .unit
  | resource (initializerChecked : Typed signature world environment ticket allowed initializer .integer)
      (bodyChecked : ∀ identity, identity ∉ world →
        Typed signature (world ++ [identity]) environment ticket (.cell identity :: residual)
          (body.instantiate (Environment.empty.bind binder identity)) answer)
      (resultBound : InWorld world answer) (effectsBound : residual.flatMap Instance.resources ⊆ world)
      (effects : residual ⊆ allowed) :
      Typed signature world environment ticket allowed (.resource binder initializer body) answer
  | cleanup : Typed signature world environment ticket allowed action (.function .unit .unit latent retained) →
      Typed signature world environment ticket allowed body answer → latent ⊆ allowed →
      Typed signature world environment ticket allowed (.cleanup action body) answer

inductive ClausesTyped (signature : Signature) : World → TypeEnv → Instance → Ty → List Instance → Clauses → Prop where
  | nil : ClausesTyped signature world environment effect answer residual .nil
  | cons : signature effect operation = some (input, output) →
      Typed signature world (environment.extend parameter input) (.bound binder output answer residual residual) residual body answer →
      ClausesTyped signature world environment effect answer residual rest →
      ClausesTyped signature world environment effect answer residual (.cons operation parameter binder body rest)
end

theorem typed_result_in_world (typed : Typed signature world environment ticket allowed code type) : InWorld world type := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | unit | boolean | integer | discard => exact List.nil_subset _
  | «variable» _ formed | lambda _ _ formed _ | perform _ _ _ formed _ | resume _ _ formed _ => exact formed
  | reference issued => intro key member; obtain rfl := List.mem_singleton.mp member; exact issued
  | pair _ _ left right =>
      intro key member
      rcases List.mem_append.mp member with here | there
      · exact left here
      · exact right there
  | app _ _ _ function argument =>
      intro key member
      exact function (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
  | bind _ _ initializer suffix => exact suffix
  | branch _ _ _ condition yes no => exact yes
  | handle _ _ _ _ _ body clauses => exact body
  | resource _ _ resultBound _ _ initializer body => exact resultBound
  | cleanup _ _ _ action body => exact body
  | nil | cons => trivial

theorem in_world_mono (formed : InWorld world type) (larger : world ⊆ next) : InWorld next type :=
  List.Subset.trans formed larger

/-- Growing history preserves typing. The resource premise remains universal
    over all names fresh for the larger history, with no change to old atoms. -/
theorem typed_world_weaken (typed : Typed signature world environment ticket allowed code type) :
    ∀ next, world ⊆ next → Typed signature next environment ticket allowed code type := by
  induction typed using Typed.rec
    (motive_2 := fun world environment effect answer residual clauses _ =>
      ∀ next, world ⊆ next → ClausesTyped signature next environment effect answer residual clauses) with
  | unit => intro next larger; exact .unit
  | boolean => intro next larger; exact .boolean
  | integer => intro next larger; exact .integer
  | «variable» known formed => intro next larger; exact .variable known (in_world_mono formed larger)
  | reference issued => intro next larger; exact .reference (larger issued)
  | pair _ _ left right => intro next larger; exact .pair (left next larger) (right next larger)
  | lambda _ retained formed body => intro next larger; exact .lambda (body next larger) retained (in_world_mono formed larger)
  | app _ _ effects function argument => intro next larger; exact .app (function next larger) (argument next larger) effects
  | bind _ _ initializer suffix => intro next larger; exact .bind (initializer next larger) (suffix next larger)
  | branch _ _ _ condition yes no => intro next larger; exact .branch (condition next larger) (yes next larger) (no next larger)
  | perform operation available _ formed operand =>
      intro next larger; exact .perform operation available (operand next larger) (in_world_mono formed larger)
  | handle _ _ coverage unique effects body clauses =>
      intro next larger; exact .handle (body next larger) (clauses next larger) coverage unique effects
  | resume _ effects formed operand => intro next larger; exact .resume (operand next larger) effects (in_world_mono formed larger)
  | discard effects => intro next larger; exact .discard effects
  | resource _ _ resultBound effectsBound effects initializer body =>
      intro next larger
      refine .resource (initializer next larger) ?_ (in_world_mono resultBound larger) (List.Subset.trans effectsBound larger) effects
      intro identity fresh
      exact body identity (fun old => fresh (larger old)) (next ++ [identity]) (by
        intro key present
        rcases List.mem_append.mp present with old | current
        · exact List.mem_append_left _ (larger old)
        · exact List.mem_append_right _ current)
  | cleanup _ _ effects action body => intro next larger; exact .cleanup (action next larger) (body next larger) effects
  | nil => exact .nil
  | cons operation _ _ body rest =>
      rename_i next larger
      exact .cons operation (body next larger) (rest next larger)

theorem frozen_argument_no_free_names (argument : TypeArgument) : (freezeArgument argument).freeNames = [] := by
  induction argument with
  | nominal | resource => rfl
  | apply head argument ihHead ihArgument => simp [freezeArgument, Argument.freeNames, ihHead, ihArgument]

theorem frozen_effect_no_free_names (effect : Instance) : (freezeEffect effect).freeNames = [] := by
  cases effect with
  | cell => rfl
  | user family arguments =>
      simp [freezeEffect, Effect.freeNames, List.flatMap_map, frozen_argument_no_free_names]

theorem fresh_world_name (world : World) : ∃ identity, identity ∉ world := by
  let prepared := prepareActivation (world.map Owner.resource)
  exact ⟨prepared.identity, fun member => prepared.fresh (List.mem_map.mpr ⟨prepared.identity, member, rfl⟩)⟩

theorem append_empty {left right : List α} (l : left = []) (r : right = []) : left ++ right = [] := by
  rw [l, r]; rfl

/-- Typing derives the resource-name closure required by actual execution. -/
theorem typed_resource_closed (typed : Typed signature world environment ticket allowed code type) : code.ResourceClosed := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ clauses _ => clauses.freeNames = []) with
  | unit | boolean | integer | «variable» | reference | discard => rfl
  | pair _ _ left right | app _ _ _ left right | bind _ _ left right | cleanup _ _ _ left right =>
      exact append_empty left right
  | lambda _ _ _ body | resume _ _ _ body => exact body
  | branch _ _ _ condition yes no => exact append_empty (append_empty condition yes) no
  | perform _ _ _ _ operand => exact append_empty (frozen_effect_no_free_names _) operand
  | handle _ _ _ _ _ body clauses =>
      exact append_empty (append_empty (frozen_effect_no_free_names _) body) clauses
  | @resource currentWorld currentEnvironment currentTicket currentAllowed init residual answer binder source
      initTyped bodyTyped resultBound effectsBound effects initializer body =>
      obtain ⟨identity, fresh⟩ := fresh_world_name currentWorld
      have closed := body identity fresh
      have covered := (source.instantiation_closes_iff (Environment.empty.bind binder identity)).mp closed
      apply append_empty initializer
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨present, different⟩ := List.mem_filter.mp member
      obtain ⟨key, known⟩ := covered name present
      have unequal : name ≠ binder := by simpa using different
      simp [Environment.bind, Environment.empty, unequal] at known
  | nil => rfl
  | cons _ _ _ body rest => exact append_empty body rest

theorem typed_value_support {value : Code}
    (typed : Typed signature world environment ticket allowed value type) (isValue : value.IsValue) :
    resourceDependencies value.dependencies ⊆ type.resources := by
  cases typed with
  | unit | boolean | integer => exact List.nil_subset _
  | «variable» => cases isValue
  | reference issued => exact List.Subset.refl _
  | pair left right =>
      intro identity retained
      rcases List.mem_append.mp (by simpa only [Code.dependencies, ScopedExecution.resource_dependencies_append] using retained) with l | r
      · exact List.mem_append_left _ (typed_value_support left isValue.1 l)
      · exact List.mem_append_right _ (typed_value_support right isValue.2 r)
  | lambda body captured formed =>
      intro identity retained
      exact List.mem_append_right _ (captured (Typing.explicit_resource_in_support (Syntax.mem_resourceDependencies.mp retained)))
  | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
termination_by sizeOf value

theorem typed_return_excludes_resource {value : Code}
    (typed : Typed signature world environment ticket allowed value type)
    (isValue : value.IsValue) (noEscape : identity ∉ type.resources) :
    identity ∉ resourceDependencies value.dependencies :=
  fun retained => noEscape (typed_value_support typed isValue retained)

theorem typed_payload_at_boundary {operand : Code}
    (typed : Typed signature world environment ticket allowed operand input)
    (isValue : operand.IsValue) (boundary : input.resources ⊆ outside) :
    resourceDependencies operand.dependencies ⊆ outside :=
  List.Subset.trans (typed_value_support typed isValue) boundary

/-- Every actually fresh owner satisfies the binder premise; allocation is
    not restricted to one chosen numeral or one proof-specific fresh policy. -/
theorem resource_body_typed_at_fresh
    (typed : Typed signature (resourceWorld issued) environment ticket allowed
      (.resource binder initializer body) answer) (fresh : Owner.resource identity ∉ issued) :
    ∃ residual, Typed signature (resourceWorld (issued ++ [.resource identity])) environment ticket
        (.cell identity :: residual) (body.instantiate (Environment.empty.bind binder identity)) answer ∧
      identity ∉ answer.resources ∧ identity ∉ residual.flatMap Instance.resources ∧ residual ⊆ allowed := by
  have freshWorld : identity ∉ resourceWorld issued := fun member => fresh (mem_resource_world.mp member)
  cases typed with
  | resource initializer opened resultBound effectsBound effects =>
      refine ⟨_, ?_, fun member => freshWorld (resultBound member), fun member => freshWorld (effectsBound member), effects⟩
      rw [resource_world_append]
      exact opened identity freshWorld

/-- A typed resource entry with a returned integer has an actual fresh step
    and a typed instantiated body. Full configuration typing/support is not
    assumed or concluded here. -/
theorem typed_resource_entry_progress (binder : Nat) (payload : Int) (body : Code)
    (scope : ScopedExecution.Scope) (answer : Ty) (tail : ScopedExecution.Stack) (issued completed : List Owner)
    (typed : Typed signature (resourceWorld issued) environment ticket allowed (.resource binder (.integer payload) body) answer)
    (ledger : Ledger (ScopedExecution.RunState.erase
      ⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩)) :
    ∃ identity residual, Owner.resource identity ∉ issued ∧
      ScopedExecution.RunStep ⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩
        ⟨⟨body.instantiate (Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) tail⟩, issued ++ [.resource identity], completed⟩ ∧
      Typed signature (resourceWorld (issued ++ [.resource identity])) environment ticket (.cell identity :: residual)
        (body.instantiate (Environment.empty.bind binder identity)) answer ∧
      identity ∉ answer.resources ∧ identity ∉ residual.flatMap Instance.resources ∧ residual ⊆ allowed ∧
      Ledger (ScopedExecution.RunState.erase
        ⟨⟨body.instantiate (Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) tail⟩, issued ++ [.resource identity], completed⟩) := by
  obtain ⟨identity, fresh, step, closed, afterLedger⟩ := ScopedExecution.resource_entry_progress binder payload body scope answer tail
    issued completed (typed_resource_closed typed) ledger
  obtain ⟨residual, bodyTyped, noEscape, noEffectEscape, effects⟩ := resource_body_typed_at_fresh typed fresh
  exact ⟨identity, residual, fresh, step, bodyTyped, noEscape, noEffectEscape, effects, afterLedger⟩

/-- A context derives input/output ports from its retained syntax. -/
inductive ContextTyped (signature : Signature) : World → TypeEnv → TicketType → List Instance → ScopedExecution.Context → Ty → Ty → Prop where
  | pairLeft : Typed signature world environment ticket allowed right rightType →
      ContextTyped signature world environment ticket allowed (.pairLeft right) leftType (.product leftType rightType)
  | pairRight : Typed signature world environment ticket allowed left leftType →
      ContextTyped signature world environment ticket allowed (.pairRight left) rightType (.product leftType rightType)
  | appFunction : Typed signature world environment ticket allowed argument input → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.appFunction argument) (.function input output latent retained) output
  | appArgument : Typed signature world environment ticket allowed function (.function input output latent retained) → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.appArgument function) input output
  | bind : Typed signature world (environment.extend parameter input) ticket allowed suffix output →
      ContextTyped signature world environment ticket allowed (.bind parameter suffix) input output
  | branch : Typed signature world environment ticket allowed yes type → Typed signature world environment ticket allowed no type →
      ContextTyped signature world environment ticket allowed (.branch yes no) .boolean type
  | perform : signature effectInst operation = some (input, output) → effectInst ∈ allowed → InWorld world output →
      ContextTyped signature world environment ticket allowed (.perform (freezeEffect effectInst) operation) input output
  | resume : residual ⊆ allowed → InWorld world answer →
      ContextTyped signature world environment (.bound binder input answer residual closing) allowed (.resume binder) input answer
  | resource : (∀ identity, identity ∉ world →
        Typed signature (world ++ [identity]) environment ticket (.cell identity :: residual)
          (body.instantiate (Environment.empty.bind binder identity)) answer) →
      InWorld world answer → residual.flatMap Instance.resources ⊆ world → residual ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.resource binder body) .integer answer
  | cleanup : Typed signature world environment ticket allowed body answer → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.cleanup body) (.function .unit .unit latent retained) answer

theorem context_plug_typed (context : ContextTyped signature world environment ticket allowed frame input output)
    (child : Typed signature world environment ticket allowed expression input) :
    Typed signature world environment ticket allowed (frame.plug expression) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | appFunction argument effects => exact .app child argument effects
  | appArgument function effects => exact .app function child effects
  | bind suffix => exact .bind child suffix
  | branch yes no => exact .branch child yes no
  | perform operation available formed => exact .perform operation available child formed
  | resume effects formed => exact .resume child effects formed
  | resource body noEscape noEffectEscape effects => exact .resource child body noEscape noEffectEscape effects
  | cleanup body effects => exact .cleanup child body effects

theorem typed_focus_decomposition (focus : ScopedExecution.Focus whole child context)
    (typed : Typed signature world environment ticket allowed whole output) :
    ∃ input, Typed signature world environment ticket allowed child input ∧
      ContextTyped signature world environment ticket allowed context input output := by
  cases focus with
  | pairLeft notValue => cases typed with
      | pair left right => exact ⟨_, left, .pairLeft right⟩
  | pairRight isValue notValue => cases typed with
      | pair left right => exact ⟨_, right, .pairRight left⟩
  | appFunction notValue => cases typed with
      | app function argument effects => exact ⟨_, function, .appFunction argument effects⟩
  | appArgument isValue notValue => cases typed with
      | app function argument effects => exact ⟨_, argument, .appArgument function effects⟩
  | bind notValue => cases typed with
      | bind initializer suffix => exact ⟨_, initializer, .bind suffix⟩
  | branch notValue => cases typed with
      | branch condition yes no => exact ⟨_, condition, .branch yes no⟩
  | perform notValue => cases typed with
      | perform operation available operand formed => exact ⟨_, operand, .perform operation available formed⟩
  | resume notValue => cases typed with
      | resume operand effects formed => exact ⟨_, operand, .resume effects formed⟩
  | resource notValue => cases typed with
      | resource initializer body noEscape noEffectEscape effects => exact ⟨_, initializer, .resource body noEscape noEffectEscape effects⟩
  | cleanup notValue => cases typed with
      | cleanup action body effects => exact ⟨_, action, .cleanup body effects⟩


namespace TypingExamples

theorem resource_read_typed (world : World) (binder : Nat) (payload : Int) :
    Typed (Typing.withCellSignatures users) world environment ticket allowed
      (.resource binder (.integer payload) (ScopedExecution.Examples.readBody binder)) .integer := by
  refine .resource .integer (residual := []) ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro identity fresh
  rw [ScopedExecution.Examples.read_body_instantiates]
  exact .perform rfl List.mem_cons_self (.reference (List.mem_append_right _ List.mem_cons_self)) (List.nil_subset _)

theorem unit_resource_typed (world : World) (binder : Nat) :
    Typed signature world environment ticket allowed (.resource binder (.integer 0) .unit) .unit :=
  .resource .integer (residual := []) (fun _ _ => .unit) (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)

theorem repeated_function_template_typed (world : World) :
    Typed signature world environment ticket allowed ScopedExecution.Examples.function (.function .unit .unit [] []) :=
  .lambda (unit_resource_typed world 4) (List.nil_subset _) (List.nil_subset _)

/-- Initial typing and an actual terminating trace, without claiming that this
    pair of facts establishes type preservation along that trace. -/
theorem repeated_program_typed_and_executes :
    Typed signature [] environment .none [] ScopedExecution.Examples.program .unit ∧
      ScopedExecution.RunSteps ScopedExecution.Examples.initial ScopedExecution.Examples.terminal := by
  refine ⟨.bind (repeated_function_template_typed []) ?_, ScopedExecution.Examples.repeated_call_execution⟩
  refine .bind (.app (.variable rfl (List.nil_subset _)) .unit (List.nil_subset _)) ?_
  exact .app (.variable rfl (List.nil_subset _)) .unit (List.nil_subset _)

theorem resource_read_typed_entry :
    ∃ next allowed,
      ScopedExecution.RunStep
        ⟨⟨.resource 4 (.integer 17) (ScopedExecution.Examples.readBody 4), .none, .nil⟩, [], []⟩ next ∧
      Typed (Typing.withCellSignatures users) (resourceWorld next.issued) environment .none allowed
        next.configuration.expression .integer ∧ Ledger next.erase := by
  obtain ⟨identity, residual, fresh, step, bodyTyped, noEscape, noEffectEscape, effects, ledger⟩ :=
    typed_resource_entry_progress 4 17 (ScopedExecution.Examples.readBody 4) .none .integer .nil [] []
      (resource_read_typed (users := users) (environment := environment) (ticket := .none) (allowed := []) [] 4 17)
      ⟨.refl _, by decide⟩
  exact ⟨_, .cell identity :: residual, step, bodyTyped, ledger⟩

theorem fresh_reference_escape_rejected :
    ¬ Typed signature world environment ticket allowed (.resource binder (.integer 0) (.resourceRef (.bound binder))) answer := by
  intro typed
  cases typed with
  | resource initializer body resultBound effectsBound effects =>
      obtain ⟨identity, fresh⟩ := fresh_world_name world
      have opened := body identity fresh
      simp only [Code.instantiate, ResourceName.instantiate, Environment.bind] at opened
      cases opened with
      | reference issued => exact fresh (resultBound List.mem_cons_self)

theorem unresolved_reference_not_typed :
    ¬ Typed signature world environment ticket allowed (.resourceRef (.bound binder)) type := by
  intro typed
  cases typed

/-- A historical name may be formed while its resource is no longer live. -/
theorem typing_world_does_not_grant_live_access :
    Typed signature [4] environment ticket allowed (.resourceRef (.activation 4)) (.reference 4) ∧
      ¬ ScopedExecution.AccessValid ⟨.resourceRef (.activation 4), .none, .nil⟩ [] := by
  refine ⟨.reference List.mem_cons_self, ?_⟩
  intro access
  have impossible : (4 : Nat) ∈ ([] : List Nat) := access.expression List.mem_cons_self
  cases impossible

end TypingExamples

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.typed_result_in_world
#print axioms Ash.OneShot.ScopedTyping.typed_world_weaken
#print axioms Ash.OneShot.ScopedTyping.typed_resource_closed
#print axioms Ash.OneShot.ScopedTyping.typed_value_support
#print axioms Ash.OneShot.ScopedTyping.typed_return_excludes_resource
#print axioms Ash.OneShot.ScopedTyping.typed_payload_at_boundary
#print axioms Ash.OneShot.ScopedTyping.resource_body_typed_at_fresh
#print axioms Ash.OneShot.ScopedTyping.typed_resource_entry_progress
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.resource_read_typed
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.repeated_function_template_typed
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.repeated_program_typed_and_executes
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.resource_read_typed_entry
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.fresh_reference_escape_rejected
#print axioms Ash.OneShot.ScopedTyping.TypingExamples.typing_world_does_not_grant_live_access

#print axioms Ash.OneShot.ScopedTyping.context_plug_typed
#print axioms Ash.OneShot.ScopedTyping.typed_focus_decomposition
