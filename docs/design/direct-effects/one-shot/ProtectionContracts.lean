import ProtectionContexts

/-!
Finite protection requirements for callable and clause contracts. This checks
supplied outward summaries at invocation, against the current ordered context.
Deriving these summaries from Code, including resumption phases and substitution,
is a separate source-admission obligation. The runtime grammar is unchanged.
-/

namespace Ash.OneShot.ProtectionContracts

structure Demand where
  effect : Instance
  operation : Nat
  /-- Protection introduced before any interpretation in the receiving context.
      This is not ambient protection remembered from function creation. -/
  held : Bool
  deriving DecidableEq, Repr

abbrev Footprint := List Demand

structure ClauseContract where
  dispose : Bool
  unprotectedRow : Option Footprint
  protectedRow : Option Footprint
  deriving DecidableEq, Repr

def ClauseContract.row (contract : ClauseContract) (held : Bool) : Option Footprint :=
  if held then contract.protectedRow else contract.unprotectedRow

def modeCheck (dispose held : Bool) : Bool := !held || !dispose

theorem mode_check_iff : modeCheck dispose held = true ↔ ProtectionContexts.SupportsMode dispose held := by
  cases dispose <;> cases held <;> simp [modeCheck, ProtectionContexts.SupportsMode]

def lookup (operation : Nat) : List (Nat × ClauseContract) → Option ClauseContract
  | [] => none
  | (key, contract) :: rest => if operation = key then some contract else lookup operation rest

inductive Layer where
  | barrier : Bool → Layer
  | builtin : Nat → Layer
  | handler : Instance → Nat → List (Nat × ClauseContract) → Layer
  deriving DecidableEq, Repr

abbrev Context := List Layer

def erase : Context → ProtectionContexts.Context
  | [] => []
  | .barrier held :: rest => .barrier held :: erase rest
  | .builtin identity :: rest => .interpretation (.cell identity) (.builtin identity) :: erase rest
  | .handler effect activation _ :: rest => .interpretation effect (.source activation) :: erase rest

/-- Selected clause requirements run outside that handler. Its mode row must
    already account for the live captured ticket while the clause owns it. -/
def checkRequest : Context → Demand → Bool
  | [], _ => false
  | .barrier held :: rest, request => checkRequest rest { request with held := request.held || held }
  | .builtin identity :: rest, request =>
      if request.effect = .cell identity then true else checkRequest rest request
  | .handler effect _ clauses :: rest, request =>
      if request.effect = effect then
        match lookup request.operation clauses with
        | none => false
        | some contract =>
            if modeCheck contract.dispose request.held then
              match contract.row request.held with
              | none => false
              | some footprint => footprint.all (checkRequest rest)
            else false
      else checkRequest rest request

def checkFootprint (context : Context) (footprint : Footprint) : Bool := footprint.all (checkRequest context)

inductive Admitted : Context → Demand → Prop where
  | barrier (next : Admitted rest { request with held := request.held || held }) :
      Admitted (.barrier held :: rest) request
  | builtin_hit (same : request.effect = .cell identity) : Admitted (.builtin identity :: rest) request
  | builtin_miss (different : request.effect ≠ .cell identity) (next : Admitted rest request) :
      Admitted (.builtin identity :: rest) request
  | handler_hit (same : request.effect = effect)
      (known : lookup request.operation clauses = some contract)
      (supported : ProtectionContexts.SupportsMode contract.dispose request.held)
      (row : contract.row request.held = some footprint)
      (body : ∀ next ∈ footprint, Admitted rest next) :
      Admitted (.handler effect activation clauses :: rest) request
  | handler_miss (different : request.effect ≠ effect) (next : Admitted rest request) :
      Admitted (.handler effect activation clauses :: rest) request

theorem check_request_sound (context : Context) (checked : checkRequest context request = true) :
    Admitted context request := by
  induction context generalizing request with
  | nil => cases checked
  | cons layer rest ih => cases layer with
      | barrier held => exact .barrier (ih checked)
      | builtin identity =>
          by_cases same : request.effect = .cell identity
          · exact .builtin_hit same
          · exact .builtin_miss same (ih (by simpa [checkRequest, same] using checked))
      | handler effect activation clauses =>
          by_cases same : request.effect = effect
          · cases known : lookup request.operation clauses with
            | none => simp [checkRequest, same, known] at checked
            | some contract =>
                by_cases permitted : modeCheck contract.dispose request.held = true
                · cases row : contract.row request.held with
                  | none => simp [checkRequest, same, known, permitted, row] at checked
                  | some footprint =>
                      have body : ∀ next ∈ footprint, checkRequest rest next = true := by
                        simpa [checkRequest, same, known, permitted, row] using checked
                      exact .handler_hit same known (mode_check_iff.mp permitted) row
                        (fun next member => ih (body next member))
                · simp [checkRequest, same, known, permitted] at checked
          · exact .handler_miss same (ih (by simpa [checkRequest, same] using checked))

theorem check_request_complete (admitted : Admitted context request) : checkRequest context request = true := by
  induction admitted with
  | barrier next ih => exact ih
  | builtin_hit same => simp [checkRequest, same]
  | builtin_miss different next ih | handler_miss different next ih => simp [checkRequest, different, ih]
  | handler_hit same known supported row body ih =>
      simpa [checkRequest, same, known, mode_check_iff.mpr supported, row] using ih

theorem check_request_iff : checkRequest context request = true ↔ Admitted context request :=
  ⟨check_request_sound context, check_request_complete⟩

theorem check_footprint_iff : checkFootprint context footprint = true ↔
    ∀ request ∈ footprint, Admitted context request := by
  simp only [checkFootprint, List.all_eq_true, check_request_iff]

/-- Sequencing requirements is finite conjunction, with no change to the
    expression sequencing syntax or a computation-model conversion. -/
theorem check_footprint_append : checkFootprint context (front ++ tail) =
    (checkFootprint context front && checkFootprint context tail) := by
  simp [checkFootprint]

def qualify (held : Bool) (footprint : Footprint) : Footprint :=
  footprint.map fun request => { request with held := request.held || held }

theorem check_qualified : checkFootprint context (qualify held footprint) =
    checkFootprint (.barrier held :: context) footprint := by
  simp [checkFootprint, qualify, checkRequest, Function.comp_def]

theorem qualify_composes : qualify right (qualify left footprint) = qualify (left || right) footprint := by
  simp [qualify, List.map_map, Function.comp_def, Bool.or_assoc]

theorem checked_footprint_subset (checked : checkFootprint context larger = true)
    (included : smaller ⊆ larger) : checkFootprint context smaller = true :=
  check_footprint_iff.mpr (fun request member => check_footprint_iff.mp checked request (included member))

/-- A selected contract is tied to the first matching interpretation occurrence
    and actual operation lookup, independently of its admission derivation. -/
inductive Selected : Context → Demand → Nat → ClauseContract → Bool → Prop where
  | hit (same : request.effect = effect) (known : lookup request.operation clauses = some contract) :
      Selected (.handler effect activation clauses :: rest) request activation contract request.held
  | handler (different : request.effect ≠ effect) (next : Selected rest request activation contract mode) :
      Selected (.handler effect other clauses :: rest) request activation contract mode
  | builtin (different : request.effect ≠ .cell identity) (next : Selected rest request activation contract mode) :
      Selected (.builtin identity :: rest) request activation contract mode
  | barrier (next : Selected rest { request with held := request.held || held } activation contract mode) :
      Selected (.barrier held :: rest) request activation contract mode

theorem selected_target (selected : Selected context request activation contract mode) :
    ProtectionContexts.select request.effect (erase context) request.held = some (.source activation, mode) := by
  induction selected with
  | hit same known => simp [erase, ProtectionContexts.select, same]
  | handler different next ih | builtin different next ih => simp [erase, ProtectionContexts.select, different, ih]
  | barrier next ih => exact ih

theorem admitted_source_contract (admitted : Admitted context request)
    (selected : ProtectionContexts.select request.effect (erase context) request.held = some (.source activation, mode)) :
    ∃ contract, Selected context request activation contract mode ∧
      ProtectionContexts.SupportsMode contract.dispose mode := by
  induction admitted with
  | barrier next ih =>
      obtain ⟨contract, found, supported⟩ := ih selected
      exact ⟨contract, .barrier found, supported⟩
  | builtin_hit same => simp [erase, ProtectionContexts.select, same] at selected
  | builtin_miss different next ih =>
      obtain ⟨contract, found, supported⟩ := ih (by simpa [erase, ProtectionContexts.select, different] using selected)
      exact ⟨contract, .builtin different found, supported⟩
  | handler_miss different next ih =>
      obtain ⟨contract, found, supported⟩ := ih (by simpa [erase, ProtectionContexts.select, different] using selected)
      exact ⟨contract, .handler different found, supported⟩
  | handler_hit same known supported row body ih =>
      simp only [erase, ProtectionContexts.select, same, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq, Target.source.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact ⟨_, .hit same known, supported⟩

/-- The bridge to a real scoped cut. Source checking must separately certify
    that the current request belongs to a checked footprint and that handler
    summaries describe the selected source clauses. -/
theorem checked_capture_contract
    (cut : ScopedExecution.HandlerCut requested whole capture tail handler)
    (realizes : erase context = ProtectionContexts.contextOf whole.erase)
    (checked : checkRequest context ⟨requested, operation, false⟩ = true)
    (held : capture.erase.protected ≠ []) :
    ∃ contract, Selected context ⟨requested, operation, false⟩ handler.activation contract true ∧
      contract.dispose = false := by
  have selection := ProtectionContexts.scoped_cut_mode cut false
  rw [← realizes] at selection
  simp only [Bool.false_or, ProtectionContexts.protected_mode_iff.mpr held] at selection
  obtain ⟨contract, found, supported⟩ := admitted_source_contract (check_request_iff.mp checked) selection
  exact ⟨contract, found, supported rfl⟩

namespace Examples

def effectE : Instance := .user 0 []
def effectF : Instance := .user 1 []
def latentCall : Footprint := [⟨effectE, 0, false⟩]
def disposeClause : ClauseContract := ⟨true, some [], none⟩
def forwardClause : ClauseContract :=
  ⟨false, some [⟨effectF, 0, false⟩], some [⟨effectF, 0, true⟩]⟩
def afterCompletionClause : ClauseContract :=
  ⟨false, some [⟨effectF, 0, false⟩], some [⟨effectF, 0, false⟩]⟩

/-- These are supplied summaries. The phase distinction must subsequently be
    justified by source derivations, not inferred from these Boolean examples. -/
theorem normal_forwarding_accepted : checkFootprint
    [.handler effectE 11 [(0, forwardClause)], .handler effectF 22 [(0, disposeClause)]] latentCall = true := by decide

theorem protected_forwarding_rejected : checkFootprint
    [.barrier true, .handler effectE 11 [(0, forwardClause)], .handler effectF 22 [(0, disposeClause)]]
    latentCall = false := by decide

theorem inner_disposal_accepted : checkFootprint
    [.handler effectE 11 [(0, disposeClause)], .barrier true] latentCall = true := by decide

theorem after_completion_summary_accepted : checkFootprint
    [.barrier true, .handler effectE 11 [(0, afterCompletionClause)], .handler effectF 22 [(0, disposeClause)]]
    latentCall = true := by decide

theorem surviving_outer_protection_rejected : checkFootprint
    [.barrier true, .handler effectE 11 [(0, afterCompletionClause)], .barrier true,
      .handler effectF 22 [(0, disposeClause)]] latentCall = false := by decide

theorem creation_context_cannot_authorize_invocation :
    checkFootprint [.handler effectE 11 [(0, disposeClause)]] latentCall = true ∧
    checkFootprint [.barrier true, .handler effectE 11 [(0, disposeClause)]] latentCall = false := by decide

theorem missing_operation_rejected : checkFootprint
    [.handler effectE 11 [(1, disposeClause)]] latentCall = false := by decide

/-- Supplied mode tables need not be monotone. A true-mode demand must not
    silently replace a distinct false-mode demand in a footprint. -/
theorem modes_cannot_be_collapsed :
    checkFootprint [.handler effectE 11 [(0, ⟨false, none, some []⟩)]] [⟨effectE, 0, true⟩] = true ∧
    checkFootprint [.handler effectE 11 [(0, ⟨false, none, some []⟩)]] latentCall = false := by decide

end Examples

end Ash.OneShot.ProtectionContracts

#print axioms Ash.OneShot.ProtectionContracts.mode_check_iff
#print axioms Ash.OneShot.ProtectionContracts.check_request_sound
#print axioms Ash.OneShot.ProtectionContracts.check_request_complete
#print axioms Ash.OneShot.ProtectionContracts.check_request_iff
#print axioms Ash.OneShot.ProtectionContracts.check_footprint_iff
#print axioms Ash.OneShot.ProtectionContracts.check_footprint_append
#print axioms Ash.OneShot.ProtectionContracts.check_qualified
#print axioms Ash.OneShot.ProtectionContracts.qualify_composes
#print axioms Ash.OneShot.ProtectionContracts.checked_footprint_subset
#print axioms Ash.OneShot.ProtectionContracts.selected_target
#print axioms Ash.OneShot.ProtectionContracts.admitted_source_contract
#print axioms Ash.OneShot.ProtectionContracts.checked_capture_contract
#print axioms Ash.OneShot.ProtectionContracts.Examples.normal_forwarding_accepted
#print axioms Ash.OneShot.ProtectionContracts.Examples.protected_forwarding_rejected
#print axioms Ash.OneShot.ProtectionContracts.Examples.inner_disposal_accepted
#print axioms Ash.OneShot.ProtectionContracts.Examples.after_completion_summary_accepted
#print axioms Ash.OneShot.ProtectionContracts.Examples.surviving_outer_protection_rejected
#print axioms Ash.OneShot.ProtectionContracts.Examples.creation_context_cannot_authorize_invocation
#print axioms Ash.OneShot.ProtectionContracts.Examples.missing_operation_rejected
#print axioms Ash.OneShot.ProtectionContracts.Examples.modes_cannot_be_collapsed
