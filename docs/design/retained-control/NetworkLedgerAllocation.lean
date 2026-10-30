import Std

/-
An isolated allocation/control fragment. The actual Effect Core provider and
continuation correspondence is a separate obligation; this model does not
establish that the interpreter is selected in any linked program.
-/
namespace Ash.NetworkLedger.Allocation

inductive Selection where
  | hostDefault | intercepted | localProvider | unknown
  deriving DecidableEq, Repr

structure State where
  protocolVersion : Nat
  nextLocation : Nat
  continuationResumes : Nat
  deriving DecidableEq, Repr

inductive Result where
  | refused
  | returned (location : Nat) (state : State)
  deriving DecidableEq, Repr

def admitted (selection : Selection) : Bool := selection == .hostDefault

def execute (selection : Selection) (s : State) (available : Bool) : Result :=
  if !available then .refused
  else
    match selection with
    | .hostDefault => .returned s.nextLocation
        { s with nextLocation := s.nextLocation + 1
                 continuationResumes := s.continuationResumes + 1 }
    | .intercepted | .localProvider | .unknown =>
        .returned s.nextLocation { s with protocolVersion := s.protocolVersion + 1 }

theorem admitted_selection (selection : Selection) (checked : admitted selection = true) :
    selection = .hostDefault := by
  cases selection <;> simp_all [admitted]

theorem accepted_success (selection : Selection) (s : State) (available : Bool)
    (location : Nat) (out : State) (checked : admitted selection = true)
    (result : execute selection s available = .returned location out) :
    location = s.nextLocation ∧ out.nextLocation = s.nextLocation + 1 ∧
      out.protocolVersion = s.protocolVersion ∧
      out.continuationResumes = s.continuationResumes + 1 := by
  have selectionEq := admitted_selection selection checked
  subst selection
  cases available with
  | false => simp [execute] at result
  | true =>
    simp only [execute, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Result.returned.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem refusal_has_no_normal_return (selection : Selection) (s : State) :
    execute selection s false = .refused := by
  simp [execute]

theorem unsupported_selections_reject :
    admitted .intercepted = false ∧ admitted .localProvider = false ∧ admitted .unknown = false := by
  decide

inductive Increment where
  | canonical | reset
  deriving DecidableEq, Repr

def checkIncrement (op : Increment) : Bool := decide (op = .canonical)

def evalIncrement (op : Increment) (selection : Selection) (s : State) (available : Bool)
    (n : Int) : Option (Int × State) :=
  match execute selection s available with
  | .refused => none
  | .returned _ next => some (match op with | .canonical => n + 1 | .reset => 0, next)

theorem checked_increment_sound (op : Increment) (selection : Selection) (s : State)
    (available : Bool) (n value : Int) (out : State) (opChecked : checkIncrement op = true)
    (selected : admitted selection = true)
    (returns : evalIncrement op selection s available n = some (value, out)) :
    value = n + 1 ∧ n < value ∧ out.protocolVersion = s.protocolVersion ∧
      out.continuationResumes = s.continuationResumes + 1 := by
  have opEq : op = .canonical := by simpa [checkIncrement] using opChecked
  have selEq := admitted_selection selection selected
  subst op
  subst selection
  cases available with
  | false => simp [evalIncrement, execute] at returns
  | true =>
    simp only [evalIncrement, execute, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at returns
    rcases returns with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, rfl, rfl⟩
    omega

end Ash.NetworkLedger.Allocation
