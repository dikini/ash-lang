import NetworkLedgerCoreInsert

/- Ordered insertion for located nominal entries, including output envelopes.
This strengthens the existing finite list proof without assuming Child payloads.
The linked definition and actual caller premises remain separate obligations. -/
namespace Ash.NetworkLedger.CoreGenericInsert

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreInsert

/-- Every admitted list element is a complete stored value. -/
def LocatedEntries (entries : List Value) : Prop :=
  ∀ entry ∈ entries, ∃ address, entry = .location address

/-- Every normal execution appends the exact new entry to the represented finite list. -/
theorem insertion_body_located (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (captureValues : List Value) (captureEnv : Environment) (selfAddress selfResolved : Nat)
    (newEntry : Value) (newAddress : Nat) (newLocation : newEntry = .location newAddress)
    (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [newEntry, list] →
      BoundedLocations start → Children c start list entries → LocatedEntries entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      InsertOutcome c start finish result (entries ++ [newEntry]) := by
  induction entries with
  | nil =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded listRep keys
      selfResolution selfCell evaluation
    have listEval := insertion_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      newEntry list result newAddress newLocation payloadResolution payloadCell evaluation
    have scope := insertion_environment_bindings c program checked captureEnv.reverse (.location payload) newEntry list
      .unit .unit (.location selfAddress) selfBinding
    cases listRep with
    | empty address resolved resolution cell =>
      have emptyEval := empty_match_executes_first program start finish _ checked.listBody checked.listScrutinee
        checked.listName c.empty c.more checked.emptyBody checked.moreBody (.tuple [.binder checked.entryName, .binder checked.tailName])
        address resolved result checked.listShape checked.listVariableShape scope.1 resolution cell listEval
      simpa using insertion_empty_outcome c program checked _ start finish result newEntry scope.2.1 bounded emptyEval
  | cons entry entries ih =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded listRep keys
      selfResolution selfCell evaluation
    have listEval := insertion_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      newEntry list result newAddress newLocation payloadResolution payloadCell evaluation
    obtain ⟨entryAddress, entryEq⟩ := keys entry (by simp)
    subst entry
    cases listRep with
    | more listAddress listResolved listPayload listTuple _ tail _ listResolution listCell listPayloadResolution listFields tailRep =>
      have scope := insertion_environment_bindings c program checked captureEnv.reverse (.location payload) newEntry (.location listAddress)
        (.location entryAddress) tail (.location selfAddress) selfBinding
      have moreEval := more_match_executes_second program start finish _ checked.listBody checked.listScrutinee
        checked.listName c.empty c.more checked.emptyBody checked.moreBody checked.entryName checked.tailName
        listAddress listResolved listPayload listTuple entryAddress tail result checked.listShape checked.listVariableShape
        scope.1 listResolution listCell listPayloadResolution listFields listEval
      have tailKeys : LocatedEntries entries := by
        intro other member
        exact keys other (by simp [member])
      have tailIH : ∀ afterArgument recursiveFinish recPayload recursiveResult,
        Resolve afterArgument recPayload recPayload → readCell afterArgument recPayload = some [newEntry, tail] →
        BoundedLocations afterArgument → Children c afterArgument tail entries →
        afterArgument.aliases = start.aliases →
        (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
        Eval program (extend captureEnv.reverse checked.parameter (.location recPayload)) checked.body
          afterArgument recursiveResult recursiveFinish →
        InsertOutcome c afterArgument recursiveFinish recursiveResult (entries ++ [newEntry]) := by
        intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recTail
          recAliases recRetained recEval
        have recKeys := tailKeys
        exact ih afterArgument recursiveFinish recPayload recPayload tail recursiveResult recResolution recCell recBound
          recTail recKeys (resolve_preserved recAliases recRetained selfResolution)
          (recRetained selfResolved _ selfCell) recEval
      simpa using insertion_more_outcome c program checked _ start finish result (.location entryAddress) newEntry tail entries
        selfAddress selfResolved captureValues captureEnv scope.2.2.2.1 scope.2.2.1 scope.2.2.2.2.1 scope.2.2.2.2.2
        selfResolution selfCell captureBindings bounded tailRep tailIH moreEval

end Ash.NetworkLedger.CoreGenericInsert
