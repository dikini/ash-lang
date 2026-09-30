import SourceDependencyScopes

/-! Proof-independent handler requirements on existing source scopes. The
checker needs no runtime stack, handler registry or clause proof. Its connection
to declaration recipes is established in SourceContextualHintChecking. -/
namespace Ash.OneShot.SourceContextualHints
open ScopedExpressions
open SourceDependencyCapture
abbrev Receiving := SourceDependencyCapture.Scope
abbrev Requirement := Instance × Nat

def checkCapability (tail : Receiving) (effect : Instance) (operation : Nat) : Bool :=
  match select effect operation tail with
  | none => false
  | some (.builtin _) => true
  | some (.handler _ _ contract modes) =>
      !contract.dispose && (contract.row false).isSome && (contract.row true).isSome &&
        (modeDependencies false modes).isSome && (modeDependencies true modes).isSome

def checkRequirements (tail : Receiving) (required : List Requirement) : Bool :=
  required.all (fun request => checkCapability tail request.1 request.2)

/-- The index retains the existing scope, including owner names, declaration
tables, dependency families and dormant captures. Only handler requirements
are added. These annotations do not introduce another computation syntax. -/
inductive Hints : Receiving → Type where
  | nil : Hints .nil
  | plain : Hints rest → Hints (.plain dependencies rest)
  | handler : List Requirement → Hints rest → Hints (.handler effect table families rest)
  | cell : Hints rest → Hints (.cell identity rest)
  | cleanup : Hints rest → Hints (.cleanup needs callback rest)
  | running : Hints rest → Hints (.running rest)
  | live : Hints captured → Hints rest → Hints (.live owner captured rest)
  | spent : Hints rest → Hints (.spent owner rest)

def Hints.append : Hints first → Hints second → Hints (first.append second)
  | .nil, tail => tail
  | .plain rest, tail => .plain (rest.append tail)
  | .handler required rest, tail => .handler required (rest.append tail)
  | .cell rest, tail => .cell (rest.append tail)
  | .cleanup rest, tail => .cleanup (rest.append tail)
  | .running rest, tail => .running (rest.append tail)
  | .live saved rest, tail => .live saved (rest.append tail)
  | .spent rest, tail => .spent (rest.append tail)

def Hints.check : {scope : Receiving} → Hints scope → Receiving → Bool
  | _, .nil, _ => true
  | _, .plain rest, outside | _, .cell rest, outside | _, .cleanup rest, outside
  | _, .running rest, outside | _, .spent rest, outside => rest.check outside
  | .handler _ _ _ restScope, .handler required rest, outside =>
      checkRequirements (restScope.append outside) required && rest.check outside
  | .live _ _ restScope, .live saved rest, outside =>
      saved.check (restScope.append outside) && rest.check outside

/-- This test examines the actual restored source scope. The caller remains
between the saved scope and the spent boundary; requirements are not checked
against the former receiving context. -/
def checkResume (saved : Hints captured) (waiting : Hints front)
    (tail : Hints rest) (owner : Nat) (outside : Receiving) : Bool :=
  (saved.append (waiting.append (.spent (owner := owner) tail))).check outside

def checkDispose (scheduled : Hints closing) (waiting : Hints front)
    (tail : Hints rest) (owner : Nat) (outside : Receiving) : Bool :=
  (scheduled.append (.running (waiting.append (.spent (owner := owner) tail)))).check outside

end Ash.OneShot.SourceContextualHints
