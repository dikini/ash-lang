import CoreSyntax

/-! Static decoration of the finite supported Core type fragment. Core's exact
function request rows are retained unchanged. Callable retention, which Core
function metadata omits, is supplied separately as finite structural data.

Successful decoration does not authenticate that data against captured values,
type a Core expression or prove admission. Resource realization is exclusively
the existing Instantiation relation. -/
namespace Ash.OneShot.CoreTypeSupport
open Instantiation

abbrev SourceType := CoreSyntax.ValueType
abbrev PortType := Instantiation.ValueType

/-- One finite annotation mirrors the type tree, with retention data only at
function nodes. It contains no execution, authority or future-invariant proof. -/
inductive SupportShape where
  | unit | boolean | integer | reference
  | product : SupportShape → SupportShape → SupportShape
  | function : SupportShape → SupportShape → List ResourceName → SupportShape
  deriving DecidableEq, Repr

inductive DecorationError where
  | unsupportedSource : CoreSyntax.UnsupportedType → DecorationError
  | shapeMismatch
  deriving DecidableEq, Repr

/-- Copy structural type metadata and exact request rows; add only supplied
retention. Unsupported source types and annotation-shape mismatches reject. -/
def decorate : SourceType → SupportShape → Except DecorationError PortType
  | .unit, .unit => .ok .unit
  | .boolean, .boolean => .ok .boolean
  | .integer, .integer => .ok .integer
  | .reference name, .reference => .ok (.reference name)
  | .product left right, .product leftSupport rightSupport => do
      let decoratedLeft ← decorate left leftSupport
      let decoratedRight ← decorate right rightSupport
      pure (.product decoratedLeft decoratedRight)
  | .function input output requests, .function inputSupport outputSupport retained => do
      let decoratedInput ← decorate input inputSupport
      let decoratedOutput ← decorate output outputSupport
      pure (.function decoratedInput decoratedOutput requests retained)
  | .unsupported kind, _ => .error (.unsupportedSource kind)
  | _, _ => .error .shapeMismatch

/-- Erasure exposes exact structural and request-row preservation; it erases
only the newly supplied callable-retention lists. -/
def erase : PortType → SourceType
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference name => .reference name
  | .product left right => .product (erase left) (erase right)
  | .function input output requests _ => .function (erase input) (erase output) requests

/-- Recover precisely the supplied annotation tree from decorated metadata. -/
def supportOf : PortType → SupportShape
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference _ => .reference
  | .product left right => .product (supportOf left) (supportOf right)
  | .function input output _ retained => .function (supportOf input) (supportOf output) retained

inductive Decorates : SourceType → SupportShape → PortType → Prop where
  | unit : Decorates .unit .unit .unit
  | boolean : Decorates .boolean .boolean .boolean
  | integer : Decorates .integer .integer .integer
  | reference : Decorates (.reference name) .reference (.reference name)
  | product (left : Decorates sourceLeft leftSupport decoratedLeft)
      (right : Decorates sourceRight rightSupport decoratedRight) :
      Decorates (.product sourceLeft sourceRight) (.product leftSupport rightSupport)
        (.product decoratedLeft decoratedRight)
  | function (input : Decorates sourceInput inputSupport decoratedInput)
      (output : Decorates sourceOutput outputSupport decoratedOutput) :
      Decorates (.function sourceInput sourceOutput requests)
        (.function inputSupport outputSupport retained)
        (.function decoratedInput decoratedOutput requests retained)

private theorem bind_ok {α β : Type} (a : Except DecorationError α)
    (f : α → Except DecorationError β) (value : β) (success : a.bind f = .ok value) :
    ∃ item, a = .ok item ∧ f item = .ok value := by
  cases h : a with
  | error e => simp [h, Except.bind] at success
  | ok item => exact ⟨item, rfl, by simpa [h, Except.bind] using success⟩

/-- Executable success yields the exact structural decoration derivation. -/
theorem decorate_sound (source : SourceType) (support : SupportShape) (decorated : PortType)
    (success : decorate source support = .ok decorated) : Decorates source support decorated := by
  induction source generalizing support decorated with
  | unit => cases support <;> simp [decorate] at success; cases success; exact .unit
  | boolean => cases support <;> simp [decorate] at success; cases success; exact .boolean
  | integer => cases support <;> simp [decorate] at success; cases success; exact .integer
  | reference name => cases support <;> simp [decorate] at success; cases success; exact .reference
  | unsupported kind => simp [decorate] at success
  | product left right ihLeft ihRight =>
      cases support <;> try simp [decorate] at success
      case product leftSupport rightSupport =>
        obtain ⟨a, ha, rest⟩ := bind_ok _ _ _ success
        obtain ⟨b, hb, result⟩ := bind_ok _ _ _ rest
        have same : Instantiation.ValueType.product a b = decorated := by simpa using result
        subst decorated
        exact .product (ihLeft _ _ ha) (ihRight _ _ hb)
  | function input output requests ihInput ihOutput =>
      cases support <;> try simp [decorate] at success
      case function inputSupport outputSupport retained =>
        obtain ⟨a, ha, rest⟩ := bind_ok _ _ _ success
        obtain ⟨b, hb, result⟩ := bind_ok _ _ _ rest
        have same : Instantiation.ValueType.function a b requests retained = decorated := by simpa using result
        subst decorated
        exact .function (ihInput _ _ ha) (ihOutput _ _ hb)

theorem Decorates.executable (related : Decorates source support decorated) :
    decorate source support = .ok decorated := by
  induction related with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp only [decorate, ihLeft, ihRight]; rfl
  | function input output ihInput ihOutput => simp only [decorate, ihInput, ihOutput]; rfl

theorem decorate_iff : decorate source support = .ok decorated ↔ Decorates source support decorated :=
  ⟨decorate_sound source support decorated, Decorates.executable⟩

theorem Decorates.erases (related : Decorates source support decorated) : erase decorated = source := by
  induction related with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp [erase, ihLeft, ihRight]
  | function input output ihInput ihOutput => simp [erase, ihInput, ihOutput]

/-- Successful decoration preserves every scalar/product/reference/function
node and every exact function request row, including nested function ports. -/
theorem successful_erasure (success : decorate source support = .ok decorated) :
    erase decorated = source := (decorate_sound _ _ _ success).erases

theorem Decorates.supported (related : Decorates source support decorated) :
    source.supported = true := by
  induction related with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp [CoreSyntax.ValueType.supported, ihLeft, ihRight]
  | function input output ihInput ihOutput => simp [CoreSyntax.ValueType.supported, ihInput, ihOutput]

theorem Decorates.support_exact (related : Decorates source support decorated) :
    supportOf decorated = support := by
  induction related with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp [supportOf, ihLeft, ihRight]
  | function input output ihInput ihOutput => simp [supportOf, ihInput, ihOutput]

/-- Both preserved Core metadata and all supplied retention are recovered
exactly. The supplied lists are not inferred, enlarged or deduplicated. -/
theorem successful_preservation (success : decorate source support = .ok decorated) :
    erase decorated = source ∧ supportOf decorated = support ∧ source.supported = true := by
  have related := decorate_sound _ _ _ success
  exact ⟨related.erases, related.support_exact, related.supported⟩

theorem unsupported_rejected (unsupported : source.supported = false) :
    decorate source support ≠ .ok decorated := by
  intro success
  have supported := (decorate_sound _ _ _ success).supported
  rw [unsupported] at supported
  cases supported

/-- At a function node, request rows come exactly from Core and retained
support comes exactly from the separate annotation, with no added requests. -/
theorem function_decoration
    (success : decorate (.function input output requests)
      (.function inputSupport outputSupport retained) = .ok decorated) :
    ∃ decoratedInput decoratedOutput,
      decorated = .function decoratedInput decoratedOutput requests retained ∧
      decorate input inputSupport = .ok decoratedInput ∧
      decorate output outputSupport = .ok decoratedOutput := by
  cases decorate_sound _ _ _ success with
  | function input output => exact ⟨_, _, rfl, input.executable, output.executable⟩

/-- Derived packaging of static output with the existing lexical realization
judgment. This is not a Core expression typing derivation. -/
def RealizedDecoration (environment : Instantiation.Environment)
    (source : SourceType) (support : SupportShape) (target : Ash.OneShot.Ty) : Prop :=
  ∃ decorated, decorate source support = .ok decorated ∧ TypeRealizes environment decorated target

/-- Existing finite lexical lookup obligations suffice for a realized output;
this grants neither liveness nor authority over the realized resources. -/
theorem realization_exists (success : decorate source support = .ok decorated)
    (bound : NamesBound environment decorated.resources) :
    ∃ target, RealizedDecoration environment source support target := by
  obtain ⟨target, realized⟩ := type_realization_exists decorated bound
  exact ⟨target, decorated, success, realized⟩

/-- Resource support at references, nested ports, requests and retention is
transported by the existing generic type/resource realization theorem. -/
theorem realized_resources (related : RealizedDecoration environment source support target) :
    ∃ decorated, decorate source support = .ok decorated ∧
      ListRealizes (NameRealizes environment) decorated.resources target.resources := by
  obtain ⟨decorated, success, realized⟩ := related
  exact ⟨decorated, success, type_resources_realize realized⟩

/-- Realized function ports, exact requests and retention remain separately
visible in the existing relation. -/
theorem realized_function
    (related : RealizedDecoration environment (.function input output requests)
      (.function inputSupport outputSupport retained) target) :
    ∃ decoratedInput decoratedOutput actualInput actualOutput actualRequests actualRetained,
      target = .function actualInput actualOutput actualRequests actualRetained ∧
      decorate input inputSupport = .ok decoratedInput ∧
      decorate output outputSupport = .ok decoratedOutput ∧
      TypeRealizes environment decoratedInput actualInput ∧
      TypeRealizes environment decoratedOutput actualOutput ∧
      ListRealizes (EffectRealizes environment) requests actualRequests ∧
      ListRealizes (NameRealizes environment) retained actualRetained := by
  obtain ⟨decorated, success, realized⟩ := related
  obtain ⟨decoratedInput, decoratedOutput, rfl, input, output⟩ := function_decoration success
  cases realized with
  | function inputRealized outputRealized requestsRealized retainedRealized =>
      exact ⟨_, _, _, _, _, _, rfl, input, output, inputRealized, outputRealized,
        requestsRealized, retainedRealized⟩

namespace Examples

def pureFunction : SourceType := .function .unit .unit []
def capturedCell : SupportShape := .function .unit .unit [.bound 3]
def outer : Instantiation.Environment := Instantiation.Environment.empty.bind 3 7
def inner : Instantiation.Environment := outer.bind 3 11

/-- Retaining a cell does not turn a pure function's exact row into a cell row. -/
example : decorate pureFunction capturedCell = .ok (.function .unit .unit [] [.bound 3]) := rfl

example : RealizedDecoration outer pureFunction capturedCell (.function .unit .unit [] [7]) := by
  refine ⟨_, rfl, .function .unit .unit .nil (.cons ?_ .nil)⟩
  exact acquired_name_realizes

/-- The nearest lexical binding realizes the same bound source name differently. -/
example : RealizedDecoration inner pureFunction capturedCell (.function .unit .unit [] [11]) := by
  refine ⟨_, rfl, .function .unit .unit .nil (.cons ?_ .nil)⟩
  exact acquired_name_realizes

/-- Previously realized atoms remain fixed under later source-name shadowing. -/
example : RealizedDecoration inner pureFunction
    (.function .unit .unit [.activation 7]) (.function .unit .unit [] [7]) := by
  exact ⟨_, rfl, .function .unit .unit .nil (.cons .activation .nil)⟩

def nested : SourceType := .product
  (.function (.reference (.bound 3))
    (.function .unit (.reference (.bound 3)) [.cell (.bound 3)]) []) .integer

def nestedSupport : SupportShape := .product
  (.function .reference (.function .unit .reference [.bound 3]) [.bound 3]) .integer

example : decorate nested nestedSupport = .ok (.product
    (.function (.reference (.bound 3))
      (.function .unit (.reference (.bound 3)) [.cell (.bound 3)] [.bound 3]) [] [.bound 3]) .integer) := rfl

example : RealizedDecoration inner nested nestedSupport (.product
    (.function (.reference 11)
      (.function .unit (.reference 11) [.cell 11] [11]) [] [11]) .integer) := by
  refine ⟨_, rfl, .product (.function (.reference ?_) (.function .unit (.reference ?_)
    (.cons (.cell ?_) .nil) (.cons ?_ .nil)) .nil (.cons ?_ .nil)) .integer⟩ <;>
    exact acquired_name_realizes

example : decorate (.product .unit .boolean) (.product .unit .integer) =
    .error .shapeMismatch := rfl

example : decorate (.reference (.bound 3)) .unit = .error .shapeMismatch := rfl

example : decorate (.function .unit .unit []) (.product .unit .unit) =
    .error .shapeMismatch := rfl

example : decorate (.unsupported .nominal) .unit = .error (.unsupportedSource .nominal) := rfl

example : decorate (.function .unit (.unsupported .variable) [])
    (.function .unit .unit [.bound 3]) = .error (.unsupportedSource .variable) := rfl

end Examples

#print axioms decorate_sound
#print axioms successful_erasure
#print axioms successful_preservation
#print axioms unsupported_rejected
#print axioms function_decoration
#print axioms realization_exists
#print axioms realized_resources
#print axioms realized_function
end Ash.OneShot.CoreTypeSupport
