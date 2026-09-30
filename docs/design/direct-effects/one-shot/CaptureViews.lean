import ResultBounds

/-!
Normalized, sort-directed views of result metadata. Capture normalization
flattens stored values but preserves full result views inside applications.
These views do not execute applications or realize actual runtime values.
-/

namespace Ash.OneShot.CaptureViews
open ResultSummaries

mutual
inductive View where
  | scalar
  | resource : Nat → View
  | parameter : Nat → View
  | product : View → View → View
  | callable : List Atom → View → View
  | application : View → View → View
  | join : View → View → View
  | unknown
  deriving Repr

inductive Atom where
  | resource : Nat → Atom
  | parameter : Nat → Atom
  | application : View → View → Atom
  | unknown
  deriving Repr
end

def View.capture : View → List Atom
  | .scalar => []
  | .resource identity => [.resource identity]
  | .parameter index => [.parameter index]
  | .product left right | .join left right => left.capture ++ right.capture
  | .callable captures _ => captures
  | .application function argument => [.application function argument]
  | .unknown => [.unknown]

def normalize : Summary → View
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => .parameter index
  | .product left right => .product (normalize left) (normalize right)
  | .callable captures result => .callable (normalize captures).capture (normalize result)
  | .application function argument => .application (normalize function) (normalize argument)
  | .join left right => .join (normalize left) (normalize right)
  | .unknown => .unknown

mutual
def View.rename (rename : Nat → Nat) : View → View
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => .parameter (rename index)
  | .product left right => .product (left.rename rename) (right.rename rename)
  | .callable captures result => .callable (captures.map (Atom.rename rename)) (result.rename (liftRename rename))
  | .application function argument => .application (function.rename rename) (argument.rename rename)
  | .join left right => .join (left.rename rename) (right.rename rename)
  | .unknown => .unknown

def Atom.rename (rename : Nat → Nat) : Atom → Atom
  | .resource identity => .resource identity
  | .parameter index => .parameter (rename index)
  | .application function argument => .application (function.rename rename) (argument.rename rename)
  | .unknown => .unknown
end

def liftSubstitution (substitute : Nat → View) : Nat → View
  | 0 => .parameter 0
  | index + 1 => (substitute index).rename Nat.succ

mutual
def View.substitute (substitute : Nat → View) : View → View
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => substitute index
  | .product left right => .product (left.substitute substitute) (right.substitute substitute)
  | .callable captures result => .callable (captures.flatMap (Atom.substitute substitute)) (result.substitute (liftSubstitution substitute))
  | .application function argument => .application (function.substitute substitute) (argument.substitute substitute)
  | .join left right => .join (left.substitute substitute) (right.substitute substitute)
  | .unknown => .unknown

def Atom.substitute (substitute : Nat → View) : Atom → List Atom
  | .resource identity => [.resource identity]
  | .parameter index => (substitute index).capture
  | .application function argument => [.application (function.substitute substitute) (argument.substitute substitute)]
  | .unknown => [.unknown]
end

def View.instantiate (body argument : View) : View :=
  body.substitute fun index => match index with
    | 0 => argument
    | index + 1 => .parameter index

def callResult (function argument : View) : View := match function with
  | .callable _ body => body.instantiate argument
  | _ => .application function argument

theorem capture_rename (view : View) :
    (view.rename rename).capture = view.capture.map (Atom.rename rename) := by
  cases view with
  | scalar | resource | parameter | callable | application | unknown => simp [View.rename, View.capture, Atom.rename]
  | product left right | join left right =>
      simp only [View.rename, View.capture, List.map_append, capture_rename left, capture_rename right]
termination_by sizeOf view

theorem capture_substitute (view : View) :
    (view.substitute substitute).capture = view.capture.flatMap (Atom.substitute substitute) := by
  cases view with
  | scalar | resource | parameter | callable | application | unknown => simp [View.substitute, View.capture, Atom.substitute]
  | product left right | join left right =>
      simp only [View.substitute, View.capture, List.flatMap_append, capture_substitute left, capture_substitute right]
termination_by sizeOf view

theorem normalize_rename (summary : Summary) (rename : Nat → Nat) :
    normalize (summary.rename rename) = (normalize summary).rename rename := by
  induction summary generalizing rename with
  | scalar | resource | parameter | unknown => simp [normalize, Summary.rename, View.rename]
  | product | application | join => simp_all [normalize, Summary.rename, View.rename]
  | callable captures result ihCaptures ihResult =>
      simp [normalize, Summary.rename, View.rename, ihCaptures, ihResult, capture_rename]

theorem normalize_substitute (summary : Summary) (substitute : Nat → Summary) :
    normalize (summary.substitute substitute) =
      (normalize summary).substitute (fun index => normalize (substitute index)) := by
  induction summary generalizing substitute with
  | scalar | resource | parameter | unknown => simp [normalize, Summary.substitute, View.substitute]
  | product | application | join => simp_all [normalize, Summary.substitute, View.substitute]
  | callable captures result ihCaptures ihResult =>
      have lifted : (fun index => normalize (ResultSummaries.liftSubstitution substitute index)) =
          liftSubstitution (fun index => normalize (substitute index)) := by
        funext index
        cases index with
        | zero => rfl
        | succ index => simp only [ResultSummaries.liftSubstitution, liftSubstitution, normalize_rename]
      simp [normalize, Summary.substitute, View.substitute, ihCaptures, ihResult, capture_substitute, lifted]

theorem normalize_call_result (function argument : Summary) :
    normalize (ResultSummaries.callResult function argument) = callResult (normalize function) (normalize argument) := by
  cases function with
  | scalar | resource | parameter | product | application | join | unknown => rfl
  | callable captures result =>
      simp only [ResultSummaries.callResult, Summary.instantiate, normalize_substitute, normalize, callResult, View.instantiate]
      congr 1
      funext index
      cases index <;> rfl

mutual
def View.encode : View → Summary
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => .parameter index
  | .product left right => .product left.encode right.encode
  | .callable captures result =>
      .callable (captures.foldr (fun atom rest => .join atom.encode rest) .scalar) result.encode
  | .application function argument => .application function.encode argument.encode
  | .join left right => .join left.encode right.encode
  | .unknown => .unknown

def Atom.encode : Atom → Summary
  | .resource identity => .resource identity
  | .parameter index => .parameter index
  | .application function argument => .application function.encode argument.encode
  | .unknown => .unknown
end

theorem normalize_encoded_atoms (atoms : List Atom)
    (exactAtoms : ∀ atom ∈ atoms, (normalize atom.encode).capture = [atom]) :
    (normalize (atoms.foldr (fun atom rest => Summary.join atom.encode rest) .scalar)).capture = atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [List.foldr_cons, normalize, View.capture,
        exactAtoms atom List.mem_cons_self, ih (fun entry member => exactAtoms entry (List.mem_cons_of_mem _ member)),
        List.singleton_append]

mutual
/-- Every normalized result view has a representative in the original metadata
    grammar. Encoding and normalizing preserve all application operands. -/
theorem normalize_encode (view : View) : normalize view.encode = view := by
  cases view with
  | scalar | resource | parameter | unknown => simp [View.encode, normalize]
  | product left right | application left right | join left right =>
      simp [View.encode, normalize, normalize_encode left, normalize_encode right]
  | callable captures result =>
      simp only [View.encode, normalize, normalize_encode result]
      rw [normalize_encoded_atoms captures (fun atom _ => normalize_encode_atom atom)]
termination_by sizeOf view

theorem normalize_encode_atom (atom : Atom) : (normalize atom.encode).capture = [atom] := by
  cases atom with
  | resource | parameter | unknown => simp [Atom.encode, normalize, View.capture]
  | application function argument =>
      simp [Atom.encode, normalize, View.capture, normalize_encode function, normalize_encode argument]
termination_by sizeOf atom
end

theorem encode_injective : Function.Injective View.encode := by
  intro first second same
  have normalized := congrArg normalize same
  simpa only [normalize_encode] using normalized

/-- Computable equality uses the existing finite Summary syntax and the checked
    injective encoding, with no classical equality decision or native oracle. -/
instance : DecidableEq View := fun first second =>
  if same : first.encode = second.encode then isTrue (encode_injective same)
  else isFalse (fun equal => same (congrArg View.encode equal))

theorem view_substitute_identity (view : View) : view.substitute View.parameter = view := by
  have source := congrArg normalize (substitute_parameters view.encode)
  simpa only [normalize_substitute, normalize_encode, normalize] using source

theorem view_substitute_comp (view : View) (first second : Nat → View) :
    (view.substitute first).substitute second = view.substitute (fun index => (first index).substitute second) := by
  have source := congrArg normalize (substitute_comp view.encode (fun index => (first index).encode)
    (fun index => (second index).encode))
  simpa only [normalize_substitute, normalize_encode] using source

/-- Equality of normalized captures retains application atoms and their result
    views; it is stronger than the previous unknown-support observation. -/
def SameCapture (left right : Summary) : Prop := (normalize left).capture = (normalize right).capture

def Related (left right : Summary) : Prop := normalize left = normalize right

namespace SameCapture

theorem refl (summary : Summary) : SameCapture summary summary := rfl
theorem symm (same : SameCapture left right) : SameCapture right left := Eq.symm same
theorem trans (first : SameCapture left middle) (second : SameCapture middle right) : SameCapture left right := Eq.trans first second

theorem rename (same : SameCapture left right) (rename : Nat → Nat) :
    SameCapture (left.rename rename) (right.rename rename) := by
  simp only [SameCapture, normalize_rename, capture_rename]
  rw [same]

theorem substitute_congr (same : SameCapture left right)
    (parameters : ∀ index, Related (first index) (second index)) :
    SameCapture (left.substitute first) (right.substitute second) := by
  have environments : (fun index => normalize (first index)) = (fun index => normalize (second index)) := funext parameters
  simp only [SameCapture, normalize_substitute, capture_substitute]
  rw [same, environments]

theorem substitute (same : SameCapture left right) (substitute : Nat → Summary) :
    SameCapture (left.substitute substitute) (right.substitute substitute) :=
  substitute_congr same (fun _ => rfl)

theorem callable_captures (captures result : Summary) : SameCapture (.callable captures result) captures := rfl

end SameCapture

namespace Related

theorem refl (summary : Summary) : Related summary summary := rfl
theorem symm (same : Related left right) : Related right left := Eq.symm same
theorem trans (first : Related left middle) (second : Related middle right) : Related left right := Eq.trans first second

theorem capture (same : Related left right) : SameCapture left right := congrArg View.capture same

theorem product (first : Related left otherLeft) (second : Related right otherRight) :
    Related (.product left right) (.product otherLeft otherRight) := by
  unfold Related normalize
  rw [first, second]

theorem application (first : Related function target) (second : Related argument supplied) :
    Related (.application function argument) (.application target supplied) := by
  unfold Related normalize
  rw [first, second]

theorem join (first : Related left otherLeft) (second : Related right otherRight) :
    Related (.join left right) (.join otherLeft otherRight) := by
  unfold Related normalize
  rw [first, second]

theorem callable (captures : SameCapture first second) (result : Related body otherBody) :
    Related (.callable first body) (.callable second otherBody) := by
  unfold Related normalize
  rw [captures, result]

theorem rename (same : Related left right) (rename : Nat → Nat) :
    Related (left.rename rename) (right.rename rename) := by
  simp only [Related, normalize_rename]
  rw [same]

theorem substitute_congr (same : Related left right)
    (parameters : ∀ index, Related (first index) (second index)) :
    Related (left.substitute first) (right.substitute second) := by
  have environments : (fun index => normalize (first index)) = (fun index => normalize (second index)) := funext parameters
  simp only [Related, normalize_substitute]
  rw [same, environments]

theorem substitute (same : Related left right) (substitute : Nat → Summary) :
    Related (left.substitute substitute) (right.substitute substitute) :=
  substitute_congr same (fun _ => rfl)

theorem call_result (function : Related first second) (argument : Related value otherValue) :
    Related (ResultSummaries.callResult first value) (ResultSummaries.callResult second otherValue) := by
  simp only [Related, normalize_call_result]
  rw [function, argument]

/-- A captured application preserves the result views of both operands. -/
theorem captured_application_operands
    (same : SameCapture (.application function argument) (.application target supplied)) :
    Related function target ∧ Related argument supplied := by
  have atomEq := (List.cons.inj same).1
  exact Atom.application.inj atomEq

theorem captured_application_call_result
    (same : SameCapture (.application function argument) (.application target supplied)) :
    Related (ResultSummaries.callResult function argument) (ResultSummaries.callResult target supplied) := by
  obtain ⟨functions, arguments⟩ := captured_application_operands same
  exact call_result functions arguments

end Related

namespace Examples

theorem pending_applications_distinguished :
    ¬ SameCapture (ObservationGap.pending 7) (ObservationGap.pending 8) := by
  simp [SameCapture, normalize, ObservationGap.pending, ObservationGap.target, View.capture]

theorem enclosing_callables_distinguished :
    ¬ Related (.callable (ObservationGap.pending 7) .scalar) (.callable (ObservationGap.pending 8) .scalar) := by
  simp [Related, normalize, ObservationGap.pending, ObservationGap.target, View.capture]

theorem retaining_factory_corresponds :
    Related
      (ResultSummaries.callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
        (analyze (fun _ => .unknown) (ResultSummaries.Examples.retainingConstant 7)))
      (analyze (fun _ => .unknown) ((ScopedExpressions.Code.lambda 2 (.variable 3)).subst 3 (ResultSummaries.Examples.retainingConstant 7))) := by
  rfl

/-- Merely matching replacement storage would lose callable result information
    when a substituted parameter becomes a function operand. -/
theorem replacement_capture_equality_is_insufficient :
    ∃ first second : Nat → Summary,
      (∀ index, SameCapture (first index) (second index)) ∧
      ¬ SameCapture ((Summary.application (.parameter 0) .scalar).substitute first)
        ((Summary.application (.parameter 0) .scalar).substitute second) := by
  refine ⟨(fun _ => .callable (.join (.resource 7) (.resource 8)) (.resource 7)),
    (fun _ => .callable (.join (.resource 7) (.resource 8)) (.resource 8)), (fun _ => rfl), ?_⟩
  simp [SameCapture, Summary.substitute, normalize, View.capture]

end Examples
end Ash.OneShot.CaptureViews

#print axioms Ash.OneShot.CaptureViews.capture_rename
#print axioms Ash.OneShot.CaptureViews.capture_substitute
#print axioms Ash.OneShot.CaptureViews.normalize_rename
#print axioms Ash.OneShot.CaptureViews.normalize_substitute
#print axioms Ash.OneShot.CaptureViews.normalize_call_result
#print axioms Ash.OneShot.CaptureViews.normalize_encoded_atoms
#print axioms Ash.OneShot.CaptureViews.normalize_encode
#print axioms Ash.OneShot.CaptureViews.normalize_encode_atom
#print axioms Ash.OneShot.CaptureViews.encode_injective
#print axioms Ash.OneShot.CaptureViews.view_substitute_identity
#print axioms Ash.OneShot.CaptureViews.view_substitute_comp
#print axioms Ash.OneShot.CaptureViews.SameCapture.refl
#print axioms Ash.OneShot.CaptureViews.SameCapture.symm
#print axioms Ash.OneShot.CaptureViews.SameCapture.trans
#print axioms Ash.OneShot.CaptureViews.SameCapture.rename
#print axioms Ash.OneShot.CaptureViews.SameCapture.substitute_congr
#print axioms Ash.OneShot.CaptureViews.SameCapture.substitute
#print axioms Ash.OneShot.CaptureViews.SameCapture.callable_captures
#print axioms Ash.OneShot.CaptureViews.Related.refl
#print axioms Ash.OneShot.CaptureViews.Related.symm
#print axioms Ash.OneShot.CaptureViews.Related.trans
#print axioms Ash.OneShot.CaptureViews.Related.capture
#print axioms Ash.OneShot.CaptureViews.Related.product
#print axioms Ash.OneShot.CaptureViews.Related.application
#print axioms Ash.OneShot.CaptureViews.Related.join
#print axioms Ash.OneShot.CaptureViews.Related.callable
#print axioms Ash.OneShot.CaptureViews.Related.rename
#print axioms Ash.OneShot.CaptureViews.Related.substitute_congr
#print axioms Ash.OneShot.CaptureViews.Related.substitute
#print axioms Ash.OneShot.CaptureViews.Related.call_result
#print axioms Ash.OneShot.CaptureViews.Related.captured_application_operands
#print axioms Ash.OneShot.CaptureViews.Related.captured_application_call_result
#print axioms Ash.OneShot.CaptureViews.Examples.pending_applications_distinguished
#print axioms Ash.OneShot.CaptureViews.Examples.enclosing_callables_distinguished
#print axioms Ash.OneShot.CaptureViews.Examples.retaining_factory_corresponds
#print axioms Ash.OneShot.CaptureViews.Examples.replacement_capture_equality_is_insufficient
