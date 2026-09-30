import OwnerClosingSource

/-!
Shared value annotations connect ordinary port typing and protection contracts
on the existing direct expression syntax. Protection shapes alone are not
ordinary types. This does not authenticate provider implementations or replace
the remaining handler/resource and continuation-record invariants.
-/

namespace Ash.OneShot.CoherentSourceTypes
open ScopedExpressions ScopedExecution ProtectionContracts

inductive Shape where
  | scalar
  | pair : Shape → Shape → Shape
  | function : Shape → Shape → Shape
  deriving DecidableEq, Repr

def protectionShape : CallableProtection.Contract → Shape
  | .scalar => .scalar
  | .pair left right => .pair (protectionShape left) (protectionShape right)
  | .function input output _ => .function (protectionShape input) (protectionShape output)

def portShape : ScopedPorts.Port → Shape
  | .unit | .boolean | .integer | .reference _ => .scalar
  | .product left right => .pair (portShape left) (portShape right)
  | .function input output _ => .function (portShape input) (portShape output)

abbrev Compatible (protection : CallableProtection.Contract) (port : ScopedPorts.Port) : Prop :=
  protectionShape protection = portShape port

def checkCompatible (protection : CallableProtection.Contract) (port : ScopedPorts.Port) : Bool :=
  decide (Compatible protection port)

theorem check_compatible_iff : checkCompatible protection port = true ↔ Compatible protection port := by
  simp [checkCompatible]

/-- Ordinary atom types stay distinct. Function annotations retain both the
    declared latent instances and the operation/protection footprint. -/
inductive Value where
  | unit | boolean | integer
  | reference : Nat → Value
  | pair : Value → Value → Value
  | function : Value → Value → List Instance → Footprint → Value
  deriving DecidableEq, Repr

def Value.port : Value → ScopedPorts.Port
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference owner => .reference owner
  | .pair left right => .product left.port right.port
  | .function input output requests _ => .function input.port output.port requests

def Value.protection : Value → CallableProtection.Contract
  | .unit | .boolean | .integer | .reference _ => .scalar
  | .pair left right => .pair left.protection right.protection
  | .function input output _ latent => .function input.protection output.protection latent

theorem value_compatible (value : Value) : Compatible value.protection value.port := by
  induction value <;> simp_all [Compatible, protectionShape, portShape, Value.protection, Value.port]

abbrev Environment := Nat → Option Value
def Environment.empty : Environment := fun _ => none
def Environment.extend (environment : Environment) (name : Nat) (value : Value) : Environment :=
  fun other => if other = name then some value else environment other
def Environment.ports (environment : Environment) : ScopedPorts.TypeEnv := fun name => (environment name).map Value.port
def Environment.protection (environment : Environment) : CallableProtection.Environment := fun name => (environment name).map Value.protection

theorem ports_extend (environment : Environment) (name : Nat) (value : Value) : (environment.extend name value).ports = environment.ports.extend name value.port := by
  funext other
  by_cases same : other = name <;> simp [Environment.extend, Environment.ports, ScopedPorts.TypeEnv.extend, same]

theorem protection_extend (environment : Environment) (name : Nat) (value : Value) : (environment.extend name value).protection = environment.protection.extend name value.protection := by
  funext other
  by_cases same : other = name <;> simp [Environment.extend, Environment.protection, CallableProtection.Environment.extend, same]

abbrev Operations := Instance → Nat → Option (Value × Value)
def Operations.ports (operations : Operations) : ScopedPorts.Signature :=
  fun effect operation => (operations effect operation).map (fun pair => (pair.1.port, pair.2.port))
def Operations.protection (operations : Operations) : CallableProtection.Operations :=
  fun effect operation => (operations effect operation).map (fun pair => (pair.1.protection, pair.2.protection))

theorem port_lookup {operations : Operations} (known : operations effect operation = some (input, output)) :
    operations.ports effect operation = some (input.port, output.port) := by simp [Operations.ports, known]

theorem protection_lookup {operations : Operations} (known : operations effect operation = some (input, output)) :
    operations.protection effect operation = some (input.protection, output.protection) := by simp [Operations.protection, known]

/-- Every binder uses one shared annotation in both analyses. The grammar is
    still Code; this judgment covers its stable callable component. -/
inductive Summary (operations : Operations) :
    List Nat → Environment → List Instance → Code → Value → Footprint → Prop where
  | unit : Summary operations world environment allowed .unit .unit []
  | boolean : Summary operations world environment allowed (.boolean value) .boolean []
  | integer : Summary operations world environment allowed (.integer value) .integer []
  | reference (issued : identity ∈ world) :
      Summary operations world environment allowed (.resourceRef (.activation identity)) (.reference identity) []
  | «variable» (known : environment name = some value) (formed : ScopedPorts.InWorld world value.port) :
      Summary operations world environment allowed (.variable name) value []
  | pair (left : Summary operations world environment allowed a first leftRow)
      (right : Summary operations world environment allowed b second rightRow) :
      Summary operations world environment allowed (.pair a b) (.pair first second) (leftRow ++ rightRow)
  | lambda (body : Summary operations world (environment.extend parameter input) latentRequests code output latentRow)
      (formed : ScopedPorts.InWorld world (Value.function input output latentRequests latentRow).port) :
      Summary operations world environment allowed (.lambda parameter code) (.function input output latentRequests latentRow) []
  | app (function : Summary operations world environment allowed f (.function input output latentRequests latentRow) functionRow)
      (argument : Summary operations world environment allowed a input argumentRow) (admitted : latentRequests ⊆ allowed) :
      Summary operations world environment allowed (.app f a) output (functionRow ++ argumentRow ++ latentRow)
  | bind (initializer : Summary operations world environment allowed a input initializerRow)
      (body : Summary operations world (environment.extend parameter input) allowed b output bodyRow) :
      Summary operations world environment allowed (.bind parameter a b) output (initializerRow ++ bodyRow)
  | branch (condition : Summary operations world environment allowed test .boolean conditionRow)
      (yes : Summary operations world environment allowed a output yesRow)
      (no : Summary operations world environment allowed b output noRow) :
      Summary operations world environment allowed (.branch test a b) output (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Summary operations world environment allowed value input operandRow) (formed : ScopedPorts.InWorld world output.port) :
      Summary operations world environment allowed (.perform (Instantiation.freezeEffect effect) operation value) output
        (operandRow ++ [⟨effect, operation, false⟩])
  | cleanup (callback : Summary operations world environment allowed action (.function .unit .unit latentRequests latentRow) callbackRow)
      (body : Summary operations world environment allowed code output bodyRow) (admitted : latentRequests ⊆ allowed) :
      Summary operations world environment allowed (.cleanup action code) output (callbackRow ++ bodyRow ++ qualify true latentRow)
  | resource {bodyRow : Nat → Footprint}
      (initializer : Summary operations world environment allowed initial .integer initialRow)
      (body : ∀ identity, identity ∉ world →
        Summary operations (world ++ [identity]) environment (.cell identity :: residual)
          (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = row) :
      Summary operations world environment allowed (.resource binder initial code) output (initialRow ++ row)

/-- Acquisition extends the resource world without changing callable contracts
    or their latent footprints. Reuse the existing port-world weakening rule. -/
theorem summary_world_weaken (source : Summary operations world environment allowed code value row)
    (larger : world ⊆ next) : Summary operations next environment allowed code value row := by
  induction source generalizing next with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference (larger issued)
  | «variable» known formed => exact .variable known (ScopedPorts.in_world_mono formed larger)
  | pair left right ihLeft ihRight => exact .pair (ihLeft larger) (ihRight larger)
  | lambda body formed ih => exact .lambda (ih larger) (ScopedPorts.in_world_mono formed larger)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction larger) (ihArgument larger) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit larger) (ihBody larger)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition larger) (ihYes larger) (ihNo larger)
  | perform known admitted operand formed ih => exact .perform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))

theorem protection_summary (source : Summary operations world environment allowed code value row) :
    CallableProtection.Summarizes operations.protection environment.protection code value.protection row := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference
  | «variable» known formed => exact .variable (by simp [Environment.protection, known])
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | lambda body formed ih => exact .lambda (by simpa only [protection_extend] using ih)
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInit ihBody => exact .bind ihInit (by simpa only [protection_extend] using ihBody)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known admitted operand formed ih => exact .perform (protection_lookup known) ih
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource ihInit ihBody outward

theorem port_typing (source : Summary operations world environment allowed code value row) (ticket : ScopedPorts.Ticket) :
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed code value.port := by
  induction source generalizing ticket with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable (by simp [Environment.ports, known]) formed
  | pair left right ihLeft ihRight => exact .pair (ihLeft ticket) (ihRight ticket)
  | lambda body formed ih => exact .lambda (by simpa only [ports_extend] using ih .none) formed
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction ticket) (ihArgument ticket) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit ticket) (by simpa only [ports_extend] using ihBody ticket)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition ticket) (ihYes ticket) (ihNo ticket)
  | perform known admitted operand formed ih => exact .perform (port_lookup known) admitted (ih ticket) formed
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback ticket) (ihBody ticket) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit ticket) (fun identity fresh => ihBody identity fresh ticket) formed effectsBound admitted

theorem owner_source (source : Summary operations world environment allowed code value raw)
    (exported : OwnerSource.exportAt inside phases raw = some row) :
    OwnerSource.Derives operations.protection policy contracts inside environment.protection scope phases code phases value.protection [] row :=
  .stable (protection_summary source) exported

theorem value_row (source : Summary operations world environment allowed code value row)
    (isValue : code.IsValue) : row = [] :=
  CallableProtection.value_has_no_immediate_demands (protection_summary source) isValue

def AgreeOn (source destination : Environment) (dependencies : List Syntax.Dependency) : Prop :=
  ∀ name, Syntax.Dependency.variable name ∈ dependencies → source name = destination name

theorem agree_left (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination left :=
  fun _ member => agree _ (List.mem_append_left _ member)

theorem agree_right (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination right :=
  fun _ member => agree _ (List.mem_append_right _ member)

theorem agree_extend (agree : AgreeOn source destination (Syntax.without (.variable binder) dependencies)) :
    AgreeOn (source.extend binder value) (destination.extend binder value) dependencies := by
  intro name member
  by_cases same : name = binder
  · simp [Environment.extend, same]
  · simp only [Environment.extend, if_neg same]
    exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)

theorem environment_congr (source : Summary operations world environment allowed code value row)
    (agree : AgreeOn environment destination code.dependencies) :
    Summary operations world destination allowed code value row := by
  induction source generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable ((agree _ List.mem_cons_self).symm.trans known) formed
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | lambda body formed ih => exact .lambda (ih (agree_extend agree)) formed
  | app function argument admitted ihFunction ihArgument =>
      exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree))) (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree))
  | perform known admitted operand formed ih => exact .perform known admitted (ih (agree_right agree)) formed
  | cleanup callback body admitted ihCallback ihBody =>
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      apply Summary.resource (ihInit (agree_left agree)) _ formed effectsBound admitted outward
      intro identity fresh
      apply ihBody identity fresh
      intro name member
      rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound _ identity _ member) with original | introduced
      · exact agree_right agree name original
      · simp at introduced

theorem closed_value_environment (source : Summary operations world environment allowed code value row)
    (closed : ClosedValue code) (destination : Environment) :
    Summary operations world destination allowed code value row :=
  environment_congr source (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem value_allowed (source : Summary operations world environment allowed code value row)
    (isValue : code.IsValue) (destination : List Instance) :
    Summary operations world environment destination code value row := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» => cases isValue
  | pair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | lambda body formed => exact .lambda body formed
  | app | bind | branch | perform | cleanup | resource => cases isValue

theorem allowed_mono (source : Summary operations world environment allowed code value row)
    (more : allowed ⊆ destination) : Summary operations world environment destination code value row := by
  induction source generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | pair left right ihLeft ihRight => exact .pair (ihLeft more) (ihRight more)
  | lambda body formed => exact .lambda body formed
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction more) (ihArgument more) (admitted.trans more)
  | bind initializer body ihInit ihBody => exact .bind (ihInit more) (ihBody more)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition more) (ihYes more) (ihNo more)
  | perform known admitted operand formed ih => exact .perform known (more admitted) (ih more) formed
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback more) (ihBody more) (admitted.trans more)
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit more) body formed effectsBound (admitted.trans more) outward

@[simp] theorem Environment.extend_shadow (environment : Environment) (name : Nat) (first second : Value) :
    (environment.extend name first).extend name second = environment.extend name second := by
  funext other
  by_cases same : other = name <;> simp [Environment.extend, same]

@[simp] theorem Environment.extend_commute (environment : Environment) (first second : Nat) (a b : Value)
    (different : first ≠ second) :
    (environment.extend first a).extend second b = (environment.extend second b).extend first a := by
  funext other
  by_cases atFirst : other = first
  · subst other; simp [Environment.extend, different]
  · by_cases atSecond : other = second <;> simp [Environment.extend, atFirst, atSecond, Ne.symm different]

/-- Substitution uses the same binder annotation in both projected analyses,
    including nested and higher-order callable contracts. -/
theorem substitution
    (source : Summary operations world (environment.extend name input) allowed code result row)
    (replacement : Summary operations world environment allowed value input []) (closed : ClosedValue value) :
    Summary operations world environment allowed (code.subst name value) result row := by
  cases source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | lambda body formed =>
      rename_i latentRequests bodyCode output latentRow domain parameter
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte]
        exact .lambda (by simpa only [Environment.extend_shadow] using body) formed
      · simp only [Code.subst, if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact .lambda (substitution rearranged
          (value_allowed (closed_value_environment replacement closed (environment.extend parameter domain)) closed.1 latentRequests) closed) formed
  | app function argument admitted => exact .app (substitution function replacement closed) (substitution argument replacement closed) admitted
  | bind initializer body =>
      rename_i a domain initializerRow parameter b bodyRow
      apply Summary.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no => exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed)
  | perform known admitted operand formed => exact .perform known admitted (substitution operand replacement closed) formed
  | cleanup callback body admitted => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) admitted
  | resource initializer body formed effectsBound admitted outward =>
      apply Summary.resource (substitution initializer replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact substitution (body identity fresh)
        (value_allowed (summary_world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

theorem beta_summary
    (source : Summary operations world environment allowed (.app (.lambda parameter body) argument) result row)
    (closed : ClosedValue argument) : Summary operations world environment allowed (body.subst parameter argument) result row := by
  cases source with
  | app function argument admitted => cases function with
      | lambda body formed =>
          have empty := value_row argument closed.1
          subst_vars
          simpa only [List.nil_append] using allowed_mono
            (substitution body (value_allowed argument closed.1 _) closed) admitted

theorem bind_summary
    (source : Summary operations world environment allowed (.bind parameter value body) result row)
    (closed : ClosedValue value) : Summary operations world environment allowed (body.subst parameter value) result row := by
  cases source with
  | bind initializer body =>
      have empty := value_row initializer closed.1
      subst_vars
      simpa only [List.nil_append] using substitution body initializer closed

/-- Stable pending positions retain one annotation for the hole and one for
    the result. Ticket and resource positions require the later source rules. -/
inductive ContextSummary (operations : Operations) (world : List Nat) (environment : Environment) (allowed : List Instance) :
    ScopedExecution.Context → Value → Value → Footprint → Prop where
  | pairLeft (right : Summary operations world environment allowed code output row) :
      ContextSummary operations world environment allowed (.pairLeft code) input (.pair input output) row
  | pairRight (left : Summary operations world environment allowed code input []) :
      ContextSummary operations world environment allowed (.pairRight code) output (.pair input output) []
  | appFunction (argument : Summary operations world environment allowed code input row) (admitted : requests ⊆ allowed) :
      ContextSummary operations world environment allowed (.appFunction code) (.function input output requests latent) output (row ++ latent)
  | appArgument (function : Summary operations world environment allowed code (.function input output requests latent) [])
      (admitted : requests ⊆ allowed) :
      ContextSummary operations world environment allowed (.appArgument code) input output latent
  | bind (body : Summary operations world (environment.extend parameter input) allowed code output row) :
      ContextSummary operations world environment allowed (.bind parameter code) input output row
  | branch (yes : Summary operations world environment allowed a output yesRow)
      (no : Summary operations world environment allowed b output noRow) :
      ContextSummary operations world environment allowed (.branch a b) .boolean output (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.port) :
      ContextSummary operations world environment allowed (.perform (Instantiation.freezeEffect effect) operation) input output [⟨effect, operation, false⟩]
  | cleanup (body : Summary operations world environment allowed code output row) (admitted : requests ⊆ allowed) :
      ContextSummary operations world environment allowed (.cleanup code) (.function .unit .unit requests latent) output (row ++ qualify true latent)
  | resource {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Summary operations (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = row) :
      ContextSummary operations world environment allowed (.resource binder code) .integer output row

theorem context_plug
    (context : ContextSummary operations world environment allowed position input output restRow)
    (child : Summary operations world environment allowed code input row) :
    Summary operations world environment allowed (position.plug code) output (row ++ restRow) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Summary.pair left child
  | appFunction argument admitted => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Summary.app child argument admitted
  | appArgument function admitted => simpa only [ScopedExecution.Context.plug, List.nil_append] using Summary.app function child admitted
  | bind body => exact .bind child body
  | branch yes no => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Summary.branch child yes no
  | perform known admitted formed => exact .perform known admitted child formed
  | cleanup body admitted => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Summary.cleanup child body admitted
  | resource body formed effectsBound admitted outward => exact .resource child body formed effectsBound admitted outward

theorem context_ports
    (context : ContextSummary operations world environment allowed position input output row) (ticket : ScopedPorts.Ticket) :
    ScopedPorts.ContextTyped operations.ports world environment.ports ticket allowed position input.port output.port := by
  cases context with
  | pairLeft right => exact .pairLeft (port_typing right ticket)
  | pairRight left => exact .pairRight (port_typing left ticket)
  | appFunction argument admitted => exact .appFunction (port_typing argument ticket) admitted
  | appArgument function admitted => exact .appArgument (port_typing function ticket) admitted
  | bind body => exact .bind (by simpa only [ports_extend] using port_typing body ticket)
  | branch yes no => exact .branch (port_typing yes ticket) (port_typing no ticket)
  | perform known admitted formed => exact .perform (port_lookup known) admitted formed
  | cleanup body admitted => exact .cleanup (port_typing body ticket) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource (fun identity fresh => port_typing (body identity fresh) ticket) formed effectsBound admitted

theorem focus_decompose (focus : Focus whole child position)
    (source : Summary operations world environment allowed whole output row) :
    ∃ input childRow restRow, Summary operations world environment allowed child input childRow ∧
      ContextSummary operations world environment allowed position input output restRow ∧ row = childRow ++ restRow := by
  cases source with
  | unit | boolean | integer | reference | «variable» | lambda => cases focus
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, left, .pairLeft right, rfl⟩
      | pairRight isValue =>
          have empty := value_row left isValue
          subst_vars
          exact ⟨_, _, _, right, .pairRight left, by simp⟩
  | app function argument admitted => cases focus with
      | appFunction => exact ⟨_, _, _, function, .appFunction argument admitted, List.append_assoc ..⟩
      | appArgument isValue =>
          have empty := value_row function isValue
          subst_vars
          exact ⟨_, _, _, argument, .appArgument function admitted, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, initializer, .bind body, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, condition, .branch yes no, List.append_assoc ..⟩
  | perform known admitted operand formed => cases focus with
      | perform => exact ⟨_, _, _, operand, .perform known admitted formed, rfl⟩
  | cleanup callback body admitted => cases focus with
      | cleanup => exact ⟨_, _, _, callback, .cleanup body admitted, List.append_assoc ..⟩
  | resource initializer body formed effectsBound admitted outward => cases focus with
      | resource notValue => exact ⟨_, _, _, initializer, .resource body formed effectsBound admitted outward, rfl⟩

theorem export_append_split (exported : OwnerSource.exportAt inside phases (left ++ right) = some row) :
    ∃ first second, OwnerSource.exportAt inside phases left = some first ∧
      OwnerSource.exportAt inside phases right = some second ∧ row = first ++ second := by
  simp only [OwnerSource.exportAt, ProtectionResiduals.residual_rows_append] at exported
  cases first : ProtectionResiduals.residualize (OwnerPhaseTransitions.project inside phases) left <;>
    cases second : ProtectionResiduals.residualize (OwnerPhaseTransitions.project inside phases) right <;>
    simp_all [ProtectionResiduals.merge, OwnerSource.exportAt]

theorem context_source
    (context : ContextSummary operations world environment allowed position input output raw)
    (exported : OwnerSource.exportAt inside phases raw = some row) :
    OwnerSource.ContextDerives operations.protection policy contracts inside environment.protection scope position
      phases input.protection phases output.protection [] row := by
  cases context with
  | pairLeft right => exact .pairLeft (owner_source right exported)
  | pairRight left =>
      have empty : row = [] := by simpa [OwnerSource.exportAt, ProtectionResiduals.residual_empty] using exported.symm
      subst row
      exact .pairRight (protection_summary left)
  | appFunction argument admitted =>
      obtain ⟨first, second, argRow, callRow, same⟩ := export_append_split exported
      subst row
      exact .appFunction (owner_source argument argRow) callRow
  | appArgument function admitted => exact .appArgument (protection_summary function) exported
  | bind body => exact .bind (by simpa only [protection_extend] using owner_source body exported)
  | branch yes no =>
      obtain ⟨first, second, yesRow, noRow, same⟩ := export_append_split exported
      subst row
      exact .branch (owner_source yes yesRow) (owner_source no noRow)
  | perform known admitted formed => exact .perform (protection_lookup known) exported
  | resource body formed effectsBound admitted outward =>
      exact .resource (fun identity fresh => protection_summary (body identity fresh)) outward exported
  | cleanup body admitted =>
      obtain ⟨first, second, bodyRow, callRow, same⟩ := export_append_split exported
      subst row
      apply OwnerSource.ContextDerives.cleanup (owner_source body bodyRow)
      simpa only [OwnerSource.exportAt, ProtectionResiduals.residualize, DisposalProtection.through_barrier] using callRow

/-- Stored code and its input/output metadata must agree with the same shared
    derivation. This checks both views of an actual plain frame. -/
theorem plain_frame
    (source : ContextSummary operations world Environment.empty allowed data.context input output raw)
    (inputAnnotation : input.port = ScopedPorts.eraseType data.input)
    (outputAnnotation : output.port = ScopedPorts.eraseType data.output)
    (scope : ScopedPorts.ScopeTyped tickets data.scope ticket)
    (exported : OwnerSource.exportAt inside phases raw = some row) :
    ScopedPorts.FrameTyped operations.ports tickets world (.plain data) ∧
    OwnerSource.FrameSource operations.protection policy contracts inside (.plain data)
      phases input.protection phases output.protection [] row := by
  refine ⟨.plain (allowed := allowed) scope ?_, .plain (context_source source exported)⟩
  have typed := context_ports source ticket
  rw [inputAnnotation, outputAnnotation] at typed
  exact typed

def checkOperation : Option (CallableProtection.Contract × CallableProtection.Contract) → Option (ScopedPorts.Port × ScopedPorts.Port) → Bool
  | none, none => true
  | some (input, output), some (inputPort, outputPort) => checkCompatible input inputPort && checkCompatible output outputPort
  | _, _ => false

theorem checked_operation
    (checked : checkOperation protection ports = true)
    (source : protection = some (input, output)) (target : ports = some (inputPort, outputPort)) :
    Compatible input inputPort ∧ Compatible output outputPort := by
  simpa only [source, target, checkOperation, Bool.and_eq_true_iff, check_compatible_iff] using checked

theorem checked_operation_domain (checked : checkOperation protection ports = true) : protection = none ↔ ports = none := by
  cases protection <;> cases ports <;> simp_all [checkOperation]

theorem shared_operation_check (operations : Operations) (effect : Instance) (operation : Nat) :
    checkOperation (operations.protection effect operation) (operations.ports effect operation) = true := by
  cases found : operations effect operation with
  | none => simp [Operations.protection, Operations.ports, found, checkOperation]
  | some pair =>
      rcases pair with ⟨input, output⟩
      simpa only [Operations.protection, Operations.ports, found, Option.map_some,
        checkOperation, Bool.and_eq_true_iff, check_compatible_iff] using
        And.intro (value_compatible input) (value_compatible output)

theorem request_output_compatible {operations : CallableProtection.Operations} {signature : ScopedPorts.Signature}
    (source : CallableProtection.Summarizes operations environment
      (.perform (Instantiation.freezeEffect effect) operation operand) output row)
    (checked : checkOperation (operations effect operation) (signature effect operation) = true)
    (known : signature effect operation = some (inputPort, outputPort)) : Compatible output outputPort := by
  generalize eq : Instantiation.freezeEffect effect = requested at source
  cases source with
  | perform actual operand =>
      have same := ScopedExecution.freeze_effect_injective eq
      cases same
      exact (checked_operation checked actual known).2

/-- The two projections share a record and check their callable shapes. This
    does not claim equality of latent effects or stored resource support. -/
structure Record where
  runtime : CallableJoint.TicketRecord
  source : OwnerSource.ResumeContract
  input : Compatible source.input runtime.joint.contract.input
  answer : Compatible source.answer runtime.joint.contract.answer

abbrev Registry := Nat → Option Record
def Registry.runtime (registry : Registry) : CallableJoint.Registry := fun owner => (registry owner).map Record.runtime
def Registry.source (registry : Registry) : OwnerSource.Contracts := fun owner => (registry owner).map Record.source
def Registry.insert (registry : Registry) (owner : Nat) (record : Record) : Registry :=
  fun other => if other = owner then some record else registry other

theorem registered (registry : Registry) :
    ∀ owner contract, registry.source owner = some contract → ∃ record, registry.runtime owner = some record := by
  intro owner contract known
  cases found : registry owner with
  | none => simp [Registry.source, found] at known
  | some record => exact ⟨record.runtime, by simp [Registry.runtime, found]⟩

theorem registry_shapes (registry : Registry)
    (source : registry.source owner = some contract) (runtime : registry.runtime owner = some record) :
    Compatible contract.input record.joint.contract.input ∧ Compatible contract.answer record.joint.contract.answer := by
  cases found : registry owner with
  | none => simp [Registry.source, found] at source
  | some entry =>
      have sourceEq : entry.source = contract := by simpa [Registry.source, found] using source
      have runtimeEq : entry.runtime = record := by simpa [Registry.runtime, found] using runtime
      subst contract
      subst record
      exact ⟨entry.input, entry.answer⟩

theorem insert_runtime (registry : Registry) :
    (registry.insert owner record).runtime = registry.runtime.insert owner record.runtime := by
  funext other
  by_cases same : other = owner <;> simp [Registry.insert, Registry.runtime, CallableJoint.Registry.insert, same]

theorem insert_source (registry : Registry) :
    (registry.insert owner record).source = OwnerCaptureContracts.insert registry.source owner record.source := by
  funext other
  by_cases same : other = owner <;> simp [Registry.insert, Registry.source, OwnerCaptureContracts.insert, same]

theorem insert_retains_projections (registry : Registry) (fresh : registry owner = none) (record : Record) :
    CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime ∧
    OwnerCaptureContracts.Extends registry.source (registry.insert owner record).source := by
  rw [insert_runtime, insert_source]
  exact ⟨CallableJoint.registry_insert_extends (by simp [Registry.runtime, fresh]),
    OwnerCaptureContracts.insert_extends (by simp [Registry.source, fresh])⟩

section Capture
variable {whole capture tail fixed : Stack} {operations : CallableProtection.Operations} {signature : ScopedPorts.Signature}

/-- The actual request and checked operation entry establish the captured
    contract's input shape. Its answer still needs a shared pending-frame check. -/
theorem capture_input_compatible
    (cut : HandlerCut effect whole capture tail handler)
    (source : OwnerSource.Source operations policy contracts tables fixed outside scope
      (.perform (Instantiation.freezeEffect effect) operation operand) whole before after output demand row)
    (isValue : operand.IsValue)
    (checked : checkOperation (operations effect operation) (signature effect operation) = true)
    (known : signature effect operation = some (inputPort, outputPort))
    (closeDemand : List Nat) (closeRow : Option Footprint) :
    ∃ contract : OwnerSource.ResumeContract, ∃ middle,
      Compatible contract.input outputPort ∧
      Nonempty (OwnerCaptureContracts.SavedSource operations policy contracts tables (tail.append fixed) capture before middle contract) ∧
      ∃ remaining restRow,
        OwnerSource.Segment operations policy contracts tables fixed tail middle contract.answer after output remaining restRow ∧
        demand = contract.resumeDemand ++ remaining := by
  obtain ⟨environment, raw, requestRow, middle, contract, remaining, restRow, summary, exported, saved,
    rest, closeNames, closeEffects, names, effects, accepted⟩ := OwnerCaptureContracts.capture_contract cut source isValue closeDemand closeRow
  exact ⟨contract, middle, request_output_compatible summary checked known, saved, remaining, restRow, rest, names⟩

end Capture

namespace Owners
open OwnerPhaseTransitions (Phases Trace)

/-- A continuation's source and ordinary port contracts use the same value
    annotations. Saved-source and closing-plan authentication remain separate. -/
structure Contract where
  input : Value
  answer : Value
  held : Bool
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint
  resumeEffects : List Instance
  closeEffects : List Instance
  deriving DecidableEq, Repr

def Contract.source (contract : Contract) : OwnerSource.ResumeContract :=
  ⟨contract.input.protection, contract.answer.protection, contract.held, contract.resumeDemand,
    contract.resumeRow, contract.closeDemand, contract.closeRow⟩

def Contract.ports (contract : Contract) : ScopedPorts.ContinuationContract :=
  ⟨contract.input.port, contract.answer.port, contract.resumeEffects, contract.closeEffects⟩

abbrev Contracts := Nat → Option Contract
def Contracts.source (contracts : Contracts) : OwnerSource.Contracts := fun owner => (contracts owner).map Contract.source
def Contracts.ports (contracts : Contracts) : ScopedPorts.EffectTickets := fun owner => (contracts owner).map Contract.ports

theorem source_lookup {contracts : Contracts} (known : contracts owner = some contract) :
    contracts.source owner = some contract.source := by simp [Contracts.source, known]

theorem ports_lookup {contracts : Contracts} (known : contracts owner = some contract) :
    contracts.ports owner = some contract.ports := by simp [Contracts.ports, known]

theorem scope_resolved {contracts : Contracts} (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) :
    ticket = .bound binder contract.input.port contract.answer.port contract.resumeEffects contract.closeEffects := by
  cases scopeTyped with
  | none => cases resolved
  | bound actual =>
      simp only [Execution.Scope.resolve] at resolved
      split at resolved
      · rename_i same
        subst binder
        cases Option.some.inj resolved
        have equal := actual.symm.trans (ports_lookup known)
        cases Option.some.inj equal
        rfl
      · cases resolved

/-- Shared value annotations are threaded through the existing one-shot owner
    transitions. This adds no computation form or sequencing operator. -/
inductive Derives (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) (world : List Nat) :
    Environment → List Instance → Scope → Phases → Code → Phases → Value → List Nat → Footprint → Prop where
  | stable (summary : Summary operations world environment allowed code result raw)
      (exported : OwnerSource.exportAt inside phases raw = some row) :
      Derives operations policy contracts inside world environment allowed scope phases code phases result [] row
  | pair (left : Derives operations policy contracts inside world environment allowed scope before a middle first leftDemand leftRow)
      (right : Derives operations policy contracts inside world environment allowed scope middle b after second rightDemand rightRow) :
      Derives operations policy contracts inside world environment allowed scope before (.pair a b) after (.pair first second)
        (leftDemand ++ rightDemand) (leftRow ++ rightRow)
  | app (function : Derives operations policy contracts inside world environment allowed scope before f middle
        (.function input output requests latent) functionDemand functionRow)
      (argument : Derives operations policy contracts inside world environment allowed scope middle a after input argumentDemand argumentRow)
      (admitted : requests ⊆ allowed) (exported : OwnerSource.exportAt inside after latent = some invocationRow) :
      Derives operations policy contracts inside world environment allowed scope before (.app f a) after output
        (functionDemand ++ argumentDemand) (functionRow ++ argumentRow ++ invocationRow)
  | bind (initializer : Derives operations policy contracts inside world environment allowed scope before a middle input initializerDemand initializerRow)
      (body : Derives operations policy contracts inside world (environment.extend parameter input) allowed scope middle b after output bodyDemand bodyRow) :
      Derives operations policy contracts inside world environment allowed scope before (.bind parameter a b) after output
        (initializerDemand ++ bodyDemand) (initializerRow ++ bodyRow)
  | branch (condition : Derives operations policy contracts inside world environment allowed scope before test middle .boolean conditionDemand conditionRow)
      (yes : Derives operations policy contracts inside world environment allowed scope middle a after output yesDemand yesRow)
      (no : Derives operations policy contracts inside world environment allowed scope middle b after output noDemand noRow) :
      Derives operations policy contracts inside world environment allowed scope before (.branch test a b) after output
        (conditionDemand ++ yesDemand) (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Derives operations policy contracts inside world environment allowed scope before value after input operandDemand operandRow)
      (formed : ScopedPorts.InWorld world output.port)
      (exported : OwnerSource.exportAt inside after [⟨effect, operation, false⟩] = some requestRow) :
      Derives operations policy contracts inside world environment allowed scope before (.perform (Instantiation.freezeEffect effect) operation value)
        after output operandDemand (operandRow ++ requestRow)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operand : Derives operations policy contracts inside world environment allowed scope before value middle contract.input operandDemand operandRow)
      (transition : Trace middle (owner :: contract.resumeDemand) after)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Derives operations policy contracts inside world environment allowed scope before (.resume binder value) after contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (operandRow ++ contract.resumeRow)
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (closable : contract.closeRow = some row) (transition : Trace before (owner :: contract.closeDemand) after)
      (admitted : contract.closeEffects ⊆ allowed) :
      Derives operations policy contracts inside world environment allowed scope before (.discard binder) after .unit
        (owner :: contract.closeDemand) row
  | cleanup (callback : Derives operations policy contracts inside world environment allowed scope before action middle
        (.function .unit .unit requests latent) callbackDemand callbackRow)
      (body : Derives operations policy contracts inside world environment allowed scope middle code after output bodyDemand bodyRow)
      (admitted : requests ⊆ allowed)
      (exported : ProtectionResiduals.residualize (.barrier true :: OwnerPhaseTransitions.project inside after) latent = some executionRow) :
      Derives operations policy contracts inside world environment allowed scope before (.cleanup action code) after output
        (callbackDemand ++ bodyDemand) (callbackRow ++ bodyRow ++ executionRow)
  | resource {bodyRow : Nat → Footprint}
      (initializer : Derives operations policy contracts inside world environment allowed scope before initial after .integer demand initialRow)
      (body : ∀ identity, identity ∉ world → Summary operations (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw)
      (exported : OwnerSource.exportAt inside after raw = some row) :
      Derives operations policy contracts inside world environment allowed scope before (.resource binder initial code)
        after output demand (initialRow ++ row)

theorem owner_source (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    OwnerSource.Derives operations.protection policy contracts.source inside environment.protection scope before code after result.protection demand row := by
  induction source with
  | stable summary exported => exact .stable (protection_summary summary) exported
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted exported ihFunction ihArgument => exact .app ihFunction ihArgument exported
  | bind initializer body ihInit ihBody => exact .bind ihInit (by simpa only [protection_extend] using ihBody)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known admitted operand formed exported ih => exact .perform (protection_lookup known) ih exported
  | resume known resolved permission operand transition admitted formed ih =>
      exact .resume (source_lookup known) resolved permission ih transition
  | discard known resolved permission unprotected closable transition admitted =>
      exact .discard (source_lookup known) resolved permission unprotected closable transition
  | cleanup callback body admitted exported ihCallback ihBody => exact .cleanup ihCallback ihBody exported
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource ih (fun identity fresh => protection_summary (body identity fresh)) outward exported

theorem port_typing (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket) :
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed code result.port := by
  induction source with
  | stable summary exported => exact CoherentSourceTypes.port_typing summary ticket
  | pair left right ihLeft ihRight => exact .pair (ihLeft scopeTyped) (ihRight scopeTyped)
  | app function argument admitted exported ihFunction ihArgument => exact .app (ihFunction scopeTyped) (ihArgument scopeTyped) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit scopeTyped) (by simpa only [ports_extend] using ihBody scopeTyped)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition scopeTyped) (ihYes scopeTyped) (ihNo scopeTyped)
  | perform known admitted operand formed exported ih => exact .perform (port_lookup known) admitted (ih scopeTyped) formed
  | resume known resolved permission operand transition admitted formed ih =>
      have same := scope_resolved scopeTyped known resolved
      subst ticket
      exact .resume (ih scopeTyped) admitted formed
  | discard known resolved permission unprotected closable transition admitted =>
      have same := scope_resolved scopeTyped known resolved
      subst ticket
      exact .discard admitted
  | cleanup callback body admitted exported ihCallback ihBody => exact .cleanup (ihCallback scopeTyped) (ihBody scopeTyped) admitted
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource (ih scopeTyped) (fun identity fresh => CoherentSourceTypes.port_typing (body identity fresh) ticket) formed effectsBound admitted

theorem source_trace (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    Trace before demand after := OwnerSource.source_trace (owner_source source)

theorem source_once (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    demand.Nodup := OwnerPhaseTransitions.trace_nodup (source_trace source)

theorem branch_demands_agree
    (yes : Derives operations policy contracts inside world environment allowed scope before a after result left leftRow)
    (no : Derives operations policy contracts inside world environment allowed scope before b after result right rightRow) :
    left.Perm right := OwnerSource.trace_same_endpoints (source_trace yes) (source_trace no)

theorem value_summary
    (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (isValue : code.IsValue) :
    Summary operations world environment allowed code result [] ∧ before = after ∧ demand = [] ∧ row = [] := by
  induction source with
  | stable summary exported =>
      have empty := value_row summary isValue
      rw [empty, OwnerSource.exportAt, ProtectionResiduals.residual_empty] at exported
      cases Option.some.inj exported
      exact ⟨empty ▸ summary, rfl, rfl, rfl⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, first, leftDemand, leftRow⟩ := ihLeft isValue.1
      obtain ⟨b, second, rightDemand, rightRow⟩ := ihRight isValue.2
      exact ⟨.pair a b, first.trans second, by simp [leftDemand, rightDemand], by simp [leftRow, rightRow]⟩
  | app | bind | branch | perform | resume | discard | cleanup | resource => cases isValue

theorem substitution
    (source : Derives operations policy contracts inside world (environment.extend name input) allowed scope before code after result demand row)
    (replacement : Summary operations world environment allowed value input []) (closed : ClosedValue value) :
    Derives operations policy contracts inside world environment allowed scope before (code.subst name value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CoherentSourceTypes.substitution summary replacement closed) exported
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | app function argument admitted exported => exact .app (substitution function replacement closed) (substitution argument replacement closed) admitted exported
  | bind initializer body =>
      rename_i a middle domain initializerDemand initializerRow parameter b bodyDemand bodyRow
      apply Derives.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no => exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed)
  | perform known admitted operand formed exported => exact .perform known admitted (substitution operand replacement closed) formed exported
  | resume known resolved permission operand transition admitted formed =>
      exact .resume known resolved permission (substitution operand replacement closed) transition admitted formed
  | discard known resolved permission unprotected closable transition admitted => exact .discard known resolved permission unprotected closable transition admitted
  | cleanup callback body admitted exported => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) admitted exported
  | resource initializer body formed effectsBound admitted outward exported =>
      apply Derives.resource (substitution initializer replacement closed) _ formed effectsBound admitted outward exported
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact CoherentSourceTypes.substitution (body identity fresh)
        (value_allowed (summary_world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem bind_summary
    (source : Derives operations policy contracts inside world environment allowed scope before (.bind parameter value body) after result demand row)
    (closed : ClosedValue value) :
    Derives operations policy contracts inside world environment allowed scope before (body.subst parameter value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CoherentSourceTypes.bind_summary summary closed) exported
  | bind initializer body =>
      obtain ⟨replacement, same, emptyDemand, emptyRow⟩ := value_summary initializer closed.1
      subst_vars
      simpa only [List.nil_append] using substitution body replacement closed

theorem beta_summary
    (source : Derives operations policy contracts inside world environment allowed scope before (.app (.lambda parameter body) value) after result demand row)
    (closed : ClosedValue value) :
    Derives operations policy contracts inside world environment allowed .none before (body.subst parameter value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CoherentSourceTypes.beta_summary summary closed) exported
  | app function argument admitted exported =>
      obtain ⟨functionSummary, functionPhase, functionDemand, functionRow⟩ := value_summary function trivial
      obtain ⟨argumentSummary, argumentPhase, argumentDemand, argumentRow⟩ := value_summary argument closed.1
      subst_vars
      have reduced := CoherentSourceTypes.beta_summary (Summary.app functionSummary argumentSummary admitted) closed
      simpa only [List.nil_append] using Derives.stable (policy := policy) (contracts := contracts) (scope := Execution.Scope.none) reduced exported

theorem resume_consumed_rejected
    (source : Derives operations policy contracts inside world environment allowed scope before (.resume binder value) after result demand row)
    (resolved : scope.resolve binder = some owner) (spent : before owner = .consumed) : False :=
  OwnerSource.resume_consumed_rejected (owner_source source) resolved spent

theorem resume_marks_consumed
    (source : Derives operations policy contracts inside world environment allowed scope before (.resume binder value) after result demand row)
    (resolved : scope.resolve binder = some owner) : after owner = .consumed := by
  cases source with
  | stable summary exported => cases summary
  | resume known actual permission operand transition admitted formed =>
      have same := Option.some.inj (actual.symm.trans resolved)
      subst_vars
      exact OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self

theorem sequential_resume_rejected
    (source : Derives operations policy contracts inside world environment allowed scope before
      (.bind parameter (.resume binder first) (.resume binder second)) after result demand row)
    (resolved : scope.resolve binder = some owner) : False := by
  cases source with
  | stable summary exported => cases summary with
      | bind first second => cases first
  | bind first second => exact resume_consumed_rejected second resolved (resume_marks_consumed first resolved)

def Contracts.Extends (before after : Contracts) : Prop :=
  ∀ owner contract, before owner = some contract → after owner = some contract

def Contracts.insert (contracts : Contracts) (owner : Nat) (contract : Contract) : Contracts :=
  fun other => if other = owner then some contract else contracts other

theorem insert_extends (contracts : Contracts) (fresh : contracts owner = none) :
    contracts.Extends (contracts.insert owner contract) := by
  intro other previous known
  by_cases same : other = owner
  · subst other; rw [fresh] at known; cases known
  · simp [Contracts.insert, same, known]

theorem source_world_weaken
    (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (larger : world ⊆ next) :
    Derives operations policy contracts inside next environment allowed scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable (summary_world_weaken summary larger) exported
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted exported ihFunction ihArgument => exact .app ihFunction ihArgument admitted exported
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known admitted operand formed exported ih => exact .perform known admitted ih (ScopedPorts.in_world_mono formed larger) exported
  | resume known resolved permission operand transition admitted formed ih =>
      exact .resume known resolved permission ih transition admitted (ScopedPorts.in_world_mono formed larger)
  | discard known resolved permission unprotected closable transition admitted =>
      exact .discard known resolved permission unprotected closable transition admitted
  | cleanup callback body admitted exported ihCallback ihBody => exact .cleanup ihCallback ihBody admitted exported
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource ih
        (fun identity fresh => summary_world_weaken (body identity (fun member => fresh (larger member)))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member))) exported

theorem source_extension (source : Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (extension : contracts.Extends larger) :
    Derives operations policy larger inside world environment allowed scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary exported
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted exported ihFunction ihArgument => exact .app ihFunction ihArgument admitted exported
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known admitted operand formed exported ih => exact .perform known admitted ih formed exported
  | resume known resolved permission operand transition admitted formed ih =>
      exact .resume (extension _ _ known) resolved permission ih transition admitted formed
  | discard known resolved permission unprotected closable transition admitted =>
      exact .discard (extension _ _ known) resolved permission unprotected closable transition admitted
  | cleanup callback body admitted exported ihCallback ihBody => exact .cleanup ihCallback ihBody admitted exported
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource ih body formed effectsBound admitted outward exported

theorem source_contracts_extension {before after : Contracts} (extension : before.Extends after) :
    OwnerCaptureContracts.Extends before.source after.source := by
  intro owner contract known
  cases found : before owner with
  | none => simp [Contracts.source, found] at known
  | some previous =>
      have same : previous.source = contract := by simpa [Contracts.source, found] using known
      subst contract
      exact source_lookup (extension _ _ found)

theorem port_contracts_extension {before after : Contracts} (extension : before.Extends after) :
    ScopedPorts.EffectExtension before.ports after.ports := by
  intro owner contract known
  cases found : before owner with
  | none => simp [Contracts.ports, found] at known
  | some previous =>
      have same : previous.ports = contract := by simpa [Contracts.ports, found] using known
      subst contract
      exact ports_lookup (extension _ _ found)

/-- The entire ordinary continuation contract, including its two effect lists,
    is shared with the runtime record. This does not authenticate its capture. -/
structure Record where
  annotation : Contract
  runtime : CallableJoint.TicketRecord
  agrees : runtime.joint.contract = annotation.ports

def Record.shapeRecord (record : Record) : CoherentSourceTypes.Record where
  runtime := record.runtime
  source := record.annotation.source
  input := by simpa only [record.agrees, Contract.source, Contract.ports] using value_compatible record.annotation.input
  answer := by simpa only [record.agrees, Contract.source, Contract.ports] using value_compatible record.annotation.answer

abbrev Registry := Nat → Option Record
def Registry.contracts (registry : Registry) : Contracts := fun owner => (registry owner).map Record.annotation
def Registry.runtime (registry : Registry) : CallableJoint.Registry := fun owner => (registry owner).map Record.runtime
def Registry.insert (registry : Registry) (owner : Nat) (record : Record) : Registry :=
  fun other => if other = owner then some record else registry other

theorem registry_ports (registry : Registry) : registry.contracts.ports = registry.runtime.joint.effects := by
  funext owner
  cases found : registry owner with
  | none => simp [Registry.contracts, Contracts.ports, Registry.runtime, CallableJoint.Registry.joint, ScopedPortJoint.Registry.effects, found]
  | some record => simp [Registry.contracts, Contracts.ports, Registry.runtime, CallableJoint.Registry.joint, ScopedPortJoint.Registry.effects, found, record.agrees]

theorem registry_registered (registry : Registry) :
    ∀ owner contract, registry.contracts.source owner = some contract → ∃ record, registry.runtime owner = some record := by
  intro owner contract known
  cases found : registry owner with
  | none => simp [Registry.contracts, Contracts.source, found] at known
  | some record => exact ⟨record.runtime, by simp [Registry.runtime, found]⟩

theorem registry_insert_contracts (registry : Registry) :
    (registry.insert owner record).contracts = registry.contracts.insert owner record.annotation := by
  funext other
  by_cases same : other = owner <;> simp [Registry.insert, Registry.contracts, Contracts.insert, same]

theorem registry_insert_runtime (registry : Registry) :
    (registry.insert owner record).runtime = registry.runtime.insert owner record.runtime := by
  funext other
  by_cases same : other = owner <;> simp [Registry.insert, Registry.runtime, CallableJoint.Registry.insert, same]

theorem registry_extension (registry : Registry) (fresh : registry owner = none) :
    registry.contracts.Extends (registry.insert owner record).contracts ∧
    CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime := by
  rw [registry_insert_contracts, registry_insert_runtime]
  exact ⟨insert_extends registry.contracts (by simp [Registry.contracts, fresh]),
    CallableJoint.registry_insert_extends (by simp [Registry.runtime, fresh])⟩

theorem insertion_retains_both {registry : Registry}
    (source : Derives operations policy registry.contracts inside world environment allowed scope before code after result demand row)
    (scopeTyped : ScopedPorts.EffectScope registry.runtime.joint.effects scope ticket)
    (fresh : registry owner = none) :
    Derives operations policy (registry.insert owner record).contracts inside world environment allowed scope before code after result demand row ∧
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed code result.port := by
  have extension := registry_extension (record := record) registry fresh
  have retained := source_extension source extension.1
  refine ⟨retained, port_typing retained ?_⟩
  apply ScopedPorts.effect_scope_extension (before := registry.contracts.ports)
  · simpa only [registry_ports] using scopeTyped
  · exact port_contracts_extension extension.1

end Owners

namespace Examples

def operations : Operations := fun _ _ => none
def identity : Code := .lambda 0 (.variable 0)
def integerFunction : Value := .function .integer .integer [] []
def higherOrder : Code := .app identity identity

theorem integer_identity : Summary operations [] Environment.empty [] identity integerFunction [] := by
  exact .lambda (.variable (by simp [Environment.extend]) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem higher_order_source : Summary operations [] Environment.empty [] higherOrder integerFunction [] := by
  exact .app (.lambda (.variable (by simp [Environment.extend])
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, integerFunction]))
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, integerFunction]))
    integer_identity (List.nil_subset _)

theorem identity_closed : ClosedValue identity := by
  simp [identity, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]

theorem higher_order_beta : RawStep ⟨higherOrder, .none, .nil⟩ ⟨identity, .none, .nil⟩ [] [] ∧
    Summary operations [] Environment.empty [] identity integerFunction [] := by
  constructor
  · simpa [higherOrder, identity, Code.subst] using
      RawStep.beta 0 (.variable 0) identity .none .nil identity_closed identity_closed
  · simpa only [Code.subst, ↓reduceIte] using beta_summary higher_order_source identity_closed

/-- The same unannotated identity admits different independent instantiations.
    Their existence does not establish that the chosen contracts agree. -/
theorem independent_derivations_need_coherence :
    CallableProtection.Summarizes operations.protection Environment.empty.protection identity
      (.function (.pair .scalar .scalar) (.pair .scalar .scalar) []) [] ∧
    ScopedPorts.Typed operations.ports [] Environment.empty.ports .none [] identity (.function .integer .integer []) ∧
    ¬ Compatible (.function (.pair .scalar .scalar) (.pair .scalar .scalar) []) (.function .integer .integer []) := by
  refine ⟨.lambda (.variable ?_), port_typing integer_identity .none, by decide⟩
  simp [CallableProtection.Environment.extend]

theorem integer_condition_has_protection_summary :
    CallableProtection.Summarizes operations.protection Environment.empty.protection
      (.branch (.integer 0) .unit .unit) .scalar [] :=
  .branch .integer .unit .unit

theorem integer_condition_rejected :
    ¬ Summary operations [] Environment.empty [] (.branch (.integer 0) .unit .unit) output row := by
  intro source
  cases source with
  | branch condition yes no => cases condition

theorem integer_condition_port_rejected :
    ¬ ScopedPorts.Typed operations.ports [] Environment.empty.ports .none [] (.branch (.integer 0) .unit .unit) output := by
  intro source
  cases source with
  | branch condition yes no => cases condition

def waiting : PlainData :=
  ⟨.bind 3 (.app (.variable 3) (.integer 17)), .none,
    .function .integer .integer [] [], .integer, [], by decide⟩

theorem waiting_source : ContextSummary operations [] Environment.empty [] waiting.context integerFunction .integer [] := by
  exact .bind (.app (.variable (by simp [Environment.extend, integerFunction])
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) .integer (List.nil_subset _))

theorem waiting_frame : ScopedPorts.FrameTyped operations.ports (fun _ => none) [] (.plain waiting) ∧
    OwnerSource.FrameSource operations.protection policy contracts [] (.plain waiting)
      phases integerFunction.protection phases Value.integer.protection [] [] :=
  plain_frame waiting_source rfl rfl .none rfl

theorem wrong_result_metadata_rejected : Value.integer.port ≠ ScopedPorts.eraseType .unit := by decide

def send : Instance := .user 81 []
def callbackOperations : Operations := fun effect operation =>
  if effect = send ∧ operation = 0 then some (.unit, integerFunction) else none

theorem callback_operation_shared :
    checkOperation (callbackOperations.protection send 0) (callbackOperations.ports send 0) = true :=
  shared_operation_check callbackOperations send 0

theorem operation_shape_mismatch_rejected :
    checkOperation (some (.scalar, integerFunction.protection)) (some (.unit, .integer)) = false := by decide

theorem missing_operation_rejected :
    checkOperation (some (.scalar, .scalar)) none = false ∧
    checkOperation none (some (.unit, .unit)) = false := by decide

theorem shape_checks_do_not_check_latent_effects :
    checkCompatible integerFunction.protection (.function .integer .integer [send]) = true := by decide

theorem shape_checks_do_not_distinguish_atoms :
    checkCompatible Value.integer.protection Value.boolean.port = true := by decide

end Examples

namespace OwnerExamples
open Owners
open OwnerPhaseTransitions (available empty)

def operations : Operations := fun _ _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def contract : Owners.Contract := ⟨.integer, .boolean, false, [], [], [], some [], [], []⟩
def record : Owners.Record :=
  ⟨contract, ⟨⟨contract.ports, ⟨true, true⟩⟩, ⟨.storage [], .storage []⟩, ⟨[], rfl, rfl⟩⟩, rfl⟩
def registry : Owners.Registry := fun owner => if owner = 19 then some record else none

theorem known : registry.contracts 19 = some contract := by simp [Owners.Registry.contracts, registry, record]

theorem scope_typed : ScopedPorts.EffectScope registry.contracts.ports (.ticket 7 19) (.bound 7 .integer .boolean [] []) :=
  .bound (Owners.ports_lookup known)

theorem consumed : OwnerPhaseTransitions.Trace (available [19]) [19] empty :=
  OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide)

theorem resume_source : Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
    (available [19]) (.resume 7 (.integer 17)) empty .boolean [19] [] := by
  exact .resume known rfl rfl (.stable (row := []) .integer rfl) consumed (List.nil_subset _) (List.nil_subset _)

theorem discard_source : Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
    (available [19]) (.discard 7) empty .unit [19] [] :=
  .discard known rfl rfl rfl rfl consumed (List.nil_subset _)

theorem resume_ports : ScopedPorts.Typed operations.ports [] Environment.empty.ports (.bound 7 .integer .boolean [] []) []
    (.resume 7 (.integer 17)) .boolean := Owners.port_typing resume_source scope_typed

theorem wrong_resume_operand_rejected :
    ¬ Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
      before (.resume 7 (.boolean true)) after result demand row := by
  intro source
  have typed := Owners.port_typing source scope_typed
  generalize endpoint : result.port = output at typed
  cases typed with
  | resume operand admitted formed => cases operand

theorem spent_resume_rejected :
    ¬ Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
      empty (.resume 7 (.integer 17)) after result demand row := by
  intro source
  exact Owners.resume_consumed_rejected source rfl rfl

theorem twice_resume_rejected :
    ¬ Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
      before (.bind 2 (.resume 7 (.integer 17)) (.resume 7 (.integer 18))) after result demand row := by
  intro source
  exact Owners.sequential_resume_rejected source rfl

def alternative : Code := .branch (.boolean true) (.resume 7 (.integer 17)) (.bind 2 (.discard 7) (.boolean false))

theorem alternative_source : Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
    (available [19]) alternative empty .boolean [19] [] := by
  exact .branch (.stable .boolean rfl) resume_source (.bind discard_source (.stable .boolean rfl))

theorem alternative_uses_once : [19].Nodup := Owners.source_once alternative_source

theorem substitution_keeps_resume : Owners.Derives operations policy registry.contracts [] [] Environment.empty [] (.ticket 7 19)
    (available [19]) (.resume 7 (.integer 17)) empty .boolean [19] [] := by
  have source : Owners.Derives operations policy registry.contracts [] [] (Environment.empty.extend 4 .integer) [] (.ticket 7 19)
      (available [19]) (.resume 7 (.variable 4)) empty .boolean [19] [] :=
    .resume known rfl rfl (.stable (row := []) (.variable (by simp [Environment.extend, contract]) (List.nil_subset _)) rfl)
      consumed (List.nil_subset _) (List.nil_subset _)
  have closed : ClosedValue (.integer 17) := by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
  simpa only [Code.subst, ↓reduceIte] using Owners.substitution source Summary.integer closed

theorem insertion_keeps_source_and_ports :
    Owners.Derives operations policy (registry.insert 23 record).contracts [] [] Environment.empty [] (.ticket 7 19)
      (available [19]) (.resume 7 (.integer 17)) empty .boolean [19] [] ∧
    ScopedPorts.Typed operations.ports [] Environment.empty.ports (.bound 7 .integer .boolean [] []) []
      (.resume 7 (.integer 17)) .boolean := by
  apply Owners.insertion_retains_both resume_source
  · simpa only [← Owners.registry_ports] using scope_typed
  · simp [registry]

def protectedContract : Owners.Contract := { contract with held := true }
def protectedContracts : Owners.Contracts := fun owner => if owner = 19 then some protectedContract else none

theorem protected_discard_rejected :
    ¬ Owners.Derives operations policy protectedContracts [] [] Environment.empty [] (.ticket 7 19)
      before (.discard 7) after result demand row := by
  intro source
  cases source with
  | stable summary exported => cases summary
  | discard known resolved permission unprotected closable transition admitted =>
      simp [Execution.Scope.resolve] at resolved
      subst_vars
      simp [protectedContracts] at known
      subst_vars
      cases unprotected

theorem protected_ports_alone_allow_discard :
    ScopedPorts.Typed operations.ports [] Environment.empty.ports (.bound 7 .integer .boolean [] []) [] (.discard 7) .unit :=
  .discard (List.nil_subset _)

end OwnerExamples

end Ash.OneShot.CoherentSourceTypes

#print axioms Ash.OneShot.CoherentSourceTypes.check_compatible_iff
#print axioms Ash.OneShot.CoherentSourceTypes.value_compatible
#print axioms Ash.OneShot.CoherentSourceTypes.ports_extend
#print axioms Ash.OneShot.CoherentSourceTypes.protection_extend
#print axioms Ash.OneShot.CoherentSourceTypes.port_lookup
#print axioms Ash.OneShot.CoherentSourceTypes.protection_lookup
#print axioms Ash.OneShot.CoherentSourceTypes.protection_summary
#print axioms Ash.OneShot.CoherentSourceTypes.port_typing
#print axioms Ash.OneShot.CoherentSourceTypes.owner_source
#print axioms Ash.OneShot.CoherentSourceTypes.value_row
#print axioms Ash.OneShot.CoherentSourceTypes.agree_left
#print axioms Ash.OneShot.CoherentSourceTypes.agree_right
#print axioms Ash.OneShot.CoherentSourceTypes.agree_extend
#print axioms Ash.OneShot.CoherentSourceTypes.environment_congr
#print axioms Ash.OneShot.CoherentSourceTypes.closed_value_environment
#print axioms Ash.OneShot.CoherentSourceTypes.value_allowed
#print axioms Ash.OneShot.CoherentSourceTypes.allowed_mono
#print axioms Ash.OneShot.CoherentSourceTypes.Environment.extend_shadow
#print axioms Ash.OneShot.CoherentSourceTypes.Environment.extend_commute
#print axioms Ash.OneShot.CoherentSourceTypes.substitution
#print axioms Ash.OneShot.CoherentSourceTypes.beta_summary
#print axioms Ash.OneShot.CoherentSourceTypes.bind_summary
#print axioms Ash.OneShot.CoherentSourceTypes.context_plug
#print axioms Ash.OneShot.CoherentSourceTypes.context_ports
#print axioms Ash.OneShot.CoherentSourceTypes.focus_decompose
#print axioms Ash.OneShot.CoherentSourceTypes.export_append_split
#print axioms Ash.OneShot.CoherentSourceTypes.context_source
#print axioms Ash.OneShot.CoherentSourceTypes.plain_frame
#print axioms Ash.OneShot.CoherentSourceTypes.checked_operation
#print axioms Ash.OneShot.CoherentSourceTypes.checked_operation_domain
#print axioms Ash.OneShot.CoherentSourceTypes.shared_operation_check
#print axioms Ash.OneShot.CoherentSourceTypes.request_output_compatible
#print axioms Ash.OneShot.CoherentSourceTypes.registered
#print axioms Ash.OneShot.CoherentSourceTypes.registry_shapes
#print axioms Ash.OneShot.CoherentSourceTypes.insert_runtime
#print axioms Ash.OneShot.CoherentSourceTypes.insert_source
#print axioms Ash.OneShot.CoherentSourceTypes.insert_retains_projections
#print axioms Ash.OneShot.CoherentSourceTypes.capture_input_compatible
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_lookup
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.ports_lookup
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.scope_resolved
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.owner_source
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.port_typing
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_trace
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_once
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.branch_demands_agree
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.value_summary
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.substitution
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.bind_summary
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.beta_summary
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.resume_consumed_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.resume_marks_consumed
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.sequential_resume_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.insert_extends
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_extension
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_contracts_extension
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.port_contracts_extension
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.registry_ports
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.registry_registered
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.registry_insert_contracts
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.registry_insert_runtime
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.registry_extension
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.insertion_retains_both
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.integer_identity
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.higher_order_source
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.identity_closed
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.higher_order_beta
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.independent_derivations_need_coherence
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.integer_condition_has_protection_summary
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.integer_condition_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.integer_condition_port_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.waiting_source
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.waiting_frame
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.wrong_result_metadata_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.callback_operation_shared
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.operation_shape_mismatch_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.missing_operation_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.shape_checks_do_not_check_latent_effects
#print axioms Ash.OneShot.CoherentSourceTypes.Examples.shape_checks_do_not_distinguish_atoms
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.known
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.scope_typed
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.consumed
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.resume_source
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.discard_source
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.resume_ports
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.wrong_resume_operand_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.spent_resume_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.twice_resume_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.alternative_source
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.alternative_uses_once
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.substitution_keeps_resume
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.insertion_keeps_source_and_ports
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.protected_discard_rejected
#print axioms Ash.OneShot.CoherentSourceTypes.OwnerExamples.protected_ports_alone_allow_discard

#print axioms Ash.OneShot.CoherentSourceTypes.summary_world_weaken
#print axioms Ash.OneShot.CoherentSourceTypes.Owners.source_world_weaken
