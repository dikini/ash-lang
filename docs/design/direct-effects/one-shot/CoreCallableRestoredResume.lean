import CoreCallableRestoredChecking
import CoreCallableAllowedTransport

/-! The actual resume operand and owner selection for the experimental callable
companion. Restored support, checked certificates and accounting are reconstructed at
the same actual physical and contextual cut. -/
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- The owner, contract and operand authentication come from one current resume
source. No independently selected same-port callable is used. -/
theorem Authenticated.resume_operand
    {source : IndexedSource registry outward owners world allowed scope environment
      (.resume binder operand) result demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver) :
    ∃ owner, ∃ contract : OwnerContract,
    ∃ operandDemand, ∃ operandRequirements : Requirements operandDemand,
    ∃ operandDependencies : Dependencies, ∃ operandPlan : Plan operandDependencies,
    ∃ operandRows : Rows (signature operandPlan),
    ∃ operandSource : IndexedSource registry outward owners world allowed scope environment
      operand contract.input operandDemand operandRequirements operandPlan operandRows,
      owners owner = some contract ∧ scope.resolve binder = some owner ∧
      result = contract.answer ∧ Authenticated registry outward operandSource lexical receiver := by
  cases authenticated with
  | checked current hereditary =>
    cases hereditary with
    | resume operandAuthentication =>
      exact ⟨_, _, _, _, _, _, _, _, by assumption, by assumption, rfl, operandAuthentication⟩

/-- Value normalization removes only the operand's immediate computation rows;
the same full input contract and private lambda evidence remain. -/
theorem Authenticated.resume_operand_summary
    {source : IndexedSource registry outward owners world allowed scope environment
      (.resume binder operand) result demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (closed : ClosedValue operand) :
    ∃ owner, ∃ contract : OwnerContract,
    ∃ operandSource : IndexedSource registry outward owners world allowed scope environment
      operand contract.input [] (.request [] []) .pure Rows.pure,
      owners owner = some contract ∧ scope.resolve binder = some owner ∧
      result = contract.answer ∧ Authenticated registry outward operandSource lexical receiver := by
  obtain ⟨owner, contract, _, _, _, _, _, operandSource, known, resolved, answer, operandAuthentication⟩ :=
    authenticated.resume_operand
  exact ⟨owner, contract, operandSource.value_summary closed.1, known, resolved, answer,
    operandAuthentication.value_summary closed.1⟩
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.resume_operand
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.resume_operand_summary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (OwnerContract)
open CoreCallableContractAdmission (Authenticated IndexedSource Source)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- Current source inversion and silent value normalization select the same
resume primitive in checking and accounting. -/
theorem Site.resume_primitives
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) runtimeScope stack result final context root)
    (closed : ClosedValue operand) :
    ∃ owner, ∃ contract : OwnerContract,
      globals.owners owner = some contract ∧ runtimeScope.resolve binder = some owner ∧
      result = contract.answer ∧
    ∃ operandSource : Source globals outward world allowed runtimeScope Environment.empty operand
      contract.input [] (.request [] []) .pure Rows.pure,
    ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
      lexical.environment = ScopedPorts.Support.empty ∧
      Authenticated globals.registry outward operandSource lexical (actualReceiver world receiving ambient) ∧
    ∃ primitive : SourceAdmission.Code outward actions budget phases world installations
      (Rows.invoke (key := ⟨owner, .resume⟩)) context,
      InstallationSupport.CodeChecked ambient outward primitive ∧
      Accounting.Run world installations (Rows.invoke (key := ⟨owner, .resume⟩)) context root := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := current.authentication
  cases authenticated with
  | checked actualSupport hereditary =>
    cases hereditary with
    | resume operandAuthentication =>
      rename_i contract operandDemand operandReq operandDependencies operandPlan operandRows owner known formed admitted permission resolved operandSource
      cases certificate with
      | sequence operandCertificate primitive =>
        cases certificateChecked with
        | sequence operandChecked primitiveChecked =>
          refine ⟨_, _, by assumption, by assumption, rfl, _, lexical, sameEnvironment,
            operandAuthentication.value_summary closed.1, primitive, primitiveChecked, ?_⟩
          exact (Accounting.silent_prefix_iff (Source.value_silent operandSource closed.1) _ _).mp accounting
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.resume_primitives

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- A contextual active-owner cut selects the same physical live owner and its
full input/answer contract from the current saved-source spine. -/
theorem Pending.owner_stack
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : Context hints}
    (pending : Pending globals outward world allowed ambient stack input output context)
    (known : globals.owners owner = some contract)
    (located : SourceDependencyCapture.OwnerCut owner receiving selected) :
    ∃ (front captured tail : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
      stack = front.append (.live owner inputType answerType captured caller tail) ∧
      ScopedPorts.eraseType inputType = contract.input.port ∧
      ScopedPorts.eraseType answerType = contract.answer.port := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {tail} {tailScope} {_} {_} _ _ =>
      ∀ selected, SourceDependencyCapture.OwnerCut owner tailScope selected →
      ∃ (front captured rest : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
        tail = front.append (.live owner inputType answerType captured caller rest) ∧
        ScopedPorts.eraseType inputType = contract.input.port ∧
        ScopedPorts.eraseType answerType = contract.answer.port)
    generalizing selected with
  | nil => cases located
  | plain frame received accepts tail ih =>
      cases located with
      | plain next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih next
          exact ⟨.push (.plain _) front, cap, rest, q, a, caller, congrArg (Stack.push _) same,
            inputAnnotation, answerAnnotation⟩
  | handler frame admitted tail ih =>
      cases located with
      | handler next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih next
          exact ⟨.push (.handler _) front, cap, rest, q, a, caller, congrArg (Stack.push _) same,
            inputAnnotation, answerAnnotation⟩
  | handlerView frame admitted entered bounded tail ih =>
      cases located with
      | handler next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih next
          exact ⟨.push (.handler _) front, cap, rest, q, a, caller, congrArg (Stack.push _) same,
            inputAnnotation, answerAnnotation⟩
  | cell issued annotation tail ih =>
      cases located with
      | cell next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih next
          exact ⟨.push (.cell _ _ _ _) front, cap, rest, q, a, caller, congrArg (Stack.push _) same,
            inputAnnotation, answerAnnotation⟩
  | spent actualKnown answerSame annotation tail ih =>
      cases located with
      | spent next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih next
          exact ⟨.spent _ _ _ front, cap, rest, q, a, caller, congrArg (Stack.spent _ _ _) same,
            inputAnnotation, answerAnnotation⟩
  | live actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
      cases located with
      | hit =>
          have sameContract := Option.some.inj (actualKnown.symm.trans known)
          cases sameContract
          exact ⟨.nil, _, _, _, _, _, rfl, by simpa only [inputSame] using inputAnnotation,
            by simpa only [answerSame] using answerAnnotation⟩
      | live different next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ihTail next
          exact ⟨.live _ _ _ _ _ front, cap, rest, q, a, caller, congrArg (Stack.live _ _ _ _ _) same,
            inputAnnotation, answerAnnotation⟩
  | capture actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
      cases located with
      | hit =>
          have sameContract := Option.some.inj (actualKnown.symm.trans known)
          cases sameContract
          exact ⟨.nil, _, _, _, _, _, rfl, by simpa only [inputSame] using inputAnnotation,
            by simpa only [answerSame] using answerAnnotation⟩
      | live different next =>
          obtain ⟨front, cap, rest, q, a, caller, same, inputAnnotation, answerAnnotation⟩ := ih _ next
          exact ⟨.live _ _ _ _ _ front, cap, rest, q, a, caller, congrArg (Stack.live _ _ _ _ _) same,
            inputAnnotation, answerAnnotation⟩
  | here frame admitted tail ih => apply ih; assumption
  | hereView frame admitted entered bounded tail ih => apply ih; assumption
  | plainPath saved received accepts selected ih => apply ih; assumption
  | handlerMiss saved admitted miss selected ih => apply ih; assumption
  | handlerMissView saved admitted entered bounded miss selected ih => apply ih; assumption
  | cellPath issued annotation selected ih => apply ih; assumption
  | spentPath actualKnown answerSame annotation selected ih => apply ih; assumption
  | liveTail actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => apply ih; assumption
  | captureTail actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih => apply ih; assumption
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.owner_stack

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- The current callable site supplies one actual Core resume step with the same
owner and full input/answer ports. This is execution evidence, not yet a restored
successor source invariant. -/
theorem Site.resume_raw
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) runtimeScope stack result final context root)
    (closed : ClosedValue operand) :
    ∃ owner, ∃ contract : OwnerContract,
    ∃ (front captured tail : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
      globals.owners owner = some contract ∧ runtimeScope.resolve binder = some owner ∧
      result = contract.answer ∧
      stack = front.append (.live owner inputType answerType captured caller tail) ∧
      ScopedPorts.eraseType inputType = contract.input.port ∧
      ScopedPorts.eraseType answerType = contract.answer.port ∧
      RawStep ⟨.resume binder operand, runtimeScope, stack⟩
        ⟨operand, runtimeScope, captured.append (front.append (.spent owner answerType caller tail))⟩
        [] [.ticket owner] := by
  obtain ⟨owner, contract, known, resolved, answer, operandSource, lexical, empty, operandAuthentication,
    primitive, primitiveChecked, run⟩ := site.resume_primitives closed
  cases run with
  | resume located waiting =>
      obtain ⟨front, captured, tail, inputType, answerType, caller, stackEq, inputAnnotation, answerAnnotation⟩ :=
        site.pending.owner_stack known located
      refine ⟨owner, contract, front, captured, tail, inputType, answerType, caller,
        known, resolved, answer, stackEq, inputAnnotation, answerAnnotation, ?_⟩
      rw [stackEq]
      exact .resume binder owner runtimeScope caller inputType answerType front captured tail operand closed resolved
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.resume_raw

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- A typed active spine ending at its actual current suffix. Every frame keeps
its original recursive source; the selected suffix is never an independently
chosen restoration source. -/
inductive ResumePrefix (globals : CoreCallableContractAdmission.Globals) (outward : List Instance)
    (world ambient : List Nat) (baseAllowed : List Instance) (baseStack : Stack)
    (baseInput final : Contract) (base : Packed) :
    List Instance → Stack → Contract → Packed → Prop where
  | nil (tail : Pending globals outward world baseAllowed ambient baseStack baseInput final base.context) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base baseAllowed .nil baseInput base
  | plain {tail : Packed}
      (frame : FrameSource globals outward world allowed data input middle parameter body demand requirements plan rows
        inputBound bodyBound (actualReceiver world tail.scope ambient))
      (received : bodyBound ⊆ tail.scope.visibleResources ++ ambient)
      (accepts : ∀ identity, identity ∈ world → identity ∈ tail.scope.visibleResources ++ ambient → identity ∈ inputBound)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front middle tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed
        (.push (.plain data) front) input (Context.plain rows tail.context).pack
  | handler {tail : Packed}
      (frame : HandlerSource globals outward world residual data answer table plans rows (actualReceiver world tail.scope ambient))
      (admitted : residual ⊆ outsideAllowed)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base outsideAllowed front answer tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base (data.effectInst :: residual)
        (.push (.handler data) front) answer
        (Context.handler (effect := data.effectInst) (table := table) data.activation rows tail.context).pack
  | handlerView {tail : Packed}
      (frame : HandlerSource globals outward world residual data answer table plans rows (actualReceiver world tail.scope ambient))
      (admitted : residual ⊆ outsideAllowed)
      (entered : (data.effectInst :: residual) ⊆ beforeAllowed)
      (bounded : beforeAllowed ⊆ (data.effectInst :: outsideAllowed))
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base outsideAllowed front answer tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base beforeAllowed
        (.push (.handler data) front) answer
        (Context.handler (effect := data.effectInst) (table := table) data.activation rows tail.context).pack
  | live {captured tail : Packed}
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captured.scope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType inputType = input.port)
      (answerAnnotation : ScopedPorts.eraseType answerType = answer.port)
      (saved : Pending globals outward world savedAllowed (tail.scope.visibleResources ++ ambient)
        cap input answer captured.context)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base tailAllowed front answer tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed
        (.live owner inputType answerType cap caller front) answer
        (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context tail.context).pack
  | capture {captured tail whole : Packed}
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captured.scope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType inputType = input.port)
      (answerAnnotation : ScopedPorts.eraseType handler.answer = answer.port)
      (frame : HandlerSource globals outward world residual handler answer table plans rows (actualReceiver world tail.scope ambient))
      (installed : SelectedPending globals outward world
        (beforeAllowed := beforeAllowed) (whole := original) (input := input) (output := final)
        (wholeContext := whole.context) (tailAllowed := tailAllowed) (tail := front.append baseStack)
        (outside := tail.context) frame)
      (physical : HandlerCut handler.effectInst original cap (front.append baseStack) handler)
      (contextual : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut handler.effectInst operation whole.context captured.context tail.context offered modes)
      (terminal : TerminalHandler handler.effectInst handler.activation rows captured.context)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base tailAllowed front answer tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base residual
        (.live owner inputType handler.answer cap handler.scope front) answer
        (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context tail.context).pack
  | spent {tail : Packed}
      (known : globals.owners owner = some contract) (answerSame : contract.answer = input)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base tailAllowed front input tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed
        (.spent owner answer caller front) input (Context.spent (owner := owner) tail.context).pack
  | cell {tail : Packed} (issued : identity ∈ world)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (next : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input tail) :
      ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed
        (.push (.cell identity payload caller answer) front) input (Context.cell (identity := identity) tail.context).pack

/-- Forgetting the selected endpoint recovers the actual current pending source
on precisely the original full physical and decorated contextual spine. -/
theorem ResumePrefix.before
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole) :
    Pending globals outward world allowed ambient (front.append baseStack) input final whole.context := by
  induction spine with
  | nil tail => exact tail
  | plain frame received accepts next ih => exact .plain frame received accepts ih
  | handler frame admitted next ih => exact .handler frame admitted ih
  | handlerView frame admitted entered bounded next ih => exact .handlerView frame admitted entered bounded ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih =>
      exact .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ih
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih =>
      exact .capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal
  | spent known answerSame annotation next ih => exact .spent known answerSame annotation ih
  | cell issued annotation next ih => exact .cell issued annotation ih
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.before

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract)
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

private def plainPacked
    (_frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver)
    (tail : Packed) : Packed := (Context.plain rows tail.context).pack

private def handlerPacked
    (_frame : HandlerSource globals outward world residual data answer table plans rows receiver)
    (tail : Packed) : Packed :=
  (Context.handler (effect := data.effectInst) (table := table) data.activation rows tail.context).pack

private def livePacked
    {globals : CoreCallableContractAdmission.Globals} {owner : Nat} {contract : CoreCallableContractRegistries.OwnerContract}
    (_known : globals.owners owner = some contract) (_resumeSame : contract.resumeDemand = savedDemand)
    (captured tail : Packed) : Packed :=
  (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context tail.context).pack

private def spentPacked
    {globals : CoreCallableContractAdmission.Globals} {owner : Nat} {contract : CoreCallableContractRegistries.OwnerContract}
    (_known : globals.owners owner = some contract) (tail : Packed) : Packed :=
  (Context.spent (owner := owner) tail.context).pack

private def cellPacked {world : List Nat} {identity : Nat} (_issued : identity ∈ world) (tail : Packed) : Packed :=
  (Context.cell (identity := identity) tail.context).pack

/-- The selected owner retains its whole current source boundary as the base of
one typed prefix. The endpoint's private saved source remains in that base. -/
def ResumePrefixAt (globals : CoreCallableContractAdmission.Globals) (outward : List Instance)
    (world : List Nat) (allowed : List Instance) (ambient : List Nat) (stack : Stack)
    (input final : Contract) (whole : Packed) (owner : Nat) (contract : OwnerContract)
    (selected : SourceDependencyCapture.OwnerSelection) : Prop :=
  ∃ baseAllowed, ∃ (front cap tail : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
  ∃ savedDemand, ∃ (captured outside before : Packed),
    selected.front = before.scope ∧ selected.captured = captured.scope ∧ selected.tail = outside.scope ∧
    whole = (before.context.append
      (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context)).pack ∧
    stack = front.append (.live owner inputType answerType cap caller tail) ∧
    ScopedPorts.eraseType inputType = contract.input.port ∧
    ScopedPorts.eraseType answerType = contract.answer.port ∧
    ResumePrefix globals outward world ambient baseAllowed (.live owner inputType answerType cap caller tail)
      contract.answer final
      (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context).pack
      allowed front input whole

private def pendingPacked
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (_pending : Pending globals outward world allowed ambient stack input output context) : Packed := context.pack

private def terminalPacked
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (_terminal : TerminalHandler effect activation rows context) : Packed := context.pack

private def cutWholePacked
    {wholeScope capturedScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {capturedHints : SourceDependencyChecks.Lexical.ReturnHints capturedScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context capturedHints} {tail : Context tailHints}
    (_cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation whole captured tail offered modes) : Packed := whole.pack

/-- Current source and its active contextual cut jointly select the full typed
physical prefix. Every private source and installed family is retained. -/
theorem Pending.resume_prefix
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : Context hints}
    (pending : Pending globals outward world allowed ambient stack input output context)
    (known : globals.owners owner = some contract)
    (located : SourceDependencyCapture.OwnerCut owner receiving selected) :
    ResumePrefixAt globals outward world allowed ambient stack input output context.pack owner contract selected := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {ambient} {_} {_} {output} {_} {_} {_} {_} {_} {input} {_} {_} {_} {_} {allowed} {tail} {_} {_} {outside} _ _ =>
      ∀ selected, SourceDependencyCapture.OwnerCut owner outside.pack.scope selected →
      ResumePrefixAt globals outward world allowed ambient tail input output outside.pack owner contract selected)
    generalizing selected with
  | nil => cases located
  | plain frame received accepts tail ih =>
      cases located with
      | plain next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, inputAnnotation, answerAnnotation, spine⟩ := ih next
          exact ⟨baseAllowed, .push (.plain _) front, cap, rest, q, a, caller, savedDemand, captured, outside, plainPacked frame before,
            (by simpa only [plainPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.plain _) scopeFront), scopeCap, scopeTail,
            (by simpa only [plainPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (plainPacked frame) contextEq), congrArg (Stack.push _) same, inputAnnotation, answerAnnotation,
            ResumePrefix.plain frame received accepts spine⟩
  | handler frame admitted tail ih =>
      cases located with
      | handler next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, inputAnnotation, answerAnnotation, spine⟩ := ih next
          exact ⟨baseAllowed, .push (.handler _) front, cap, rest, q, a, caller, savedDemand, captured, outside, handlerPacked frame before,
            (by simpa only [handlerPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.handler _ _ _) scopeFront), scopeCap, scopeTail,
            (by simpa only [handlerPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (handlerPacked frame) contextEq), congrArg (Stack.push _) same, inputAnnotation, answerAnnotation,
            ResumePrefix.handler frame admitted spine⟩
  | handlerView frame admitted entered bounded tail ih =>
      cases located with
      | handler next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, inputAnnotation, answerAnnotation, spine⟩ := ih next
          exact ⟨baseAllowed, .push (.handler _) front, cap, rest, q, a, caller, savedDemand, captured, outside, handlerPacked frame before,
            (by simpa only [handlerPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.handler _ _ _) scopeFront), scopeCap, scopeTail,
            (by simpa only [handlerPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (handlerPacked frame) contextEq), congrArg (Stack.push _) same, inputAnnotation, answerAnnotation,
            ResumePrefix.handlerView frame admitted entered bounded spine⟩
  | cell issued annotation tail ih =>
      cases located with
      | cell next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, inputAnnotation, answerAnnotation, spine⟩ := ih next
          exact ⟨baseAllowed, .push (.cell _ _ _ _) front, cap, rest, q, a, caller, savedDemand, captured, outside, cellPacked issued before,
            (by simpa only [cellPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.cell _) scopeFront), scopeCap, scopeTail,
            (by simpa only [cellPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (cellPacked issued) contextEq), congrArg (Stack.push _) same, inputAnnotation, answerAnnotation,
            ResumePrefix.cell issued annotation spine⟩
  | spent actualKnown answerSame annotation tail ih =>
      cases located with
      | spent next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, inputAnnotation, answerAnnotation, spine⟩ := ih next
          exact ⟨baseAllowed, .spent _ _ _ front, cap, rest, q, a, caller, savedDemand, captured, outside, spentPacked actualKnown before,
            (by simpa only [spentPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.spent _) scopeFront), scopeCap, scopeTail,
            (by simpa only [spentPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (spentPacked actualKnown) contextEq), congrArg (Stack.spent _ _ _) same, inputAnnotation, answerAnnotation,
            ResumePrefix.spent actualKnown answerSame annotation spine⟩
  | live actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
      cases located with
      | hit =>
          have sameContract := Option.some.inj (actualKnown.symm.trans known)
          cases sameContract
          cases inputSame
          cases answerSame
          exact ⟨_, .nil, _, _, _, _, _, _, pendingPacked saved, pendingPacked tail, Context.nil.pack, rfl, rfl, rfl, rfl, rfl, inputAnnotation, answerAnnotation,
            ResumePrefix.nil (.live actualKnown rfl rfl heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail)⟩
      | live different next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, qAnnotation, aAnnotation, spine⟩ := ihTail next
          exact ⟨baseAllowed, .live _ _ _ _ _ front, cap, rest, q, a, caller, savedDemand, captured, outside, livePacked actualKnown resumeSame (pendingPacked saved) before,
            (by simpa only [livePacked, pendingPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.live _ _) scopeFront), scopeCap, scopeTail,
            (by simpa only [livePacked, pendingPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (livePacked actualKnown resumeSame (pendingPacked saved)) contextEq), congrArg (Stack.live _ _ _ _ _) same, qAnnotation, aAnnotation,
            ResumePrefix.live (captured := pendingPacked saved) actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved spine⟩
  | capture actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
      cases located with
      | hit =>
          have sameContract := Option.some.inj (actualKnown.symm.trans known)
          cases sameContract
          cases inputSame
          cases answerSame
          exact ⟨_, .nil, _, _, _, _, _, _, terminalPacked terminal, pendingPacked installed.outside, Context.nil.pack, rfl, rfl, rfl, rfl, rfl, inputAnnotation, answerAnnotation,
            ResumePrefix.nil (.capture actualKnown rfl rfl heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal)⟩
      | live different next =>
          obtain ⟨baseAllowed, front, cap, rest, q, a, caller, savedDemand, captured, outside, before,
            scopeFront, scopeCap, scopeTail, contextEq, same, qAnnotation, aAnnotation, spine⟩ := ih _ next
          cases same
          exact ⟨baseAllowed, .live _ _ _ _ _ front, cap, rest, q, a, caller, savedDemand, captured, outside, livePacked actualKnown resumeSame (terminalPacked terminal) before,
            (by simpa only [livePacked, terminalPacked, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (SourceDependencyCapture.Scope.live _ _) scopeFront), scopeCap, scopeTail,
            (by simpa only [livePacked, terminalPacked, Context.append, Context.pack, SourceDependencyCapture.OwnerSelection.prepend, SourceDependencyCapture.Scope.append, SourceDependencyChecks.Lexical.ReturnHints.append] using congrArg (livePacked actualKnown resumeSame (terminalPacked terminal)) contextEq), rfl, qAnnotation, aAnnotation,
            ResumePrefix.capture (captured := terminalPacked terminal) (whole := cutWholePacked contextual) actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal spine⟩
  | here frame admitted tail ih => apply ih; assumption
  | hereView frame admitted entered bounded tail ih => apply ih; assumption
  | plainPath saved received accepts selected ih => apply ih; assumption
  | handlerMiss saved admitted miss selected ih => apply ih; assumption
  | handlerMissView saved admitted entered bounded miss selected ih => apply ih; assumption
  | cellPath issued annotation selected ih => apply ih; assumption
  | spentPath actualKnown answerSame annotation selected ih => apply ih; assumption
  | liveTail actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => apply ih; assumption
  | captureTail actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih => apply ih; assumption
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.resume_prefix

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- The base is the original source endpoint retained by prefix selection. -/
theorem ResumePrefix.base_source
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole) :
    Pending globals outward world baseAllowed ambient baseStack baseInput final base.context := by
  induction spine with
  | nil tail => exact tail
  | plain frame received accepts next ih => exact ih
  | handler frame admitted next ih => exact ih
  | handlerView frame admitted entered bounded next ih => exact ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih => exact ih
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih => exact ih
  | spent known answerSame annotation next ih => exact ih
  | cell issued annotation next ih => exact ih

/-- The typed prefix determines the full decorated contextual split as well as
its physical front. Every dormant capture and saved row remains present. -/
theorem ResumePrefix.decomposition
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole) :
    ∃ prefixContext : Packed, whole = (prefixContext.context.append base.context).pack := by
  induction spine with
  | nil tail => exact ⟨Context.nil.pack, rfl⟩
  | plain frame received accepts next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨plainPacked frame before, rfl⟩
  | handler frame admitted next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨handlerPacked frame before, rfl⟩
  | handlerView frame admitted entered bounded next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨handlerPacked frame before, rfl⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨livePacked known resumeSame (pendingPacked saved) before, rfl⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨livePacked known resumeSame (terminalPacked terminal) before, rfl⟩
  | spent known answerSame annotation next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨spentPacked known before, rfl⟩
  | cell issued annotation next ih =>
      obtain ⟨before, rfl⟩ := ih
      exact ⟨cellPacked issued before, rfl⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.base_source
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.decomposition

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- The current selected installation exposes its actual typed prefix ending
at the same full handler source. The endpoint retains its original outside
source; no replacement saved source is chosen. -/
theorem SelectedPending.handler_prefix
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame) :
    ∃ endpointAllowed : List Instance, ∃ front : Stack,
      whole = front.append (.push (.handler handler) tail) ∧
      (handler.effectInst :: residual) ⊆ endpointAllowed ∧
      endpointAllowed ⊆ (handler.effectInst :: tailAllowed) ∧
      ResumePrefix globals outward world ambient endpointAllowed
        (.push (.handler handler) tail) answer output
        (handlerPacked frame outside.pack) beforeAllowed front input wholeContext.pack := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True) with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih =>
      exact ⟨_, .nil, rfl, List.Subset.refl _, by
        intro effect member
        cases List.mem_cons.mp member with
        | inl same => exact List.mem_cons.mpr (.inl same)
        | inr member => exact List.mem_cons.mpr (.inr (admitted member)),
        ResumePrefix.nil (.handler frame admitted tail)⟩
  | hereView frame admitted entered bounded tail ih =>
      exact ⟨_, .nil, rfl, entered, bounded, ResumePrefix.nil (.handlerView frame admitted entered bounded tail)⟩
  | plainPath saved received accepts selected ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .push (.plain _) front, congrArg (Stack.push _) same, endpointEntered, endpointBounded,
        ResumePrefix.plain saved received accepts spine⟩
  | handlerMiss saved admitted miss selected ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .push (.handler _) front, congrArg (Stack.push _) same, endpointEntered, endpointBounded,
        ResumePrefix.handler saved admitted spine⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .push (.handler _) front, congrArg (Stack.push _) same, endpointEntered, endpointBounded,
        ResumePrefix.handlerView saved admitted entered bounded spine⟩
  | cellPath issued annotation selected ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .push (.cell _ _ _ _) front, congrArg (Stack.push _) same, endpointEntered, endpointBounded,
        ResumePrefix.cell issued annotation spine⟩
  | spentPath known answerSame annotation selected ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .spent _ _ _ front, congrArg (Stack.spent _ _ _) same, endpointEntered, endpointBounded,
        ResumePrefix.spent known answerSame annotation spine⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      exact ⟨endpointAllowed, .live _ _ _ _ _ front, congrArg (Stack.live _ _ _ _ _) same, endpointEntered, endpointBounded,
        ResumePrefix.live (captured := pendingPacked saved) known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved spine⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      obtain ⟨endpointAllowed, front, same, endpointEntered, endpointBounded, spine⟩ := ih
      cases same
      exact ⟨endpointAllowed, .live _ _ _ _ _ front, rfl, endpointEntered, endpointBounded,
        ResumePrefix.capture (captured := terminalPacked terminal) (whole := cutWholePacked contextual)
          known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal spine⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.handler_prefix

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)

private def SelectionRebases (effect : Instance) (operation : Nat) (selected : Option Selection) : Prop :=
  ∀ (captured tail : Packed) contract modes,
    selected = some (.handler captured tail contract modes) →
    ∀ after : Packed,
      select effect operation (captured.context.append after.context) =
        some (.handler captured after contract modes)

private theorem selection_rebases_prepend
    (frame : Packed → Packed)
    (commutes : ∀ (captured after : Packed),
      select effect operation ((frame captured).context.append after.context) =
        (select effect operation (captured.context.append after.context)).map (Selection.prepend frame))
    (next : SelectionRebases effect operation selected) :
    SelectionRebases effect operation (selected.map (Selection.prepend frame)) := by
  intro captured tail contract modes found after
  cases selected with
  | none => cases found
  | some selected => cases selected with
    | builtin identity => cases found
    | handler first rest offered families =>
      cases found
      rw [commutes, next first tail contract modes rfl after]
      rfl

/-- Nearest-handler selection keeps the same complete captured decoration when
only its outside tail changes. Matching-handler failures still stop lookup. -/
theorem select_rebases_tail
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope}
    (context : Context hints) : SelectionRebases effect operation (select effect operation context) := by
  induction context with
  | nil => intro _ _ _ _ found; cases found
  | handler activation rows tail ih =>
      simp only [select]
      split
      · split
        · intro captured rest contract modes found after
          cases found
          simp_all [Context.append, select, Context.pack]
          cases after
          rfl
        · intro _ _ _ _ found; cases found
      · apply selection_rebases_prepend _ _ ih
        intro captured after
        simp_all [Context.append, select, Context.pack]
  | cell tail ih =>
      simp only [select]
      split
      · intro _ _ _ _ found; cases found
      · apply selection_rebases_prepend _ _ ih
        intro captured after
        simp_all [Context.append, select, Context.pack]
  | plain rows tail ih | cleanup latent rows tail ih | normal tail ih | unwinding tail ih
  | closing tail ih | retiring owner tail ih | spent tail ih =>
      exact selection_rebases_prepend _ (fun _ _ => rfl) ih
  | live saved tail ihSaved ihTail =>
      exact selection_rebases_prepend _ (fun _ _ => rfl) ihTail

/-- Replacing the exact selected outside tail preserves its public contract,
modes and full private captured source rows. -/
theorem Cut.rebase_tail
    {wholeScope capturedScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : ReturnHints wholeScope} {capturedHints : ReturnHints capturedScope}
    {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context capturedHints} {tail : Context tailHints}
    (cut : Cut effect operation whole captured tail offered modes)
    (after : Packed) :
    Cut effect operation (captured.append after.context) captured after.context offered modes :=
  select_rebases_tail whole captured.pack tail.pack offered modes cut after
end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut.rebase_tail

namespace Ash.OneShot.SourceDependencyCapture
/-- The active receiver of an appended prefix contains exactly its visible
resources followed by the outside receiver; dormant captures stay dormant. -/
theorem Scope.visibleResources_append (front tail : Scope) :
    (front.append tail).visibleResources = front.visibleResources ++ tail.visibleResources := by
  induction front <;> simp_all [Scope.append, Scope.visibleResources]
end Ash.OneShot.SourceDependencyCapture

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section

private theorem resume_prepend_selection
    (found : selected.map (Selection.prepend frame) = some (.handler captured outside contract modes)) :
    ∃ inside, selected = some (.handler inside outside contract modes) ∧ captured = frame inside := by
  cases selected with
  | none => cases found
  | some selected => cases selected with
    | builtin identity => cases found
    | handler inside outside actual actualModes =>
      simp only [Option.map_some, Selection.prepend, Option.some.injEq, Selection.handler.injEq] at found
      obtain ⟨rfl, rfl, rfl, rfl⟩ := found
      exact ⟨inside, rfl, rfl⟩

private theorem cut_receiver_rebase
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {whole : Context hints} {captured outside after : Packed}
    (cut : select effect operation whole = some (.handler captured outside offered modes))
    (visible : outside.scope.visibleResources = after.scope.visibleResources) :
    scope.visibleResources = (captured.context.append after.context).pack.scope.visibleResources := by
  have decomposes := Cut.decomposition (captured := captured.context) (tail := outside.context) cut
  have scopes := congrArg (fun packed : Packed => packed.scope.visibleResources) decomposes
  simpa only [Context.pack, SourceDependencyCapture.Scope.visibleResources_append, visible] using scopes
end
end Ash.OneShot.CoreCallableContractExecution

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

omit [DeclarationPolicy] in
theorem actualReceiver.congr_visible
    (same : first.visibleResources = second.visibleResources) :
    actualReceiver world first ambient = actualReceiver world second ambient := by
  simp only [actualReceiver, same]

theorem FrameSource.receiver_congr
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver)
    (same : receiver = nextReceiver) :
    FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound nextReceiver := by
  cases same
  exact frame

theorem HandlerSource.receiver_congr
    (frame : HandlerSource globals outward world residual handler answer table plans rows receiver)
    (same : receiver = nextReceiver) :
    HandlerSource globals outward world residual handler answer table plans rows nextReceiver := by
  cases same
  exact frame

omit [DeclarationPolicy] in
theorem actualReceiver.congr_received
    (same : first.visibleResources ++ ambient = second.visibleResources ++ nextAmbient) :
    actualReceiver world first ambient = actualReceiver world second nextAmbient := by
  unfold actualReceiver
  rw [same]

omit [DeclarationPolicy] in
private theorem cut_receiving_rebase
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {whole : Context hints} {captured outside after : Packed}
    (cut : select effect operation whole = some (.handler captured outside offered modes))
    (visible : outside.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient) :
    scope.visibleResources ++ ambient =
      (captured.context.append after.context).pack.scope.visibleResources ++ afterAmbient := by
  have decomposes := Cut.decomposition (captured := captured.context) (tail := outside.context) cut
  have scopes := congrArg (fun packed : Packed => packed.scope.visibleResources ++ ambient) decomposes
  simpa only [Context.pack, SourceDependencyCapture.Scope.visibleResources_append,
    List.append_assoc, visible] using scopes

/-- Rebase the same selected installation onto a derived outside source with
an equal active receiver. Every full private row and dormant source remains. -/
theorem SelectedPending.rebase_boundary
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame)
    (physical : HandlerCut handler.effectInst whole cap tail handler)
    (captured after : Packed)
    (contextual : select handler.effectInst operation wholeContext =
      some (.handler captured outside.pack offered modes))
    (visible : outside.pack.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient)
    (nextTail : Pending globals outward world tailAllowed afterAmbient afterStack answer nextOutput after.context) :
    ∃ nextFrame : HandlerSource globals outward world residual handler answer table plans rows
        (actualReceiver world after.scope afterAmbient),
      SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := afterAmbient)
        (whole := cap.append afterStack) (input := input) (output := nextOutput)
        (wholeContext := captured.context.append after.context)
        (tailAllowed := tailAllowed) (tail := afterStack) (outside := after.context) nextFrame := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    generalizing cap captured after afterStack afterAmbient nextOutput operation offered modes with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih =>
      cases physical with
      | hit handler tail same =>
        simp only [select, ↓reduceIte] at contextual
        split at contextual <;> try { cases contextual }
        obtain ⟨sameCaptured, _, _, _⟩ := Selection.handler.inj (Option.some.inj contextual)
        subst captured
        let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
        exact ⟨nextFrame, .here nextFrame admitted nextTail⟩
      | push runtimeFrame rest cap tail handler miss next => exact False.elim (miss rfl)
  | hereView frame admitted entered bounded tail ih =>
      cases physical with
      | hit handler tail same =>
        simp only [select, ↓reduceIte] at contextual
        split at contextual <;> try { cases contextual }
        obtain ⟨sameCaptured, _, _, _⟩ := Selection.handler.inj (Option.some.inj contextual)
        subst captured
        let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
        exact ⟨nextFrame, .hereView nextFrame admitted entered bounded nextTail⟩
      | push runtimeFrame rest cap tail handler miss next => exact False.elim (miss rfl)
  | plainPath saved received accepts selected ih =>
      cases physical with
      | push runtimeFrame rest cap tail handler miss next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .plainPath nextSaved
          (by simpa only [receiverSame] using received)
          (by simpa only [receiverSame] using accepts) path⟩
  | handlerMiss saved admitted miss selected ih =>
      cases physical with
      | hit handler tail same => exact False.elim (miss same)
      | push runtimeFrame rest cap tail handler physicalMiss next =>
        simp only [select, if_neg (Ne.symm miss)] at contextual
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .handlerMiss nextSaved admitted miss path⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      cases physical with
      | hit handler tail same => exact False.elim (miss same)
      | push runtimeFrame rest cap tail handler physicalMiss next =>
        simp only [select, if_neg (Ne.symm miss)] at contextual
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .handlerMissView nextSaved admitted entered bounded miss path⟩
  | cellPath issued annotation selected ih =>
      cases physical with
      | push runtimeFrame rest cap tail handler miss next =>
        simp only [select] at contextual
        split at contextual
        · cases contextual
        · obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
          subst captured
          obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
            next inside after found visible nextTail
          exact ⟨nextFrame, .cellPath issued annotation path⟩
  | spentPath known answerSame annotation selected ih =>
      cases physical with
      | spent ticket a scope rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        exact ⟨nextFrame, .spentPath known answerSame annotation path⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      cases physical with
      | live ticket q a savedStack caller rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        exact ⟨nextFrame, .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          (by simpa only [receiverSame] using saved) path⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed oldPhysical oldContextual terminal selected ihInstalled ih =>
      cases physical with
      | live ticket q a savedStack caller rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨nextFrame, path⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside after found visible nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        obtain ⟨nextInstalledFrame, nextInstallation⟩ := ihInstalled oldPhysical (terminalPacked terminal)
          (inside.context.append after.context).pack oldContextual receiverSame path.before
        exact ⟨nextFrame, .captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          nextInstalledFrame nextInstallation (physical_rebase oldPhysical _)
          (oldContextual.rebase_tail (inside.context.append after.context).pack) terminal path⟩

/-- The fixed-ambient suffix case follows from exact receiving-list equality. -/
theorem SelectedPending.rebase_tail
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame)
    (physical : HandlerCut handler.effectInst whole cap tail handler)
    (captured after : Packed)
    (contextual : select handler.effectInst operation wholeContext =
      some (.handler captured outside.pack offered modes))
    (visible : outside.pack.scope.visibleResources = after.scope.visibleResources)
    (nextTail : Pending globals outward world tailAllowed ambient afterStack answer output after.context) :
    ∃ nextFrame : HandlerSource globals outward world residual handler answer table plans rows
        (actualReceiver world after.scope ambient),
      SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
        (whole := cap.append afterStack) (input := input) (output := output)
        (wholeContext := captured.context.append after.context)
        (tailAllowed := tailAllowed) (tail := afterStack) (outside := after.context) nextFrame :=
  selected.rebase_boundary physical captured after contextual
    (congrArg (fun resources => resources ++ ambient) visible) nextTail

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.rebase_tail

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

omit [DeclarationPolicy] in
private theorem prefix_visible_rebase (head before after : Packed)
    (same : before.scope.visibleResources = after.scope.visibleResources) :
    (head.context.append before.context).pack.scope.visibleResources =
      (head.context.append after.context).pack.scope.visibleResources := by
  simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources_append, same]

omit [DeclarationPolicy] in
private theorem prefix_receiving_rebase (head before after : Packed)
    (same : before.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient) :
    (head.context.append before.context).pack.scope.visibleResources ++ ambient =
      (head.context.append after.context).pack.scope.visibleResources ++ afterAmbient := by
  simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources_append, List.append_assoc, same]

/-- Replace the actual typed endpoint while preserving every original prefix
source at an equal active receiver. Embedded installations are rebased from
their same original selected source and exact cuts. -/
theorem ResumePrefix.rebase_boundary
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole)
    (after : Packed)
    (same : base.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient)
    (nextBase : Pending globals outward world baseAllowed afterAmbient afterStack baseInput nextFinal after.context) :
    ∃ before : Packed,
      whole = (before.context.append base.context).pack ∧
      Pending globals outward world allowed afterAmbient (front.append afterStack) input nextFinal
        (before.context.append after.context) := by
  induction spine with
  | nil tail => exact ⟨Context.nil.pack, rfl, nextBase⟩
  | plain frame received accepts next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨plainPacked frame before, rfl, .plain nextFrame
        (by simpa only [visible, Context.pack] using received)
        (by simpa only [visible, Context.pack] using accepts) nextTail⟩
  | handler frame admitted next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨handlerPacked frame before, rfl, .handler nextFrame admitted nextTail⟩
  | handlerView frame admitted entered bounded next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨handlerPacked frame before, rfl, .handlerView nextFrame admitted entered bounded nextTail⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      exact ⟨livePacked known resumeSame (pendingPacked saved) before, rfl,
        .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          (by simpa only [visible, Context.pack, pendingPacked] using saved) nextTail⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      obtain ⟨nextFrame, nextInstalled⟩ := installed.rebase_boundary physical (terminalPacked terminal)
        (before.context.append after.context).pack contextual visible nextTail
      exact ⟨livePacked known resumeSame (terminalPacked terminal) before, rfl,
        .capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          nextFrame nextInstalled (physical_rebase physical _)
          (contextual.rebase_tail (before.context.append after.context).pack) terminal⟩
  | spent known answerSame annotation next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      exact ⟨spentPacked known before, rfl, .spent known answerSame annotation nextTail⟩
  | cell issued annotation next ih =>
      obtain ⟨before, rfl, nextTail⟩ := ih
      exact ⟨cellPacked issued before, rfl, .cell issued annotation nextTail⟩

/-- Equal active resources give the fixed-ambient suffix case. -/
theorem ResumePrefix.rebase_tail
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole)
    (after : Packed)
    (same : base.scope.visibleResources = after.scope.visibleResources)
    (nextBase : Pending globals outward world baseAllowed ambient afterStack baseInput final after.context) :
    ∃ before : Packed,
      whole = (before.context.append base.context).pack ∧
      Pending globals outward world allowed ambient (front.append afterStack) input final
        (before.context.append after.context) :=
  spine.rebase_boundary after (congrArg (fun resources => resources ++ ambient) same) nextBase

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.rebase_tail

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- The current live endpoint supplies its own outside source and full answer
contract for the spent endpoint. -/
theorem Pending.spend_boundary
    {capturedScope outsideScope : SourceDependencyCapture.Scope}
    {capturedHints : SourceDependencyChecks.Lexical.ReturnHints capturedScope}
    {outsideHints : SourceDependencyChecks.Lexical.ReturnHints outsideScope}
    {captured : Context capturedHints} {outside : Context outsideHints}
    (pending : Pending globals outward world allowed ambient
      (.live owner inputType answerType cap caller tail) answer final
      (.live (owner := owner) (resumeDemand := savedDemand) captured outside)) :
    Pending globals outward world allowed ambient (.spent owner answerType caller tail) answer final
      (.spent (owner := owner) outside) := by
  cases pending with
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail =>
      exact .spent known answerSame answerAnnotation tail
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal =>
      exact .spent known answerSame answerAnnotation installed.outside

/-- The selected current endpoint becomes spent under the same typed front.
The source is constructed from the current boundary, not assumed as a desired
successor invariant. -/
theorem ResumePrefix.spend_endpoint
    {captured outside : Packed}
    (spine : ResumePrefix globals outward world ambient baseAllowed
      (.live owner inputType answerType cap caller tail) answer final
      (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context).pack
      allowed front input whole) :
    ∃ before : Packed,
      whole = (before.context.append
        (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context)).pack ∧
      Pending globals outward world allowed ambient
        (front.append (.spent owner answerType caller tail)) input final
        (before.context.append (Context.spent (owner := owner) outside.context)) := by
  exact spine.rebase_tail (Context.spent (owner := owner) outside.context).pack rfl
    spine.base_source.spend_boundary
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.spend_boundary
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.spend_endpoint
namespace Ash.OneShot.ScopedExecution
theorem Stack.append_nil (stack : Stack) : stack.append .nil = stack := by
  induction stack <;> simp_all [Stack.append]
end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.rebase_boundary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract)
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

private theorem Pending.context_congr
    {before after : Packed}
    (pending : Pending globals outward world allowed ambient stack input output before.context)
    (same : before = after) :
    Pending globals outward world allowed ambient stack input output after.context := by
  cases same
  exact pending

/-- The actual installation and its exact cuts supply the original captured
source. Outside resources move into its ambient list by equality only. -/
theorem SelectedPending.captured_source
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame)
    (physical : HandlerCut handler.effectInst whole cap tail handler)
    (captured : Packed)
    (contextual : select handler.effectInst operation wholeContext =
      some (.handler captured outside.pack offered modes)) :
    Pending globals outward world beforeAllowed (outside.pack.scope.visibleResources ++ ambient)
      cap input answer captured.context := by
  obtain ⟨nextFrame, path⟩ := selected.rebase_boundary (afterAmbient := outside.pack.scope.visibleResources ++ ambient)
    physical captured Context.nil.pack contextual (by simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources, List.nil_append])
    (Pending.nil (input := answer) (allowed := tailAllowed))
  have derived := Pending.context_congr (before := (captured.context.append Context.nil).pack)
    (after := captured) path.before captured.context.append_nil_pack
  simpa only [Stack.append_nil] using derived

/-- A current live owner exposes its same saved source and full owner input
contract in both explicit-save and selected-capture representations. -/
theorem Pending.saved_boundary
    {capturedScope outsideScope : SourceDependencyCapture.Scope}
    {capturedHints : SourceDependencyChecks.Lexical.ReturnHints capturedScope}
    {outsideHints : SourceDependencyChecks.Lexical.ReturnHints outsideScope}
    {captured : Context capturedHints} {outside : Context outsideHints}
    (pending : Pending globals outward world allowed ambient
      (.live owner inputType answerType cap caller tail) contract.answer final
      (.live (owner := owner) (resumeDemand := savedDemand) captured outside))
    (known : globals.owners owner = some contract) :
    ∃ savedAllowed, Pending globals outward world savedAllowed
      (outsideScope.visibleResources ++ ambient) cap contract.input contract.answer captured := by
  cases pending with
  | live actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail =>
      have same := Option.some.inj (actualKnown.symm.trans known)
      cases same
      cases inputSame
      exact ⟨_, saved⟩
  | capture actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal =>
      have same := Option.some.inj (actualKnown.symm.trans known)
      cases same
      cases inputSame
      exact ⟨_, installed.captured_source physical captured.pack contextual⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.captured_source
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.saved_boundary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- Actual selection through an installed source reaches its same outside
context and full terminal declaration rows. -/
theorem SelectedPending.selection_endpoint
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {tailContext : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := tailContext) frame)
    (captured outside : Packed)
    (found : select handler.effectInst operation wholeContext =
      some (.handler captured outside offered modes)) :
    outside = tailContext.pack ∧ TerminalHandler handler.effectInst handler.activation rows captured.context := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    generalizing captured outside operation offered modes with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih =>
      simp only [select, ↓reduceIte] at found
      split at found <;> try { cases found }
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Selection.handler.inj (Option.some.inj found)
      exact ⟨rfl, .here⟩
  | hereView frame admitted entered bounded tail ih =>
      simp only [select, ↓reduceIte] at found
      split at found <;> try { cases found }
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Selection.handler.inj (Option.some.inj found)
      exact ⟨rfl, .here⟩
  | plainPath saved received accepts selected ih =>
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .plain terminal⟩
  | handlerMiss saved admitted miss selected ih =>
      simp only [select, if_neg (Ne.symm miss)] at found
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .handler terminal⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      simp only [select, if_neg (Ne.symm miss)] at found
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .handler terminal⟩
  | cellPath issued annotation selected ih =>
      simp only [select] at found
      split at found
      · cases found
      · obtain ⟨inside, next, same⟩ := resume_prepend_selection found
        subst captured
        obtain ⟨outsideSame, terminal⟩ := ih inside outside next
        exact ⟨outsideSame, .cell terminal⟩
  | spentPath known answerSame annotation selected ih =>
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .spent terminal⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .live terminal⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      obtain ⟨inside, next, same⟩ := resume_prepend_selection found
      subst captured
      obtain ⟨outsideSame, terminal⟩ := ih inside outside next
      exact ⟨outsideSame, .live terminal⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.selection_endpoint
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.rebase_boundary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

/-- A current saved source determines its typed prefix down to the actual
empty endpoint, retaining every intermediate full contract and installation. -/
theorem Pending.as_prefix
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (pending : Pending globals outward world allowed ambient stack input output context) :
    ∃ endpointAllowed,
      ResumePrefix globals outward world ambient endpointAllowed .nil output output Context.nil.pack
        allowed stack input context.pack := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {ambient} {_} {_} {output} {_} {_} {_} {_} {_} {answer} {_} {_} {_} {_} {allowed} {tail} {_} {_} {outside} _ _ =>
      ∃ endpointAllowed,
        ResumePrefix globals outward world ambient endpointAllowed .nil output output Context.nil.pack
          allowed tail answer outside.pack) with
  | nil => exact ⟨_, .nil .nil⟩
  | plain frame received accepts tail ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .plain frame received accepts spine⟩
  | handler frame admitted tail ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .handler frame admitted spine⟩
  | handlerView frame admitted entered bounded tail ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .handlerView frame admitted entered bounded spine⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
      obtain ⟨endpointAllowed, spine⟩ := ihTail
      exact ⟨endpointAllowed, .live (captured := pendingPacked saved) known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved spine⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .capture (captured := terminalPacked terminal) (whole := cutWholePacked contextual)
        known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame
        (by simpa only [Stack.append_nil, cutWholePacked, terminalPacked, Context.pack] using installed)
        (by simpa only [Stack.append_nil] using physical) contextual terminal spine⟩
  | spent known answerSame annotation tail ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .spent known answerSame annotation spine⟩
  | cell issued annotation tail ih =>
      obtain ⟨endpointAllowed, spine⟩ := ih
      exact ⟨endpointAllowed, .cell issued annotation spine⟩
  | here frame admitted tail ih => exact ih
  | hereView frame admitted entered bounded tail ih => exact ih
  | plainPath saved received accepts selected ih => exact ih
  | handlerMiss saved admitted miss selected ih => exact ih
  | handlerMissView saved admitted entered bounded miss selected ih => exact ih
  | cellPath issued annotation selected ih => exact ih
  | spentPath known answerSame annotation selected ih => exact ih
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => exact ih
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih => exact ih


end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.as_prefix

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableRestoredSupport (RestoredContext)
open CoreCallableRestoredChecking (RestoredContextReceipts)
open SourcePlanSignatures (clauseSignatures)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

omit [DeclarationPolicy] in
theorem actualReceiver.ambient_mono
    (larger : ambient ⊆ nextAmbient) :
    actualReceiver world receiving ambient ⊆ actualReceiver world receiving nextAmbient := by
  intro identity member
  obtain ⟨present, issued⟩ := List.mem_filter.mp member
  apply List.mem_filter.mpr
  refine ⟨?_, issued⟩
  obtain here | outer := List.mem_append.mp present
  · exact List.mem_append_left _ here
  · exact List.mem_append_right _ (larger outer)

omit [DeclarationPolicy] in
private theorem ambient_prefix_mono (head : List Nat) (larger : ambient ⊆ nextAmbient) :
    head ++ ambient ⊆ head ++ nextAmbient := by
  intro identity member
  obtain here | outer := List.mem_append.mp member
  · exact List.mem_append_left _ here
  · exact List.mem_append_right _ (larger outer)

private def SelectedAmbientResult
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (_selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail) (outside := outside) frame)
    (nextAmbient : List Nat) : Prop :=
    (∃ nextOutside : Context tailHints,
      RestoredContextReceipts world nextAmbient outside nextOutside ∧
      Pending globals outward world tailAllowed nextAmbient tail answer output nextOutside) ∧
    (∀ nextOutside : Context tailHints,
      RestoredContextReceipts world nextAmbient outside nextOutside →
      Pending globals outward world tailAllowed nextAmbient tail answer output nextOutside →
      ∃ nextWhole : Context wholeHints,
      ∃ nextRows : ClauseRows (clauseSignatures plans),
      ∃ nextFrame : HandlerSource globals outward world residual handler answer table plans nextRows
        (actualReceiver world tailScope nextAmbient),
        RestoredContextReceipts world nextAmbient wholeContext nextWhole ∧
        HandlerRestorationReceipt frame nextFrame ∧
        SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := nextAmbient)
          (whole := whole) (input := input) (output := output) (wholeContext := nextWhole)
          (tailAllowed := tailAllowed) (tail := tail) (outside := nextOutside) nextFrame)

omit [DeclarationPolicy] in
private theorem context_pack_same
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {before after : Context hints} (same : before.pack = after.pack) : before = after := by
  cases same
  rfl

/-- Rebuild the same current saved source at its enlarged actual receiver.
Every changed row comes from its original source's canonical receipt. -/
theorem Pending.restore_ambient
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints}
    (pending : Pending globals outward world allowed ambient stack input output context)
    (larger : ambient ⊆ nextAmbient) :
    ∃ nextContext : Context hints,
      RestoredContextReceipts world nextAmbient context nextContext ∧
      Pending globals outward world allowed nextAmbient stack input output nextContext := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {ambient} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}
      {_} {_} {_} {_} {_} frame selected =>
      ∀ nextAmbient, ambient ⊆ nextAmbient → SelectedAmbientResult selected nextAmbient)
    generalizing nextAmbient with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | plain frame received accepts tail ih =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ih larger
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      refine ⟨.plain nextRows nextTail, .plain actualReceiver.received rowReceipt tailReceipt,
        .plain nextFrame (nextFrame.bodySource.actual_received.trans actualReceiver.received) ?_ nextPending⟩
      intro identity issued receiving
      exact List.mem_filter.mpr ⟨receiving, by simpa using issued⟩
  | handler frame admitted tail ih =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ih larger
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextTail, .handler actualReceiver.received rowReceipt.declarations tailReceipt,
        .handler nextFrame admitted nextPending⟩
  | handlerView frame admitted entered bounded tail ih =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ih larger
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextTail, .handler actualReceiver.received rowReceipt.declarations tailReceipt,
        .handlerView nextFrame admitted entered bounded nextPending⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ihTail larger
      obtain ⟨nextSaved, savedReceipt, nextSavedPending⟩ := ihSaved (ambient_prefix_mono _ larger)
      exact ⟨.live nextSaved nextTail, .live savedReceipt tailReceipt,
        .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation nextSavedPending nextPending⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
      obtain ⟨nextOutside, outsideReceipt, nextOutsidePending⟩ := (ih nextAmbient larger).1
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextCaptured, nextTail, nextCut, capturedReceipt, tailReceipt⟩ := wholeReceipt.cut contextual
      obtain ⟨sameOutside, nextTerminal⟩ := path.selection_endpoint nextCaptured.pack nextTail.pack nextCut
      have sameTail := context_pack_same sameOutside
      cases sameTail
      exact ⟨.live nextCaptured nextOutside, .live capturedReceipt outsideReceipt,
        .capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          nextFrame path physical nextCut nextTerminal⟩
  | spent known answerSame annotation tail ih =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ih larger
      exact ⟨.spent nextTail, .spent tailReceipt, .spent known answerSame annotation nextPending⟩
  | cell issued annotation tail ih =>
      obtain ⟨nextTail, tailReceipt, nextPending⟩ := ih larger
      exact ⟨.cell nextTail, .cell tailReceipt, .cell issued annotation nextPending⟩
  | here frame admitted tail ih =>
      rename_i nextAmbient larger
      refine ⟨ih larger, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextOutside, nextRows, nextFrame,
        .handler actualReceiver.received rowReceipt.declarations outsideReceipt,
        rowReceipt, .here nextFrame admitted nextOutsidePending⟩
  | hereView frame admitted entered bounded tail ih =>
      rename_i nextAmbient larger
      refine ⟨ih larger, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextOutside, nextRows, nextFrame,
        .handler actualReceiver.received rowReceipt.declarations outsideReceipt,
        rowReceipt, .hereView nextFrame admitted entered bounded nextOutsidePending⟩
  | plainPath saved received accepts selected ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextSavedRows, nextSaved, rowReceipt⟩ := saved.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      refine ⟨.plain nextSavedRows nextWhole, nextRows, nextFrame,
        .plain actualReceiver.received rowReceipt wholeReceipt, frameReceipt,
        .plainPath nextSaved (nextSaved.bodySource.actual_received.trans actualReceiver.received) ?_ path⟩
      intro identity issued receiving
      exact List.mem_filter.mpr ⟨receiving, by simpa using issued⟩
  | handlerMiss saved admitted miss selected ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextSavedRows, nextSaved, rowReceipt⟩ := saved.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextSavedRows nextWhole, nextRows, nextFrame,
        .handler actualReceiver.received rowReceipt.declarations wholeReceipt, frameReceipt,
        .handlerMiss nextSaved admitted miss path⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextSavedRows, nextSaved, rowReceipt⟩ := saved.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextSavedRows nextWhole, nextRows, nextFrame,
        .handler actualReceiver.received rowReceipt.declarations wholeReceipt, frameReceipt,
        .handlerMissView nextSaved admitted entered bounded miss path⟩
  | cellPath issued annotation selected ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      exact ⟨.cell nextWhole, nextRows, nextFrame, .cell wholeReceipt, frameReceipt,
        .cellPath issued annotation path⟩
  | spentPath known answerSame annotation selected ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      exact ⟨.spent nextWhole, nextRows, nextFrame, .spent wholeReceipt, frameReceipt,
        .spentPath known answerSame annotation path⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextSaved, savedReceipt, nextSavedPending⟩ := ihSaved (ambient_prefix_mono _ larger)
      exact ⟨.live nextSaved nextWhole, nextRows, nextFrame, .live savedReceipt wholeReceipt, frameReceipt,
        .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation nextSavedPending path⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      rename_i nextAmbient larger
      refine ⟨(ih nextAmbient larger).1, ?_⟩
      intro nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextWhole, nextRows, nextFrame, wholeReceipt, frameReceipt, path⟩ :=
        (ih nextAmbient larger).2 nextOutside outsideReceipt nextOutsidePending
      obtain ⟨nextInstalledWhole, nextInstalledRows, nextInstalledFrame, installedReceipt, installedFrameReceipt, nextInstalled⟩ :=
        (ihInstalled nextAmbient larger).2 nextWhole wholeReceipt path.before
      obtain ⟨nextCaptured, nextTail, nextCut, capturedReceipt, tailReceipt⟩ := installedReceipt.cut contextual
      obtain ⟨sameOutside, nextTerminal⟩ := nextInstalled.selection_endpoint nextCaptured.pack nextTail.pack nextCut
      have sameTail := context_pack_same sameOutside
      cases sameTail
      exact ⟨.live nextCaptured nextWhole, nextRows, nextFrame, .live capturedReceipt wholeReceipt, frameReceipt,
        .captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          nextInstalledFrame nextInstalled physical nextCut nextTerminal path⟩
end
end Ash.OneShot.CoreCallableContractExecution

#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.restore_ambient

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]

omit [DeclarationPolicy] in
private theorem allowance_left (allowed extra : List Instance) : allowed ⊆ allowed ++ extra :=
  fun _ member => List.mem_append.mpr (.inl member)

omit [DeclarationPolicy] in
private theorem allowance_append {allowed next : List Instance} (admitted : allowed ⊆ next)
    (extra : List Instance) : allowed ++ extra ⊆ next ++ extra := by
  intro effect member
  cases List.mem_append.mp member with
  | inl member => exact List.mem_append.mpr (.inl (admitted member))
  | inr member => exact List.mem_append.mpr (.inr member)

omit [DeclarationPolicy] in
private theorem allowance_bounded {allowed outside : List Instance} {effect : Instance}
    (bounded : allowed ⊆ effect :: outside) (extra : List Instance) :
    allowed ++ extra ⊆ effect :: (outside ++ extra) := by
  intro action member
  cases List.mem_append.mp member with
  | inl member =>
    cases List.mem_cons.mp (bounded member) with
    | inl same => exact List.mem_cons.mpr (.inl same)
    | inr member => exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inl member)))
  | inr member => exact List.mem_cons.mpr (.inr (List.mem_append.mpr (.inr member)))

omit [DeclarationPolicy] in
private theorem allowance_handler {residual outside : List Instance} (admitted : residual ⊆ outside)
    (effect : Instance) : effect :: residual ⊆ effect :: outside := by
  intro action member
  cases List.mem_cons.mp member with
  | inl same => exact List.mem_cons.mpr (.inl same)
  | inr member => exact List.mem_cons.mpr (.inr (admitted member))

set_option linter.unusedVariables false in
/-- The same actual continuation admits an appended outer allowance. Installed
handler residuals and all dormant saved sources retain their original evidence. -/
theorem Pending.allowed_append
    (pending : Pending globals outward world allowed ambient stack input output context)
    (extra : List Instance) :
    Pending globals outward world (allowed ++ extra) ambient stack input output context := by
  induction pending using Pending.rec
    (motive_2 := fun {beforeAllowed} {ambient} {whole} {input} {output} {_} {_} {wholeContext}
      {_} {_} {_} {_} {_} {_} {_} {tailAllowed} {tail} {_} {_} {outside} frame _ =>
      SelectedPending globals outward world (beforeAllowed := beforeAllowed ++ extra) (ambient := ambient)
        (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
        (tailAllowed := tailAllowed ++ extra) (tail := tail) (outside := outside) frame) with
  | nil => exact .nil
  | plain frame received accepts tail ih =>
      exact .plain (frame.allowed_weaken (allowance_left _ extra)) received accepts ih
  | handler frame admitted tail ih =>
      exact .handlerView frame (admitted.trans (allowance_left _ extra))
        (allowance_left _ extra) (allowance_bounded (allowance_handler admitted _) extra) ih
  | handlerView frame admitted entered bounded tail ih =>
      exact .handlerView frame (admitted.trans (allowance_left _ extra))
        (entered.trans (allowance_left _ extra)) (allowance_bounded bounded extra) ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
      exact .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ihTail
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
      have saved := installed.captured_source physical _ contextual
      exact .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ih.outside
  | spent known answerSame annotation tail ih => exact .spent known answerSame annotation ih
  | cell issued annotation tail ih => exact .cell issued annotation ih
  | here frame admitted tail ih =>
      exact .hereView frame (admitted.trans (allowance_left _ extra))
        (allowance_left _ extra) (allowance_bounded (allowance_handler admitted _) extra) ih
  | hereView frame admitted entered bounded tail ih =>
      exact .hereView frame (admitted.trans (allowance_left _ extra))
        (entered.trans (allowance_left _ extra)) (allowance_bounded bounded extra) ih
  | plainPath saved received accepts selected ih =>
      exact .plainPath (saved.allowed_weaken (allowance_left _ extra)) received accepts ih
  | handlerMiss saved admitted miss selected ih =>
      exact .handlerMissView saved (admitted.trans (allowance_left _ extra))
        (allowance_left _ extra) (allowance_bounded (allowance_handler admitted _) extra) miss ih
  | handlerMissView saved admitted entered bounded miss selected ih =>
      exact .handlerMissView saved (admitted.trans (allowance_left _ extra))
        (entered.trans (allowance_left _ extra)) (allowance_bounded bounded extra) miss ih
  | cellPath issued annotation selected ih => exact .cellPath issued annotation ih
  | spentPath known answerSame annotation selected ih => exact .spentPath known answerSame annotation ih
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      exact .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ih
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      have saved := installed.captured_source physical _ contextual
      exact .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ih
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.allowed_append

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- The actual selected boundary supplies its own entry allowance. Only that
allowance is admitted into the derived target tail; private residuals stay fixed. -/
theorem SelectedPending.rebase_entry_boundary
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame)
    (physical : HandlerCut handler.effectInst whole cap tail handler)
    (captured : Packed)
    (contextual : select handler.effectInst operation wholeContext =
      some (.handler captured outside.pack offered modes))
    : ∃ entryAllowed : List Instance,
      (handler.effectInst :: residual) ⊆ entryAllowed ∧
      entryAllowed ⊆ (handler.effectInst :: tailAllowed) ∧
      ∀ (after : Packed) (afterAllowed : List Instance) (afterStack : Stack)
        (nextOutput : CoreCallableContractSource.Contract) (afterAmbient : List Nat),
      outside.pack.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient →
      entryAllowed ⊆ afterAllowed →
      Pending globals outward world afterAllowed afterAmbient afterStack answer nextOutput after.context →
      ∃ nextFrame : HandlerSource globals outward world residual handler answer table plans rows
          (actualReceiver world after.scope afterAmbient),
      SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := afterAmbient)
        (whole := cap.append afterStack) (input := input) (output := nextOutput)
        (wholeContext := captured.context.append after.context)
        (tailAllowed := afterAllowed) (tail := afterStack) (outside := after.context) nextFrame := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    generalizing cap captured operation offered modes with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih =>
      refine ⟨_, List.Subset.refl _, allowance_handler admitted _, ?_⟩
      intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
      cases physical with
      | hit handler tail same =>
        simp only [select, ↓reduceIte] at contextual
        split at contextual <;> try { cases contextual }
        obtain ⟨sameCaptured, _, _, _⟩ := Selection.handler.inj (Option.some.inj contextual)
        subst captured
        let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
        exact ⟨nextFrame, .hereView nextFrame
          (fun _ member => gate (List.mem_cons.mpr (.inr member))) (List.Subset.refl _)
          (fun _ member => List.mem_cons.mpr (.inr (gate member))) nextTail⟩
      | push runtimeFrame rest cap tail handler miss next => exact False.elim (miss rfl)
  | hereView frame admitted entered bounded tail ih =>
      refine ⟨_, entered, bounded, ?_⟩
      intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
      cases physical with
      | hit handler tail same =>
        simp only [select, ↓reduceIte] at contextual
        split at contextual <;> try { cases contextual }
        obtain ⟨sameCaptured, _, _, _⟩ := Selection.handler.inj (Option.some.inj contextual)
        subst captured
        let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
        exact ⟨nextFrame, .hereView nextFrame
          (fun _ member => gate (entered (List.mem_cons.mpr (.inr member)))) entered
          (fun _ member => List.mem_cons.mpr (.inr (gate member))) nextTail⟩
      | push runtimeFrame rest cap tail handler miss next => exact False.elim (miss rfl)
  | plainPath saved received accepts selected ih =>
      cases physical with
      | push runtimeFrame rest cap tail handler miss next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .plainPath nextSaved
          (by simpa only [receiverSame] using received)
          (by simpa only [receiverSame] using accepts) path⟩
  | handlerMiss saved admitted miss selected ih =>
      cases physical with
      | hit handler tail same => exact False.elim (miss same)
      | push runtimeFrame rest cap tail handler physicalMiss next =>
        simp only [select, if_neg (Ne.symm miss)] at contextual
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .handlerMiss nextSaved admitted miss path⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      cases physical with
      | hit handler tail same => exact False.elim (miss same)
      | push runtimeFrame rest cap tail handler physicalMiss next =>
        simp only [select, if_neg (Ne.symm miss)] at contextual
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        let nextSaved := saved.receiver_congr (actualReceiver.congr_received receiverSame)
        exact ⟨nextFrame, .handlerMissView nextSaved admitted entered bounded miss path⟩
  | cellPath issued annotation selected ih =>
      cases physical with
      | push runtimeFrame rest cap tail handler miss next =>
        simp only [select] at contextual
        split at contextual
        · cases contextual
        · obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
          subst captured
          obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
            next inside found
          refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
          intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
          obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
          exact ⟨nextFrame, .cellPath issued annotation path⟩
  | spentPath known answerSame annotation selected ih =>
      cases physical with
      | spent ticket a scope rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        exact ⟨nextFrame, .spentPath known answerSame annotation path⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      cases physical with
      | live ticket q a savedStack caller rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        exact ⟨nextFrame, .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          (by simpa only [receiverSame] using saved) path⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed oldPhysical oldContextual terminal selected ihInstalled ih =>
      cases physical with
      | live ticket q a savedStack caller rest cap tail handler next =>
        obtain ⟨inside, found, same⟩ := resume_prepend_selection contextual
        subst captured
        obtain ⟨entryAllowed, entryEntered, entryBounded, restore⟩ := ih (operation := operation) (offered := offered) (modes := modes)
          next inside found
        refine ⟨entryAllowed, entryEntered, entryBounded, ?_⟩
        intro after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        obtain ⟨nextFrame, path⟩ := restore after afterAllowed afterStack nextOutput afterAmbient visible gate nextTail
        have receiverSame := cut_receiving_rebase (after := after) found visible
        simp only [Context.pack] at receiverSame
        obtain ⟨nextInstalledFrame, nextInstallation⟩ := installed.rebase_boundary oldPhysical (terminalPacked terminal)
          (inside.context.append after.context).pack oldContextual receiverSame path.before
        exact ⟨nextFrame, .captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          nextInstalledFrame nextInstallation (physical_rebase oldPhysical _)
          (oldContextual.rebase_tail (inside.context.append after.context).pack) terminal path⟩

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.rebase_entry_boundary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- The same selected installation with its derived nil outside retains the
exact entry allowance at the saved source endpoint. -/
theorem SelectedPending.tail_prefix
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame) :
    ∃ front : Stack,
      whole = front.append tail ∧
      ResumePrefix globals outward world ambient tailAllowed tail answer output outside.pack beforeAllowed front input wholeContext.pack := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True) with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih =>
      exact ⟨.push (.handler _) .nil, rfl, ResumePrefix.handler frame admitted (.nil tail)⟩
  | hereView frame admitted entered bounded tail ih =>
      exact ⟨.push (.handler _) .nil, rfl, ResumePrefix.handlerView frame admitted entered bounded (.nil tail)⟩
  | plainPath saved received accepts selected ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.push (.plain _) front, congrArg (Stack.push _) same,
        ResumePrefix.plain saved received accepts spine⟩
  | handlerMiss saved admitted miss selected ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.push (.handler _) front, congrArg (Stack.push _) same,
        ResumePrefix.handler saved admitted spine⟩
  | handlerMissView saved admitted entered bounded miss selected ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.push (.handler _) front, congrArg (Stack.push _) same,
        ResumePrefix.handlerView saved admitted entered bounded spine⟩
  | cellPath issued annotation selected ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.push (.cell _ _ _ _) front, congrArg (Stack.push _) same,
        ResumePrefix.cell issued annotation spine⟩
  | spentPath known answerSame annotation selected ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.spent _ _ _ front, congrArg (Stack.spent _ _ _) same,
        ResumePrefix.spent known answerSame annotation spine⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      obtain ⟨front, same, spine⟩ := ih
      exact ⟨.live _ _ _ _ _ front, congrArg (Stack.live _ _ _ _ _) same,
        ResumePrefix.live (captured := pendingPacked saved) known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved spine⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      obtain ⟨front, same, spine⟩ := ih
      cases same
      exact ⟨.live _ _ _ _ _ front, rfl,
        ResumePrefix.capture (captured := terminalPacked terminal) (whole := cutWholePacked contextual)
          known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal spine⟩

theorem SelectedPending.saved_prefix
    {wholeScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {wholeContext : Context wholeHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world .nil ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := entryAllowed) (tail := .nil)
      (outside := .nil) frame) :
    ResumePrefix globals outward world ambient entryAllowed .nil answer output Context.nil.pack
      beforeAllowed whole input wholeContext.pack := by
  obtain ⟨front, same, spine⟩ := selected.tail_prefix
  simp only [Stack.append_nil] at same
  cases same
  exact spine

/-- The actual installed entry allowance and saved spine are derived together
from the original source and both current cuts. -/
theorem SelectedPending.captured_entry_prefix
    {wholeScope tailScope : SourceDependencyCapture.Scope}
    {wholeHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    {tailHints : SourceDependencyChecks.Lexical.ReturnHints tailScope}
    {wholeContext : Context wholeHints} {outside : Context tailHints}
    {frame : HandlerSource globals outward world residual handler answer table plans rows
      (actualReceiver world tailScope ambient)}
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame)
    (physical : HandlerCut handler.effectInst whole cap tail handler)
    (captured : Packed)
    (contextual : select handler.effectInst operation wholeContext =
      some (.handler captured outside.pack offered modes)) :
    ∃ entryAllowed : List Instance,
      (handler.effectInst :: residual) ⊆ entryAllowed ∧
      entryAllowed ⊆ (handler.effectInst :: tailAllowed) ∧
      ResumePrefix globals outward world (outside.pack.scope.visibleResources ++ ambient)
        entryAllowed .nil answer answer Context.nil.pack beforeAllowed cap input captured := by
  obtain ⟨entryAllowed, entered, bounded, restore⟩ := selected.rebase_entry_boundary physical captured contextual
  obtain ⟨nextFrame, path⟩ := restore Context.nil.pack entryAllowed .nil answer
    (outside.pack.scope.visibleResources ++ ambient)
    (by simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources, List.nil_append])
    (List.Subset.refl _) (Pending.nil (input := answer) (allowed := entryAllowed))
  have spine := path.saved_prefix
  refine ⟨entryAllowed, entered, bounded, ?_⟩
  change ResumePrefix globals outward world (outside.pack.scope.visibleResources ++ ambient)
    entryAllowed .nil answer answer Context.nil.pack beforeAllowed (cap.append .nil) input
    (captured.context.append Context.nil).pack at spine
  rw [Stack.append_nil, captured.context.append_nil_pack] at spine
  exact spine

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.saved_prefix
#print axioms Ash.OneShot.CoreCallableContractExecution.SelectedPending.captured_entry_prefix

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- Rebase one actual typed suffix endpoint into its derived admitted allowance.
Only ordinary outer source allowances grow; private handler families stay fixed. -/
theorem ResumePrefix.rebase_allowance_boundary
    (spine : ResumePrefix globals outward world ambient baseAllowed baseStack baseInput final base allowed front input whole)
    (after : Packed)
    (same : base.scope.visibleResources ++ ambient = after.scope.visibleResources ++ afterAmbient)
    (admitted : baseAllowed ⊆ afterAllowed)
    (nextBase : Pending globals outward world afterAllowed afterAmbient afterStack baseInput nextFinal after.context) :
    ∃ before : Packed, ∃ nextAllowed : List Instance,
      whole = (before.context.append base.context).pack ∧ allowed ⊆ nextAllowed ∧
      Pending globals outward world nextAllowed afterAmbient (front.append afterStack) input nextFinal
        (before.context.append after.context) := by
  induction spine with
  | nil tail => exact ⟨Context.nil.pack, _, rfl, admitted, nextBase⟩
  | plain frame received accepts next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨plainPacked frame before, _, rfl, enlarged, .plain (nextFrame.allowed_weaken enlarged)
        (by simpa only [visible, Context.pack] using received)
        (by simpa only [visible, Context.pack] using accepts) nextTail⟩
  | handler frame admitted next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨handlerPacked frame before, _, rfl, List.Subset.refl _, .handler nextFrame (admitted.trans enlarged) nextTail⟩
  | handlerView frame admitted entered bounded next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      let nextFrame := frame.receiver_congr (actualReceiver.congr_received visible)
      exact ⟨handlerPacked frame before, _, rfl, List.Subset.refl _, .handlerView nextFrame (admitted.trans enlarged) entered
        (bounded.trans (allowance_handler enlarged _)) nextTail⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      exact ⟨livePacked known resumeSame (pendingPacked saved) before, _, rfl, List.Subset.refl _,
        .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          (by simpa only [visible, Context.pack, pendingPacked] using saved) nextTail⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      have visible := prefix_receiving_rebase before base after same
      simp only [Context.pack] at visible
      have saved := installed.captured_source physical (terminalPacked terminal) contextual
      exact ⟨livePacked known resumeSame (terminalPacked terminal) before, _, rfl, List.Subset.refl _,
        .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
          (by simpa only [visible, Context.pack, terminalPacked] using saved) nextTail⟩
  | spent known answerSame annotation next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      exact ⟨spentPacked known before, _, rfl, List.Subset.refl _, .spent known answerSame annotation nextTail⟩
  | cell issued annotation next ih =>
      obtain ⟨before, nextAllowed, rfl, enlarged, nextTail⟩ := ih
      exact ⟨cellPacked issued before, _, rfl, enlarged, .cell issued annotation nextTail⟩

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.rebase_allowance_boundary

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
open CoreCallableRestoredChecking
section
variable [DeclarationPolicy]
set_option linter.unusedVariables false in
/-- Restore the actual saved spine while retaining its same derived nil endpoint
allowance. Every changed support leaf comes from the original installed source. -/
theorem ResumePrefix.restore_saved_ambient
    (spine : ResumePrefix globals outward world ambient baseAllowed .nil baseInput final Context.nil.pack
      allowed front input whole)
    (larger : ambient ⊆ nextAmbient) :
    ∃ nextContext : Context whole.hints,
      RestoredContextReceipts world nextAmbient whole.context nextContext ∧
      ResumePrefix globals outward world nextAmbient baseAllowed .nil baseInput final Context.nil.pack
        allowed front input nextContext.pack := by
  induction spine with
  | nil tail =>
      cases tail
      exact ⟨.nil, .nil, .nil .nil⟩
  | plain frame received accepts next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      refine ⟨.plain nextRows nextTail, .plain actualReceiver.received rowReceipt tailReceipt,
        .plain (tail := nextTail.pack) nextFrame (nextFrame.bodySource.actual_received.trans actualReceiver.received) ?_ nextSpine⟩
      intro identity issued receiving
      exact List.mem_filter.mpr ⟨receiving, by simpa using issued⟩
  | handler frame admitted next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextTail, .handler actualReceiver.received rowReceipt.declarations tailReceipt,
        .handler (tail := nextTail.pack) nextFrame admitted nextSpine⟩
  | handlerView frame admitted entered bounded next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      obtain ⟨nextRows, nextFrame, rowReceipt⟩ := frame.restore_receipt
        (fun _ member => member) (actualReceiver.ambient_mono larger)
      exact ⟨.handler _ nextRows nextTail, .handler actualReceiver.received rowReceipt.declarations tailReceipt,
        .handlerView (tail := nextTail.pack) nextFrame admitted entered bounded nextSpine⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      obtain ⟨nextSaved, savedReceipt, nextSavedPending⟩ := saved.restore_ambient (ambient_prefix_mono _ larger)
      exact ⟨.live nextSaved nextTail, .live savedReceipt tailReceipt,
        .live (captured := nextSaved.pack) (tail := nextTail.pack) known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation nextSavedPending nextSpine⟩
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      have saved := installed.captured_source physical (terminalPacked terminal) contextual
      obtain ⟨nextSaved, savedReceipt, nextSavedPending⟩ := saved.restore_ambient (ambient_prefix_mono _ larger)
      exact ⟨.live nextSaved nextTail, .live savedReceipt tailReceipt,
        .live (captured := nextSaved.pack) (tail := nextTail.pack) known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation nextSavedPending nextSpine⟩
  | spent known answerSame annotation next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      exact ⟨.spent nextTail, .spent tailReceipt, .spent known answerSame annotation nextSpine⟩
  | cell issued annotation next ih =>
      obtain ⟨nextTail, tailReceipt, nextSpine⟩ := ih
      exact ⟨.cell nextTail, .cell tailReceipt, .cell issued annotation nextSpine⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.restore_saved_ambient

namespace Ash.OneShot.CoreCallableRestoredChecking
open ScopedExpressions ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- Unchanged complete rows carry the reflexive receipt at the same scope. -/
theorem RestoredContextReceipts.refl (context : Context hints) :
    RestoredContextReceipts world ambient context context := by
  induction context generalizing ambient with
  | nil => exact .nil
  | plain rows tail ih => exact .plain (receiver := []) (by simp) .same ih
  | handler activation rows tail ih => exact .handler (receiver := []) (by simp) .same ih
  | cleanup latent rows tail ih => exact .cleanup (receiver := []) (by simp) .same ih
  | cell tail ih => exact .cell ih
  | normal tail ih => exact .normal ih
  | unwinding tail ih => exact .unwinding ih
  | closing tail ih => exact .closing ih
  | retiring owner tail ih => exact .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih
end
end Ash.OneShot.CoreCallableRestoredChecking

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractRegistries (OwnerContract)
open SourcePlannedChecks (DeclarationPolicy)
open CoreCallableRestoredChecking
section
variable [DeclarationPolicy]
/-- The same current owner boundary supplies its saved spine and one actual
endpoint allowance. Selected captures retain their exact installed entry. -/
theorem Pending.saved_spine
    {capturedScope outsideScope : SourceDependencyCapture.Scope}
    {capturedHints : SourceDependencyChecks.Lexical.ReturnHints capturedScope}
    {outsideHints : SourceDependencyChecks.Lexical.ReturnHints outsideScope}
    {captured : Context capturedHints} {outside : Context outsideHints}
    (pending : Pending globals outward world allowed ambient
      (.live owner inputType answerType cap caller tail) contract.answer final
      (.live (owner := owner) (resumeDemand := savedDemand) captured outside))
    (known : globals.owners owner = some contract) :
    ∃ savedAllowed entryAllowed,
      ResumePrefix globals outward world (outsideScope.visibleResources ++ ambient)
        entryAllowed .nil contract.answer contract.answer Context.nil.pack
        savedAllowed cap contract.input captured.pack := by
  cases pending with
  | live actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail =>
      have same := Option.some.inj (actualKnown.symm.trans known)
      cases same
      cases inputSame
      obtain ⟨entryAllowed, spine⟩ := saved.as_prefix
      exact ⟨_, entryAllowed, spine⟩
  | capture actualKnown inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal =>
      have same := Option.some.inj (actualKnown.symm.trans known)
      cases same
      cases inputSame
      obtain ⟨entryAllowed, entered, bounded, spine⟩ := installed.captured_entry_prefix physical captured.pack contextual
      exact ⟨_, entryAllowed, spine⟩

/-- One actual saved source is restored and spliced over its own derived spent
front. The successor pending proof and complete paired receipt are constructed
from the predecessor; no desired successor source or check is assumed. -/
theorem ResumePrefix.resume_pending
    {captured outside : Packed}
    (spine : ResumePrefix globals outward world ambient baseAllowed
      (.live owner inputType answerType cap caller tail) contract.answer final
      (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context).pack
      allowed front contract.answer whole)
    (known : globals.owners owner = some contract) :
    ∃ before : Packed, ∃ nextCaptured : Context captured.hints, ∃ nextAllowed,
      whole = (before.context.append
        (Context.live (owner := owner) (resumeDemand := savedDemand) captured.context outside.context)).pack ∧
      Pending globals outward world nextAllowed ambient
        (cap.append (front.append (.spent owner answerType caller tail))) contract.input final
        (nextCaptured.append (before.context.append (Context.spent (owner := owner) outside.context))) ∧
      RestoredContextReceipts world ambient
        (captured.context.append (before.context.append (Context.spent (owner := owner) outside.context)))
        (nextCaptured.append (before.context.append (Context.spent (owner := owner) outside.context))) := by
  obtain ⟨savedAllowed, entryAllowed, savedSpine⟩ := spine.base_source.saved_spine known
  obtain ⟨before, same, frontPending⟩ := spine.spend_endpoint
  let receiving := (before.context.append (Context.spent (owner := owner) outside.context)).pack
  have ambientLarger : outside.scope.visibleResources ++ ambient ⊆ receiving.scope.visibleResources ++ ambient := by
    dsimp only [receiving, Context.pack]
    simp only [SourceDependencyCapture.Scope.visibleResources_append, SourceDependencyCapture.Scope.visibleResources, List.append_assoc]
    exact fun _ member => List.mem_append.mpr (.inr member)
  obtain ⟨nextCaptured, receipt, nextSavedSpine⟩ := savedSpine.restore_saved_ambient ambientLarger
  have nextFront := frontPending.allowed_append entryAllowed
  obtain ⟨head, nextAllowed, decomposition, enlarged, restored⟩ := nextSavedSpine.rebase_allowance_boundary
    receiving (afterAmbient := ambient)
    (by simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources, List.nil_append])
    (fun _ member => List.mem_append.mpr (.inr member)) nextFront
  have headSame : head = nextCaptured.pack := by
    change nextCaptured.pack = (head.context.append Context.nil).pack at decomposition
    rw [head.context.append_nil_pack] at decomposition
    exact decomposition.symm
  cases headSame
  exact ⟨before, nextCaptured, nextAllowed, same, restored,
    receipt.append (RestoredContextReceipts.refl receiving.context)⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Pending.saved_spine
#print axioms Ash.OneShot.CoreCallableContractExecution.ResumePrefix.resume_pending

namespace Ash.OneShot.SourceDependencyCapture
private def Scope.activeLength : Scope → Nat
  | .nil => 0
  | .plain _ tail | .handler _ _ _ tail | .cell _ tail | .cleanup _ _ tail |
      .running tail | .live _ _ tail | .spent _ tail => tail.activeLength + 1
private theorem Scope.activeLength_append (a b : Scope) :
    (a.append b).activeLength = a.activeLength + b.activeLength := by
  induction a <;> simp_all [Scope.append, Scope.activeLength, Nat.add_comm, Nat.add_left_comm]
/-- Equality of the complete appended scope cancels its same actual suffix. -/
theorem Scope.append_right_cancel (a b tail : Scope)
    (same : a.append tail = b.append tail) : a = b := by
  have lengthSame := congrArg Scope.activeLength same
  simp only [Scope.activeLength_append] at lengthSame
  have lengths : a.activeLength = b.activeLength := Nat.add_right_cancel lengthSame
  induction a generalizing b with
  | nil => cases b <;> simp_all [Scope.activeLength]
  | plain deps rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | handler effect table deps rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | cell identity rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | cleanup needs deps rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | running rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | live owner saved rest ihSaved ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
  | spent owner rest ih =>
      cases b <;> simp_all [Scope.activeLength, Scope.append]
      apply ih <;> simp_all
end Ash.OneShot.SourceDependencyCapture

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (OwnerContract)
open CoreCallableContractAdmission (Source Authenticated IndexedSource)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open CoreCallableRestoredChecking
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- The current rich source constructs its actual full-prefix successor. The
owner, saved family, checked certificate and accounting all come from the same
predecessor; support receipts are produced at the actual restored receiver. -/
theorem Site.resume
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) runtimeScope stack result final context (root : Requirements rootDemand))
    (closed : ClosedValue operand) :
    ∃ owner, ∃ contract : OwnerContract,
    ∃ (front cap tail : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
      globals.owners owner = some contract ∧ runtimeScope.resolve binder = some owner ∧
      result = contract.answer ∧
      stack = front.append (.live owner inputType answerType cap caller tail) ∧
      ScopedPorts.eraseType inputType = contract.input.port ∧
      ScopedPorts.eraseType answerType = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : Requirements nextDemand,
      rootDemand = owner :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ _next : Site globals outward world nextAllowed actions (OwnerPhaseTransitions.spend phases owner)
        budget ambient installations operand runtimeScope
        (cap.append (front.append (.spent owner answerType caller tail)))
        contract.input final restored.context nextRoot,
      RawStep ⟨.resume binder operand, runtimeScope, stack⟩
        ⟨operand, runtimeScope, cap.append (front.append (.spent owner answerType caller tail))⟩
        [] [.ticket owner] := by
  obtain ⟨owner, contract, known, resolved, answer, operandSource, lexical, empty, operandAuth,
    primitive, primitiveChecked, run⟩ := site.resume_primitives closed
  cases answer
  obtain ⟨rawRow, rawChecked, within⟩ := (disposal_annotation_map site.annotation).checked site.checked
  obtain ⟨⟨frontScope, frontHints, oldFront⟩, ⟨capScope, capHints, oldCap⟩,
    ⟨tailScope, tailHints, oldTail⟩, actualDemand, nextDemand, nextRoot,
    accountingSame, located, rootSame, waiting, nextChecked⟩ := run.resume_accounting (entries := []) (receiving := []) rawChecked
  obtain ⟨baseAllowed, front, cap, tail, inputType, answerType, caller, savedDemand,
    ⟨savedScope, savedHints, saved⟩, ⟨outsideScope, outsideHints, outside⟩,
    before, scopeFront, scopeCap, scopeTail, sourceSame, stackSame, inputAnnotation, answerAnnotation, spine⟩ :=
      site.pending.resume_prefix known located
  cases scopeCap
  cases scopeTail
  obtain ⟨⟨nextFrontScope, nextFrontHints, nextFront⟩, nextCaptured, nextAllowed,
    producedSame, restoredPending, receipt⟩ := spine.resume_pending known
  have frontScopeSame : nextFrontScope = frontScope := by
    apply SourceDependencyCapture.Scope.append_right_cancel _ _ (.live owner capScope tailScope)
    exact congrArg Packed.scope (producedSame.symm.trans accountingSame)
  cases frontScopeSame
  obtain ⟨frontSame, liveSame⟩ := context_append_pack_injective nextFront oldFront
    (Context.live (owner := owner) (resumeDemand := savedDemand) saved outside)
    (Context.live (owner := owner) (resumeDemand := actualDemand) oldCap oldTail)
    (producedSame.symm.trans accountingSame)
  have hintsSame := eq_of_heq (Packed.mk.inj liveSame).2.1
  obtain ⟨capHintsSame, tailHintsSame⟩ := ReturnHints.live.inj hintsSame
  cases capHintsSame
  cases tailHintsSame
  have contextSame := eq_of_heq (Packed.mk.inj liveSame).2.2
  obtain ⟨demandSame, capSame, tailSame⟩ := Context.live.inj contextSame
  cases demandSame
  cases capSame
  cases tailSame
  have frontHintsSame := eq_of_heq (Packed.mk.inj frontSame).2.1
  cases frontHintsSame
  have frontContextSame := eq_of_heq (Packed.mk.inj frontSame).2.2
  cases frontContextSame
  let primitiveAt := primitive.reindex_context producedSame
  have checkedAt := primitiveChecked.reindex_context producedSame
  have locatedAt : SourceDependencyCapture.OwnerCut owner
      (frontScope.append (.live owner capScope tailScope)) ⟨frontScope, capScope, tailScope⟩ := by
    have scopeSame := congrArg Packed.scope producedSame
    cases scopeSame
    exact located
  have retained := (primitiveAt.resume_evidence_at locatedAt).2
  have retainedChecked := checkedAt.resume_pending_at locatedAt
  have modeSame : (frontHints.append (.live (owner := owner) capHints tailHints)).returnMode .ordinary = .ordinary := by
    exact (site.retained.reindex_context producedSame).return_mode
  let retainedOrdinary := modeSame ▸ retained
  have retainedOrdinaryChecked := retainedChecked.output_mode modeSame
  have nextRetained := retainedOrdinary.restore_support receipt.complete (.refl Context.nil)
  have nextRetainedChecked := retainedOrdinaryChecked.restore_receipts receipt (RestoredContextReceipts.refl Context.nil)
  have nextWaiting := waiting.restore_support receipt.complete
  let restored := (nextCaptured.append (oldFront.append (Context.spent (owner := owner) oldTail))).pack
  have operandReceived : ScopedPorts.Support.evaluate lexical.environment operand.dependencies ⊆
      actualReceiver world restored.scope ambient := by
    intro identity member
    have oldMember := operandAuth.current_support.resources
    obtain ⟨dependency, belongs, supported⟩ := List.mem_flatMap.mp member
    cases dependency with
    | «variable» name => exact False.elim (ScopedTyping.closedValue_no_variable closed belongs)
    | ticket ticket => simp at supported
    | resource resource =>
        simp only [List.mem_singleton] at supported
        subst identity
        have resourceMember := Syntax.mem_resourceDependencies.mpr belongs
        have oldReceived := oldMember resourceMember
        have issued := actualReceiver.issued oldReceived
        have visible := actualReceiver.received oldReceived
        have receivingSame := congrArg (fun packed : Packed => packed.scope.visibleResources ++ ambient) producedSame
        simp only [Context.pack, SourceDependencyCapture.Scope.visibleResources_append,
          SourceDependencyCapture.Scope.visibleResources, List.append_assoc] at receivingSame
        rw [receivingSame] at visible
        apply List.mem_filter.mpr
        constructor
        · change resource ∈ (capScope.append (frontScope.append (.spent owner tailScope))).visibleResources ++ ambient
          simp only [SourceDependencyCapture.Scope.visibleResources_append,
            SourceDependencyCapture.Scope.visibleResources, List.append_assoc]
          exact List.mem_append.mpr (.inr visible)
        · simpa using issued
  let nextSource := IndexedSource.value_allowed operandSource closed.1 nextAllowed runtimeScope
  have nextAuth : Authenticated globals.registry outward nextSource lexical
      (actualReceiver world restored.scope ambient) :=
    (operandAuth.value_allowed closed.1 nextAllowed runtimeScope).value_reauthenticate closed operandReceived
  have nextSupport : SourceSupport.Bounds ScopedPorts.Support.empty operand.dependencies
      (actualReceiver world restored.scope ambient) := by
    apply SourceSupport.bounds_iff.mpr
    simpa only [empty] using operandReceived
  let next : Site globals outward world nextAllowed actions (OwnerPhaseTransitions.spend phases owner)
      budget ambient installations operand runtimeScope
      (cap.append (front.append (.spent owner answerType caller tail))) contract.input final restored.context nextRoot :=
    { sourceDemand := [], requirements := .request [] [], dependencies := .pure, plan := .pure,
      rows := .pure, bound := actualReceiver world restored.scope ambient,
      current := ⟨nextSource, nextSupport, actualReceiver.issued, ⟨lexical, empty, nextAuth⟩, actualReceiver.issued⟩,
      received := actualReceiver.received,
      certificate := .pure, certificateChecked := .pure,
      pending := restoredPending, retained := nextRetained, retainedChecked := nextRetainedChecked,
      accounting := .pure nextWaiting, annotated := nextRoot, row := rawRow, annotation := .original,
      checked := nextChecked, bounded := within.trans site.bounded }
  refine ⟨owner, contract, front, cap, tail, inputType, answerType, caller, known, resolved, rfl,
    stackSame, inputAnnotation, answerAnnotation, nextDemand, nextRoot, rootSame,
    nextAllowed, restored, next, ?_⟩
  rw [stackSame]
  exact .resume binder owner runtimeScope caller inputType answerType front cap tail operand closed resolved
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.resume

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- A current physical plain frame reveals its own rich mapped source. The
existing bind consumer uses precisely that source and its checked certificate. -/
theorem Site.plug_plain
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.plain data) stack) input final context root)
    (closed : ClosedValue value) :
    ∃ parameter body, data.context = .bind parameter body ∧
    ∃ output : Contract, ∃ rest : Packed,
    ∃ _next : Site globals outward world allowed actions phases budget ambient installations
        (.bind parameter value body) data.scope stack output final rest.context root,
      RawStep ⟨value, runtimeScope, .push (.plain data) stack⟩
        ⟨.bind parameter value body, data.scope, stack⟩ [] [] := by
  cases site.pending with
  | plain frame received accepts tail =>
      obtain ⟨parameter, body, same, output, next, step⟩ := site.plug_bind closed
      exact ⟨parameter, body, same, output, pendingPacked tail, next, step⟩
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.plug_plain

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractRegistries (OwnerContract)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [DeclarationPolicy]
/-- Resume constructs the current successor and its own bind consumer. A
physical plain head exposes the mapped restored frame carried by that same
successor, rather than requiring a future source or certificate. -/
theorem Site.resume_plug
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) runtimeScope stack result final context (root : Requirements rootDemand))
    (closed : ClosedValue operand) :
    ∃ owner, ∃ contract : OwnerContract,
    ∃ (front cap tail : Stack) (inputType answerType : Ty) (caller : Execution.Scope),
      globals.owners owner = some contract ∧ runtimeScope.resolve binder = some owner ∧
      result = contract.answer ∧
      stack = front.append (.live owner inputType answerType cap caller tail) ∧
      ScopedPorts.eraseType inputType = contract.input.port ∧
      ScopedPorts.eraseType answerType = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : Requirements nextDemand,
      rootDemand = owner :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ _resumed : Site globals outward world nextAllowed actions (OwnerPhaseTransitions.spend phases owner)
        budget ambient installations operand runtimeScope
        (cap.append (front.append (.spent owner answerType caller tail)))
        contract.input final restored.context nextRoot,
      RawStep ⟨.resume binder operand, runtimeScope, stack⟩
        ⟨operand, runtimeScope, cap.append (front.append (.spent owner answerType caller tail))⟩
        [] [.ticket owner] ∧
      ∀ data rest, cap.append (front.append (.spent owner answerType caller tail)) = .push (.plain data) rest →
        ∃ parameter body, data.context = .bind parameter body ∧
        ∃ output : Contract, ∃ after : Packed,
        ∃ _next : Site globals outward world nextAllowed actions (OwnerPhaseTransitions.spend phases owner)
            budget ambient installations (.bind parameter operand body) data.scope rest output final after.context nextRoot,
          RawStep ⟨operand, runtimeScope, .push (.plain data) rest⟩
            ⟨.bind parameter operand body, data.scope, rest⟩ [] [] := by
  obtain ⟨owner, contract, front, cap, tail, inputType, answerType, caller,
    known, resolved, answer, same, inputAnnotation, answerAnnotation,
    nextDemand, nextRoot, rootSame, nextAllowed, restored, resumed, step⟩ := site.resume closed
  refine ⟨owner, contract, front, cap, tail, inputType, answerType, caller,
    known, resolved, answer, same, inputAnnotation, answerAnnotation,
    nextDemand, nextRoot, rootSame, nextAllowed, restored, resumed, step, ?_⟩
  intro data rest plain
  have current : Site globals outward world nextAllowed actions (OwnerPhaseTransitions.spend phases owner)
      budget ambient installations operand runtimeScope (.push (.plain data) rest)
      contract.input final restored.context nextRoot := by
    simpa only [plain] using resumed
  exact current.plug_plain closed
end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.resume_plug
