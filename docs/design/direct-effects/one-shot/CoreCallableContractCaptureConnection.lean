import CoreCallableContractExecution
import CorePayloadReceiver

/-! Selected-handler capture consumers for recursive callable contracts.
The handler's retained declaration proof selects its private source and complete
row family. Payload origins use actual operand support, independently of a
conservative syntax bound. This is experimental evidence under DN-0033. -/
namespace Ash.OneShot.CoreCallableContractCaptureConnection
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry Owners OwnerContract)
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds)
open SourcePlannedRecipeDeclarations (Selected)
open SourcePlannedChecks (DeclarationPolicy)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)

section
variable [DeclarationPolicy]

/-- Selection comes from the same installed declaration and clause syntax.
Both mode choice and every owner-indexed private row remain connected. -/
theorem selected_family
    {plans : ClausePlans clauses families}
    {declarationRows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans declarationRows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects,
    ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
    ∃ _known : registry.operations requested operation = some (argument, input),
    ∃ bodyRows : ∀ owner, Rows (signature (bodies owner)),
    ∃ body : ∀ owner (contract : OwnerContract),
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.lower, offered.dispose, row⟩
          (bodies owner) (bodyRows owner),
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation held plans parameter binder code bodies ∧
      ClauseRows.Selected operation held declarationRows bodyRows ∧
      ∀ owner contract a b c d e balanced,
        BodyAuthentication registry outward (body owner contract a b c d e balanced)
          (lexical.extend parameter receiver) receiver := by
  induction selected generalizing table families with
  | hit => cases authenticated with
    | cons known bodyBound storedReceived ordinary protectedMode rest =>
      simp only [lookup, if_true] at found
      cases Option.some.inj found
      cases held with
      | false =>
        simp [ClauseContract.row] at available
        cases available
        cases ordinary with
        | available resumeInterface closeInterface bodyChecked =>
          exact ⟨_, _, _, _, _, _, known, _, _, resumeInterface, closeInterface, .ordinary, .ordinary, bodyChecked⟩
      | true =>
        simp [ClauseContract.row] at available
        cases available
        cases protectedMode with
        | available resumeInterface closeInterface bodyChecked =>
          exact ⟨_, _, _, _, _, _, known, _, _, resumeInterface, closeInterface, .protectedMode, .protectedMode, bodyChecked⟩
  | pass different next ih => cases authenticated with
    | cons known bodyBound storedReceived ordinary protectedMode rest =>
      obtain ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, bodyRows, body,
        resumeInterface, closeInterface, chosen, located, bodyChecked⟩ :=
        ih rest (by simpa only [lookup, if_neg different] using found)
      exact ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, bodyRows, body,
        resumeInterface, closeInterface, .pass different chosen, .pass different located, bodyChecked⟩

theorem domain_selected_family
    {plans : ClausePlans clauses families}
    {declarationRows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans declarationRows}
    (authenticated : DomainDeclarationAuthentication registry outward source lexical receiver)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ formalSupport, ∃ argument input resumeEffects closeEffects,
    ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
    ∃ _known : registry.operations requested operation = some (argument, input),
    ∃ bodyRows : ∀ owner, Rows (signature (bodies owner)),
    ∃ body : ∀ owner (contract : OwnerContract),
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.lower, offered.dispose, row⟩
          (bodies owner) (bodyRows owner),
      CoreCallableContractOperandDomain.domainSupport argument receiver ⊆ formalSupport ∧
      formalSupport ⊆ receiver ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation held plans parameter binder code bodies ∧
      ClauseRows.Selected operation held declarationRows bodyRows ∧
      ∀ owner contract a b c d e balanced,
        BodyAuthentication registry outward (body owner contract a b c d e balanced)
          (lexical.extend parameter formalSupport) receiver := by
  induction selected generalizing table families with
  | hit => cases authenticated with
    | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest =>
      simp only [lookup, if_true] at found
      cases Option.some.inj found
      cases held with
      | false =>
        simp [ClauseContract.row] at available
        cases available
        cases ordinary with
        | available resumeInterface closeInterface bodyChecked =>
          exact ⟨_, _, _, _, _, _, _, known, _, _, domainCovered, formalReceived, resumeInterface, closeInterface, .ordinary, .ordinary, bodyChecked⟩
      | true =>
        simp [ClauseContract.row] at available
        cases available
        cases protectedMode with
        | available resumeInterface closeInterface bodyChecked =>
          exact ⟨_, _, _, _, _, _, _, known, _, _, domainCovered, formalReceived, resumeInterface, closeInterface, .protectedMode, .protectedMode, bodyChecked⟩
  | pass different next ih => cases authenticated with
    | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest =>
      obtain ⟨formalSupport, argument, input, resumeEffects, closeEffects, family, bodies, known, bodyRows, body,
        domainCovered, formalReceived, resumeInterface, closeInterface, chosen, located, bodyChecked⟩ :=
        ih rest (by simpa only [lookup, if_neg different] using found)
      exact ⟨formalSupport, argument, input, resumeEffects, closeEffects, family, bodies, known, bodyRows, body,
        domainCovered, formalReceived, resumeInterface, closeInterface, .pass different chosen, .pass different located, bodyChecked⟩

theorem selected_family_at
    {plans : ClausePlans clauses families}
    {declarationRows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans declarationRows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver ∨
      DomainDeclarationAuthentication registry outward source lexical receiver)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ formalSupport, ∃ argument input resumeEffects closeEffects,
    ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
    ∃ _known : registry.operations requested operation = some (argument, input),
    ∃ bodyRows : ∀ owner, Rows (signature (bodies owner)),
    ∃ body : ∀ owner (contract : OwnerContract),
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.lower, offered.dispose, row⟩
          (bodies owner) (bodyRows owner),
      CoreCallableContractOperandDomain.domainSupport argument receiver ⊆ formalSupport ∧
      formalSupport ⊆ receiver ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation held plans parameter binder code bodies ∧
      ClauseRows.Selected operation held declarationRows bodyRows ∧
      ∀ owner contract a b c d e balanced,
        BodyAuthentication registry outward (body owner contract a b c d e balanced)
          (lexical.extend parameter formalSupport) receiver := by
  cases authenticated with
  | inl whole =>
    obtain ⟨argument,input,resumeEffects,closeEffects,family,bodies,known,bodyRows,body,
      resumeInterface,closeInterface,chosen,located,checked⟩ := selected_family whole selected found available
    exact ⟨receiver,argument,input,resumeEffects,closeEffects,family,bodies,known,bodyRows,body,
      CoreCallableContractOperandDomain.domainSupport_received,List.Subset.refl _,
      resumeInterface,closeInterface,chosen,located,checked⟩
  | inr domain => exact domain_selected_family domain selected found available

/-- Request inversion keeps the actual closed payload's recursive source and
hereditary authentication from the same current expression. -/
theorem perform_payload
    (current : CoreCallableContractAdmission.Supported globals outward world allowed scope Environment.empty
      ScopedPorts.Support.empty (.perform effect operation operand) result demand requirements plan rows bound receiver)
    (closed : ClosedValue operand) :
    ∃ requested argument, ∃ payload : Source globals outward world allowed scope Environment.empty
      operand argument [] (.request [] []) .pure Rows.pure,
    ∃ lexical : LexicalBounds,
      effect = Instantiation.freezeEffect requested ∧
      globals.operations requested operation = some (argument, result) ∧
      lexical.environment = ScopedPorts.Support.empty ∧
      Authenticated globals.registry outward payload lexical receiver := by
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := current.authentication
  cases authenticated with
  | checked support hereditary =>
    cases hereditary with
    | perform operandAuthentication =>
      exact ⟨_, _, _, lexical, rfl, by assumption, sameEnvironment,
        operandAuthentication.value_summary closed.1⟩

/-- The same closed payload travels to the selected owner's registry and
clause scope. Reauthentication uses its proven post-cut actual support. -/
theorem payload_supported
    (current : CoreCallableContractAdmission.Supported globals outward world allowed scope Environment.empty
      ScopedPorts.Support.empty (.perform effect operation operand) result demand requirements plan rows bound receiver)
    (closed : ClosedValue operand)
    (owner : Nat) (contract : OwnerContract) (residual : List Instance) (binder : Nat)
    (nextLexical : LexicalBounds) (empty : nextLexical.environment = ScopedPorts.Support.empty)
    (received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆ nextReceiver)
    (issued : nextReceiver ⊆ world) :
    ∃ requested argument,
      effect = Instantiation.freezeEffect requested ∧
      globals.operations requested operation = some (argument, result) ∧
      CoreCallableContractAdmission.Supported (globals.withOwner owner contract) outward world residual
        (.ticket binder owner) Environment.empty ScopedPorts.Support.empty operand argument [] (.request [] [])
        .pure Rows.pure nextReceiver nextReceiver := by
  obtain ⟨requested, argument, payload, lexical, sameEffect, known, sameEnvironment, authentication⟩ :=
    perform_payload current closed
  let nextSource := (IndexedSource.value_owner_insert payload closed.1 owner contract).value_allowed closed.1 residual (.ticket binder owner)
  have nextAuthentication := (authentication.value_owner_insert closed.1 owner contract).value_allowed closed.1 residual (.ticket binder owner)
  have completed : Authenticated globals.registry outward nextSource nextLexical nextReceiver :=
    nextAuthentication.value_reauthenticate closed (by simpa only [empty] using received)
  refine ⟨requested, argument, sameEffect, known, ⟨nextSource, ?_, issued, ⟨nextLexical, empty, completed⟩, issued⟩⟩
  exact SourceSupport.bounds_iff.mpr received

/-- The SAME current closed rich operand supplies the formal-S substitution bound. -/
theorem payload_supported_at
    (current : CoreCallableContractAdmission.Supported globals outward world allowed scope Environment.empty
      ScopedPorts.Support.empty (.perform (Instantiation.freezeEffect requested) operation operand) result demand requirements plan rows bound currentReceiver)
    (closed : ClosedValue operand)
    (known : globals.operations requested operation = some (argument,result))
    (domainCovered : CoreCallableContractOperandDomain.domainSupport argument receiver ⊆ formalSupport)
    (formalReceived : formalSupport ⊆ receiver)
    (received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆ receiver)
    (issued : receiver ⊆ world)
    (owner : Nat) (contract : OwnerContract) (residual : List Instance) (binder : Nat)
    (nextLexical : LexicalBounds) (empty : nextLexical.environment = ScopedPorts.Support.empty) :
    CoreCallableContractAdmission.Supported (globals.withOwner owner contract) outward world residual
      (.ticket binder owner) Environment.empty ScopedPorts.Support.empty operand argument [] (.request [] [])
      .pure Rows.pure formalSupport receiver := by
  obtain ⟨actualRequested,actualArgument,payload,lexical,sameEffect,payloadKnown,sameEnvironment,authentication⟩ :=
    perform_payload current closed
  have sameRequested : requested = actualRequested := Instantiation.effect_realization_unique
    (Instantiation.frozen_effect_realizes Instantiation.Environment.empty requested)
    (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actualRequested)
  subst actualRequested
  have sameArgument := (Prod.mk.inj (Option.some.inj (payloadKnown.symm.trans known))).1
  subst actualArgument
  have actualBound := (payload.closed_support_in_domain closed received).trans domainCovered
  let nextSource := (IndexedSource.value_owner_insert payload closed.1 owner contract).value_allowed closed.1 residual (.ticket binder owner)
  let nextAuthentication := (authentication.value_owner_insert closed.1 owner contract).value_allowed closed.1 residual (.ticket binder owner)
  have completed : Authenticated globals.registry outward nextSource nextLexical receiver :=
    nextAuthentication.value_reauthenticate closed (by simpa only [empty] using received)
  exact ⟨nextSource,SourceSupport.bounds_iff.mpr actualBound,formalReceived.trans issued,
    ⟨nextLexical,empty,completed⟩,issued⟩

/-- The selected operation's clause syntax is recovered from the installed
source declaration order, rather than supplied as a private body premise. -/
theorem declaration_clause
    {declarations : ClausePlans clauses families}
    {declarationRows : ClauseRows (clauseSignatures declarations)}
    (source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table declarations declarationRows)
    (found : lookup operation table = some offered) :
    ∃ parameter binder code, ClauseAt operation clauses parameter binder code := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families with
  | nil => cases source; cases found
  | cons other parameter binder code rest ihCode ihRest =>
    cases source with
    | cons supportBound known ordinary protectedMode restSource =>
      by_cases same : operation = other
      · subst other; exact ⟨parameter, binder, code, .hit⟩
      · obtain ⟨parameter, binder, code, located⟩ := ihRest restSource (by simpa only [lookup, if_neg same] using found)
        exact ⟨parameter, binder, code, .pass same located⟩
  | _ => trivial

/-- The selected authenticated body supplies its own recursive demand and
requirements. Its full receiver authenticates private callable captures. -/
theorem selected_body_supported
    {lexical : LexicalBounds}
    {body : SourceBody globals.registry outward globals.owners world allowed (.ticket binder owner)
      (Environment.empty.extend parameter argument) code answer header plan rows}
    (authenticated : BodyAuthentication globals.registry outward body (lexical.extend parameter receiver) receiver)
    (empty : lexical.environment = ScopedPorts.Support.empty)
    (issued : receiver ⊆ world) :
    ∃ demand, ∃ requirements : RecursiveRequirements.Requirements demand,
      CoreCallableContractAdmission.Supported globals outward world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument)
        (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiver)
        code answer demand requirements plan rows receiver receiver := by
  cases authenticated with
  | typed authenticated =>
    refine ⟨_, _, ⟨_, ?_, issued, ⟨lexical.extend parameter receiver, ?_, authenticated⟩, issued⟩⟩
    · simpa only [CoreCallableReceiverRefinement.LexicalBounds.environment_extend, empty] using authenticated.current_support
    · simp only [CoreCallableReceiverRefinement.LexicalBounds.environment_extend, empty]

theorem selected_body_supported_at
    {lexical : LexicalBounds}
    {body : SourceBody globals.registry outward globals.owners world allowed (.ticket binder owner)
      (Environment.empty.extend parameter argument) code answer header plan rows}
    (authenticated : BodyAuthentication globals.registry outward body (lexical.extend parameter formalSupport) receiver)
    (empty : lexical.environment = ScopedPorts.Support.empty)
    (issued : receiver ⊆ world) :
    ∃ demand, ∃ requirements : RecursiveRequirements.Requirements demand,
      CoreCallableContractAdmission.Supported globals outward world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument)
        (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter formalSupport)
        code answer demand requirements plan rows receiver receiver := by
  cases authenticated with
  | typed authenticated =>
    refine ⟨_, _, ⟨_, ?_, issued, ⟨lexical.extend parameter formalSupport, ?_, authenticated⟩, issued⟩⟩
    · simpa only [CoreCallableReceiverRefinement.LexicalBounds.environment_extend, empty] using authenticated.current_support
    · simp only [CoreCallableReceiverRefinement.LexicalBounds.environment_extend, empty]

/-- Saved recursive source identifies the actual active receiver. Dormant
captures contribute no visible resource to an executing clause. -/
theorem pending_visible
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints}
    (pending : CoreCallableContractExecution.Pending globals outward world allowed ambient stack input output context) :
    receiving.visibleResources = stack.erase.visible := by
  induction pending using CoreCallableContractExecution.Pending.rec
    (motive_2 := fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {tail} {tailScope} {_} {_} _ _ =>
      tailScope.visibleResources = tail.erase.visible) with
  | nil => rfl
  | plain frame received accepts tail ih => exact ih
  | handler frame admitted tail ih => exact ih
  | handlerView frame admitted entered bounded tail ih => exact ih
  | spent known answerSame annotation tail ih => exact ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail => exact ihTail
  | cell issued annotation tail ih =>
    simpa only [SourceDependencyCapture.Scope.visibleResources, Stack.erase, Control.visible, ExecFrame.erase, Frame.visible, List.singleton_append] using congrArg (List.cons _) ih

  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih => exact ih
  | here frame admitted tail ih => exact ih
  | hereView frame admitted entered bounded tail ih => exact ih
  | plainPath saved received accepts selected ih => exact ih
  | handlerMiss saved admitted miss selected ih => exact ih
  | handlerMissView saved admitted entered bounded miss selected ih => exact ih
  | cellPath issued annotation selected ih => exact ih
  | spentPath known answerSame annotation selected ih => exact ih
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => exact ih
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation installedFrame installation physical contextual terminal selected ihInstallation ih => exact ih
omit [DeclarationPolicy] in
private theorem prepend_selection
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

/-- Physical and annotated selection jointly recover the same installation,
complete row decoration and actual outside continuation source. -/
theorem pending_selected_handler
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (pending : CoreCallableContractExecution.Pending globals outward world allowed ambient whole input output context)
    (physical : HandlerCut requested whole cap tail handler)
    (selected : select requested operation context = some (.handler captured outside offered modes)) :
    ∃ answer residual table families, ∃ plans : ClausePlans handler.clauses families,
    ∃ rows : ClauseRows (clauseSignatures plans),
    ∃ frame : CoreCallableContractExecution.HandlerSource globals outward world residual handler answer table plans rows
        (CoreCallableContractExecution.actualReceiver world outside.scope ambient),
    ∃ outsideAllowed,
      lookup operation table = some offered ∧
      SourceDependencyCapture.lookupDependencies operation families = some modes ∧
      TerminalHandler requested handler.activation rows captured.context ∧
      outside.scope.visibleResources = tail.erase.visible ∧
      captured.scope.visibleResources = cap.erase.visible ∧
      CoreCallableContractExecution.Pending globals outward world outsideAllowed ambient tail answer output outside.context ∧
      CoreCallableContractExecution.SelectedPending globals outward world
        (beforeAllowed := allowed) (whole := whole) (input := input) (output := output)
        (wholeContext := context) (tailAllowed := outsideAllowed) (tail := tail) (outside := outside.context) frame := by
  induction pending using CoreCallableContractExecution.Pending.rec
    (motive_2 := fun {_} {ambient} {_} {_} {selectedOutput} {_} {_} {_} {_} {_} {selectedAnswer} {_} {_} {_} {_} {selectedAllowed} {selectedTail} {_} {_} {selectedOutside} _ _ =>
      ∀ {cap tail handler captured outside offered modes},
        HandlerCut requested selectedTail cap tail handler →
        select requested operation selectedOutside = some (.handler captured outside offered modes) →
    ∃ answer residual table families, ∃ plans : ClausePlans handler.clauses families,
    ∃ rows : ClauseRows (clauseSignatures plans),
    ∃ frame : CoreCallableContractExecution.HandlerSource globals outward world residual handler answer table plans rows
        (CoreCallableContractExecution.actualReceiver world outside.scope ambient),
    ∃ outsideAllowed,
      lookup operation table = some offered ∧
      SourceDependencyCapture.lookupDependencies operation families = some modes ∧
      TerminalHandler requested handler.activation rows captured.context ∧
      outside.scope.visibleResources = tail.erase.visible ∧
      captured.scope.visibleResources = cap.erase.visible ∧
      CoreCallableContractExecution.Pending globals outward world outsideAllowed ambient tail answer selectedOutput outside.context ∧
      CoreCallableContractExecution.SelectedPending globals outward world
        (beforeAllowed := selectedAllowed) (whole := selectedTail) (input := selectedAnswer) (output := selectedOutput)
        (wholeContext := selectedOutside) (tailAllowed := outsideAllowed) (tail := tail) (outside := outside.context) frame) generalizing cap tail handler captured outside offered modes with
  | nil => cases physical
  | plain frame received accepts rest ih =>
    cases physical with
    | push runtimeFrame rest cap tail handler miss next =>
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      exact ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .plain terminal, outsideVisible,
        insideVisible, outsidePending, .plainPath frame received accepts path⟩
  | handler frame admitted rest ih =>
    rename_i residual data answer table families plans rows scope ambient outsideAllowed stack output hints context
    cases physical with
    | hit data stack same =>
      rw [← same] at selected
      simp only [select, ↓reduceIte] at selected
      split at selected <;> try { cases selected }
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Selection.handler.inj (Option.some.inj selected)
      rw [← same]
      exact ⟨_, _, _, _, _, _, frame, _, by assumption, by assumption, .here, pending_visible rest, rfl, rest, .here frame admitted rest⟩
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ data.effectInst := by
        intro same
        apply miss
        simp only [ExecFrame.erase, HandlerData.erase, Frame.target, same]
      simp only [select, if_neg different] at selected
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      exact ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .handler terminal, outsideVisible,
        insideVisible, outsidePending, .handlerMiss frame admitted (by simpa only [ScopedTyping.handler_cut_instance next] using Ne.symm different) path⟩
  | handlerView frame admitted entered bounded rest ih =>
    rename_i residual data answer table families plans rows scope ambient beforeAllowed outsideAllowed stack output hints context
    cases physical with
    | hit data stack same =>
      rw [← same] at selected
      simp only [select, ↓reduceIte] at selected
      split at selected <;> try { cases selected }
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Selection.handler.inj (Option.some.inj selected)
      rw [← same]
      exact ⟨_, _, _, _, _, _, frame, _, by assumption, by assumption, .here, pending_visible rest, rfl, rest, .hereView frame admitted entered bounded rest⟩
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ data.effectInst := by
        intro same
        apply miss
        simp only [ExecFrame.erase, HandlerData.erase, Frame.target, same]
      simp only [select, if_neg different] at selected
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      exact ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .handler terminal, outsideVisible,
        insideVisible, outsidePending, .handlerMissView frame admitted entered bounded (by simpa only [ScopedTyping.handler_cut_instance next] using Ne.symm different) path⟩
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved rest ihSaved ihTail =>
    cases physical with
    | live ticket q a saved scope rest cap tail handler next =>
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ihTail next found
      exact ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .live terminal, outsideVisible,
        insideVisible, outsidePending, .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved path⟩
  | spent known answerSame annotation rest ih =>
    cases physical with
    | spent ticket a scope rest cap tail handler next =>
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      exact ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .spent terminal, outsideVisible,
        insideVisible, outsidePending, .spentPath known answerSame annotation path⟩
  | cell issued annotation rest ih =>
    rename_i identity answerType allowed ambient stack input output scope hints context payload caller
    cases physical with
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ .cell identity := by
        intro same
        apply miss
        simp only [ExecFrame.erase, Frame.target, same]
      simp only [select, if_neg different] at selected
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, terminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      refine ⟨answer, residual, table, families, plans, rows, installed, outsideAllowed, foundAt, modesAt, .cell terminal, outsideVisible,
        ?_, outsidePending, .cellPath issued annotation path⟩
      simpa only [Context.pack, SourceDependencyCapture.Scope.visibleResources, Stack.erase, Control.visible,
        ExecFrame.erase, Frame.visible, List.singleton_append] using congrArg (List.cons _) insideVisible
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed originalPhysical contextual terminal ih =>
    cases physical with
    | live ticket q a saved scope rest cap tail handler next =>
      obtain ⟨inside, found, same⟩ := prepend_selection selected
      subst captured
      obtain ⟨answer, residual, table, families, plans, rows, selectedFrame, outsideAllowed, foundAt, modesAt, selectedTerminal, outsideVisible, insideVisible, outsidePending, path⟩ := ih next found
      exact ⟨answer, residual, table, families, plans, rows, selectedFrame, outsideAllowed, foundAt, modesAt, .live selectedTerminal, outsideVisible,
        insideVisible, outsidePending, .captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed originalPhysical contextual terminal path⟩
  | here frame admitted tail ih => exact ih (by assumption) (by assumption)
  | hereView frame admitted entered bounded tail ih => exact ih (by assumption) (by assumption)
  | plainPath saved received accepts selected ih => exact ih (by assumption) (by assumption)
  | handlerMiss saved admitted miss selected ih => exact ih (by assumption) (by assumption)
  | handlerMissView saved admitted entered bounded miss selected ih => exact ih (by assumption) (by assumption)
  | cellPath issued annotation selected ih => exact ih (by assumption) (by assumption)
  | spentPath known answerSame annotation selected ih => exact ih (by assumption) (by assumption)
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => exact ih (by assumption) (by assumption)
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation installedFrame installation physical contextual terminal selected ihInstallation ih => exact ih (by assumption) (by assumption)

omit [DeclarationPolicy] in
private theorem prepend_builtin
    (found : selected.map (Selection.prepend frame) = some (.builtin identity)) :
    selected = some (.builtin identity) := by
  cases selected with
  | none => cases found
  | some selected => cases selected with
    | builtin id => simpa only [Option.map_some, Selection.prepend, Option.some.injEq] using found
    | handler => cases found

/-- A current physical user-handler cut excludes a builtin route in the
same saved source chain. Matching cell boundaries stop physical selection. -/
theorem handler_not_builtin
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (pending : CoreCallableContractExecution.Pending globals outward world allowed ambient whole input output context)
    (physical : HandlerCut requested whole cap tail handler) :
    select requested operation context ≠ some (.builtin identity) := by
  intro found
  induction pending using CoreCallableContractExecution.Pending.rec
    (motive_2 := fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {selectedTail} {_} {_} {selectedOutside} _ _ =>
      ∀ {cap tail handler}, HandlerCut requested selectedTail cap tail handler →
        select requested operation selectedOutside ≠ some (.builtin identity)) generalizing cap tail handler with
  | nil => cases physical
  | plain frame received accepts rest ih => cases physical with
    | push runtimeFrame rest cap tail handler miss next =>
      simp only [select] at found
      exact ih next (prepend_builtin found)
  | handler frame admitted rest ih =>
    rename_i residual data answer table families plans rows scope ambient outsideAllowed stack output hints context
    cases physical with
    | hit data stack same =>
      rw [← same] at found
      simp only [select, ↓reduceIte] at found
      split at found <;> cases found
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ data.effectInst := by
        intro same; apply miss; simp only [ExecFrame.erase, HandlerData.erase, Frame.target, same]
      simp only [select, if_neg different] at found
      exact ih next (prepend_builtin found)
  | handlerView frame admitted entered bounded rest ih =>
    rename_i residual data answer table families plans rows scope ambient beforeAllowed outsideAllowed stack output hints context
    cases physical with
    | hit data stack same =>
      rw [← same] at found
      simp only [select, ↓reduceIte] at found
      split at found <;> cases found
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ data.effectInst := by
        intro same; apply miss; simp only [ExecFrame.erase, HandlerData.erase, Frame.target, same]
      simp only [select, if_neg different] at found
      exact ih next (prepend_builtin found)
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved rest ihSaved ihTail =>
    cases physical with
    | live ticket q a saved scope rest cap tail handler next =>
      simp only [select] at found
      exact ihTail next (prepend_builtin found)
  | spent known answerSame annotation rest ih =>
    cases physical with
    | spent ticket a scope rest cap tail handler next =>
      simp only [select] at found
      exact ih next (prepend_builtin found)
  | cell issued annotation rest ih =>
    rename_i identity answerType allowed ambient stack input output scope hints context payload caller
    cases physical with
    | push runtimeFrame rest cap tail handler miss next =>
      have different : requested ≠ .cell identity := by
        intro same; apply miss; simp only [ExecFrame.erase, Frame.target, same]
      simp only [select, if_neg different] at found
      exact ih next (prepend_builtin found)

  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed originalPhysical contextual terminal ih =>
    cases physical with
    | live ticket q a saved scope rest cap tail handler next =>
      simp only [select] at found
      exact ih next (prepend_builtin found)
  | here frame admitted tail ih => exact ih (by assumption)
  | hereView frame admitted entered bounded tail ih => exact ih (by assumption)
  | plainPath saved received accepts selected ih => exact ih (by assumption)
  | handlerMiss saved admitted miss selected ih => exact ih (by assumption)
  | handlerMissView saved admitted entered bounded miss selected ih => exact ih (by assumption)
  | cellPath issued annotation selected ih => exact ih (by assumption)
  | spentPath known answerSame annotation selected ih => exact ih (by assumption)
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => exact ih (by assumption)
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation installedFrame installation physical contextual terminal selected ihInstallation ih => exact ih (by assumption)

/-- The origin premise covers actual payload dependencies only. The separate
aggregate bound is never used as origin evidence. -/
theorem request_receiver
    (current : CoreCallableContractAdmission.Supported globals outward world allowed scope Environment.empty
      ScopedPorts.Support.empty (.perform effect operation operand) result demand requirements plan rows bound receiver)
    (closed : ClosedValue operand)
    (checked : CorePayloadReceiver.CheckedRequest table port)
    (origins : CorePayloadReceiver.ActivationOrigins)
    (dependencies : ∀ identity, identity ∈ ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies →
      identity ∉ ambient → ∃ origin, CorePayloadReceiver.originAt origins identity = some origin ∧
        origin ∈ checked.record.dependencyOrigins)
    (captured : CorePayloadReceiver.CapturedRealizes checked origins cap ambient)
    (wholeReceived : receiver ⊆ whole.erase.visible ++ ambient)
    (cut : HandlerCut requested whole cap tail handler) :
    CoreCallableReceiverRefinement.ClauseInputSupport operand
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies) (tail.erase.visible ++ ambient) ∧
    ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆ world := by
  have actualSubset : ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆
      ScopedPorts.Support.evaluate ScopedPorts.Support.empty (Code.perform effect operation operand).dependencies := by
    intro identity member
    simpa only [Code.dependencies, ScopedPorts.Support.evaluate, List.flatMap_append, List.mem_append] using
      Or.inr member
  let payload : CorePayloadReceiver.PayloadRealizes checked origins operand
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies) ambient :=
    ⟨closed, SourceSupport.Bounds.canonical _ _, dependencies⟩
  exact ⟨CorePayloadReceiver.receiver_support payload captured
    (actualSubset.trans (current.actual_received.trans wholeReceived)) cut,
    actualSubset.trans (current.actual_received.trans current.receiverIssued)⟩

/-- Current execution evidence supplies whole receiver membership. Checked
origin separation then derives the full issued post-cut receiver. -/
theorem site_payload_receiver
    {receiving : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receiving}
    {context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints}
    (site : CoreCallableContractExecution.Site globals outward world allowed actions phases budget ambient installations
      (.perform effect operation operand) runtimeScope whole result final context root)
    (closed : ClosedValue operand)
    (checked : CorePayloadReceiver.CheckedRequest table port)
    (origins : CorePayloadReceiver.ActivationOrigins)
    (dependencies : ∀ identity, identity ∈ ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies →
      identity ∉ ambient → ∃ origin, CorePayloadReceiver.originAt origins identity = some origin ∧
        origin ∈ checked.record.dependencyOrigins)
    (captured : CorePayloadReceiver.CapturedRealizes checked origins cap ambient)
    (cut : HandlerCut requested whole cap tail handler) :
    CoreCallableReceiverRefinement.ClauseInputSupport operand
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies)
      ((tail.erase.visible ++ ambient).filter (fun identity => identity ∈ world)) := by
  have wholeReceived : CoreCallableContractExecution.actualReceiver world receiving ambient ⊆ whole.erase.visible ++ ambient := by
    rw [← pending_visible site.pending]
    exact CoreCallableContractExecution.actualReceiver.received
  obtain ⟨supported, issued⟩ := request_receiver site.current closed checked origins dependencies captured wholeReceived cut
  refine ⟨supported.actual, ?_⟩
  intro identity member
  exact List.mem_filter.mpr ⟨supported.received member, by simpa using issued member⟩

/-- A ready operand's immediate rows are silent. Current request checking
and accounting come from the same perform source and predecessor evidence. -/
theorem perform_admission
    (source : Source globals outward world allowed runtimeScope Environment.empty
      (.perform effect operation operand) result demand requirements plan rows)
    (certificate : SourceAdmission.Code outward actions budget phases world installations rows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (accounting : Accounting.Run world installations rows context root)
    (closed : ClosedValue operand) :
    ∃ requested,
      effect = Instantiation.freezeEffect requested ∧
      ∃ requestCertificate : SourceAdmission.Code outward actions budget phases world installations
        (Rows.request (effect := requested) (operation := operation)) context,
        InstallationSupport.CodeChecked ambient outward requestCertificate ∧
        Accounting.Run world installations (Rows.request (effect := requested) (operation := operation)) context root := by
  cases source with
  | perform known admitted operandSource formed =>
    cases certificate with
    | sequence operandCertificate requestCertificate =>
      cases checked with
      | sequence operandChecked requestChecked =>
        exact ⟨_, rfl, requestCertificate, requestChecked,
          (Accounting.silent_prefix_iff (CoreCallableContractExecution.Source.value_silent operandSource closed.1) _ _).mp accounting⟩

omit [DeclarationPolicy] in
/-- Mode availability is current guard evidence at the same annotated cut. -/
theorem capture_row
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    (guarded : SourceDependencyChecks.Lexical.Capture wholeScope effect operation)
    (cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation whole captured tail offered modes) :
    ∃ row, offered.row captureScope.held = some row := by
  have actual := cut.select_sound
  cases guarded with
  | builtin found => have impossible := found.symm.trans actual; cases impossible
  | handler found permission row family =>
    have same := SourceDependencyCapture.Selection.handler.inj (Option.some.inj (found.symm.trans actual))
    obtain ⟨rfl, rfl, rfl, rfl⟩ := same
    exact ⟨_, row⟩

/-- The predecessor request certificate determines the actual annotated cut.
A physical user-handler cut cannot be substituted for a builtin route. -/
theorem site_handler_cut
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : CoreCallableContractExecution.Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect requested) operation operand) runtimeScope whole result final context root)
    (closed : ClosedValue operand)
    (physical : HandlerCut requested whole cap tail handler) :
    ∃ captured outside : Packed, ∃ offered modes,
      select requested operation context = some (.handler captured outside offered modes) ∧
      SourceDependencyChecks.Lexical.Capture receiving requested operation ∧
      ∃ row, offered.row captured.scope.held = some row := by
  obtain ⟨actualRequested, sameEffect, requestCertificate, requestChecked, requestRun⟩ :=
    perform_admission site.current.source site.certificate site.certificateChecked site.accounting closed
  have sameRequested : requested = actualRequested := Instantiation.effect_realization_unique
    (Instantiation.frozen_effect_realizes Instantiation.Environment.empty requested)
    (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actualRequested)
  subst actualRequested
  cases requestCertificate with
  | builtin found => exact False.elim (handler_not_builtin site.pending physical found)
  | request cut guarded callbacks ownerBound cleanupBudget selected terminal requiredRights retained body =>
    exact ⟨_, _, _, _, cut, guarded, capture_row guarded cut⟩

omit [DeclarationPolicy] in
/-- Existing retained checks split at the same current cut and construct the
fresh live boundary with the actual clause rights. -/
theorem retained_capture
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    {retained : SourceAdmission.Pending outward actions budget phases world installations whole .nil .ordinary .ordinary}
    (checked : InstallationSupport.PendingChecked ambient outward retained)
    (cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation whole captured tail offered modes)
    (fresh : actions owner = none) (absent : owner ∉ whole.ticketNames)
    (rights : Syntax.OneShotRights) (resumeDemand : List Nat) :
    ∃ next : SourceAdmission.Pending outward (actions.insert owner rights) budget
      (OwnerPhaseTransitions.introduce phases owner) world installations
      (Context.live (owner := owner) (resumeDemand := resumeDemand) captured tail) .nil .ordinary .ordinary,
      InstallationSupport.PendingChecked ambient outward next := by
  have permission := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have absentAll : owner ∉ (whole.append Context.nil).ticketNames := by
    simpa only [Context.append_ticketNames, Context.ticketNames, List.append_nil] using absent
  let permitted := (retained.permissions permission).introduce_absent absentAll
  let checkedPermitted := (checked.permissions permission).introduce_absent absentAll
  obtain ⟨middle, saved, waiting, savedChecked, waitingChecked⟩ := checkedPermitted.at_cut cut
  exact ⟨.live (saved.reindex_outside tail.append_nil_pack.symm) waiting,
    .live (savedChecked.reindex_outside tail.append_nil_pack.symm) waitingChecked⟩

omit [DeclarationPolicy] in
/-- The successor root check is derived from the predecessor annotation and
selected request accounting, within the same budget. -/
theorem capture_root
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    {family : Nat → Dependencies} {bodySignatures : ∀ owner, SourcePlanSignatures.Signature (family owner)}
    {bodyRows : ∀ owner, Rows (bodySignatures owner)}
    (run : Accounting.Run world installations (Rows.request (effect := effect) (operation := operation)) whole root)
    (cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut effect operation whole captured tail offered modes)
    (selected : CapturedClauseRows effect operation captureScope.held captured bodyRows)
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (checked : RecursiveRequirements.Checked [] [] phases (annotateDisposals annotated) row)
    (bounded : row ⊆ budget)
    (owner : Nat) (resumeDemand : List Nat) (absent : owner ∉ whole.ticketNames) :
    ∃ localDemand, ∃ localRoot : RecursiveRequirements.Requirements localDemand, ∃ localRow,
      Accounting.Run world installations (bodyRows owner)
        (Context.live (owner := owner) (resumeDemand := resumeDemand) captured tail) localRoot ∧
      RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.introduce phases owner)
        (annotateDisposals localRoot) localRow ∧ localRow ⊆ budget := by
  obtain ⟨localDemand, localRoot, body, binding⟩ := run.request_body cut selected owner resumeDemand absent
  obtain ⟨normalRow, normalChecked, within⟩ := (disposal_annotation_map annotation).checked checked
  rw [binding.annotate_disposals.2] at normalChecked
  have nextChecked := binding.checked normalChecked
  refine ⟨localDemand, localRoot, normalRow, body, ?_, within.trans bounded⟩
  have samePhase : RecursiveRequirements.withPhase phases owner .available = OwnerPhaseTransitions.introduce phases owner := rfl
  rw [samePhase] at nextChecked
  rw [binding.annotate_disposals.1]
  exact nextChecked

omit [DeclarationPolicy] in
/-- Signature equality and complete row identity transport every current
checking facet together, including accounting for the actual successor root. -/
theorem reindex_admission
    {firstSignature secondSignature : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows firstSignature} {secondRows : Rows secondSignature}
    (sameSignature : firstSignature = secondSignature)
    (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code outward actions budget phases world installations secondRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (run : Accounting.Run world installations secondRows context root) :
    ∃ next : SourceAdmission.Code outward actions budget phases world installations firstRows context,
      InstallationSupport.CodeChecked ambient outward next ∧
      Accounting.Run world installations firstRows context root := by
  cases sameSignature
  cases eq_of_heq sameRows
  exact ⟨certificate, checked, run⟩

/-- A selected installation supplies the private family and the actual
substituted body. Public contracts and complete private row data are retained. -/
theorem handler_capture_source
    (stable : SubstitutionPolicyStable outward)
    (frame : CoreCallableContractExecution.HandlerSource globals outward world residual handler answer table declarations declarationRows receiver)
    (current : CoreCallableContractAdmission.Supported globals outward world allowed scope Environment.empty
      ScopedPorts.Support.empty (.perform (Instantiation.freezeEffect handler.effectInst) operation operand)
      result demand requirements plan rows bound currentReceiver)
    (closed : ClosedValue operand)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row)
    (received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆ receiver)
    (issued : receiver ⊆ world)
    (owner : Nat) (resumeDemand : List Nat) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ resumeEffects closeEffects,
    ∃ family : Nat → Dependencies, ∃ bodies : ∀ owner, Plan (family owner),
    ∃ bodyRows : ∀ owner, Rows (signature (bodies owner)),
    let allocated : OwnerContract := ⟨result, answer, held, resumeDemand, resumeRow, resumeDemand, closeRow, resumeEffects, closeEffects⟩
    ∃ bodyDemand, ∃ bodyRequirements : RecursiveRequirements.Requirements bodyDemand,
    ∃ nextPlan : Plan (family owner), ∃ nextRows : Rows (signature nextPlan),
      Selected operation held declarations parameter binder code bodies ∧
      ClauseRows.Selected operation held declarationRows bodyRows ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      CoreCallableContractAdmission.Supported (globals.withOwner owner allocated) outward world residual
        (.ticket binder owner) Environment.empty ScopedPorts.Support.empty (code.subst parameter operand) answer
        bodyDemand bodyRequirements nextPlan nextRows receiver receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan code (bodies owner) parameter operand ∧
      signature nextPlan = signature (bodies owner) ∧ HEq nextRows (bodyRows owner) := by
  obtain ⟨lexical, empty, authentication⟩ := frame.authentication
  obtain ⟨formalSupport, argument, input, resumeEffects, closeEffects, family, bodies, known, bodyRows, body,
    domainCovered, formalReceived, resumeInterface, closeInterface, chosen, selectedRows, bodyAuthentication⟩ :=
    selected_family_at authentication selected found available
  obtain ⟨payloadRequested, payloadArgument, payload, payloadLexical, sameEffect, payloadKnown, payloadEmpty, payloadAuthentication⟩ :=
    perform_payload current closed
  have sameRequested : handler.effectInst = payloadRequested := Instantiation.effect_realization_unique
    (Instantiation.frozen_effect_realizes Instantiation.Environment.empty handler.effectInst)
    (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty payloadRequested)
  subst payloadRequested
  have interfaces := Option.some.inj (known.symm.trans payloadKnown)
  obtain ⟨sameArgument, sameInput⟩ := Prod.mk.inj interfaces
  subst payloadArgument
  subst input
  let allocated : OwnerContract := ⟨result, answer, held, resumeDemand, resumeRow, resumeDemand, closeRow, resumeEffects, closeEffects⟩
  have bodyAuth := bodyAuthentication owner allocated rfl rfl rfl rfl rfl (List.Perm.refl _)
  obtain ⟨bodyDemand, bodyRequirements, bodySupported⟩ := selected_body_supported_at (globals := globals.withOwner owner allocated) bodyAuth empty issued
  have replacement := payload_supported_at current closed known domainCovered formalReceived received issued
    owner allocated residual binder lexical empty
  obtain ⟨nextPlan, nextRows, successor, exactPlan, sameSignature, sameRows⟩ :=
    bodySupported.substitution_reannotated stable replacement closed
  exact ⟨resumeEffects, closeEffects, family, bodies, bodyRows, bodyDemand, bodyRequirements,
    nextPlan, nextRows, chosen, selectedRows, resumeInterface, closeInterface,
    successor, exactPlan, sameSignature, sameRows⟩

/-- Actual selected-handler capture constructs its successor from current
recursive source, installed private declarations and the same physical cut. -/
theorem capture
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable outward)
    (site : CoreCallableContractExecution.Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect requested) operation operand) runtimeScope whole result final context root)
    (closed : ClosedValue operand)
    (physical : HandlerCut requested whole cap tail handler)
    (ready : ∀ parameter binder code, ClauseAt operation handler.clauses parameter binder code → ClosedExcept parameter code)
    (checkedRequest : CorePayloadReceiver.CheckedRequest requestTable requestPort)
    (origins : CorePayloadReceiver.ActivationOrigins)
    (dependencies : ∀ identity, identity ∈ ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies →
      identity ∉ ambient → ∃ origin, CorePayloadReceiver.originAt origins identity = some origin ∧
        origin ∈ checkedRequest.record.dependencyOrigins)
    (crossed : CorePayloadReceiver.CapturedRealizes checkedRequest origins cap ambient)
    (owner : Nat) (freshOwner : globals.owners owner = none)
    (freshAction : actions owner = none) (absent : owner ∉ context.ticketNames)
    (resumeDemand : List Nat) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ captured outside : Packed,
    ∃ answer residual parameter binder code resumeEffects closeEffects,
    ∃ family : Nat → Dependencies, ∃ bodies : ∀ owner, Plan (family owner),
    ∃ bodyRows : ∀ owner, Rows (signature (bodies owner)),
    let allocated : OwnerContract := ⟨result, answer, captured.scope.held, resumeDemand, resumeRow,
      resumeDemand, closeRow, resumeEffects, closeEffects⟩
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
    ∃ next : CoreCallableContractExecution.Site (globals.withOwner owner allocated) outward world residual
      (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner) budget ambient installations
      (code.subst parameter operand) (.ticket binder owner)
      (.live owner (CoreCallableContractExecution.runtimeType result) handler.answer cap handler.scope tail)
      answer final (Context.live (owner := owner) (resumeDemand := resumeDemand) captured.context outside.context) nextRoot,
      ClauseAt operation handler.clauses parameter binder code ∧
      SourceDependencyChecks.Lexical.Capture receiving requested operation ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, runtimeScope, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (CoreCallableContractExecution.runtimeType result) handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      next.dependencies = family owner ∧
      HEq next.plan (CoreCallablePlanSubstitution.plan code (bodies owner) parameter operand) ∧
      HEq (signature next.plan) (signature (bodies owner)) ∧ HEq next.rows (bodyRows owner) := by
  obtain ⟨captured, outside, offered, modes, staticCut, guarded, row, rowAvailable⟩ := site_handler_cut site closed physical
  obtain ⟨answer, residual, table, families, declarations, declarationRows, frame, outsideAllowed, found, modesAt,
    terminal, outsideVisible, capturedVisible, outsidePending, installed⟩ :=
    pending_selected_handler site.pending physical staticCut
  obtain ⟨parameter, binder, code, located⟩ := declaration_clause frame.source found
  have payloadReceiver := site_payload_receiver site closed checkedRequest origins dependencies crossed physical
  have received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies ⊆
      CoreCallableContractExecution.actualReceiver world outside.scope ambient := by
    simpa only [CoreCallableContractExecution.actualReceiver, outsideVisible] using payloadReceiver.received
  have effectSame := ScopedTyping.handler_cut_instance physical
  subst requested
  have currentAt := site.current
  obtain ⟨resumeEffects, closeEffects, family, bodies, bodyRows, bodyDemand, bodyRequirements,
    nextPlan, nextRows, chosen, selectedRows, resumeInterface, closeInterface,
    nextCurrent, exactPlan, sameSignature, sameRows⟩ :=
    handler_capture_source stable frame currentAt closed located found rowAvailable received
      CoreCallableContractExecution.actualReceiver.issued owner resumeDemand resumeRow closeRow
  let allocated : OwnerContract := ⟨result, answer, captured.scope.held, resumeDemand, resumeRow,
    resumeDemand, closeRow, resumeEffects, closeEffects⟩
  obtain ⟨actualRequested, sameEffect, requestCertificate, requestChecked, requestRun⟩ :=
    perform_admission site.current.source site.certificate site.certificateChecked site.accounting closed
  have sameRequested : handler.effectInst = actualRequested := Instantiation.effect_realization_unique
    (Instantiation.frozen_effect_realizes Instantiation.Environment.empty handler.effectInst)
    (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actualRequested)
  subst actualRequested
  let selected : CapturedClauseRows handler.effectInst operation captured.scope.held captured.context bodyRows := .selected terminal selectedRows
  have rights := SourceAdmission.rightsAt_clause located declarations
  let bodyCertificate := requestCertificate.capture_body_with_rights staticCut selected terminal rights freshAction absent resumeDemand
  let bodyChecked := requestChecked.capture_body_with_rights staticCut selected terminal rights freshAction absent resumeDemand
  obtain ⟨localDemand, localRoot, localRow, bodyRun, localChecked, localBounded⟩ :=
    capture_root requestRun staticCut selected site.annotation site.checked site.bounded owner resumeDemand absent
  obtain ⟨nextCertificate, nextChecked, nextRun⟩ := reindex_admission sameSignature sameRows bodyCertificate bodyChecked bodyRun
  obtain ⟨nextRetained, nextRetainedChecked⟩ := retained_capture site.retainedChecked staticCut freshAction absent code.requiredActions resumeDemand
  have ownerExtension := OwnerKnownMonotone.insert_fresh (contract := allocated) freshOwner
  -- Exact transport of the joint installed path produces before/frame/tail.
  let transportedFrame := frame.owners_congr (globals.owners.insert owner allocated)
  have transportedInstalled := installed.owners_known_mono ownerExtension
  let nextPending := CoreCallableContractExecution.Pending.capture (contract := allocated)
    (by exact Owners.insert_here) rfl rfl rfl rfl (List.Perm.refl _)
    (CoreCallableContractExecution.runtimeType_port result) frame.annotation
    transportedFrame transportedInstalled physical staticCut terminal
  let next : CoreCallableContractExecution.Site (globals.withOwner owner allocated) outward world residual
      (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner) budget ambient installations
      (code.subst parameter operand) (.ticket binder owner)
      (.live owner (CoreCallableContractExecution.runtimeType result) handler.answer cap handler.scope tail)
      answer final (Context.live (owner := owner) (resumeDemand := resumeDemand) captured.context outside.context) localRoot :=
    { sourceDemand := bodyDemand, requirements := bodyRequirements, dependencies := family owner,
      plan := nextPlan, rows := nextRows, bound := CoreCallableContractExecution.actualReceiver world outside.scope ambient,
      current := nextCurrent, received := CoreCallableContractExecution.actualReceiver.received,
      certificate := nextCertificate, certificateChecked := nextChecked, pending := nextPending,
      retained := nextRetained, retainedChecked := nextRetainedChecked, accounting := nextRun,
      annotated := localRoot, row := localRow, annotation := .original, checked := localChecked, bounded := localBounded }
  exact ⟨captured, outside, answer, residual, parameter, binder, code, resumeEffects, closeEffects,
    family, bodies, bodyRows, localDemand, localRoot, next, located, guarded,
    .capture _ _ _ _ _ _ _ _ _ _ _ _ _ physical located closed (ready _ _ _ located),
    rfl, heq_of_eq exactPlan, heq_of_eq sameSignature, sameRows⟩

end
end Ash.OneShot.CoreCallableContractCaptureConnection
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.domain_selected_family
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.selected_family_at
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.selected_family

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.request_receiver

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.pending_visible

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.selected_body_supported_at
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.payload_supported_at
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.selected_body_supported


#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.site_payload_receiver

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.perform_payload

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.payload_supported

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.handler_capture_source

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.pending_selected_handler

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.perform_admission

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.retained_capture
#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.capture_root

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.handler_not_builtin

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.capture_row

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.reindex_admission

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.site_handler_cut

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.declaration_clause

#print axioms Ash.OneShot.CoreCallableContractCaptureConnection.capture
