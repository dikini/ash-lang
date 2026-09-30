import SourcePlannedCheckedInterfaces

/-! Extend the registry, permissions and available phases of joint source/checking
segments without changing their plans, refined values, hints or ownership records.
The existing source-extension and Local-transport proofs supply the substantive
expression and invocation cases. -/
namespace Ash.OneShot.SourcePlannedCheckedFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Contracts)
open SourcePlannedSources (Expression Body Offer Declarations Context expression_extension)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (Signature)
open SourceContextualHints (Hints)

theorem erased_extension {contracts next : Contracts} (extension : contracts.Extends next) :
    contracts.erase.Extends next.erase := by
  intro owner previous known
  simp only [Contracts.erase, Option.map_eq_some_iff] at known
  obtain ⟨actual, known, rfl⟩ := known
  simp only [Contracts.erase, extension _ _ known, Option.map_some]

theorem body_extension {checking : Signature dependencies}
    (source : Body operations policy contracts world allowed scope environment code answer header checking)
    (extension : contracts.Extends next) :
    Body operations policy next world allowed scope environment code answer header checking := by
  cases source with | typed source rows closingRows => exact .typed (expression_extension source extension) rows closingRows

theorem offer_extension {plans : SourceDeclarationPlans.ModePlans family}
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans)
    (extension : contracts.Extends next) :
    Offer operations policy next world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface body =>
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact body_extension (body owner contract (SourcePlannedTyping.extension_fresh extension fresh)
        inputSame answerSame resumeSame closeSame heldSame balance) (SourcePlannedTyping.insert_extension extension)

theorem declarations_extension {plans : ClausePlans clauses families}
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table plans)
    (extension : contracts.Extends next) :
    Declarations operations policy next world environment allowed effect answer clauses table plans := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest => cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_extension ordinary extension) (offer_extension protectedMode extension) (ihRest rest)
  all_goals trivial

theorem context_extension {checking : Signature dependencies}
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements checking)
    (extension : contracts.Extends next) :
    Context operations policy next world environment allowed scope position input output demand requirements checking := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_extension right extension)
  | pairRight left => exact .pairRight (expression_extension left extension)
  | appFunction argument admitted => exact .appFunction (expression_extension argument extension) admitted
  | appArgument function admitted => exact .appArgument (expression_extension function extension) admitted
  | bind body => exact .bind (expression_extension body extension)
  | branch yes no same => exact .branch (expression_extension yes extension) (expression_extension no extension) same
  | perform known admitted formed => exact .perform known admitted formed
  | resume known resolved permission admitted formed => exact .resume (extension _ _ known) resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (expression_extension body extension) admitted
  | resource body formed effectsBound admitted hidden =>
      exact .resource (fun identity fresh => expression_extension (body identity fresh) extension) formed effectsBound admitted hidden

theorem Frame.transport [certification : SourcePlannedChecks.DeclarationPolicy]
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate incoming outgoing)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Frame (evidence := evidence) operations policy nextContracts tables families required outward nextActions after world
      receiving entry input output demand requirements layer decorate incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension
    (SourceDependencyFrames.erased_contract_extension (erased_extension extension))
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked =>
      exact .plain (context_extension context extension) (ScopedPorts.effect_scope_extension scope ports)
        inputAnnotation outputAnnotation (SourcePlannedPhases.local_transport checked phases permissions)
  | handler scope annotation clauses coverage unique declarations recipes capabilities modes =>
      exact .handler (ScopedPorts.effect_scope_known_extension scope ports) annotation clauses coverage unique
        (declarations_extension declarations extension) recipes capabilities modes
  | cell scope noEscape annotation interface =>
      exact .cell (ScopedPorts.scope_known_extension scope types) noEscape annotation (ScopedPorts.effect_frame_extension interface ports)
  | armed scope callback annotation interface checked =>
      exact .armed (ScopedPorts.scope_known_extension scope types) (expression_extension callback extension) annotation
        (ScopedPorts.effect_frame_extension interface ports) (SourcePlannedPhases.local_transport checked phases permissions)
  | running scope callback saved annotation interface =>
      exact .running (ScopedPorts.scope_known_extension scope types) (expression_extension callback extension)
        (expression_extension saved extension) annotation (ScopedPorts.effect_frame_extension interface ports)
  | closing scope interface =>
      exact .closing (ScopedPorts.scope_known_extension scope types) (ScopedPorts.effect_frame_extension interface ports)
  | retiring known interface => exact .retiring (extension _ _ known) (ScopedPorts.effect_frame_extension interface ports)

theorem Segment.transport [certification : SourcePlannedChecks.DeclarationPolicy]
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records hints outside incoming outgoing)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Segment (evidence := evidence) operations policy nextContracts tables families required nextActions outward after world
      stack input output demand requirements records hints outside incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension
    (SourceDependencyFrames.erased_contract_extension (erased_extension extension))
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.transport extension phases permissions) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ actionKnown) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension scope ports) held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports) ih bound

end Ash.OneShot.SourcePlannedCheckedFrames

#print axioms Ash.OneShot.SourcePlannedCheckedFrames.erased_extension
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.body_extension
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.offer_extension
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.declarations_extension
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.context_extension
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Frame.transport
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Segment.transport
