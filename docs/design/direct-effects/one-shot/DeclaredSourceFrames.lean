import DeclaredSourceSubstitution
import DeclaredSourceEntry

/-! Hereditary evidence for all existing waiting contexts and execution frames.
    The same full values, owner demand and recursive requirement indices are
    retained. The indexed AnnotatedSegment reuses capture and allocation; no
    execution rule changes. -/
namespace Ash.OneShot.DeclaredSourceFrames
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open Owners (Contracts)
open RecursiveRequirements (Requirements)
open DeclaredSources (Expression Callable Declarations)
open DeclaredSourceValues (ValueSummary)

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) (scope : Execution.Scope) :
    ScopedExecution.Context → Value → Value → (demand : List Nat) → Requirements demand → Prop where
  | pairLeft (right : Expression operations policy contracts world allowed scope environment code output demand requirements) :
      Context operations policy contracts world environment allowed scope (.pairLeft code) input (.pair input output) demand requirements
  | pairRight (left : ValueSummary operations policy contracts world environment allowed code input) :
      Context operations policy contracts world environment allowed scope (.pairRight code) output (.pair input output) [] (.request [] [])
  | appFunction (argument : Expression operations policy contracts world allowed scope environment code input demand requirements)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appFunction code) (.function input output requests latent)
        output demand (.emitAfter requirements [] latent)
  | appArgument (function : ValueSummary operations policy contracts world environment allowed code (.function input output requests latent))
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appArgument code) input output [] (.request [] latent)
  | bind (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) code output demand requirements) :
      Context operations policy contracts world environment allowed scope (.bind parameter code) input output demand requirements
  | branch (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no)
      (same : yesDemand.Perm noDemand) :
      Context operations policy contracts world environment allowed scope (.branch a b) .boolean output yesDemand (.choice yes no same)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.port) :
      Context operations policy contracts world environment allowed scope (.perform (Instantiation.freezeEffect effect) operation)
        input output [] (.request [] [⟨effect, operation, false⟩])
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Context operations policy contracts world environment allowed scope (.resume binder) contract.input contract.answer
        (owner :: contract.resumeDemand) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])
  | cleanup (body : Expression operations policy contracts world allowed scope environment code output demand requirements)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.cleanup code) (.function .unit .unit requests latent)
        output demand (.emitAfter requirements [] (qualify true latent))
  | resource {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Callable operations policy contracts
        (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output [] (.request [] raw)
  | scopedResource {bodyRequirements : Nat → Requirements demand}
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand (bodyRequirements identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output demand outward
inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → Prop where
  | plain (source : Context operations policy contracts world Environment.empty allowed plain.scope plain.context input output demand requirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports plain.scope ticket)
      (inputAnnotation : input.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.port = ScopedPorts.eraseType plain.output) :
      Frame operations policy contracts tables world (.plain plain) input output demand requirements
  | handler (typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types world (.handler handler))
      (annotation : answer.port = ScopedPorts.eraseType handler.answer)
      (declarations : Declarations operations policy contracts world Environment.empty allowed
        handler.effectInst answer handler.clauses (tables handler))
      (capabilities : ClausesUse policy handler.clauses)
      (modes : SourceTemplates.ClauseModes handler.clauses (tables handler)) :
      Frame operations policy contracts tables world (.handler handler) answer answer [] (.request [] [])
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.port = ScopedPorts.eraseType answer) :
      Frame operations policy contracts tables world (.cell identity payload scope answer) result result [] (.request [] [])
  | armed (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      Frame operations policy contracts tables world (.armed action) result result [] (.request [] (qualify true latent))
  | running (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (saved : ValueSummary operations policy contracts world Environment.empty [] value result)
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      Frame operations policy contracts tables world (.running action value closed) .unit result [] (.request [] [])
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
      Frame operations policy contracts tables world (.closing identity scope) .unit .unit [] (.request [] [])
  | retiring (known : contracts owner = some contract) :
      Frame operations policy contracts tables world (.retiring owner) .unit .unit [owner] (.retire owner)

theorem context_erase
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements) :
    SourceTemplates.Context operations policy contracts world environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (DeclaredSources.expression_erase right)
  | pairRight left => exact .pairRight (DeclaredSourceValues.erase left)
  | appFunction argument admitted => exact .appFunction (DeclaredSources.expression_erase argument) admitted
  | appArgument function admitted => exact .appArgument (DeclaredSourceValues.erase function) admitted
  | bind body => exact .bind (DeclaredSources.expression_erase body)
  | branch yes no same => exact .branch (DeclaredSources.expression_erase yes) (DeclaredSources.expression_erase no) same
  | perform known admitted formed => exact .perform known admitted formed
  | resume known resolved permission admitted formed => exact .resume known resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (DeclaredSources.expression_erase body) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource (fun identity fresh => (body identity fresh).erase) formed effectsBound admitted outward
  | scopedResource body formed effectsBound admitted hidden =>
      exact .scopedResource (fun identity fresh => DeclaredSources.expression_erase (body identity fresh)) formed effectsBound admitted hidden

theorem frame_erase
    (source : Frame operations policy contracts tables world entry input output demand requirements) :
    SourceTemplates.Frame operations policy contracts world entry input output demand requirements := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation => exact .plain (context_erase source) scopeTyped inputAnnotation outputAnnotation
  | handler typed annotation declarations capabilities modes => exact .handler typed annotation
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation => exact .armed scopeKnown (DeclaredSourceValues.erase callback) annotation
  | running scopeKnown callback saved annotation => exact .running scopeKnown (DeclaredSourceValues.erase callback) (DeclaredSourceValues.erase saved) annotation
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known => exact .retiring known

theorem frame_declarations
    (source : Frame operations policy contracts tables world entry input output demand requirements) :
    DeclaredSourceEntry.FrameDeclarations operations policy contracts tables world entry input output := by
  cases source with
  | handler typed annotation declarations capabilities modes => exact ⟨_, declarations⟩
  | _ => trivial

abbrev Segment operations policy contracts tables world :=
  RecursiveCapture.AnnotatedSegment (Frame operations policy contracts tables world)
    operations policy contracts tables world

theorem push
    (head : Frame operations policy contracts tables world entry input middle headDemand first)
    (tail : Segment operations policy contracts tables world rest middle output tailDemand second records) :
    Segment operations policy contracts tables world (.push entry rest) input output (headDemand ++ tailDemand)
      (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records :=
  .push head (frame_erase head) tail

theorem segment_declarations
    (source : Segment operations policy contracts tables world stack input output demand requirements records) :
    DeclaredSourceEntry.HandlerSegment operations policy contracts tables world stack input output demand requirements records :=
  source.extension (fun _ _ known => known) (fun _ _ _ _ _ current => frame_declarations current)

theorem context_world_weaken
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements)
    (larger : world ⊆ next) :
    Context operations policy contracts next environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (DeclaredSourceTransport.expression_world_weaken right larger)
  | pairRight left => exact .pairRight (DeclaredSourceValues.world_weaken left larger)
  | appFunction argument admitted => exact .appFunction (DeclaredSourceTransport.expression_world_weaken argument larger) admitted
  | appArgument function admitted => exact .appArgument (DeclaredSourceValues.world_weaken function larger) admitted
  | bind body => exact .bind (DeclaredSourceTransport.expression_world_weaken body larger)
  | branch yes no same => exact .branch (DeclaredSourceTransport.expression_world_weaken yes larger) (DeclaredSourceTransport.expression_world_weaken no larger) same
  | perform known admitted formed => exact .perform known admitted (ScopedPorts.in_world_mono formed larger)
  | resume known resolved permission admitted formed => exact .resume known resolved permission admitted (ScopedPorts.in_world_mono formed larger)
  | cleanup body admitted => exact .cleanup (DeclaredSourceTransport.expression_world_weaken body larger) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource
        (fun identity fresh => DeclaredSourceTransport.callable_world_weaken (body identity (fun member => fresh (larger member)))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))
  | scopedResource body formed effectsBound admitted hidden =>
      exact .scopedResource
        (fun identity fresh => DeclaredSourceTransport.expression_world_weaken (body identity (fun member => fresh (larger member)))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))
theorem frame_world_weaken
    (source : Frame operations policy contracts tables world entry input output demand requirements)
    (larger : world ⊆ next) : Frame operations policy contracts tables next entry input output demand requirements := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      exact .plain (context_world_weaken source larger) scopeTyped inputAnnotation outputAnnotation
  | handler typed annotation declarations capabilities modes =>
      exact .handler (ScopedPorts.frame_world_weaken typed larger) annotation
        (DeclaredSourceTransport.declarations_world_weaken declarations larger) capabilities modes
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation => exact .armed scopeKnown (DeclaredSourceValues.world_weaken callback larger) annotation
  | running scopeKnown callback saved annotation =>
      exact .running scopeKnown (DeclaredSourceValues.world_weaken callback larger) (DeclaredSourceValues.world_weaken saved larger) annotation
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known => exact .retiring known
theorem context_extension
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements)
    (extension : contracts.Extends larger) :
    Context operations policy larger world environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (DeclaredSourceTransport.expression_extension right extension)
  | pairRight left => exact .pairRight (DeclaredSourceValues.extension left extension)
  | appFunction argument admitted => exact .appFunction (DeclaredSourceTransport.expression_extension argument extension) admitted
  | appArgument function admitted => exact .appArgument (DeclaredSourceValues.extension function extension) admitted
  | bind body => exact .bind (DeclaredSourceTransport.expression_extension body extension)
  | branch yes no same => exact .branch (DeclaredSourceTransport.expression_extension yes extension) (DeclaredSourceTransport.expression_extension no extension) same
  | perform known admitted formed => exact .perform known admitted formed
  | resume known resolved permission admitted formed => exact .resume (extension _ _ known) resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (DeclaredSourceTransport.expression_extension body extension) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource
        (fun identity fresh => DeclaredSourceTransport.callable_extension (body identity fresh) extension) formed effectsBound admitted outward
  | scopedResource body formed effectsBound admitted hidden =>
      exact .scopedResource (fun identity fresh => DeclaredSourceTransport.expression_extension (body identity fresh) extension)
        formed effectsBound admitted hidden
theorem frame_extension (source : Frame operations policy contracts tables world entry input output demand requirements)
    (extension : contracts.Extends larger) : Frame operations policy larger tables world entry input output demand requirements := by
  have ports := Owners.port_contracts_extension extension
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      exact .plain (context_extension source extension) (ScopedPorts.effect_scope_extension scopeTyped ports) inputAnnotation outputAnnotation
  | handler typed annotation declarations capabilities modes =>
      exact .handler (ScopedPorts.frame_typed_extension typed types) annotation
        (DeclaredSourceTransport.declarations_extension declarations extension) capabilities modes
  | cell scopeKnown noEscape annotation => exact .cell (ScopedPorts.scope_known_extension scopeKnown types) noEscape annotation
  | armed scopeKnown callback annotation => exact .armed (ScopedPorts.scope_known_extension scopeKnown types) (DeclaredSourceValues.extension callback extension) annotation
  | running scopeKnown callback saved annotation => exact .running (ScopedPorts.scope_known_extension scopeKnown types) (DeclaredSourceValues.extension callback extension) (DeclaredSourceValues.extension saved extension) annotation
  | closing scopeKnown => exact .closing (ScopedPorts.scope_known_extension scopeKnown types)
  | retiring known => exact .retiring (extension _ _ known)

theorem segment_world_weaken
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (larger : world ⊆ next) :
    Segment operations policy contracts tables next stack input output demand requirements records :=
  source.world_weaken larger (fun _ _ _ _ _ current => frame_world_weaken current larger)

theorem segment_extension
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (extension : contracts.Extends larger) :
    Segment operations policy larger tables world stack input output demand requirements records :=
  source.extension extension (fun _ _ _ _ _ current => frame_extension current extension)

theorem frame_tables_congr
    (source : Frame operations policy contracts first world entry input output demand requirements)
    (agree : ∀ handler, handler.activation ∈ entry.erase.activation → first handler = second handler) :
    Frame operations policy contracts second world entry input output demand requirements := by
  cases source with
  | plain context scopeTyped inputAnnotation outputAnnotation => exact .plain context scopeTyped inputAnnotation outputAnnotation
  | handler typed annotation declarations capabilities modes =>
      exact .handler typed annotation (agree _ List.mem_cons_self ▸ declarations) capabilities
        (agree _ List.mem_cons_self ▸ modes)
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation => exact .armed scopeKnown callback annotation
  | running scopeKnown callback saved annotation => exact .running scopeKnown callback saved annotation
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known => exact .retiring known

theorem segment_tables_congr
    (source : Segment operations policy contracts first world stack input output demand requirements records)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    Segment operations policy contracts second world stack input output demand requirements records :=
  RecursiveHandlerTables.annotated_segment_congr source
    (fun _ _ _ _ _ agreed current => frame_tables_congr current agreed) agree

/-- Allocation first extends the checked kernel records. This projection then
    extends the retained hereditary frame evidence under that same contract. -/
theorem segment_reindex_contracts
    (source : RecursiveCapture.AnnotatedSegment (Frame operations policy before tables world)
      operations policy after tables world stack input output demand requirements records)
    (extension : before.Extends after) :
    Segment operations policy after tables world stack input output demand requirements records :=
  source.extension (fun _ _ known => known) (fun _ _ _ _ _ current => frame_extension current extension)

end Ash.OneShot.DeclaredSourceFrames
#print axioms Ash.OneShot.DeclaredSourceFrames.context_erase
#print axioms Ash.OneShot.DeclaredSourceFrames.frame_erase
#print axioms Ash.OneShot.DeclaredSourceFrames.frame_declarations
#print axioms Ash.OneShot.DeclaredSourceFrames.push
#print axioms Ash.OneShot.DeclaredSourceFrames.segment_declarations

#print axioms Ash.OneShot.DeclaredSourceFrames.context_world_weaken
#print axioms Ash.OneShot.DeclaredSourceFrames.frame_world_weaken
#print axioms Ash.OneShot.DeclaredSourceFrames.context_extension
#print axioms Ash.OneShot.DeclaredSourceFrames.frame_extension
#print axioms Ash.OneShot.DeclaredSourceFrames.segment_world_weaken
#print axioms Ash.OneShot.DeclaredSourceFrames.segment_extension
#print axioms Ash.OneShot.DeclaredSourceFrames.frame_tables_congr
#print axioms Ash.OneShot.DeclaredSourceFrames.segment_tables_congr
#print axioms Ash.OneShot.DeclaredSourceFrames.segment_reindex_contracts
