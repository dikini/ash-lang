import SourceAnnotatedRuntimeHandlers

/-! Resource-world extension preserves actual annotated current and saved
sources. The existing source and scheduling transports supply the recursive cases. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExpressions
open SourceDeclarationPlans (ClausePlans)
open SourcePlanSignatures (Signature)

theorem body_world_weaken {checking : Signature dependencies}
    (source : Body operations policy contracts world allowed scope environment code answer header checking)
    (larger : world ⊆ nextWorld) :
    Body operations policy contracts nextWorld allowed scope environment code answer header checking := by
  cases source with | typed source rows closingRows => exact .typed (expression_world_weaken source larger) rows closingRows

theorem offer_world_weaken {plans : SourceDeclarationPlans.ModePlans family}
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans)
    (larger : world ⊆ nextWorld) :
    Offer operations policy contracts nextWorld environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface body =>
      exact .available resumeInterface closeInterface
        (fun owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
          body_world_weaken (body owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance) larger)

theorem declarations_world_weaken {plans : ClausePlans clauses.erase families}
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table plans)
    (larger : world ⊆ nextWorld) :
    Declarations operations policy contracts nextWorld environment allowed effect answer clauses table plans := by
  induction clauses using SourceAnnotatedCode.Clauses.rec (motive_1 := fun _ => True) generalizing table families
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest => cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_world_weaken ordinary larger) (offer_world_weaken protectedMode larger) (ihRest rest)
  all_goals trivial

theorem context_world_weaken {checking : Signature dependencies}
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements checking)
    (larger : world ⊆ nextWorld) :
    Context operations policy contracts nextWorld environment allowed scope position input output demand requirements checking := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_world_weaken right larger)
  | pairRight left isValue => exact .pairRight (expression_world_weaken left larger) isValue
  | appFunction argument admitted => exact .appFunction (expression_world_weaken argument larger) admitted
  | appArgument function isValue admitted => exact .appArgument (expression_world_weaken function larger) isValue admitted
  | bind body => exact .bind (expression_world_weaken body larger)
  | branch yes no same => exact .branch (expression_world_weaken yes larger) (expression_world_weaken no larger) same
  | perform known admitted formed => exact .perform known admitted (ScopedPorts.in_world_mono formed larger)
  | resume known resolved permission admitted formed =>
      exact .resume known resolved permission admitted (ScopedPorts.in_world_mono formed larger)
  | cleanup body admitted => exact .cleanup (expression_world_weaken body larger) admitted
  | resource body formed effectsBound admitted hidden =>
      exact .resource
        (fun identity fresh => expression_world_weaken (body identity (fun member => fresh (larger member)))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))

end Ash.OneShot.SourceAnnotatedSources

namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open SourceAnnotatedSources

theorem Frame.world_weaken
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (larger : world ⊆ nextWorld) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions phases nextWorld receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation checked =>
      exact .plain (context_world_weaken context larger) hint closed scope inputAnnotation outputAnnotation
        (SourceScheduledTransport.local_transport_world checked (fun _ same => same) (fun _ _ known => known) larger)
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      exact .handler scope annotation (ScopedPorts.clauses_world_weaken clauses larger) coverage unique
        (declarations_world_weaken declarations larger) recipes supplied capabilities modes
  | cell scope noEscape annotation interface =>
      exact .cell scope noEscape annotation (ScopedPorts.effect_frame_world_weaken interface larger)
  | armed scope callback annotation interface checked =>
      exact .armed scope (Values.world_weaken callback larger) annotation
        (ScopedPorts.effect_frame_world_weaken interface larger)
        (SourceScheduledTransport.local_transport_world checked (fun _ same => same) (fun _ _ known => known) larger)
  | running scope callback saved annotation interface =>
      exact .running scope (Values.world_weaken callback larger) (Values.world_weaken saved larger) annotation
        (ScopedPorts.effect_frame_world_weaken interface larger)
  | closing scope interface => exact .closing scope (ScopedPorts.effect_frame_world_weaken interface larger)
  | retiring known interface => exact .retiring known (ScopedPorts.effect_frame_world_weaken interface larger)

theorem Segment.world_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing)
    (larger : world ⊆ nextWorld) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases nextWorld
      stack input output demand requirements records forest outside incoming outgoing := by
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.world_weaken larger) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

end Ash.OneShot.SourceAnnotatedRuntimeTyping


#print axioms Ash.OneShot.SourceAnnotatedSources.body_world_weaken

#print axioms Ash.OneShot.SourceAnnotatedSources.offer_world_weaken

#print axioms Ash.OneShot.SourceAnnotatedSources.declarations_world_weaken

#print axioms Ash.OneShot.SourceAnnotatedSources.context_world_weaken

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.world_weaken

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.world_weaken
