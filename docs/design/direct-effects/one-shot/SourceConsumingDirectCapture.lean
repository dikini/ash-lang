import SourceConsumingBoundAnnotations
import SourceScheduledCapabilityTransport
import SourceScheduledCapabilityPhases
import SourceScheduledCapabilityProviders

/-! Capture generation for consuming clauses with builtin resource scopes and
pure cleanup callbacks.
The captured source is an arbitrary recursive capability annotation, including
branches and calls to owners in the waiting tail. Source induction handles
operation prefixes and choices; existing neutral transport handles the new spent
marker and pure cleanup wrappers, and provider transport handles resource
wrappers. Handlers and effectful cleanup require separate transport. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceDependencyOwners (owners)
open OwnerPhaseTransitions (spend introduce)

section
variable [declarations : DeclarationPolicy]

/-- This source fragment can request effects, branch, allocate builtin
resources and register pure cleanup before consumption. It imposes no
restriction on the captured source or on the owners that source may invoke. -/
inductive Body.Direct : {world : List Nat} → {owner : Nat} →
    {dependencies : SourceDependencyAnnotations.Dependencies} → {plan : Plan dependencies} →
    Body world owner plan → Prop where
  | resume : Body.Direct .resume
  | dispose : Body.Direct .dispose
  | sequence : Body.Direct body → Body.Direct (.sequence required footprint declared body)
  | choice : Body.Direct first → Body.Direct second → Body.Direct (.choice first second)
  | cleanup : Body.Direct body →
      Body.Direct (.cleanup (needs := []) (callback := .pure) required footprint declared body)
  | resource (body : ∀ identity fresh, Body.Direct (code identity fresh)) : Body.Direct (.resource code)

def Modes.Direct {plans : SourceDeclarationPlans.ModePlans family} (modes : Modes world plans) : Prop :=
  match modes with
  | .unavailable => True
  | .available bodies => ∀ owner, (bodies owner).Direct

def Declarations.Direct {plans : ClausePlans clauses families} (source : Declarations world plans) : Prop :=
  match source with
  | .nil => True
  | .cons ordinary protectedMode rest => ordinary.Direct ∧ protectedMode.Direct ∧ rest.Direct

/-- Exact offered-mode selection keeps the direct-source derivation together
with the bounds and requirements of that same body. -/
theorem Bounded.selected_direct {plans : ClausePlans clauses families} {annotations : Declarations world plans}
    {bounds : ClauseBounds plans} (admitted : Bounded bounds annotations required)
    (direct : annotations.Direct)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    ∃ contract needed, ∃ body : Body world owner (bodies owner),
      bounds.lookup operation held = some contract ∧
      Admitted code.requiredActions contract.resume contract.close body needed ∧ needed ⊆ required ∧ body.Direct := by
  induction selected generalizing required with
  | ordinary => cases admitted with
    | cons ordinary protectedMode rest => cases ordinary with
      | available source nested =>
          exact ⟨_, _, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
            (fun item member => List.mem_append_left _ (List.mem_append_left _ member)), direct.1 owner⟩
  | protectedMode => cases admitted with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available source nested =>
          exact ⟨_, _, _, by simp [ClauseBounds.lookup, ModeBounds.value], available_body source,
            (fun item member => List.mem_append_left _ (List.mem_append_right _ member)), direct.2.1 owner⟩
  | pass different next ih => cases admitted with
    | cons ordinary protectedMode rest =>
        obtain ⟨contract, needed, body, found, source, included, bodyDirect⟩ := ih rest direct.2.2
        exact ⟨contract, needed, body, by simpa only [ClauseBounds.lookup, if_neg different] using found,
          source, (fun item member => List.mem_append_right _ (included member)), bodyDirect⟩

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The generator consumes the clause's structural bound check and annotations
of the actual retained source. Its recursive calls follow source syntax, never
the length of an execution or an assumed successful successor check. -/
theorem Body.Direct.generate
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {body : Body world owner plan} (direct : body.Direct)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved waiting)
    (before : SourceScheduledRetainedInterfaces.Interfaces world front)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases
      wholeScope waitingScope before)
    (resumption : (actions owner).any (fun rights => rights.resume) = true →
      ∃ inside : Retained world saved (front.append (.spent (owner := owner) waiting)),
        inside.Valid outward actions (spend phases owner))
    (closing : (actions owner).any (fun rights => rights.dispose) = true →
      ∃ inside : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) waiting))),
        inside.Valid outward actions (spend phases owner))
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (after : Retained world waiting .nil) (tailReady : after.Valid outward actions (spend phases owner)) :
    ∃ annotation : Code world plan whole,
      annotation.Valid outward actions phases := by
  induction direct generalizing wholeScope frontScope savedScope waitingScope with
  | resume =>
      obtain ⟨inside, ready⟩ := resumption checked.1
      exact ⟨.resume cut inside (.operations before) after,
        checked.1, checked.2.1, ready, checked.2.2.2, tailReady⟩
  | dispose =>
      obtain ⟨inside, ready⟩ := closing checked.1
      exact ⟨.dispose cut inside (.operations before) after,
        checked.1, checked.2.1, (disposal checked.1).1, (disposal checked.1).2,
        ready, checked.2.2.2, tailReady⟩
  | sequence rest ih =>
      rename_i footprint declared
      obtain ⟨annotation, ready⟩ := ih cut before checked.2 resumption closing disposal after tailReady
      exact ⟨.sequence (.operations _ footprint declared) annotation, checked.1, ready⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨first, firstReady⟩ := ihFirst cut before checked.1 resumption closing disposal after tailReady
      obtain ⟨second, secondReady⟩ := ihSecond cut before checked.2 resumption closing disposal after tailReady
      exact ⟨.choice first second, firstReady, secondReady⟩
  | cleanup body ih =>
      rename_i required footprint declared
      obtain ⟨annotation, ready⟩ := ih (.cleanup cut)
        (.cleanup front required footprint declared before) checked.1
        (fun permission => by
          obtain ⟨inside, insideReady⟩ := resumption permission
          exact inside.expand_with laws project insideReady .refl (.completion .refl))
        (fun permission => by
          obtain ⟨inside, insideReady⟩ := closing permission
          exact inside.expand_with laws project insideReady .refl (.running (.completion .refl)))
        disposal after tailReady
      exact ⟨.cleanup annotation (.operations required footprint declared), ready, checked.2⟩
  | resource body ih =>
      rename_i localWorld localOwner families plans code
      have generated : ∀ identity, identity ∉ localWorld →
          ∃ annotation : Code (localWorld ++ [identity]) (plans identity) (.cell (identity := identity) whole),
            annotation.Valid outward actions phases := by
        intro identity fresh
        obtain ⟨nextAfter, nextReady⟩ := after.weaken_world_with laws project tailReady
          (List.subset_append_left _ [identity])
        apply ih identity fresh (.cell cut) (.cell (before.world_weaken (List.subset_append_left _ _)))
          (checked identity fresh) _ _ disposal nextAfter nextReady
        · intro permission
          obtain ⟨inside, ready⟩ := resumption permission
          exact inside.provide_outside_with laws project ready (List.subset_append_left _ _) .here
        · intro permission
          obtain ⟨inside, ready⟩ := closing permission
          exact inside.provide_outside_with laws project ready (List.subset_append_left _ _) (.running .here)
      exact ⟨.resource (fun identity fresh => Classical.choose (generated identity fresh)),
        fun identity fresh => Classical.choose_spec (generated identity fresh)⟩

/-- Source admission generates the selected clause for a general saved forest.
Only original saved/waiting/closing annotations are checked. In particular no
post-capture annotation or adaptation proof is a premise. The new ticket is
fresh both in the permission map and in the actual owner inventory. -/
theorem Body.Direct.capture_body
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {body : Body world owner plan} (direct : body.Direct)
    (admitted : Admitted rights resumeRequired closeRequired body required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (inside : Retained world saved waiting) (after : Retained world waiting .nil)
    (resumeReady : rights.resume = true → inside.Valid outward actions phases)
    (closing : rights.dispose = true → ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases)
    (disposal : rights.dispose = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.Valid outward actions phases)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners (savedScope.append waitingScope)) :
    ∃ annotation : Code world plan (.live (owner := owner) saved waiting),
      annotation.Valid outward (actions.insert owner rights) (introduce phases owner) := by
  have known : (actions.insert owner rights) owner = some rights := by
    simp [Syntax.UsageTickets.insert]
  have available : introduce phases owner owner = .available := by
    simp [introduce]
  have tailAbsent : owner ∉ owners (waitingScope.append .nil) := by
    simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil] at absent ⊢
    exact fun member => absent (List.mem_append_right _ member)
  apply direct.generate laws project .hit .nil (admitted.at_capture known available supplied)
  · intro permission
    have allowed : rights.resume = true := by simpa only [known, Option.any_some] using permission
    exact inside.expand_with laws project
      (inside.valid_spent_fresh_owner (resumeReady allowed) fresh absent) .refl (.history .refl)
  · intro permission
    have allowed : rights.dispose = true := by simpa only [known, Option.any_some] using permission
    obtain ⟨annotation, ready⟩ := closing allowed
    have closingAbsent : owner ∉ owners (savedScope.forClosing.append (.running waitingScope)) := by
      intro member
      apply absent
      simp only [SourceScheduledPhaseRestriction.owners_append, owners] at member ⊢
      exact (ScopedExpressions.append_subset (SourceScheduledPhaseRestriction.owners_closing savedScope)
        (List.Subset.refl (owners waitingScope))) member
    exact annotation.expand_with laws project
      (annotation.valid_spent_fresh_owner ready fresh closingAbsent) .refl (.running (.history .refl))
  · intro permission
    exact disposal (by simpa only [known, Option.any_some] using permission)
  · exact after.valid_spent_fresh_owner tailReady fresh tailAbsent

/-- Generate a capture certificate from the current request and whole retained
source. Closing annotations and protection follow from that request's existing
disposal check. No operation-only or owner-chain assumption is made about the
captured forest, and no successful capture certificate is supplied by a caller. -/
theorem Bounded.capture_direct
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required) (direct : annotations.Direct)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (source : Retained world whole .nil) (retained : source.Valid outward actions phases)
    (request : Code world (.request (effect := effect) (operation := operation)) whole)
    (requested : request.Valid outward actions phases)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners wholeScope) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code whole, certificate.Valid outward actions phases := by
  obtain ⟨contract, needed, body, _, bodyAdmitted, included, bodyDirect⟩ := admitted.selected_direct direct selected
  obtain ⟨⟨inside, insideReady⟩, ⟨after, afterReady⟩⟩ :=
    SourceScheduledCapabilityAnnotations.retained_at_cut cut source retained
  have scheduled := request.compile_with laws requested
  cases scheduled with
  | request guard scheduled =>
      have closing : code.requiredActions.dispose = true →
          ∃ annotation : Retained world saved.forClosing (.running waiting),
            annotation.Valid outward actions phases := by
        intro permission
        exact (SourceScheduledCapabilityAnnotations.annotate_all_with outward actions project).2 _ _ _ _
          (scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest (permits permission))
      have disposal : code.requiredActions.dispose = true → savedScope.held = false ∧
          SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true := by
        intro permission
        obtain ⟨unprotected, route, _⟩ := SourceDependencyCapture.disposing_capture
          (SourceDependencySchemes.checked_request guard) cut.erase.lookup (permits permission)
        exact ⟨unprotected, SourceDependencyCapture.check_closing_iff.mpr route⟩
      obtain ⟨annotation, ready⟩ := bodyDirect.capture_body laws project bodyAdmitted inside after
        (fun _ => insideReady) closing disposal afterReady
        (SourceContextualRequirements.check_requirements_subset included supplied) fresh
        (by simpa only [cut.erase.reconstruct_scope] using absent)
      exact ⟨.site cut selected annotation, ready⟩

end
end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Direct.generate
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Direct.capture_body
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.selected_direct
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.capture_direct
