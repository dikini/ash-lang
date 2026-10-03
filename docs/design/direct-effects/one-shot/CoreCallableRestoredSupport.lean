import CoreCallableContractCaptureConnection

/-! Restoration support transport for the experimental common callable source.
World extension alone preserves the source's lexical receiver and complete rows.
Changing the receiver is a separate obligation: saved formal and clause support
bounds must be computed again from the actual dependency environment. -/
namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature modeSignatures clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableReceiverRefinement (LexicalBounds)

private def sequenceLeft (rows : Rows (.sequence first second)) : Rows first := match rows with | .sequence left _ => left
private def sequenceRight (rows : Rows (.sequence first second)) : Rows second := match rows with | .sequence _ right => right
private def choiceLeft (rows : Rows (.choice first second)) : Rows first := match rows with | .choice left _ => left
private def choiceRight (rows : Rows (.choice first second)) : Rows second := match rows with | .choice _ right => right

mutual
/-- Recompute support decorations only at actual source positions. Public
callable contract rows in the application suffix retain their complete data. -/
def restoredRows (code : Code) (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Rows (signature plan) :=
  match plan with
  | .sequence first second =>
    match rows with
    | .sequence left right =>
      match code with
      | .pair a b => .sequence (restoredRows a first left lexical receiver) (restoredRows b second right lexical receiver)
      | .bind parameter initial body => .sequence (restoredRows initial first left lexical receiver)
          (restoredRows body second right (lexical.extend parameter receiver) receiver)
      | .app function argument =>
        match second with
        | .sequence argumentPlan publicPlan =>
          .sequence (restoredRows function first left lexical receiver)
            (.sequence (restoredRows argument argumentPlan (sequenceLeft right) lexical receiver) (sequenceRight right))
        | _ => .sequence left right
      | .branch condition yes no =>
        match second with
        | .choice yesPlan noPlan =>
          .sequence (restoredRows condition first left lexical receiver)
            (.choice (restoredRows yes yesPlan (choiceLeft right) lexical receiver)
              (restoredRows no noPlan (choiceRight right) lexical receiver))
        | _ => .sequence left right
      | .cleanup action body =>
        match second with
        | .cleanup _publicPlan bodyPlan =>
          match right with
          | .cleanup latent publicRows bodyRows =>
            .sequence (restoredRows action first left lexical receiver)
              (.cleanup latent publicRows (restoredRows body bodyPlan bodyRows lexical receiver))
        | _ => .sequence left right
      | .resource binder initial body =>
        match second with
        | .resource bodyPlans =>
          match right with
          | .resource bodyRows =>
            .sequence (restoredRows initial first left lexical receiver)
              (.resource (fun identity => restoredRows
                (body.instantiate (Instantiation.Environment.empty.bind binder identity))
                (bodyPlans identity) (bodyRows identity) lexical (identity :: receiver)))
        | _ => .sequence left right
      | .perform _ _ operand | .resume _ operand => .sequence (restoredRows operand first left lexical receiver) right
      | _ => .sequence left right
  | .handler _required declarations bodyPlan =>
    match rows with
    | .handler declarationRows bodyRows =>
      match code with
      | .handle _ body _ => .handler (restoredClauses declarations declarationRows lexical receiver)
          (restoredRows body bodyPlan bodyRows lexical receiver)
      | _ => .handler declarationRows bodyRows
  | _ => rows
termination_by structural plan

/-- Every owner instance retains its exact plan and recomputes only source
support decorations under the same actual lexical receiver. -/
def restoredModes (body : Code) (plan : ModePlans family) (rows : ModeRows (modeSignatures plan))
    (lexical : LexicalBounds) (receiver : List Nat) : ModeRows (modeSignatures plan) :=
  match plan with
  | .unavailable => .unavailable
  | .available plans =>
    match rows with
    | .available rows => .available (fun owner => restoredRows body (plans owner) (rows owner) lexical receiver)
termination_by structural plan

/-- The full clause body is evaluated under the full formal receiver. Its exact
computed support replaces the stored cons bound; no other clause data changes. -/
def restoredClauses (plan : ClausePlans arms families) (rows : ClauseRows (clauseSignatures plan))
    (lexical : LexicalBounds) (receiver : List Nat) : ClauseRows (clauseSignatures plan) :=
  match plan with
  | .nil => .nil
  | @ClausePlans.cons ordinaryFamily protectedFamily rest restFamilies operation parameter binder body ordinary protectedMode restPlans =>
    match rows with
    | .cons ordinaryRows protectedRows restRows _oldBound =>
      let formal := lexical.extend parameter receiver
      .cons (restoredModes body ordinary ordinaryRows formal receiver)
        (restoredModes body protectedMode protectedRows formal receiver)
        (restoredClauses restPlans restRows lexical receiver)
        (ScopedPorts.Support.evaluate formal.environment body.dependencies)
termination_by structural plan
end

mutual
/-- Complete row data with only stored declaration support leaves erased. -/
def eraseSupportBounds (rows : Rows checking) : Rows checking :=
  match rows with
  | .pure => .pure
  | .request => .request
  | .invoke => .invoke
  | .sequence left right => .sequence (eraseSupportBounds left) (eraseSupportBounds right)
  | .choice left right => .choice (eraseSupportBounds left) (eraseSupportBounds right)
  | .handler clauses body => .handler (eraseModeSupportBoundsClauses clauses) (eraseSupportBounds body)
  | .cleanup latent callback body => .cleanup latent (eraseSupportBounds callback) (eraseSupportBounds body)
  | .resource body => .resource (fun identity => eraseSupportBounds (body identity))
termination_by structural rows

def eraseModeSupportBounds (rows : ModeRows checking) : ModeRows checking :=
  match rows with
  | .unavailable => .unavailable
  | .available body => .available (fun owner => eraseSupportBounds (body owner))
termination_by structural rows

def eraseModeSupportBoundsClauses (rows : ClauseRows checking) : ClauseRows checking :=
  match rows with
  | .nil => .nil
  | .cons ordinary protectedMode rest _ =>
      .cons (eraseModeSupportBounds ordinary) (eraseModeSupportBounds protectedMode)
        (eraseModeSupportBoundsClauses rest) []
termination_by structural rows
end

/-- Equality of every complete row constructor and all non-support fields.
The signature index separately fixes keys, rights, modes and owner families. -/
def SupportOnly (before after : Rows checking) : Prop := eraseSupportBounds after = eraseSupportBounds before

mutual
/-- Restoration retains every complete row field except the declaration support
leaves recomputed by restoredClauses. -/
theorem erase_restoredRows (code : Code) (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) :
    eraseSupportBounds (restoredRows code plan rows lexical receiver) = eraseSupportBounds rows := by
  cases plan with
  | pure | request | invoke | choice | cleanup | resource => rfl
  | sequence first second =>
    cases rows with
    | sequence left right =>
      cases code <;> try rfl
      · change Rows.sequence _ _ = Rows.sequence _ _
        congr 1
        · apply erase_restoredRows
        · apply erase_restoredRows
      · cases second <;> cases right <;> try rfl
        change Rows.sequence _ (Rows.sequence _ _) = Rows.sequence _ (Rows.sequence _ _)
        congr 1
        · apply erase_restoredRows
        · congr 1; apply erase_restoredRows
      · change Rows.sequence _ _ = Rows.sequence _ _
        congr 1
        · apply erase_restoredRows
        · apply erase_restoredRows
      · cases second <;> cases right <;> try rfl
        change Rows.sequence _ (Rows.choice _ _) = Rows.sequence _ (Rows.choice _ _)
        congr 1
        · apply erase_restoredRows
        · congr 1 <;> apply erase_restoredRows
      · change Rows.sequence _ _ = Rows.sequence _ _
        congr 1; apply erase_restoredRows
      · change Rows.sequence _ _ = Rows.sequence _ _
        congr 1; apply erase_restoredRows
      · cases second <;> try rfl
        cases right with
        | resource bodyRows =>
          change Rows.sequence _ _ = Rows.sequence _ _
          congr 1
          · apply erase_restoredRows
          · change Rows.resource _ = Rows.resource _
            congr 1
            funext identity
            apply erase_restoredRows
      · cases second <;> try rfl
        cases right with
        | cleanup latent publicRows bodyRows =>
          change Rows.sequence _ _ = Rows.sequence _ _
          congr 1
          · apply erase_restoredRows
          · change Rows.cleanup _ _ _ = Rows.cleanup _ _ _
            congr 1
            apply erase_restoredRows
  | handler required declarations bodyPlan =>
    cases rows with
    | handler clauseRows bodyRows =>
      cases code <;> try rfl
      change Rows.handler _ _ = Rows.handler _ _
      congr 1
      · apply erase_restoredClauses
      · apply erase_restoredRows
termination_by structural plan

theorem erase_restoredModes (body : Code) (plan : ModePlans family) (rows : ModeRows (modeSignatures plan))
    (lexical : LexicalBounds) (receiver : List Nat) :
    eraseModeSupportBounds (restoredModes body plan rows lexical receiver) = eraseModeSupportBounds rows := by
  cases plan with
  | unavailable => cases rows; rfl
  | available plans =>
    cases rows with
    | available rows =>
      change ModeRows.available _ = ModeRows.available _
      congr 1
      funext owner
      exact erase_restoredRows body (plans owner) (rows owner) lexical receiver
termination_by structural plan

theorem erase_restoredClauses (plan : ClausePlans arms families) (rows : ClauseRows (clauseSignatures plan))
    (lexical : LexicalBounds) (receiver : List Nat) :
    eraseModeSupportBoundsClauses (restoredClauses plan rows lexical receiver) = eraseModeSupportBoundsClauses rows := by
  cases plan with
  | nil => cases rows; rfl
  | cons ordinary protectedMode rest =>
    cases rows with
    | cons ordinaryRows protectedRows restRows bound =>
      change ClauseRows.cons _ _ _ [] = ClauseRows.cons _ _ _ []
      congr 1
      · apply erase_restoredModes
      · apply erase_restoredModes
      · apply erase_restoredClauses
termination_by structural plan
end

theorem restoredRows_supportOnly (code : Code) (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) :
    SupportOnly rows (restoredRows code plan rows lexical receiver) := erase_restoredRows code plan rows lexical receiver

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature clauseSignatures modeSignatures)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Registry OwnerContract Owners)
open CoreCallableRootRefinement (Refines RootTransport)
open CoreCallableReceiverRefinement (CallBounds ReceiverRefines LexicalBounds)
open SourceDependencyAnnotations (RowAnnotation)
open RecursiveRequirements (Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

omit evidence in
private theorem restored_port_clauses_world
    (checked : ScopedPorts.ClausesTyped ports world environment effect answer residual clauses)
    (larger : world ⊆ nextWorld) :
    ScopedPorts.ClausesTyped ports nextWorld environment effect answer residual clauses := by
  induction checked using ScopedPorts.ClausesTyped.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | nil => exact .nil
  | cons known body rest ihBody ihRest =>
      exact .cons known (ScopedPorts.typed_world_weaken body _ larger) (ihRest larger)
  | unit | boolean | integer | «variable» | reference | pair | lambda | app | bind | branch | perform | handle | resume | discard | resource | cleanup => trivial

open CoreCallableRestoredSupport (restoredRows restoredModes restoredClauses)
open SourceScheduledCleanupInterfaces.Lexical.Recursive

/-- Finite names survive restoration; the lists attached to them can change. -/
def RestoredLexicalDomain (before after : LexicalBounds) : Prop :=
  ∀ name resources, before.lookup name = some resources → ∃ next, after.lookup name = some next

omit evidence in
private theorem RestoredLexicalDomain.extend
    (domain : RestoredLexicalDomain before after) :
    RestoredLexicalDomain (before.extend parameter oldReceiver) (after.extend parameter nextReceiver) := by
  intro name resources found
  by_cases same : name = parameter
  · subst name
    exact ⟨nextReceiver, by simp⟩
  · obtain ⟨next, located⟩ := domain name resources (by simpa [lexical_lookup_extend, same] using found)
    exact ⟨next, by simpa [lexical_lookup_extend, same] using located⟩

omit evidence in
private theorem restored_known
    (domain : RestoredLexicalDomain before after)
    (known : LexicalBounds.Known before dependencies) : LexicalBounds.Known after dependencies := by
  intro name member
  obtain ⟨resources, found⟩ := known name member
  exact domain _ _ found

omit evidence in
private theorem restored_lexical_range {lexical : LexicalBounds} {parameter : Nat} {receiver : List Nat}
    (received : ∀ name, lexical.environment name ⊆ receiver) :
    ∀ name, (lexical.extend parameter receiver).environment name ⊆ receiver := by
  intro name
  by_cases same : name = parameter
  · subst name
    simp only [LexicalBounds.environment_extend, ScopedPorts.Support.extend]
    exact List.Subset.refl _
  · simpa [LexicalBounds.environment_extend, ScopedPorts.Support.extend, same] using received name

omit evidence in
private theorem restored_bounds {before after : LexicalBounds}
    (bounds : SourceSupport.Bounds before.environment dependencies bound)
    (included : bound ⊆ receiver)
    (received : ∀ name, after.environment name ⊆ receiver) :
    SourceSupport.Bounds after.environment dependencies receiver := by
  induction bounds with
  | nil => exact .nil
  | resource present rest ih => exact .resource (included present) (ih included)
  | «variable» old rest ih => exact .variable (received _) (ih included)
  | ticket rest ih => exact .ticket (ih included)

/-- Reconstruct authentication at the actual receiving support. Every visible
stored bound is the deterministic dependency evaluation, while the original
plan, complete signature, contracts and scalar requirement remain fixed. -/
theorem Authenticated.restore_receiver
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan
        (restoredRows code plan rows nextLexical nextReceiver),
      Authenticated registry outward nextSource nextLexical nextReceiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ nextLexical nextReceiver, receiver ⊆ nextReceiver → RestoredLexicalDomain lexical nextLexical →
      (∀ name, nextLexical.environment name ⊆ nextReceiver) →
      ∃ nextSource : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan
        (restoredRows code plan rows nextLexical nextReceiver),
      Hereditary registry outward nextSource nextLexical nextReceiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ nextLexical nextReceiver, receiver ⊆ nextReceiver → RestoredLexicalDomain lexical nextLexical →
      (∀ name, nextLexical.environment name ⊆ nextReceiver) →
      ∃ nextSource : SourceBody registry outward owners world allowed scope environment code answer header plan
        (restoredRows code plan rows nextLexical nextReceiver),
      BodyAuthentication registry outward nextSource nextLexical nextReceiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ nextLexical nextReceiver, receiver ⊆ nextReceiver → RestoredLexicalDomain lexical nextLexical →
      (∀ name, nextLexical.environment name ⊆ nextReceiver) →
      ∃ nextSource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans
        (restoredModes code plans rows nextLexical nextReceiver),
      OfferAuthentication registry outward nextSource nextLexical nextReceiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ nextLexical nextReceiver, receiver ⊆ nextReceiver → RestoredLexicalDomain lexical nextLexical →
      (∀ name, nextLexical.environment name ⊆ nextReceiver) →
      ∃ nextSource : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans
        (restoredClauses plans rows nextLexical nextReceiver),
      DeclarationAuthentication registry outward nextSource nextLexical nextReceiver)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ nextLexical nextReceiver, receiver ⊆ nextReceiver → RestoredLexicalDomain lexical nextLexical →
      (∀ name, nextLexical.environment name ⊆ nextReceiver) →
      ∃ nextSource : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans
        (restoredClauses plans rows nextLexical nextReceiver),
      DeclarationAuthentication registry outward nextSource nextLexical nextReceiver)
    generalizing nextLexical nextReceiver with
  | checked current hereditary ih =>
      obtain ⟨nextSource, nextAuth⟩ := ih nextLexical nextReceiver receiverLarger domain received
      exact ⟨nextSource, .checked (restored_bounds current receiverLarger received) nextAuth⟩
  | unit => exact ⟨.unit, .unit⟩
  | boolean => exact ⟨.boolean, .boolean⟩
  | integer => exact ⟨.integer, .integer⟩
  | reference => exact ⟨.reference (by assumption), .reference (issued := by assumption)⟩
  | «variable» knownSupport =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨resources, found⟩ := knownSupport
      exact ⟨.variable (by assumption) (by assumption), .variable (known := by assumption) (formed := by assumption) (domain _ _ found)⟩
  | purePair left right ihL ihR =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceL, authL⟩ := ihL receiverLarger domain received
      obtain ⟨sourceR, authR⟩ := ihR receiverLarger domain received
      exact ⟨.purePair sourceL sourceR, .purePair authL authR⟩
  | pair left right ihL ihR =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceL, authL⟩ := ihL receiverLarger domain received
      obtain ⟨sourceR, authR⟩ := ihR receiverLarger domain received
      exact ⟨.pair sourceL sourceR, .pair authL authR⟩
  | app function argument ihF ihA =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceF, authF⟩ := ihF receiverLarger domain received
      obtain ⟨sourceA, authA⟩ := ihA receiverLarger domain received
      exact ⟨.app sourceF sourceA (by assumption) (by assumption),
        .app (admitted := by assumption) (publicCertified := by assumption) authF authA⟩
  | resource initial body ihI ihB =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      rename_i bodyDemand owners world allowed scope environment initialCode initialDemand initialRequirements
        initialDependencies initialPlan initialRows residual binder output lexical receiver template
        bodyRequirements bodyDependencies bodyPlans bodyRows initialSource bodySource outwardRequirements
        formed effectsBound admitted hidden
      obtain ⟨sourceI, authI⟩ := ihI receiverLarger domain received
      let nextRows := fun identity => restoredRows
        (template.instantiate (Instantiation.Environment.empty.bind binder identity))
        (bodyPlans identity) (bodyRows identity) nextLexical (identity :: nextReceiver)
      have produced : ∀ identity (fresh : identity ∉ world),
          ∃ source : IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
            scope environment (template.instantiate (Instantiation.Environment.empty.bind binder identity))
            output bodyDemand (bodyRequirements identity) (bodyPlans identity) (nextRows identity),
          Authenticated registry outward source nextLexical (identity :: nextReceiver) := by
        intro identity fresh
        apply ihB identity fresh (List.cons_subset_cons _ receiverLarger) domain
        intro name id member
        exact List.mem_cons_of_mem _ (received name member)
      let opened := fun identity fresh => Classical.choose (produced identity fresh)
      exact ⟨IndexedSource.resource sourceI opened formed effectsBound admitted hidden,
        Hereditary.resource (bodySource := opened) (formed := formed) (effectsBound := effectsBound)
          (admitted := admitted) (hidden := hidden) authI
          (fun identity fresh => Classical.choose_spec (produced identity fresh))⟩
  | cleanup callback body ihC ihB =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceC, authC⟩ := ihC receiverLarger domain received
      obtain ⟨sourceB, authB⟩ := ihB receiverLarger domain received
      exact ⟨.cleanup sourceC sourceB (by assumption) (by assumption),
        .cleanup (admitted := by assumption) (publicCertified := by assumption) authC authB⟩
  | bind initial body ihI ihB =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceI, authI⟩ := ihI receiverLarger domain received
      obtain ⟨sourceB, authB⟩ := ihB receiverLarger domain.extend (restored_lexical_range received)
      exact ⟨.bind sourceI sourceB, .bind authI authB⟩
  | branch condition yes no ihC ihY ihN =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceC, authC⟩ := ihC receiverLarger domain received
      obtain ⟨sourceY, authY⟩ := ihY receiverLarger domain received
      obtain ⟨sourceN, authN⟩ := ihN receiverLarger domain received
      exact ⟨.branch sourceC sourceY sourceN (by assumption), .branch authC authY authN⟩
  | perform operand ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨nextSource, nextAuth⟩ := ih receiverLarger domain received
      exact ⟨.perform (by assumption) (by assumption) nextSource (by assumption),
        .perform (known := by assumption) (admitted := by assumption) (formed := by assumption) nextAuth⟩
  | resume operand ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨nextSource, nextAuth⟩ := ih receiverLarger domain received
      exact ⟨.resume (by assumption) (by assumption) (by assumption) nextSource (by assumption) (by assumption),
        .resume (known := by assumption) (resolved := by assumption) (permission := by assumption)
          (admitted := by assumption) (formed := by assumption) nextAuth⟩
  | discard known resolved permission unprotected admitted =>
      exact ⟨.discard known resolved permission unprotected admitted, .discard known resolved permission unprotected admitted⟩
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      rename_i environment bodySource contractDeps contractPlan contractRows
      exact ⟨.lambda bodySource refinement bodyOutward latentBound publicCertified formed,
        .lambda (bodySource := bodySource) refinement bodyOutward latentBound publicCertified formed (restored_known domain known) body⟩
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      rename_i owners world environment privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows
      exact ⟨.receiverLambda bodySource bodyOutward latentBound publicCertified formed,
        .receiverLambda (bodySource := bodySource) bodyOutward latentBound publicCertified formed (restored_known domain known) body refinement⟩
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceB, authB⟩ := ihB receiverLarger domain received
      obtain ⟨sourceD, authD⟩ := ihD nextLexical nextReceiver receiverLarger domain received
      exact ⟨.handler sourceB clauses capabilities coverage unique admitted _ modes sourceD recipes,
        .handler clauses capabilities coverage unique admitted modes recipes authB authD⟩
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceB, authB⟩ := ihB receiverLarger domain received
      obtain ⟨sourceD, authD⟩ := ihD nextLexical nextReceiver receiverLarger domain received
      exact ⟨.handler sourceB clauses capabilities coverage unique admitted _ modes sourceD recipes,
        .handler clauses capabilities coverage unique admitted modes recipes authB authD⟩
  | typed source ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨nextSource, nextAuth⟩ := ih receiverLarger domain received
      exact ⟨.typed nextSource (by assumption) (by assumption), .typed (normal := by assumption) (closing := by assumption) nextAuth⟩
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body ih =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      rename_i resumeEffects closeEffects held allowed binder parameter code disposes row lexical receiver owners world environment argument input answer family plans rows bodySource
      let changed := fun owner contract a b c d e balanced =>
        Classical.choose (ih owner contract a b c d e balanced nextLexical nextReceiver receiverLarger domain received)
      refine ⟨.available resumeInterface closeInterface changed, .available (bodySource := changed) resumeInterface closeInterface ?_⟩
      intro owner contract a b c d e balanced
      exact Classical.choose_spec (ih owner contract a b c d e balanced nextLexical nextReceiver receiverLarger domain received)
  | nil => exact ⟨.nil, .nil⟩
  | domainNil => exact ⟨.nil, .nil⟩
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceO, authO⟩ := ihO _ nextReceiver receiverLarger domain.extend (restored_lexical_range received)
      obtain ⟨sourceP, authP⟩ := ihP _ nextReceiver receiverLarger domain.extend (restored_lexical_range received)
      obtain ⟨sourceR, authR⟩ := ihR nextLexical nextReceiver receiverLarger domain received
      exact ⟨.cons _ known sourceO sourceP sourceR,
        .cons known (SourceSupport.Bounds.canonical _ _)
          (SourceSupport.bounds_iff.mp (restored_bounds bodyBound (storedReceived.trans receiverLarger) (restored_lexical_range received))) authO authP authR⟩

  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i nextLexical nextReceiver receiverLarger domain received
      obtain ⟨sourceO, authO⟩ := ihO _ nextReceiver receiverLarger domain.extend (restored_lexical_range received)
      obtain ⟨sourceP, authP⟩ := ihP _ nextReceiver receiverLarger domain.extend (restored_lexical_range received)
      obtain ⟨sourceR, authR⟩ := ihR nextLexical nextReceiver receiverLarger domain received
      exact ⟨.cons _ known sourceO sourceP sourceR,
        .cons known (SourceSupport.Bounds.canonical _ _)
          (SourceSupport.bounds_iff.mp (restored_bounds bodyBound (storedReceived.trans receiverLarger) (restored_lexical_range received))) authO authP authR⟩

/-- The enlarged issuance history changes no receiver, finite lexical binding,
public contract, private plan, complete contextual row or scalar requirement. -/
theorem Authenticated.world_transport
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (larger : world ⊆ nextWorld)
    (nextSource : IndexedSource registry outward owners nextWorld allowed scope environment code contract demand requirements plan rows) :
    Authenticated registry outward nextSource lexical receiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ nextWorld, world ⊆ nextWorld →
      ∀ nextSource : IndexedSource registry outward owners nextWorld allowed scope environment code contract demand requirements plan rows,
      Hereditary registry outward nextSource lexical receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ nextWorld, world ⊆ nextWorld →
      ∃ nextSource : SourceBody registry outward owners nextWorld allowed scope environment code answer header plan rows,
      BodyAuthentication registry outward nextSource lexical receiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ nextWorld, world ⊆ nextWorld →
      ∃ nextSource : SourceOffer registry outward owners nextWorld environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows,
      OfferAuthentication registry outward nextSource lexical receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ nextWorld, world ⊆ nextWorld →
      ∃ nextSource : SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans rows,
      DeclarationAuthentication registry outward nextSource lexical receiver)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ nextWorld, world ⊆ nextWorld →
      ∃ nextSource : SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans rows,
      DomainDeclarationAuthentication registry outward nextSource lexical receiver)
    generalizing nextWorld with
  | checked current hereditary ih =>
      rename_i nextWorld larger nextSource
      exact .checked current (ih nextWorld larger nextSource)
  | unit => rename_i nextWorld larger nextSource; exact .unit
  | boolean => rename_i nextWorld larger nextSource; exact .boolean
  | integer => rename_i nextWorld larger nextSource; exact .integer
  | reference =>
      rename_i nextWorld larger nextSource
      exact .reference (issued := larger (by assumption))
  | «variable» knownSupport =>
      rename_i nextWorld larger nextSource
      exact .variable (known := by assumption) (formed := ScopedPorts.in_world_mono (by assumption) larger) knownSupport
  | purePair left right ihL ihR =>
      rename_i nextWorld larger nextSource
      refine .purePair (ihL larger ?_) (ihR larger ?_)
      all_goals apply IndexedSource.world_weaken (by assumption); exact larger
  | pair left right ihL ihR =>
      rename_i nextWorld larger nextSource
      refine .pair (ihL larger ?_) (ihR larger ?_)
      all_goals apply IndexedSource.world_weaken (by assumption); exact larger
  | app function argument ihF ihA =>
      rename_i nextWorld larger nextSource
      exact .app (admitted := by assumption) (publicCertified := certified_world (by assumption) larger)
        (ihF larger (IndexedSource.world_weaken (by assumption) larger)) (ihA larger (IndexedSource.world_weaken (by assumption) larger))
  | resource initial body ihI ihB =>
      rename_i nextWorld larger nextSource
      rename_i bodyDemand owners world allowed scope environment initialCode initialDemand initialRequirements
        initialDependencies initialPlan initialRows residual binder output lexical receiver template
        bodyRequirements bodyDependencies bodyPlans bodyRows initialSource bodySource outwardRequirements
        formed effectsBound admitted hidden
      have extended : ∀ identity, world ++ [identity] ⊆ nextWorld ++ [identity] := by
        intro identity name member
        rcases List.mem_append.mp member with old | current
        · exact List.mem_append_left _ (larger old)
        · exact List.mem_append_right _ current
      let opened := fun identity (fresh : identity ∉ nextWorld) =>
        (bodySource identity (fun old => fresh (larger old))).world_weaken (extended identity)
      refine .resource (bodySource := opened) (formed := ScopedPorts.in_world_mono formed larger)
        (effectsBound := effectsBound.trans larger) (admitted := admitted)
        (hidden := fun identity fresh => hidden identity (fun old => fresh (larger old)))
        (ihI larger (initialSource.world_weaken larger)) ?_
      intro identity fresh
      exact ihB identity (fun old => fresh (larger old)) (extended identity) (opened identity fresh)
  | cleanup callback body ihC ihB =>
      rename_i nextWorld larger nextSource
      exact .cleanup (admitted := by assumption) (publicCertified := certified_world (by assumption) larger)
        (ihC larger (IndexedSource.world_weaken (by assumption) larger)) (ihB larger (IndexedSource.world_weaken (by assumption) larger))
  | bind initial body ihI ihB =>
      rename_i nextWorld larger nextSource
      refine .bind (ihI larger ?_) (ihB larger ?_)
      all_goals apply IndexedSource.world_weaken (by assumption); exact larger
  | branch condition yes no ihC ihY ihN =>
      rename_i nextWorld larger nextSource
      refine .branch (ihC larger ?_) (ihY larger ?_) (ihN larger ?_)
      all_goals apply IndexedSource.world_weaken (by assumption); exact larger
  | perform operand ih =>
      rename_i nextWorld larger nextSource
      exact .perform (known := by assumption) (admitted := by assumption)
        (formed := ScopedPorts.in_world_mono (by assumption) larger) (ih larger (IndexedSource.world_weaken (by assumption) larger))
  | resume operand ih =>
      rename_i nextWorld larger nextSource
      exact .resume (known := by assumption) (resolved := by assumption) (permission := by assumption)
        (admitted := by assumption) (formed := ScopedPorts.in_world_mono (by assumption) larger) (ih larger (IndexedSource.world_weaken (by assumption) larger))
  | discard known resolved permission unprotected admitted =>
      rename_i nextWorld larger nextSource
      exact .discard known resolved permission unprotected admitted
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i nextWorld larger nextSource
      rename_i environment bodySource contractDeps contractPlan contractRows
      apply Hereditary.lambda (bodySource := bodySource.world_weaken larger) refinement bodyOutward latentBound
        (certified_world publicCertified larger) (ScopedPorts.in_world_mono formed larger) known
      intro nextLexical call known received
      exact ih nextLexical (call.rebase larger) known received (List.Subset.refl _) _
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i nextWorld larger nextSource
      rename_i owners world environment privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows
      apply Hereditary.receiverLambda (bodySource := fun lexical call => bodySource lexical (call.rebase larger))
        bodyOutward latentBound (certified_world publicCertified larger) (ScopedPorts.in_world_mono formed larger) known
      · intro nextLexical call known received
        exact ih nextLexical (call.rebase larger) known received (List.Subset.refl _) _
      · intro nextLexical call known received
        exact refinement nextLexical (call.rebase larger) known received
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i nextWorld larger nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD nextWorld larger
      exact .handler (restored_port_clauses_world clauses larger) capabilities coverage unique admitted modes recipes
        (ihB larger (IndexedSource.world_weaken (by assumption) larger)) authDecl
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i nextWorld larger nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD nextWorld larger
      exact .handlerDomain (restored_port_clauses_world clauses larger) capabilities coverage unique admitted modes recipes
        (ihB larger (IndexedSource.world_weaken (by assumption) larger)) authDecl
  | typed source ih =>
      rename_i nextWorld larger
      refine ⟨SourceBody.typed (IndexedSource.world_weaken (by assumption) larger) (by assumption) (by assumption), ?_⟩
      exact .typed (normal := by assumption) (closing := by assumption) (ih larger (IndexedSource.world_weaken (by assumption) larger))
  | unavailable => rename_i nextWorld larger; exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body ih =>
      rename_i nextWorld larger
      rename_i resumeEffects closeEffects held allowed binder parameter code disposes row lexical receiver owners world environment argument input answer family plans rows bodySource
      let changed := fun owner contract a b c d e balanced =>
        Classical.choose (ih owner contract a b c d e balanced nextWorld larger)
      refine ⟨SourceOffer.available resumeInterface closeInterface changed,
        .available (bodySource := changed) resumeInterface closeInterface ?_⟩
      intro owner contract a b c d e balanced
      exact Classical.choose_spec (ih owner contract a b c d e balanced nextWorld larger)
  | nil => rename_i nextWorld larger; exact ⟨.nil, .nil⟩
  | domainNil => rename_i nextWorld larger; exact ⟨.nil, .domainNil⟩
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i nextWorld larger
      obtain ⟨nextOrd, authOrd⟩ := ihO nextWorld larger
      obtain ⟨nextProt, authProt⟩ := ihP nextWorld larger
      obtain ⟨nextRest, authRest⟩ := ihR nextWorld larger
      exact ⟨.cons _ known nextOrd nextProt nextRest, .cons known bodyBound storedReceived authOrd authProt authRest⟩
  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i nextWorld larger
      obtain ⟨nextOrd, authOrd⟩ := ihO nextWorld larger
      obtain ⟨nextProt, authProt⟩ := ihP nextWorld larger
      obtain ⟨nextRest, authRest⟩ := ihR nextWorld larger
      exact ⟨.cons _ known nextOrd nextProt nextRest, .domainCons known domainCovered formalReceived bodyBound storedReceived authOrd authProt authRest⟩
/-- A leading clause that reads its formal needs every resource in the actual
receiver. In particular its stored declaration support cannot remain empty
when restoration admits a newly acquired resource. -/
theorem DeclarationAuthentication.formal_resource_in_stored_support
    {source : SourceDeclarations registry outward owners world environment allowed requested answer
      (.cons operation parameter binder (.variable parameter) clauses) table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver)
    (received : identity ∈ receiver) : identity ∈ rows.resourceSupport := by
  cases authenticated with
  | cons known bodyBound storedReceived ordinary protectedMode rest =>
      apply List.mem_append_left
      apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp bodyBound
      simpa [Code.dependencies, ScopedPorts.Support.evaluate, LexicalBounds.environment_extend, ScopedPorts.Support.extend] using received

theorem DeclarationAuthentication.formal_cannot_keep_empty_support
    {source : SourceDeclarations registry outward owners world environment allowed requested answer
      (.cons operation parameter binder (.variable parameter) clauses) table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver)
    (received : identity ∈ receiver) (empty : rows.resourceSupport = []) : False := by
  have member := authenticated.formal_resource_in_stored_support received
  rw [empty] at member
  cases member

theorem Authenticated.world_weaken
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) :
    Authenticated registry outward (source.world_weaken larger) lexical receiver :=
  authenticated.world_transport larger _
/-- World extension and receiver reconstruction compose from the deterministic
world transport of the saved source; the actual restored rows are not a premise. -/
theorem Authenticated.restore_world_receiver
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : IndexedSource registry outward owners nextWorld allowed scope environment code contract demand requirements plan
        (restoredRows code plan rows nextLexical nextReceiver),
      Authenticated registry outward nextSource nextLexical nextReceiver :=
  (authenticated.world_weaken larger).restore_receiver receiverLarger domain received

/-- Canonical aggregate support remains separate from the full actual receiver.
This wrapper reconstructs source and authentication before calculating its bound. -/
theorem Supported.restore_world_receiver
    (supported : Supported globals outward world allowed scope environment supportEnvironment code contract
      demand requirements plan rows bound receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (issued : nextReceiver ⊆ nextWorld)
    (lexical : LexicalBounds) (_sameEnvironment : lexical.environment = supportEnvironment)
    (authentication : Authenticated globals.registry outward supported.source lexical receiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    Supported globals outward nextWorld allowed scope environment nextLexical.environment code contract
      demand requirements plan (restoredRows code plan rows nextLexical nextReceiver)
      (ScopedPorts.Support.evaluate nextLexical.environment code.dependencies) nextReceiver := by
  obtain ⟨nextSource, nextAuthentication⟩ := authentication.restore_world_receiver larger receiverLarger domain received
  exact Supported.canonical nextSource nextLexical nextReceiver nextAuthentication
    ((SourceSupport.bounds_iff.mp nextAuthentication.current_support).trans issued) issued

/-- World-only transport preserves every literal private row. -/
theorem BodyAuthentication.world_transport
    {source : SourceBody registry outward owners world allowed scope environment code answer header plan rows}
    (authenticated : BodyAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) :
    ∃ nextSource : SourceBody registry outward owners nextWorld allowed scope environment code answer header plan rows,
      BodyAuthentication registry outward nextSource lexical receiver := by
  cases authenticated with
  | typed checked =>
    exact ⟨.typed (IndexedSource.world_weaken (by assumption) larger) (by assumption) (by assumption),
      .typed (normal := by assumption) (closing := by assumption) (checked.world_weaken larger)⟩

/-- Both modes retain their complete owner-indexed private source rows. -/
theorem OfferAuthentication.world_transport
    {source : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans rows}
    (authenticated : OfferAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) :
    ∃ nextSource : SourceOffer registry outward owners nextWorld environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans rows,
      OfferAuthentication registry outward nextSource lexical receiver := by
  cases authenticated with
  | unavailable => exact ⟨.unavailable,.unavailable⟩
  | available resumeInterface closeInterface bodies =>
    let changed := fun owner contract a b c d e balanced =>
      Classical.choose ((bodies owner contract a b c d e balanced).world_transport larger)
    exact ⟨.available resumeInterface closeInterface changed,
      .available (bodySource := changed) resumeInterface closeInterface
        (fun owner contract a b c d e balanced =>
          Classical.choose_spec ((bodies owner contract a b c d e balanced).world_transport larger))⟩

/-- Same lexical receiver and literal full declaration rows in the later world. -/
theorem DomainDeclarationAuthentication.world_transport
    {families : ClauseDependencies} {plans : ClausePlans clauses families} {rows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DomainDeclarationAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) :
    ∃ nextSource : SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans rows,
      DomainDeclarationAuthentication registry outward nextSource lexical receiver := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families with
  | nil => cases authenticated; exact ⟨.nil,.domainNil⟩
  | cons operation parameter binder body rest ihBody ihRest =>
    cases authenticated with
    | domainCons known covered received bounded stored ordinary protectedMode tail =>
      obtain ⟨sourceO,authO⟩ := ordinary.world_transport larger
      obtain ⟨sourceP,authP⟩ := protectedMode.world_transport larger
      obtain ⟨sourceR,authR⟩ := ihRest tail
      exact ⟨.cons _ known sourceO sourceP sourceR,.domainCons known covered received bounded stored authO authP authR⟩
  | unit | boolean | integer | resourceRef | «variable» | pair | lambda | app | bind | branch | perform | resume | discard | handle | cleanup | resource => trivial

theorem BodyAuthentication.restore_world_receiver
    {source : SourceBody registry outward owners world allowed scope environment code answer header plan rows}
    (authenticated : BodyAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : SourceBody registry outward owners nextWorld allowed scope environment code answer header plan
        (restoredRows code plan rows nextLexical nextReceiver),
      BodyAuthentication registry outward nextSource nextLexical nextReceiver := by
  cases authenticated with
  | typed checked =>
      obtain ⟨nextSource, nextAuth⟩ := checked.restore_world_receiver larger receiverLarger domain received
      exact ⟨.typed nextSource (by assumption) (by assumption),
        .typed (normal := by assumption) (closing := by assumption) nextAuth⟩

theorem OfferAuthentication.restore_world_receiver
    {source : SourceOffer registry outward owners world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans rows}
    (authenticated : OfferAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : SourceOffer registry outward owners nextWorld environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes row plans (restoredModes code plans rows nextLexical nextReceiver),
      OfferAuthentication registry outward nextSource nextLexical nextReceiver := by
  cases authenticated with
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface bodies =>
      let changed := fun owner contract a b c d e balanced =>
        Classical.choose ((bodies owner contract a b c d e balanced).restore_world_receiver larger receiverLarger domain received)
      refine ⟨.available resumeInterface closeInterface changed,
        .available (bodySource := changed) resumeInterface closeInterface ?_⟩
      intro owner contract a b c d e balanced
      exact Classical.choose_spec ((bodies owner contract a b c d e balanced).restore_world_receiver larger receiverLarger domain received)

theorem DeclarationAuthentication.restore_world_receiver
    {families : ClauseDependencies} {plans : ClausePlans clauses families} {rows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans
        (restoredClauses plans rows nextLexical nextReceiver),
      DeclarationAuthentication registry outward nextSource nextLexical nextReceiver := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families with
  | nil => cases authenticated; exact ⟨.nil, .nil⟩
  | cons operation parameter binder body rest ihBody ihRest =>
      cases authenticated with
      | cons known bodyBound storedReceived ordinary protectedMode tail =>
          obtain ⟨sourceO, authO⟩ := ordinary.restore_world_receiver larger receiverLarger domain.extend (restored_lexical_range received)
          obtain ⟨sourceP, authP⟩ := protectedMode.restore_world_receiver larger receiverLarger domain.extend (restored_lexical_range received)
          obtain ⟨sourceR, authR⟩ := ihRest tail
          exact ⟨.cons _ known sourceO sourceP sourceR,
            .cons known (SourceSupport.Bounds.canonical _ _)
              (SourceSupport.bounds_iff.mp (restored_bounds bodyBound (storedReceived.trans receiverLarger) (restored_lexical_range received))) authO authP authR⟩
  | unit | boolean | integer | resourceRef | «variable» | pair | lambda | app | bind | branch | perform | resume | discard | handle | cleanup | resource => trivial

theorem DomainDeclarationAuthentication.restore_world_receiver
    {families : ClauseDependencies} {plans : ClausePlans clauses families} {rows : ClauseRows (clauseSignatures plans)}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DomainDeclarationAuthentication registry outward source lexical receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (domain : RestoredLexicalDomain lexical nextLexical)
    (received : ∀ name, nextLexical.environment name ⊆ nextReceiver) :
    ∃ nextSource : SourceDeclarations registry outward owners nextWorld environment allowed requested answer clauses table plans
        (restoredClauses plans rows nextLexical nextReceiver),
      DeclarationAuthentication registry outward nextSource nextLexical nextReceiver := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families with
  | nil => cases authenticated; exact ⟨.nil, .nil⟩
  | cons operation parameter binder body rest ihBody ihRest =>
      cases authenticated with
      | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode tail =>
          obtain ⟨sourceO, authO⟩ := ordinary.restore_world_receiver larger receiverLarger domain.extend (restored_lexical_range received)
          obtain ⟨sourceP, authP⟩ := protectedMode.restore_world_receiver larger receiverLarger domain.extend (restored_lexical_range received)
          obtain ⟨sourceR, authR⟩ := ihRest tail
          exact ⟨.cons _ known sourceO sourceP sourceR,
            .cons known (SourceSupport.Bounds.canonical _ _)
              (SourceSupport.bounds_iff.mp (restored_bounds bodyBound (storedReceived.trans receiverLarger) (restored_lexical_range received))) authO authP authR⟩
  | unit | boolean | integer | resourceRef | «variable» | pair | lambda | app | bind | branch | perform | resume | discard | handle | cleanup | resource => trivial

end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.world_transport
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.world_weaken

#print axioms Ash.OneShot.CoreCallableContractAdmission.DeclarationAuthentication.formal_resource_in_stored_support
#print axioms Ash.OneShot.CoreCallableContractAdmission.DeclarationAuthentication.formal_cannot_keep_empty_support

#print axioms Ash.OneShot.CoreCallableRestoredSupport.restoredRows_supportOnly

#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.restore_receiver

#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.restore_world_receiver
#print axioms Ash.OneShot.CoreCallableContractAdmission.Supported.restore_world_receiver

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractAdmission (Authenticated RestoredLexicalDomain)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRestoredSupport (restoredRows SupportOnly)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]

/-- Rebuild the same saved suffix at the restored full receiver. The new formal
bound and aggregate body bound are calculated separately; public contracts and
the saved runtime frame, plan and scalar requirements remain unchanged. -/
theorem FrameSource.restore_support
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows
      inputBound bodyBound receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver)
    (issued : nextReceiver ⊆ nextWorld) :
    ∃ lexical : LexicalBounds,
      lexical.environment = ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiver ∧
      ∃ nextRows : Rows (signature plan),
        FrameSource globals outward nextWorld allowed data input output parameter body demand requirements plan nextRows
          nextReceiver (ScopedPorts.Support.evaluate
            (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter nextReceiver) body.dependencies) nextReceiver ∧
        nextRows = restoredRows body plan rows (lexical.extend parameter nextReceiver) nextReceiver ∧
        SupportOnly rows nextRows := by
  obtain ⟨lexical, sameEnvironment, authentication⟩ := frame.bodySource.authentication
  let nextLexical := lexical.extend parameter nextReceiver
  have domain : RestoredLexicalDomain lexical nextLexical := by
    intro name resources found
    by_cases same : name = parameter
    · subst name
      exact ⟨nextReceiver, by simp [nextLexical]⟩
    · exact ⟨resources, by simpa [nextLexical, CoreCallableContractAdmission.lexical_lookup_extend, same] using found⟩
  have nextEnvironment : nextLexical.environment =
      ScopedPorts.Support.extend ScopedPorts.Support.empty parameter nextReceiver := by
    rw [show nextLexical.environment = ScopedPorts.Support.extend lexical.environment parameter nextReceiver from
      LexicalBounds.environment_extend]
    rw [sameEnvironment]
    funext name
    by_cases same : name = parameter <;> simp [ScopedPorts.Support.extend, same]
  have received : ∀ name, nextLexical.environment name ⊆ nextReceiver := by
    intro name
    rw [nextEnvironment]
    by_cases same : name = parameter
    · subst name
      simp [ScopedPorts.Support.extend]
    · simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty, same]
  obtain ⟨nextSource, nextAuthentication⟩ :=
    authentication.restore_world_receiver larger receiverLarger domain received
  let nextRows := restoredRows body plan rows nextLexical nextReceiver
  have supported : CoreCallableContractAdmission.Supported globals outward nextWorld allowed data.scope
      (CoreCallableContractSource.Environment.empty.extend parameter input) nextLexical.environment body output
      demand requirements plan nextRows
      (ScopedPorts.Support.evaluate nextLexical.environment body.dependencies) nextReceiver :=
    CoreCallableContractAdmission.Supported.canonical nextSource nextLexical nextReceiver nextAuthentication
      ((SourceSupport.bounds_iff.mp nextAuthentication.current_support).trans issued) issued
  refine ⟨lexical, sameEnvironment, nextRows, ?_, rfl, CoreCallableRestoredSupport.restoredRows_supportOnly _ _ _ _ _⟩
  exact ⟨frame.position, frame.inputAnnotation, frame.outputAnnotation, issued, by simpa only [nextEnvironment] using supported⟩
/-- Rebuild the same installed source declaration family in the enlarged world.
Only the computed support leaves change, pointwise over every offered owner. -/
theorem HandlerSource.restore_support
    (frame : HandlerSource globals outward world residual data answer table plans rows receiver)
    (larger : world ⊆ nextWorld) (receiverLarger : receiver ⊆ nextReceiver) :
    ∃ lexical : LexicalBounds,
      lexical.environment = ScopedPorts.Support.empty ∧
      HandlerSource globals outward nextWorld residual data answer table plans
        (CoreCallableRestoredSupport.restoredClauses plans rows lexical nextReceiver) nextReceiver ∧
      CoreCallableRestoredSupport.eraseModeSupportBoundsClauses
        (CoreCallableRestoredSupport.restoredClauses plans rows lexical nextReceiver) =
        CoreCallableRestoredSupport.eraseModeSupportBoundsClauses rows := by
  obtain ⟨lexical, empty, authentication⟩ := frame.authentication
  have domain : RestoredLexicalDomain lexical lexical := fun name resources found => ⟨resources, found⟩
  have received : ∀ name, lexical.environment name ⊆ nextReceiver := by
    intro name
    rw [empty]
    simp [ScopedPorts.Support.empty]
  have restored : ∃ nextSource : CoreCallableContractAdmission.SourceDeclarations globals.registry outward globals.owners nextWorld
      CoreCallableContractSource.Environment.empty residual data.effectInst answer data.clauses table plans
      (CoreCallableRestoredSupport.restoredClauses plans rows lexical nextReceiver),
      CoreCallableContractAdmission.DeclarationAuthentication globals.registry outward nextSource lexical nextReceiver := by
    cases authentication with
    | inl whole => exact whole.restore_world_receiver larger receiverLarger domain received
    | inr precise => exact precise.restore_world_receiver larger receiverLarger domain received
  obtain ⟨nextSource,nextAuth⟩ := restored
  refine ⟨lexical, empty, ?_, CoreCallableRestoredSupport.erase_restoredClauses _ _ _ _⟩
  exact ⟨frame.annotation, frame.modes, nextSource, lexical, empty, Or.inl nextAuth⟩

end
end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableContractExecution.FrameSource.restore_support

#print axioms Ash.OneShot.CoreCallableContractAdmission.DeclarationAuthentication.restore_world_receiver

#print axioms Ash.OneShot.CoreCallableContractExecution.HandlerSource.restore_support

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Remove only stored support leaves throughout the complete decorated stack,
including dormant saved contexts. Physical handler identities, latent cleanup
footprints, signatures and return hints are retained. -/
def eraseContextSupport : {scope : Scope} → {hints : ReturnHints scope} → Context hints → Context hints
  | _, _, .nil => .nil
  | _, _, .plain rows tail => .plain (eraseSupportBounds rows) (eraseContextSupport tail)
  | _, _, .handler activation rows tail =>
      .handler activation (eraseModeSupportBoundsClauses rows) (eraseContextSupport tail)
  | _, _, .cell tail => .cell (eraseContextSupport tail)
  | _, _, .cleanup latent rows tail => .cleanup latent (eraseSupportBounds rows) (eraseContextSupport tail)
  | _, _, .normal tail => .normal (eraseContextSupport tail)
  | _, _, .unwinding tail => .unwinding (eraseContextSupport tail)
  | _, _, .closing tail => .closing (eraseContextSupport tail)
  | _, _, .retiring owner tail => .retiring owner (eraseContextSupport tail)
  | _, _, .live (resumeDemand := demand) saved tail =>
      .live (resumeDemand := demand) (eraseContextSupport saved) (eraseContextSupport tail)
  | _, _, .spent tail => .spent (eraseContextSupport tail)

def erasePackedSupport (packed : Packed) : Packed := (eraseContextSupport packed.context).pack

def eraseSelectionSupport : Selection → Selection
  | .builtin identity => .builtin identity
  | .handler captured tail contract modes =>
      .handler (erasePackedSupport captured) (erasePackedSupport tail) contract modes

/-- The complete context comparison fixes every decoration except the support
leaves already located by the source row reconstruction. -/
def ContextSupportOnly {hints : ReturnHints scope} (before after : Context hints) : Prop :=
  eraseContextSupport after = eraseContextSupport before

theorem eraseContextSupport_context {hints : ReturnHints scope} (context : Context hints) :
    (eraseContextSupport context).context = context.context := by
  induction context <;> simp_all [eraseContextSupport, Context.context] <;> rfl

theorem eraseContextSupport_append {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    (head : Context first) (tail : Context second) :
    eraseContextSupport (head.append tail) = (eraseContextSupport head).append (eraseContextSupport tail) := by
  induction head <;> simp_all [eraseContextSupport, Context.append] <;> rfl

private theorem eraseSelection_prepend (frame nextFrame : Packed → Packed)
    (same : ∀ packed, erasePackedSupport (frame packed) = nextFrame (erasePackedSupport packed))
    (selected : Option Selection) :
    (selected.map (Selection.prepend frame)).map eraseSelectionSupport =
      (selected.map eraseSelectionSupport).map (Selection.prepend nextFrame) := by
  cases selected with
  | none => rfl
  | some selected => cases selected with
    | builtin identity => rfl
    | handler captured tail contract modes => simp only [Option.map_some, Selection.prepend,
        eraseSelectionSupport, same]

/-- Actual nearest-handler selection commutes with support erasure, including
all captured frames and the retained tail. -/
theorem select_eraseContextSupport (effect : Instance) (operation : Nat)
    {hints : ReturnHints scope} (context : Context hints) :
    select effect operation (eraseContextSupport context) =
      (select effect operation context).map eraseSelectionSupport := by
  induction context with
  | nil => rfl
  | handler activation rows tail ih =>
      simp only [eraseContextSupport, select]
      split
      · split <;> rfl
      · rw [ih]
        symm
        apply eraseSelection_prepend
        intro packed
        rfl
  | cell tail ih =>
      simp only [eraseContextSupport, select]
      split
      · rfl
      · rw [ih]
        symm
        apply eraseSelection_prepend
        intro packed
        rfl
  | plain rows tail ih | cleanup latent rows tail ih | normal tail ih | unwinding tail ih
  | closing tail ih | retiring owner tail ih | spent tail ih =>
      simp only [eraseContextSupport, select]
      rw [ih]
      symm
      apply eraseSelection_prepend
      intro packed
      rfl
  | live saved tail ihSaved ihTail =>
      simp only [eraseContextSupport, select]
      rw [ihTail]
      symm
      apply eraseSelection_prepend
      intro packed
      rfl

theorem Cut.erase_support
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    (cut : Contextual.Cut effect operation whole captured tail contract modes) :
    Contextual.Cut effect operation (eraseContextSupport whole) (eraseContextSupport captured)
      (eraseContextSupport tail) contract modes := by
  unfold Contextual.Cut at *
  rw [select_eraseContextSupport, cut]
  rfl

end Ash.OneShot.CoreCallableRestoredSupport
#print axioms Ash.OneShot.CoreCallableRestoredSupport.select_eraseContextSupport
#print axioms Ash.OneShot.CoreCallableRestoredSupport.Cut.erase_support

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

theorem eraseContextSupport_closing {hints : ReturnHints scope} (context : Context hints) :
    (eraseContextSupport context).closing? = context.closing? := by
  induction context <;> simp_all [eraseContextSupport, Context.closing?]

theorem eraseContextSupport_ticketNames {hints : ReturnHints scope} (context : Context hints) :
    (eraseContextSupport context).ticketNames = context.ticketNames := by
  induction context <;> simp_all [eraseContextSupport, Context.ticketNames]

theorem eraseContextSupport_callback {hints : ReturnHints scope} (context : Context hints) (mode : LexicalUnwind.UseMode) :
    eraseContextSupport (context.callback mode) = (eraseContextSupport context).callback mode := by
  cases mode <;> rfl

theorem TerminalHandler.erase_support
    (terminal : TerminalHandler effect activation rows context) :
    TerminalHandler effect activation (eraseModeSupportBoundsClauses rows) (eraseContextSupport context) := by
  induction terminal with
  | here => exact .here
  | plain terminal ih => exact .plain ih
  | handler terminal ih => exact .handler ih
  | cell terminal ih => exact .cell ih
  | cleanup terminal ih => exact .cleanup ih
  | normal terminal ih => exact .normal ih
  | unwinding terminal ih => exact .unwinding ih
  | closing terminal ih => exact .closing ih
  | retiring terminal ih => exact .retiring ih
  | live terminal ih => exact .live ih
  | spent terminal ih => exact .spent ih

theorem ClauseRows.Selected.erase_support
    (selected : ClauseRows.Selected operation held declarations bodyRows) :
    ClauseRows.Selected operation held (eraseModeSupportBoundsClauses declarations)
      (fun owner => eraseSupportBounds (bodyRows owner)) := by
  induction selected with
  | ordinary => exact .ordinary
  | protectedMode => exact .protectedMode
  | pass different rest ih => exact .pass different ih

theorem CapturedClauseRows.erase_support
    (selected : CapturedClauseRows effect operation held context bodyRows) :
    CapturedClauseRows effect operation held (eraseContextSupport context)
      (fun owner => eraseSupportBounds (bodyRows owner)) := by
  cases selected with
  | selected terminal chosen => exact .selected (TerminalHandler.erase_support terminal) (ClauseRows.Selected.erase_support chosen)

theorem RequestBudget.erase_support
    (checked : RequestBudget budget phases effect operation context) :
    RequestBudget budget phases effect operation (eraseContextSupport context) := by
  unfold RequestBudget at *
  rw [select_eraseContextSupport]
  cases found : select effect operation context with
  | none => trivial
  | some selected =>
    simp only [found] at checked
    cases selected with
    | builtin identity => trivial
    | handler captured tail contract modes =>
      simp only [Option.map_some, eraseSelectionSupport, erasePackedSupport, Context.pack]
      simpa only [eraseContextSupport_closing, eraseContextSupport_context] using checked

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission
open Ash.OneShot.CoreCallableRestoredSupport
open SourceDependencyChecks.Lexical (ReturnHints)

/-- Structural admission observes the complete decorations but does not read
stored support leaves. Erasure preserves its actual selected handler family. -/
theorem Code.erase_support
    {checking : SourcePlanSignatures.Signature dependencies} {rows : Rows checking}
    {hints : ReturnHints scope} {context : Context hints}
    (checked : Code outward actions budget phases world installations rows context) :
    Code outward actions budget phases world installations
      (eraseSupportBounds rows) (eraseContextSupport context) := by
  apply Code.rec
    (motive_1 := fun actions budget phases world installations {dependencies checking} rows {scope hints} context _ =>
      Code outward actions budget phases world installations (eraseSupportBounds rows) (eraseContextSupport context))
    (motive_2 := fun actions budget phases world installations {scope outsideScope hints external} context outside input output _ =>
      Pending outward actions budget phases world installations (eraseContextSupport context) (eraseContextSupport outside) input output)
    (t := checked)
  · intros; exact .pure
  · intros
    rename_i found
    apply Code.builtin
    rw [select_eraseContextSupport, found]
    rfl
  · intros
    rename_i cut guarded callbacks ownerBound cleanupBudget family bodies bodyRows declarations declarationRows selected terminal requiredRights retained body ihCallbacks ihRetained ihBody
    refine .request (CoreCallableRestoredSupport.Cut.erase_support cut) guarded
      (fun disposing => ihCallbacks disposing) ownerBound
      (CoreCallableRestoredSupport.RequestBudget.erase_support cleanupBudget)
      (CoreCallableRestoredSupport.CapturedClauseRows.erase_support selected)
      (CoreCallableRestoredSupport.TerminalHandler.erase_support terminal) requiredRights ihRetained ?_
    intro owner demand fresh absent
    apply ihBody owner demand fresh
    simpa only [eraseContextSupport_ticketNames] using absent
  · intros
    rename_i located known permission available shape restored ih
    simp only [eraseContextSupport_append, eraseContextSupport] at ih ⊢
    apply Code.resume located known permission available _ ih
    simpa only [ResumeShape, eraseContextSupport_closing] using shape
  · intros
    rename_i located known permission available unprotected abandoned waiting ihAbandoned ihWaiting
    simp only [eraseContextSupport_append, eraseContextSupport] at ihAbandoned ihWaiting ⊢
    exact .dispose located known permission available unprotected ihAbandoned ihWaiting
  · intros
    rename_i first second ihFirst ihSecond
    exact .sequence ihFirst ihSecond
  · intros
    rename_i first second ihFirst ihSecond
    exact .choice ihFirst ihSecond
  · intros
    rename_i body ih
    exact .handler (fun activation fresh => ih activation fresh)
  · intros
    rename_i body callback ihBody ihCallback
    exact .cleanup ihBody ihCallback
  · intros
    rename_i body ih
    exact .resource (fun identity fresh => ih identity fresh)
  · intros; exact .nil
  · intros
    rename_i code tail ihCode ihTail
    rw [eraseContextSupport_append] at ihCode
    exact .plain ihCode ihTail
  · intros
    rename_i tail ih
    exact .skipped ih
  · intros
    rename_i tail ih
    exact .handler ih
  · intros
    rename_i tail ih
    exact .cell ih
  · intros
    rename_i callback tail ihCallback ihTail
    rw [eraseContextSupport_callback, eraseContextSupport_append] at ihCallback
    exact .cleanup ihCallback ihTail
  · intros
    rename_i tail ih
    exact .normal ih
  · intros
    rename_i tail ih
    exact .unwinding ih
  · intros
    rename_i tail ih
    exact .closing ih
  · intros
    rename_i tail ih
    exact .retiring ih
  · intros
    rename_i saved tail ihSaved ihTail
    rw [eraseContextSupport_append] at ihSaved
    exact .live ihSaved ihTail
  · intros
    rename_i saved tail ihSaved ihTail
    simp only [eraseContextSupport, eraseContextSupport_append] at ihSaved
    exact .opening ihSaved ihTail
  · intros
    rename_i tail ih
    exact .spent ih

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code.erase_support

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Support-only changes retain the actual handler selection and the complete
captured and retained decorations modulo exactly the same support leaves. -/
theorem ContextSupportOnly.selected
    {hints : ReturnHints scope} {before after : Context hints}
    (delta : ContextSupportOnly before after)
    (found : select effect operation before = some (.handler captured tail contract modes)) :
    ∃ nextCaptured nextTail,
      select effect operation after = some (.handler nextCaptured nextTail contract modes) ∧
      erasePackedSupport nextCaptured = erasePackedSupport captured ∧
      erasePackedSupport nextTail = erasePackedSupport tail := by
  have same := congrArg (select effect operation) delta
  rw [select_eraseContextSupport, select_eraseContextSupport, found] at same
  cases next : select effect operation after with
  | none => rw [next] at same; cases same
  | some selected => cases selected with
    | builtin identity => rw [next] at same; cases same
    | handler nextCaptured nextTail nextContract nextModes =>
      rw [next] at same
      have sameParts := Option.some.inj same
      injection sameParts with capturedSame tailSame contractSame modesSame
      cases contractSame
      cases modesSame
      exact ⟨nextCaptured, nextTail, rfl, capturedSame, tailSame⟩

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableContractAdmission
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

/-- The stored support in every complete declaration row is received by the
same authenticated formal receiver, including modes with no runtime offer. -/
theorem DeclarationAuthentication.received_support
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DeclarationAuthentication registry outward source lexical receiver) :
    rows.resourceSupport ⊆ receiver := by
  apply DeclarationAuthentication.rec
    (motive_1 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => rows.resourceSupport ⊆ receiver)
    (t := authenticated)
  all_goals intros
  all_goals first | trivial | exact List.append_subset.mpr ⟨by assumption, by assumption⟩ | simp [ClauseRows.resourceSupport]

theorem DomainDeclarationAuthentication.received_support
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DomainDeclarationAuthentication registry outward source lexical receiver) :
    rows.resourceSupport ⊆ receiver := by
  apply DomainDeclarationAuthentication.rec
    (motive_1 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => rows.resourceSupport ⊆ receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
    (t := authenticated)
  all_goals intros
  all_goals first | trivial | exact List.append_subset.mpr ⟨by assumption, by assumption⟩ | simp [ClauseRows.resourceSupport]

end Ash.OneShot.CoreCallableContractAdmission

namespace Ash.OneShot.CoreCallableContractExecution
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

/-- Installation checking uses the reconstructed source's actual receiving
support. This follows authentication, not a general support-only comparison. -/
theorem HandlerSource.received_support
    (source : HandlerSource globals outward world residual data answer table plans rows receiver) :
    rows.resourceSupport ⊆ receiver := by
  obtain ⟨lexical, empty, authenticated⟩ := source.authentication
  cases authenticated with
  | inl whole => exact whole.received_support
  | inr domain => exact domain.received_support

end Ash.OneShot.CoreCallableContractExecution
#print axioms Ash.OneShot.CoreCallableRestoredSupport.ContextSupportOnly.selected
#print axioms Ash.OneShot.CoreCallableContractExecution.HandlerSource.received_support

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- A restoration delta locates each changed row decoration constructively.
Every constructor fixes its complete signature and non-support metadata. -/
inductive RestoredContext : {scope : Scope} → {hints : ReturnHints scope} → Context hints → Context hints → Prop where
  | nil : RestoredContext .nil .nil
  | plain (rows : SupportOnly beforeRows afterRows) (tail : RestoredContext before after) :
      RestoredContext (.plain beforeRows before) (.plain afterRows after)
  | handler (rows : eraseModeSupportBoundsClauses afterRows = eraseModeSupportBoundsClauses beforeRows)
      (tail : RestoredContext before after) :
      RestoredContext (.handler activation beforeRows before) (.handler activation afterRows after)
  | cell (tail : RestoredContext before after) : RestoredContext (.cell before) (.cell after)
  | cleanup (rows : SupportOnly beforeRows afterRows) (tail : RestoredContext before after) :
      RestoredContext (.cleanup latent beforeRows before) (.cleanup latent afterRows after)
  | normal (tail : RestoredContext before after) : RestoredContext (.normal before) (.normal after)
  | unwinding (tail : RestoredContext before after) : RestoredContext (.unwinding before) (.unwinding after)
  | closing (tail : RestoredContext before after) : RestoredContext (.closing before) (.closing after)
  | retiring (tail : RestoredContext before after) : RestoredContext (.retiring owner before) (.retiring owner after)
  | live (saved : RestoredContext beforeSaved afterSaved) (tail : RestoredContext before after) :
      RestoredContext (.live (owner := owner) (resumeDemand := demand) beforeSaved before)
        (.live (owner := owner) (resumeDemand := demand) afterSaved after)
  | spent (tail : RestoredContext before after) : RestoredContext (.spent before) (.spent after)

theorem RestoredContext.complete (delta : RestoredContext before after) : ContextSupportOnly before after := by
  induction delta <;> simp_all [ContextSupportOnly, SupportOnly, eraseContextSupport] <;> rfl

theorem RestoredContext.refl {hints : ReturnHints scope} (context : Context hints) : RestoredContext context context := by
  induction context with
  | nil => exact .nil
  | plain rows tail ih => exact .plain rfl ih
  | handler activation rows tail ih => exact .handler rfl ih
  | cell tail ih => exact .cell ih
  | cleanup latent rows tail ih => exact .cleanup rfl ih
  | normal tail ih => exact .normal ih
  | unwinding tail ih => exact .unwinding ih
  | closing tail ih => exact .closing ih
  | retiring owner tail ih => exact .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem RestoredContext.append (head : RestoredContext beforeHead afterHead)
    (tail : RestoredContext beforeTail afterTail) :
    RestoredContext (beforeHead.append beforeTail) (afterHead.append afterTail) := by
  induction head with
  | nil => exact tail
  | plain rows rest ih => exact .plain rows ih
  | handler rows rest ih => exact .handler rows ih
  | cell rest ih => exact .cell ih
  | cleanup rows rest ih => exact .cleanup rows ih
  | normal rest ih => exact .normal ih
  | unwinding rest ih => exact .unwinding ih
  | closing rest ih => exact .closing ih
  | retiring rest ih => exact .retiring ih
  | live saved rest ihSaved ihRest => exact .live saved ihRest
  | spent rest ih => exact .spent ih

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourcePlanSignatures (ClauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Locate the same terminal handler in the rebuilt actual captured spine.
The resulting complete declaration signature is identical. -/
theorem RestoredContext.terminal
    {declarations : ClauseSignatures families} {rows : ClauseRows declarations}
    (terminal : TerminalHandler effect activation rows before)
    (delta : RestoredContext before after) :
    ∃ nextRows : ClauseRows declarations,
      eraseModeSupportBoundsClauses nextRows = eraseModeSupportBoundsClauses rows ∧
      TerminalHandler effect activation nextRows after := by
  induction terminal with
  | here => cases delta with
    | handler rows tail => cases tail with
      | nil => exact ⟨_, rows, .here⟩
  | plain terminal ih => cases delta with
    | plain rows tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .plain found⟩
  | handler terminal ih => cases delta with
    | handler rows tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .handler found⟩
  | cell terminal ih => cases delta with
    | cell tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .cell found⟩
  | cleanup terminal ih => cases delta with
    | cleanup rows tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .cleanup found⟩
  | normal terminal ih => cases delta with
    | normal tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .normal found⟩
  | unwinding terminal ih => cases delta with
    | unwinding tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .unwinding found⟩
  | closing terminal ih => cases delta with
    | closing tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .closing found⟩
  | retiring terminal ih => cases delta with
    | retiring tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .retiring found⟩
  | live terminal ih => cases delta with
    | live saved tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .live found⟩
  | spent terminal ih => cases delta with
    | spent tail => obtain ⟨nextRows, same, found⟩ := ih tail; exact ⟨nextRows, same, .spent found⟩

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

private def PackedRestored (before after : Packed) : Prop :=
  ∃ next : Context before.hints, after = next.pack ∧ RestoredContext before.context next

private inductive SelectionRestored : Selection → Selection → Prop where
  | builtin : SelectionRestored (.builtin identity) (.builtin identity)
  | handler (captured : PackedRestored beforeCaptured afterCaptured) (tail : PackedRestored beforeTail afterTail) :
      SelectionRestored (.handler beforeCaptured beforeTail contract modes)
        (.handler afterCaptured afterTail contract modes)

private def LookupRestored (before after : Option Selection) : Prop :=
  ∀ selected, before = some selected → ∃ next, after = some next ∧ SelectionRestored selected next

private theorem lookupRestored_prepend
    (frame nextFrame : Packed → Packed)
    (lift : ∀ before after, PackedRestored before after → PackedRestored (frame before) (nextFrame after))
    (found : LookupRestored before after) :
    LookupRestored (before.map (Selection.prepend frame)) (after.map (Selection.prepend nextFrame)) := by
  intro selected same
  cases before with
  | none => cases same
  | some actual =>
    obtain ⟨next, nextFound, delta⟩ := found actual rfl
    cases same
    cases delta with
    | builtin => exact ⟨_, by rw [nextFound]; rfl, .builtin⟩
    | handler captured tail => exact ⟨_, by rw [nextFound]; rfl, .handler (lift _ _ captured) tail⟩

private theorem restored_lookup (delta : RestoredContext before after) :
    LookupRestored (select effect operation before) (select effect operation after) := by
  induction delta with
  | nil => intro selected found; cases found
  | handler rows tail ih =>
    simp only [select]
    split
    · split
      · intro selected found
        cases found
        exact ⟨_, rfl, .handler ⟨_, rfl, .handler rows .nil⟩ ⟨_, rfl, tail⟩⟩
      · intro selected found; cases found
    · apply lookupRestored_prepend _ _ _ ih
      intro before after delta
      obtain ⟨next, rfl, change⟩ := delta
      exact ⟨_, rfl, .handler rows change⟩
  | cell tail ih =>
    simp only [select]
    split
    · intro selected found; cases found; exact ⟨_, rfl, .builtin⟩
    · apply lookupRestored_prepend _ _ _ ih
      intro before after delta
      obtain ⟨next, rfl, change⟩ := delta
      exact ⟨_, rfl, .cell change⟩
  | plain rows tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .plain rows change⟩
  | cleanup rows tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .cleanup rows change⟩
  | normal tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .normal change⟩
  | unwinding tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .unwinding change⟩
  | closing tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .closing change⟩
  | retiring tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .retiring change⟩
  | live saved tail ihSaved ihTail =>
    apply lookupRestored_prepend _ _ _ ihTail
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .live saved change⟩
  | spent tail ih =>
    apply lookupRestored_prepend _ _ _ ih
    intro before after delta
    obtain ⟨next, rfl, change⟩ := delta
    exact ⟨_, rfl, .spent change⟩

theorem RestoredContext.cut
    (delta : RestoredContext before after)
    (cut : Contextual.Cut effect operation before captured tail contract modes) :
    ∃ nextCaptured : Context captured.hints, ∃ nextTail : Context tail.hints,
      Contextual.Cut effect operation after nextCaptured nextTail contract modes ∧
      RestoredContext captured nextCaptured ∧ RestoredContext tail nextTail := by
  obtain ⟨next, found, change⟩ := restored_lookup delta _ cut
  cases change with
  | handler capturedDelta tailDelta =>
    obtain ⟨nextCaptured, rfl, capturedChange⟩ := capturedDelta
    obtain ⟨nextTail, rfl, tailChange⟩ := tailDelta
    exact ⟨nextCaptured, nextTail, found, capturedChange, tailChange⟩

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableRestoredSupport
open SourcePlanSignatures (ClauseSignatures Signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows

theorem ClauseRows.Selected.restore_support
    {family : Nat → SourceDependencyAnnotations.Dependencies}
    {bodies : ∀ owner, Signature (family owner)} {bodyRows : ∀ owner, Rows (bodies owner)}
    {declarationSignature : ClauseSignatures families}
    {declarations nextDeclarations : ClauseRows declarationSignature}
    (selected : ClauseRows.Selected operation held declarations bodyRows)
    (same : eraseModeSupportBoundsClauses nextDeclarations = eraseModeSupportBoundsClauses declarations) :
    ∃ nextBodyRows : ∀ owner, Rows (bodies owner),
      ClauseRows.Selected operation held nextDeclarations nextBodyRows ∧
      ∀ owner, SupportOnly (bodyRows owner) (nextBodyRows owner) := by
  induction selected with
  | ordinary =>
    rename_i rights ordinaryFamily ordinarySignatures originalBodyRows protectedFamily protectedSignatures protectedRows restFamilies restSignatures restRows supportBound
    cases nextDeclarations with
    | cons nextOrdinary nextProtected nextRest nextBound =>
      cases nextOrdinary with
      | available nextBodyRows =>
        simp only [eraseModeSupportBoundsClauses, eraseModeSupportBounds] at same
        refine ⟨nextBodyRows, .ordinary, ?_⟩
        intro owner
        unfold SupportOnly
        have modeSame : ModeRows.available (fun owner => eraseSupportBounds (nextBodyRows owner)) =
            ModeRows.available (fun owner => eraseSupportBounds (originalBodyRows owner)) := by
          injection same
        have bodySame := ModeRows.available.inj modeSame
        exact congrFun bodySame owner
  | protectedMode =>
    rename_i rights ordinaryFamily ordinarySignatures ordinaryRows protectedFamily protectedSignatures originalBodyRows restFamilies restSignatures restRows supportBound
    cases nextDeclarations with
    | cons nextOrdinary nextProtected nextRest nextBound =>
      cases nextProtected with
      | available nextBodyRows =>
        simp only [eraseModeSupportBoundsClauses, eraseModeSupportBounds] at same
        refine ⟨nextBodyRows, .protectedMode, ?_⟩
        intro owner
        unfold SupportOnly
        have modeSame : ModeRows.available (fun owner => eraseSupportBounds (nextBodyRows owner)) =
            ModeRows.available (fun owner => eraseSupportBounds (originalBodyRows owner)) := by
          injection same
        have bodySame := ModeRows.available.inj modeSame
        exact congrFun bodySame owner
  | pass different rest ih =>
    cases nextDeclarations with
    | cons nextOrdinary nextProtected nextRest nextBound =>
      simp only [eraseModeSupportBoundsClauses] at same
      obtain ⟨nextBodyRows, chosen, rowsSame⟩ := ih (nextDeclarations := nextRest) (by injection same)
      exact ⟨nextBodyRows, .pass different chosen, rowsSame⟩

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Split the rebuilt context at the exact saved prefix boundary. -/
theorem RestoredContext.split
    {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    (head : Context first) (tail : Context second) {after : Context (first.append second)}
    (delta : RestoredContext (head.append tail) after) :
    ∃ nextHead : Context first, ∃ nextTail : Context second,
      after = nextHead.append nextTail ∧ RestoredContext head nextHead ∧ RestoredContext tail nextTail := by
  induction head with
  | nil => exact ⟨.nil, after, rfl, .nil, delta⟩
  | plain rows rest ih => cases delta with
    | plain rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.plain _ nextHead, nextTail, rfl, .plain rowsSame headDelta, tailDelta⟩
  | handler activation rows rest ih => cases delta with
    | handler rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.handler activation _ nextHead, nextTail, rfl, .handler rowsSame headDelta, tailDelta⟩
  | cell rest ih => cases delta with
    | cell restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.cell nextHead, nextTail, rfl, .cell headDelta, tailDelta⟩
  | cleanup latent rows rest ih => cases delta with
    | cleanup rowsSame restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.cleanup latent _ nextHead, nextTail, rfl, .cleanup rowsSame headDelta, tailDelta⟩
  | normal rest ih => cases delta with
    | normal restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.normal nextHead, nextTail, rfl, .normal headDelta, tailDelta⟩
  | unwinding rest ih => cases delta with
    | unwinding restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.unwinding nextHead, nextTail, rfl, .unwinding headDelta, tailDelta⟩
  | closing rest ih => cases delta with
    | closing restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.closing nextHead, nextTail, rfl, .closing headDelta, tailDelta⟩
  | retiring owner rest ih => cases delta with
    | retiring restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.retiring owner nextHead, nextTail, rfl, .retiring headDelta, tailDelta⟩
  | live saved rest ihSaved ihRest => cases delta with
    | live savedDelta restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ihRest restDelta
      exact ⟨.live _ nextHead, nextTail, rfl, .live savedDelta headDelta, tailDelta⟩
  | spent rest ih => cases delta with
    | spent restDelta =>
      obtain ⟨nextHead, nextTail, rfl, headDelta, tailDelta⟩ := ih restDelta
      exact ⟨.spent nextHead, nextTail, rfl, .spent headDelta, tailDelta⟩

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourcePlanSignatures (Signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

theorem RestoredContext.closing_same (delta : RestoredContext before after) : after.closing? = before.closing? := by
  rw [← eraseContextSupport_closing after, ← eraseContextSupport_closing before, delta.complete]

theorem RestoredContext.context (delta : RestoredContext before after) : after.context = before.context := by
  rw [← eraseContextSupport_context after, ← eraseContextSupport_context before, delta.complete]

theorem RestoredContext.ticketNames (delta : RestoredContext before after) : after.ticketNames = before.ticketNames := by
  rw [← eraseContextSupport_ticketNames after, ← eraseContextSupport_ticketNames before, delta.complete]

theorem requestBudget_erase_iff {hints : ReturnHints scope} (context : Context hints) :
    RequestBudget budget phases effect operation (eraseContextSupport context) ↔
      RequestBudget budget phases effect operation context := by
  unfold RequestBudget
  rw [select_eraseContextSupport]
  cases found : select effect operation context with
  | none => rfl
  | some selected => cases selected with
    | builtin identity => rfl
    | handler captured tail contract modes =>
      simp only [Option.map_some, eraseSelectionSupport, erasePackedSupport, Context.pack,
        eraseContextSupport_closing, eraseContextSupport_context]

theorem RequestBudget.restore_support
    (checked : RequestBudget budget phases effect operation before)
    (delta : RestoredContext before after) : RequestBudget budget phases effect operation after := by
  apply (requestBudget_erase_iff after).mp
  rw [delta.complete]
  exact (requestBudget_erase_iff before).mpr checked

theorem CapturedClauseRows.restore_support
    {family : Nat → SourceDependencyAnnotations.Dependencies}
    {bodies : ∀ owner, Signature (family owner)} {bodyRows : ∀ owner, Rows (bodies owner)}
    (selected : CapturedClauseRows effect operation held before bodyRows)
    (delta : RestoredContext before after) :
    ∃ nextBodyRows : ∀ owner, Rows (bodies owner),
      CapturedClauseRows effect operation held after nextBodyRows ∧
      ∀ owner, SupportOnly (bodyRows owner) (nextBodyRows owner) := by
  cases selected with
  | selected terminal chosen =>
    obtain ⟨nextDeclarations, declarationsSame, nextTerminal⟩ := delta.terminal terminal
    obtain ⟨nextBodyRows, nextChosen, rowsSame⟩ := ClauseRows.Selected.restore_support chosen declarationsSame
    exact ⟨nextBodyRows, .selected nextTerminal nextChosen, rowsSame⟩

end Ash.OneShot.CoreCallableRestoredSupport
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.complete
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.cut
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.terminal
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.split
#print axioms Ash.OneShot.CoreCallableRestoredSupport.ClauseRows.Selected.restore_support
#print axioms Ash.OneShot.CoreCallableRestoredSupport.CapturedClauseRows.restore_support
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RequestBudget.restore_support

#print axioms Ash.OneShot.CoreCallableContractAdmission.DomainDeclarationAuthentication.world_transport
#print axioms Ash.OneShot.CoreCallableContractAdmission.DomainDeclarationAuthentication.restore_world_receiver
#print axioms Ash.OneShot.CoreCallableContractAdmission.DomainDeclarationAuthentication.received_support
