import SourceResourceRoutes

/-! Recursive source scope annotations retain normal and closing lookup
separately. Saved continuations contribute providers only to closing. This
connects finite structural annotations to existing closing evidence; their
hereditary source inference and preservation remain separate obligations. -/
namespace Ash.OneShot.SourceRecursiveRoutes
open ScopedExpressions ScopedExecution
open SourceResourceRoutes (Entry Route)

abbrev Context := SourceResourceRoutes.Context

def scopeProviders : Context → List Instance
  | [] => []
  | .cell identity :: rest => .cell identity :: scopeProviders rest
  | _ :: rest => scopeProviders rest

theorem scope_providers_append (left right : Context) : scopeProviders (left ++ right) = scopeProviders left ++ scopeProviders right := by
  induction left with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp [scopeProviders, ih]

/-- Realize an interpretation projection, ignoring dormant source scopes and
frames that cannot select an operation. Handler activation names stay actual. -/
inductive Scope : Context → Control → Prop where
  | nil : Scope [] .nil
  | handler (kind : frame.kind = .handler effect activation) (tail : Scope rest retained) :
      Scope (.handler effect :: rest) (.push frame retained)
  | cell (kind : frame.kind = .resource identity) (tail : Scope rest retained) :
      Scope (.cell identity :: rest) (.push frame retained)
  | skip (silent : frame.target = none) (tail : Scope context retained) : Scope context (.push frame retained)
  | live (tail : Scope context rest) : Scope context (.live owner input answer capture rest)
  | spent (tail : Scope context rest) : Scope context (.spent owner answer rest)

theorem Scope.append (front : Scope first a) (tail : Scope second b) : Scope (first ++ second) (a.append b) := by
  induction front with
  | nil => exact tail
  | handler kind rest ih => exact .handler kind ih
  | cell kind rest ih => exact .cell kind ih
  | skip silent rest ih => exact .skip silent ih
  | live rest ih => exact .live ih
  | spent rest ih => exact .spent ih

theorem Scope.route (scope : Scope context retained) (route : Route outward context requested target) :
    retained.resolve requested = target.map Target.builtin ∧ requested ∈ scopeProviders context ++ outward := by
  induction scope generalizing target with
  | nil => cases route with | outside included => exact ⟨rfl, included⟩
  | handler kind tail ih => cases route with
      | handler different next =>
          obtain ⟨found, bound⟩ := ih next
          exact ⟨by simpa [Control.resolve, Frame.resolve, kind, different] using found, bound⟩
  | cell kind tail ih => cases route with
      | cell same =>
          subst requested
          exact ⟨by simp [Control.resolve, Frame.resolve, kind], by simp [scopeProviders]⟩
      | cellMiss different next =>
          obtain ⟨found, bound⟩ := ih next
          exact ⟨by simpa [Control.resolve, Frame.resolve, kind, different] using found,
            List.mem_cons_of_mem _ bound⟩
  | @skip context retained frame silent tail ih =>
      have noTarget : frame.resolve requested = none := by
        cases kind : frame.kind <;> simp_all [Frame.target, Frame.resolve]
      obtain ⟨found, bound⟩ := ih route
      exact ⟨by simpa [Control.resolve, noTarget] using found, bound⟩
  | live tail ih | spent tail ih => exact ih route

theorem Route.outside (route : Route outward context requested target) (absent : target = none) : requested ∈ outward := by
  induction route with
  | outside included => exact included
  | cell same => cases absent
  | cellMiss different tail ih | handler different tail ih | cleanup tail ih => exact ih absent

inductive Shape where
  | nil
  | plain : Shape → Shape
  | handler : Instance → Shape → Shape
  | cell : Nat → Shape → Shape
  | cleanup : List Instance → Shape → Shape
  | live : Shape → Shape → Shape
  | spent : Shape → Shape

def Shape.normal : Shape → Context
  | .nil => []
  | .handler effect rest => .handler effect :: rest.normal
  | .cell identity rest => .cell identity :: rest.normal
  | .plain rest | .cleanup _ rest | .live _ rest | .spent rest => rest.normal

def Shape.closing : Shape → Context
  | .nil => []
  | .cell identity rest => .cell identity :: rest.closing
  | .live capture rest => capture.closing ++ rest.closing
  | .plain rest | .handler _ rest | .cleanup _ rest | .spent rest => rest.closing

inductive Closing (outward : List Instance) : Shape → Context → Context → Prop where
  | nil : Closing outward .nil original surviving
  | plain (tail : Closing outward rest original surviving) : Closing outward (.plain rest) original surviving
  | handler (tail : Closing outward rest original surviving) : Closing outward (.handler effect rest) original surviving
  | cell (tail : Closing outward rest original surviving) : Closing outward (.cell identity rest) original surviving
  | cleanup
      (routes : ∀ effect ∈ needs, ∃ target,
        Route outward (rest.normal ++ original) effect target ∧
        Route outward (rest.closing ++ surviving) effect target)
      (tail : Closing outward rest original surviving) : Closing outward (.cleanup needs rest) original surviving
  | live (inside : Closing outward capture (rest.normal ++ original) (rest.closing ++ surviving))
      (outside : Closing outward rest original surviving) : Closing outward (.live capture rest) original surviving
  | spent (tail : Closing outward rest original surviving) : Closing outward (.spent rest) original surviving

inductive Realizes : Shape → Stack → List CloseEntry → Prop where
  | nil : Realizes .nil .nil []
  | plain (tail : Realizes rest stack plan) : Realizes (.plain rest) (.push (.plain plain) stack) plan
  | handler (tail : Realizes rest stack plan) :
      Realizes (.handler handler.effectInst rest) (.push (.handler handler) stack) plan
  | cell (tail : Realizes rest stack plan) :
      Realizes (.cell identity rest) (.push (.cell identity payload scope answer) stack) (.release identity payload :: plan)
  | cleanup (tail : Realizes rest stack plan) :
      Realizes (.cleanup action.requests rest) (.push (.armed action) stack) (.invoke action :: plan)
  | live (inside : Realizes capture saved first) (outside : Realizes rest stack second) :
      Realizes (.live capture rest) (.live owner input answer saved scope stack) (first ++ .retire owner :: second)
  | spent (tail : Realizes rest stack plan) : Realizes (.spent rest) (.spent owner answer scope stack) plan

theorem Realizes.built (realized : Realizes shape stack plan) : makePlan stack = some plan := by
  induction realized with
  | nil => rfl
  | plain tail ih | handler tail ih | spent tail ih => exact ih
  | cell tail ih | cleanup tail ih => simp [makePlan, ih]
  | live inside outside ihInside ihOutside => simp [makePlan, ihInside, ihOutside]

/-- Reuse the kernel's existing ownership theorem for this same plan,
including every recursively owned continuation retirement. -/
theorem Realizes.owner_accounting (realized : Realizes shape stack plan) :
    (planOwners (plan.map CloseEntry.erase)).Perm stack.erase.owners :=
  raw_plan_accounting stack.erase (by
    simpa only [realized.built, Option.map_some] using (make_plan_erases stack).symm)

theorem Realizes.normal_scope (realized : Realizes shape stack plan) : Scope shape.normal stack.erase := by
  induction realized with
  | nil => exact .nil
  | plain tail ih => exact .skip rfl ih
  | handler tail ih => exact .handler rfl ih
  | cell tail ih => exact .cell rfl ih
  | cleanup tail ih => exact .skip rfl ih
  | live inside outside ihInside ihOutside => exact .live ihOutside
  | spent tail ih => exact .spent ih

theorem Realizes.closing_scope (realized : Realizes shape stack plan) :
    Scope shape.closing (planControl (plan.map CloseEntry.erase)) := by
  induction realized with
  | nil => exact .nil
  | plain tail ih | handler tail ih | spent tail ih => exact ih
  | cell tail ih => exact .cell rfl ih
  | cleanup tail ih => exact .skip rfl ih
  | live inside outside ihInside ihOutside =>
      simpa only [Shape.closing, List.map_append, List.map_cons, CloseEntry.erase, plan_control_append, planControl]
        using ihInside.append (Scope.skip (frame := (CloseItem.retire _).frame) rfl ihOutside)

theorem Realizes.providers (realized : Realizes shape stack plan) : scopeProviders shape.closing = ScopedPorts.planProvides plan := by
  induction realized with
  | nil => rfl
  | plain tail ih | handler tail ih | cleanup tail ih | spent tail ih => exact ih
  | cell tail ih => exact congrArg (List.cons _) ih
  | live inside outside ihInside ihOutside =>
      simp only [Shape.closing, scope_providers_append, ScopedPorts.plan_provides_append, ScopedPorts.planProvides,
        ihInside, ihOutside]

theorem Realizes.visible_subset (realized : Realizes shape stack plan) :
    stack.erase.visible ⊆ (planControl (plan.map CloseEntry.erase)).visible := by
  induction realized with
  | nil => exact List.Subset.refl _
  | plain tail ih | handler tail ih | cleanup tail ih | spent tail ih => exact ih
  | cell tail ih => exact List.cons_subset_cons _ ih
  | live inside outside ihInside ihOutside =>
      simpa only [List.map_append, List.map_cons, CloseEntry.erase, plan_control_append, visible_append,
        planControl, CloseItem.frame, Control.visible, Frame.visible, List.nil_append, Stack.erase] using
        (List.Subset.trans ihOutside (List.subset_append_right
          (planControl (List.map CloseEntry.erase _)).visible _))

/-- A suffix may expose additional saved cells during closing. Existing
support transports by inclusion; callback dependencies need not be recounted. -/
private theorem accessible_extension {a b c d resources : List Nat} (inside : a ⊆ b) (outside : c ⊆ d ++ resources) :
    a ++ (c ++ resources) ⊆ b ++ (d ++ resources) := by
  intro identity member
  rcases List.mem_append.mp member with localMember | outsideMember
  · exact List.mem_append_left _ (inside localMember)
  · rcases List.mem_append.mp outsideMember with callerMember | externalMember
    · exact List.mem_append_right _ (outside callerMember)
    · exact List.mem_append_right _ (List.mem_append_right _ externalMember)

/-- Both recursive branches use the same source annotations and actual
suffixes. The existing plan-composition, support and closing rules supply
the operational interface; no later successful disposal is a premise. -/
theorem Realizes.interfaces (realized : Realizes shape stack plan)
    (closing : Closing outward shape originalContext survivingContext)
    (originalScope : Scope originalContext original)
    (survivingScope : Scope survivingContext surviving)
    (supported : Supported stack.erase (original.visible ++ resources))
    (available : original.visible ⊆ surviving.visible ++ resources)
    (typed : ScopedPorts.StackTyped signature tickets world stack input output) :
    ScopedPorts.PlanTyped signature world (scopeProviders survivingContext ++ outward) plan ∧
      Admission.OpenCloses stack.erase original surviving resources outward (plan.map CloseEntry.erase) := by
  induction realized generalizing originalContext survivingContext original surviving input output with
  | nil => exact ⟨.nil, .nil _ _ _ _⟩
  | plain tail ih =>
      cases closing with
      | plain closing => cases supported with
          | push frame rest ambient support access => cases typed with
              | push frameTyped restTyped =>
                  obtain ⟨types, closed⟩ := ih closing originalScope survivingScope support available restTyped
                  exact ⟨types, .bind _ _ _ _ _ _ _ rfl closed⟩
  | handler tail ih =>
      cases closing with
      | handler closing => cases supported with
          | push frame rest ambient support access => cases typed with
              | push frameTyped restTyped =>
                  obtain ⟨types, closed⟩ := ih closing originalScope survivingScope support available restTyped
                  exact ⟨types, .handler _ _ _ _ _ _ _ _ _ rfl closed⟩
  | cell tail ih =>
      cases closing with
      | cell closing => cases supported with
          | push frame rest ambient support access => cases typed with
              | push frameTyped restTyped =>
                  obtain ⟨types, closed⟩ := ih closing originalScope survivingScope support available restTyped
                  exact ⟨.release types, .resource _ _ _ _ _ _ _ _ rfl closed⟩
  | @cleanup rest stack plan action tail ih =>
      cases closing with
      | cleanup requests closing => cases supported with
          | push frame restControl ambient support access => cases typed with
              | push frameTyped restTyped => cases frameTyped with
                  | armed scope callback =>
                      obtain ⟨types, closed⟩ := ih closing originalScope survivingScope support available restTyped
                      have normal := tail.normal_scope.append originalScope
                      have closingScope := tail.closing_scope.append survivingScope
                      have effects : action.requests ⊆ ScopedPorts.planProvides plan ++
                          (scopeProviders survivingContext ++ outward) := by
                        intro effect member
                        obtain ⟨target, before, after⟩ := requests effect member
                        simpa only [scope_providers_append, tail.providers, List.append_assoc] using (closingScope.route after).2
                      have routes : Admission.OpenRequests (stack.erase.append original)
                          ((planControl (plan.map CloseEntry.erase)).append surviving) outward action.requests := by
                        have each := requests
                        generalize same : action.requests = needs at each ⊢
                        clear same
                        induction needs with
                        | nil => exact .nil
                        | cons effect needs ih =>
                            obtain ⟨target, before, after⟩ := each effect List.mem_cons_self
                            have first := (normal.route before).1
                            have second := (closingScope.route after).1
                            have next := ih (fun next member => each next (List.mem_cons_of_mem _ member))
                            cases target with
                            | none => exact .outside effect needs first second (Route.outside before rfl) next
                            | some identity => exact .localTarget effect needs (.builtin identity) first second next
                      exact ⟨.invoke callback effects types,
                        .armed _ _ _ _ _ _ _ _ rfl rfl
                          (by simpa only [visible_append, List.append_assoc] using
                            List.Subset.trans access (accessible_extension tail.visible_subset available))
                          (by simpa only [ExecFrame.erase, ActionData.erase] using routes) closed⟩
  | @live capture saved first rest stack second owner inputType answerType scope inside outside ihInside ihOutside =>
      cases closing with
      | live closingInside closingOutside => cases supported with
          | live owner input answer savedControl restControl ambient supportInside supportOutside => cases typed with
              | live known scopeTyped typedInside typedOutside =>
                  obtain ⟨typesOutside, closedOutside⟩ := ihOutside closingOutside originalScope survivingScope
                    supportOutside available typedOutside
                  have innerAvailable : (stack.erase.append original).visible ⊆
                      ((planControl (second.map CloseEntry.erase)).append surviving).visible ++ resources := by
                    simp only [visible_append, List.append_assoc]
                    exact List.append_subset.mpr
                      ⟨fun identity member => List.mem_append_left _ (outside.visible_subset member),
                        fun identity member => List.mem_append_right _ (available member)⟩
                  obtain ⟨typesInside, closedInside⟩ := ihInside closingInside
                    (outside.normal_scope.append originalScope) (outside.closing_scope.append survivingScope)
                    (by simpa only [visible_append, List.append_assoc] using supportInside)
                    innerAvailable typedInside
                  refine ⟨ScopedPorts.plan_typed_append (right := .retire owner :: second) ?_ (.retire typesOutside), ?_⟩
                  · simpa only [scope_providers_append, outside.providers, List.append_assoc, ScopedPorts.planProvides] using typesInside
                  · simpa only [List.map_append, List.map_cons, CloseEntry.erase, Stack.erase] using
                      Admission.OpenCloses.live owner _ _ _ _ _ _ _ _ _ _ closedInside closedOutside
  | spent tail ih =>
      cases closing with
      | spent closing => cases supported with
          | spent owner answer rest ambient support => cases typed with
              | spent known scope restTyped =>
                  obtain ⟨types, closed⟩ := ih closing originalScope survivingScope support available restTyped
                  exact ⟨types, .spent _ _ _ _ _ _ _ _ closed⟩

/-- Ownership inclusion is the existing independent structural judgment.
This theorem adds no new recursive ownership argument. -/
def Realizes.certificate (realized : Realizes shape stack plan)
    (closing : Closing record.annotation.closeEffects shape [] [])
    (supported : Supported stack.erase (Admission.outsideResources stack.erase))
    (typed : ScopedPorts.StackTyped signature tickets world stack input output)
    (internal : InternalUses stack.erase.liveTickets stack.erase.pending) :
    DeclaredClosingInvariant.Certificate signature world record stack :=
  let checked := realized.interfaces closing Scope.nil Scope.nil
    supported (List.nil_subset _) typed
  ⟨plan, realized.built, checked.1, checked.2, internal⟩

namespace Examples
open ScopedPorts.CompletionExamples (action callback_typed signature nested)

def nestedShape : Shape := .live (.cleanup [.cell 4] .nil) (.cell 4 .nil)

theorem nested_closing (outward : List Instance) : Closing outward nestedShape [] [] :=
  .live (.cleanup (by
    intro effect member
    cases List.mem_singleton.mp member
    exact ⟨some 4, .cell rfl, .cell rfl⟩) .nil) (.cell .nil)

theorem nested_realized : Realizes nestedShape nested [.invoke action, .retire 6, .release 4 17] :=
  .live (.cleanup (action := action) .nil) (.cell .nil)

theorem nested_supported : Supported nested.erase [] := by
  refine .live _ _ _ _ _ _ (.push _ _ _ (.nil _) ?_) (.push _ _ _ (.nil _) (by simp [ExecFrame.erase]))
  change Syntax.resourceDependencies action.action.dependencies ⊆ [4]
  decide

theorem nested_typed (known : tickets 6 = some (ScopedPorts.Port.unit, .unit)) :
    ScopedPorts.StackTyped signature tickets [4] nested .unit .unit :=
  .live known ⟨_, .none⟩ (.push (.armed ⟨_, .none⟩ callback_typed) .nil)
    (.push (.cell ⟨_, .none⟩ (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources])) .nil)

theorem nested_certificate (record : CoherentSourceTypes.Owners.Record)
    {tickets : ScopedPorts.TicketSignatures}
    (known : tickets 6 = some (ScopedPorts.Port.unit, .unit)) :
    Nonempty (DeclaredClosingInvariant.Certificate signature [4] record nested) :=
  ⟨nested_realized.certificate (nested_closing _) (supported_mono nested_supported (List.nil_subset _))
    (nested_typed known) InternalUses.nil⟩

/-- The inner callback's normal source scope still contains the override;
the closing scope cannot replace it with the retained cell. -/
theorem nested_override_rejected (outward : List Instance) :
    ¬ Closing outward (.live (.cleanup [.cell 4] .nil) (.handler (.cell 4) (.cell 4 .nil))) [] [] := by
  intro closing
  cases closing with
  | live inside outside => cases inside with
      | cleanup routes tail =>
          obtain ⟨target, before, after⟩ := routes (.cell 4) List.mem_cons_self
          cases before with
          | handler different tail => exact different rfl

/-- A cell made active only by closing is not silently substituted for an
outside request, even if the outward row contains that effect. -/
theorem newly_visible_cell_rejected (outward : List Instance) :
    ¬ Closing outward (.cleanup [.cell 4] (.live (.cell 4 .nil) .nil)) [] [] := by
  intro closing
  cases closing with
  | cleanup routes tail =>
      obtain ⟨target, before, after⟩ := routes (.cell 4) List.mem_cons_self
      cases before with
      | outside included => cases after with
          | cellMiss different tail => exact different rfl

end Examples

end Ash.OneShot.SourceRecursiveRoutes

#print axioms Ash.OneShot.SourceRecursiveRoutes.scope_providers_append
#print axioms Ash.OneShot.SourceRecursiveRoutes.Scope.append
#print axioms Ash.OneShot.SourceRecursiveRoutes.Scope.route
#print axioms Ash.OneShot.SourceRecursiveRoutes.Route.outside
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.built
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.owner_accounting
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.normal_scope
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.closing_scope
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.providers
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.visible_subset
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.interfaces
#print axioms Ash.OneShot.SourceRecursiveRoutes.Realizes.certificate
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_closing
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_realized
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_supported
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_typed
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_certificate
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.nested_override_rejected
#print axioms Ash.OneShot.SourceRecursiveRoutes.Examples.newly_visible_cell_rejected
