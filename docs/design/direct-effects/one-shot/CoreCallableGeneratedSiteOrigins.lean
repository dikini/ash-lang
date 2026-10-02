import CoreCallableGeneratedChronology

/-! Chronological current-site and saved strict-right origins for the existing
thirteen generated operation families. Physical-history promotion is excluded. -/
namespace Ash.OneShot.CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open CoreStrictStack CoreCallableReachableResume CoreCallableCleanupOrigins
open CoreCallableSiteLineage CoreCallableGeneralHistory CoreCallableRunningOccurrence
open ScopedExpressions ScopedExecution

def MapsCanonical (current : Endpoint graph) : Prop :=
  ∀ mapped ∈ current.maps, CanonicalOwnerMap graph mapped.1

def SavedRightSite (graph : Graph) (owners : OwnerMap) (scope : Execution.Scope)
    (frame : CoreMachine.Frame) : Prop :=
  match frame with
  | .applyFunction right _ | .tupleLeft right _ => SiteLineage graph owners scope right
  | _ => True

def SavedRightSites (current : Endpoint graph) : Prop :=
  ∀ mapped ∈ current.maps, SavedRightSite graph mapped.1 current.focus.scope mapped.2

def EvaluatingSite (current : Endpoint graph) : Prop :=
  match current.state.control with
  | .evaluate site _ => SiteLineage graph current.owners current.focus.scope site
  | .returned _ | .discard _ _ => True

structure SiteOrigins (current : Endpoint graph) : Prop where
  canonical : CanonicalOwnerMap graph current.owners
  maps : MapsCanonical current
  evaluating : EvaluatingSite current
  right : SavedRightSites current

theorem SiteOrigins.at {graph : Graph} {current : Endpoint graph} (origins : SiteOrigins current)
    (control : current.state.control = .evaluate site environment) :
    SiteLineage graph current.owners current.focus.scope site := by
  simpa only [EvaluatingSite,control] using origins.evaluating

private theorem singleton_canonical {graph : Graph} {current : Endpoint graph} (origins : SiteOrigins current)
    (same : current.maps = [(owners,frame)]) : CanonicalOwnerMap graph owners :=
  origins.maps (owners,frame) (by simp [same])

private theorem singleton_right {graph : Graph} {current : Endpoint graph} (origins : SiteOrigins current)
    (same : current.maps = [(owners,frame)]) :
    SavedRightSite graph owners current.focus.scope frame :=
  origins.right (owners,frame) (by simp [same])

theorem started_site_origins
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target) :
    SiteOrigins (started start) := by
  have canonical := CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical start.installed.origin
  refine ⟨canonical,?_,?_,?_⟩
  · simp [MapsCanonical,started]
  · change SiteLineage graph cleanupOwners .none action
    exact .inactive canonical
  · simp [SavedRightSites,started]

private theorem entry_child (kind : EntryKind node index frame) : index ∈ node.kind.children := by
  cases kind <;> simp_all [Kind.children]

private theorem entry_right (kind : EntryKind node index frame)
    (children : ∀ child ∈ node.kind.children, SiteLineage graph owners scope child) :
    SavedRightSite graph owners scope frame := by
  cases kind with
  | application kind => exact children _ (by simp [kind,Kind.children])
  | tuple kind => exact children _ (by simp [kind,Kind.children])
  | request => trivial
  | resume => trivial

/-- The preceding current-evaluate site, rather than an operation's duplicate
current lineage input, produces literal descent and both strict child sites. -/
theorem Operation.site_origins {graph : Graph} {before after : Endpoint graph} (ordered : Postorder graph)
    (operation : Operation before after created discharged) (origins : SiteOrigins before) :
    SiteOrigins after := by
  cases operation with
  | cleanup input =>
    have parent : SiteLineage graph before.owners input.data.scope input.site := by
      simpa only [input.empty.focus] using origins.at input.control
    have child := parent.child ordered input.known (by simp [input.kind,Kind.children]) (child := input.body)
    refine ⟨origins.canonical,?_,?_,?_⟩
    · simp [MapsCanonical,cleanup_result]
    · simpa only [EvaluatingSite,cleanup_result,CoreCallableGeneralCleanupRegistration.registeredState] using child
    · simp [SavedRightSites,cleanup_result]
  | bind input =>
    have parent : SiteLineage graph input.owners input.plain.scope input.past.site := by
      simpa only [input.ownersSame,input.empty.focus] using origins.at input.control
    have child := parent.child ordered input.past.known
      (by simp [input.past.kind,Kind.children]) (child := input.past.initializer)
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [bind_result,← input.ownersSame] using origins.canonical
    · simp [MapsCanonical,bind_result]
    · simpa only [EvaluatingSite,bind_result] using child
    · simp [SavedRightSites,bind_result]
  | beta input =>
    refine ⟨CanonicalOwnerMap.empty graph,?_,?_,?_⟩
    · simp [MapsCanonical,beta_result]
    · change SiteLineage graph [] .none input.body
      exact SiteLineage.beta
    · simp [SavedRightSites,beta_result]
  | bindReturn input =>
    refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical input.past.saved.saved.origin,?_,?_,?_⟩
    · simp [MapsCanonical,bind_return_result]
    · simpa only [EvaluatingSite,bind_return_result] using input.past.saved.site
    · simp [SavedRightSites,bind_return_result]
  | handler input =>
    have parent : SiteLineage graph input.owners input.data.scope input.site := by
      simpa only [input.ownersSame,input.empty.focus] using origins.at input.control
    have child := parent.child ordered input.installation.known
      (by simp [input.installation.kind,Kind.children]) (child := input.installation.body)
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [handler_result,← input.ownersSame] using origins.canonical
    · simp [MapsCanonical,handler_result]
    · simpa only [EvaluatingSite,handler_result] using child
    · simp [SavedRightSites,handler_result]
  | handlerReturn input =>
    refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical input.installation.origin,?_,?_,?_⟩
    · simp [MapsCanonical,handler_return_result]
    · simp [EvaluatingSite,handler_return_result,input.control]
    · simp [SavedRightSites,handler_return_result]
  | literal input =>
    refine ⟨origins.canonical,?_,?_,?_⟩
    · exact origins.maps
    · simp [EvaluatingSite,literal_result]
    · exact origins.right
  | entry input =>
    have parent := origins.at input.control
    have child := parent.child ordered input.known (entry_child input.kind)
    have right := entry_right input.kind (fun child member => parent.child ordered input.known member)
    refine ⟨origins.canonical,?_,?_,?_⟩
    · simp [MapsCanonical,entry_result,origins.canonical]
    · simpa only [EvaluatingSite,entry_result] using child
    · simpa [SavedRightSites,entry_result] using right
  | swap input =>
    have canonical := singleton_canonical origins input.maps
    have right := singleton_right origins input.maps
    have next : SiteLineage graph input.frameOwners before.focus.scope input.nextIndex := by
      obtain same | same := input.frameBefore
      · simpa only [same,SavedRightSite] using right
      · simpa only [same,SavedRightSite] using right
    refine ⟨canonical,?_,?_,?_⟩
    · simp [MapsCanonical,swap_result,canonical]
    · simpa only [EvaluatingSite,swap_result] using next
    · obtain same | same := input.frameAfter <;> simp [SavedRightSites,swap_result,same,SavedRightSite]
  | tuple input =>
    refine ⟨origins.canonical,?_,?_,?_⟩
    · simp [MapsCanonical,tuple_result]
    · simp [EvaluatingSite,tuple_result]
    · simp [SavedRightSites,tuple_result]
  | capture input =>
    have canonical := CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical (location before input.index).installation.origin
    have selected := SiteLineage.selected_clause (dynamicTicket := before.state.nextOwner)
      ordered canonical (location before input.index).installation.known
      (location before input.index).installation.kind (List.mem_of_find?_eq_some input.selected)
    refine ⟨canonical.clause,?_,?_,?_⟩
    · simp [MapsCanonical,capture_result]
    · simpa only [EvaluatingSite,capture_result,CoreGeneralCaptureResume.captureAfter] using selected
    · simp [SavedRightSites,capture_result]
  | resume input =>
    refine ⟨origins.canonical,?_,?_,?_⟩
    · simp [MapsCanonical,resume_result]
    · simp [EvaluatingSite,resume_result,CoreGeneralCaptureResume.resumeAfter]
    · simp [SavedRightSites,resume_result]
  | spentReturn input =>
    refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical input.installation.installation.origin,?_,?_,?_⟩
    · simp [MapsCanonical,spent_return_result]
    · simp [EvaluatingSite,spent_return_result,CoreGeneralRestoration.observedState]
    · simp [SavedRightSites,spent_return_result]

theorem Generated.current_site_origins {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) : SiteOrigins current := by
  induction run with
  | initial => exact started_site_origins _
  | next earlier operation ih => exact operation.site_origins ordered ih

theorem Generated.current_canonical_owners {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) : CanonicalOwnerMap graph current.owners :=
  (run.current_site_origins ordered).canonical

#print axioms SiteOrigins.at
#print axioms started_site_origins
#print axioms Operation.site_origins
#print axioms Generated.current_site_origins
#print axioms Generated.current_canonical_owners
end Ash.OneShot.CoreCallableGeneratedChronology
