import SourceScheduledEntries

/-! Fresh handler registration preserves the existing source forest. Registry
agreement is needed only at retained activations, including dormant captures. -/
namespace Ash.OneShot.SourceScheduledFrames
open ScopedExpressions ScopedExecution

theorem Frame.registries_congr
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (tablesAgree : ∀ handler, handler.activation ∈ entry.erase.activation → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ entry.erase.activation → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ entry.erase.activation → required handler = nextRequired handler) :
    Frame (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked => exact .plain context scope inputAnnotation outputAnnotation checked
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      have tableSame := tablesAgree _ List.mem_cons_self
      have familiesSame := familiesAgree _ List.mem_cons_self
      have requiredSame := requiredAgree _ List.mem_cons_self
      rename_i handler plans
      generalize oldFamily : families handler = family at *
      generalize oldTable : tables handler = table at *
      generalize oldRequired : required handler = needed at *
      clear oldFamily oldTable oldRequired
      subst family table needed
      exact .handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes
  | cell scope noEscape annotation interface => exact .cell scope noEscape annotation interface
  | armed scope callback annotation interface checked => exact .armed scope callback annotation interface checked
  | running scope callback saved annotation interface => exact .running scope callback saved annotation interface
  | closing scope interface => exact .closing scope interface
  | retiring known interface => exact .retiring known interface

theorem Segment.registries_congr
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing)
    (tablesAgree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ stack.erase.activations → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ stack.erase.activations → required handler = nextRequired handler) :
    Segment (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      have nextTablesAgree := fun handler member => tablesAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr nextTablesAgree
      have changed := head.registries_congr
        (fun handler member => tablesAgree handler (List.mem_append_left _ member))
        (fun handler member => familiesAgree handler (List.mem_append_left _ member))
        (fun handler member => requiredAgree handler (List.mem_append_left _ member))
      simpa only [same] using Segment.push changed (ih nextTablesAgree
        (fun handler member => familiesAgree handler (List.mem_append_right _ member))
        (fun handler member => requiredAgree handler (List.mem_append_right _ member))) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held
        (ihSaved
          (fun handler member => tablesAgree handler (List.mem_append_left _ member))
          (fun handler member => familiesAgree handler (List.mem_append_left _ member))
          (fun handler member => requiredAgree handler (List.mem_append_left _ member))) savedBound
        (ihTail
          (fun handler member => tablesAgree handler (List.mem_append_right _ member))
          (fun handler member => familiesAgree handler (List.mem_append_right _ member))
          (fun handler member => requiredAgree handler (List.mem_append_right _ member))) resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent known annotation scope (ih tablesAgree familiesAgree requiredAgree) bound

end Ash.OneShot.SourceScheduledFrames

namespace Ash.OneShot.SourcePlannedClosingPlans

/-- Closing plans install no handlers, so their exact stored requirements are
independent of the registry. Reuse the existing closing-context equation. -/
theorem Template.tables_congr
    (template : Template operations policy contracts tables world caller plans raw requirements) :
    Template operations policy contracts nextTables world caller plans raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih =>
      simpa only [RecursiveHandlerTables.closing_context_congr tables nextTables] using Template.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih =>
      simpa only [RecursiveHandlerTables.closing_context_congr tables nextTables] using Template.invoke callback ih

end Ash.OneShot.SourcePlannedClosingPlans

namespace Ash.OneShot.SourceScheduledClosingData

theorem Certificate.tables_congr
    (certificate : Certificate operations policy contracts tables world plan saved raw requirements) :
    Certificate operations policy contracts nextTables world plan saved raw requirements := by
  obtain ⟨plans, template, same⟩ := certificate
  exact ⟨plans, template.tables_congr, same⟩

end Ash.OneShot.SourceScheduledClosingData

namespace Ash.OneShot.SourceScheduledClosingRecords

theorem Records.tables_congr
    (records : Records operations policy contracts tables annotations world root entries) :
    Records operations policy contracts nextTables annotations world root entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved located built recorded certificate.tables_congr) ih

end Ash.OneShot.SourceScheduledClosingRecords

#print axioms Ash.OneShot.SourceScheduledFrames.Frame.registries_congr
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.registries_congr
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.tables_congr
#print axioms Ash.OneShot.SourceScheduledClosingData.Certificate.tables_congr
#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.tables_congr
