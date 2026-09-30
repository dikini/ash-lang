import CoreSyntax
import CoreTranslation

/-! Generated from independently validated Effect Core by the test-only
alignment exporter. Regenerate with the ignored Rust regeneration test.
The manifest retains static identities and signatures; it is not admission. -/
namespace Ash.OneShot.CoreExportedFixture
open CoreSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def graph : Graph := ⟨[
  { originalId := 48, type := .unit, effects := [], source := some ⟨1, 1, 69, 548⟩, kind := (.variable 0) },
  { originalId := 0, type := .integer, effects := [], source := some ⟨1, 1, 119, 120⟩, kind := (.integer (0)) },
  { originalId := 1, type := (.reference (.bound 0)), effects := [], source := some ⟨1, 1, 98, 548⟩, kind := (.variable 1) },
  { originalId := 2, type := .integer, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 98, 548⟩, kind := (.request (.cell (.bound 0)) 0 2) },
  { originalId := 3, type := (.function (.reference (.bound 0)) .integer [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 98, 548⟩, kind := (.function ⟨1, (.reference (.bound 0))⟩ 3) },
  { originalId := 4, type := (.product (.reference (.bound 0)) .integer), effects := [], source := some ⟨1, 1, 98, 548⟩, kind := (.variable 2) },
  { originalId := 5, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 98, 548⟩, kind := (.request (.cell (.bound 0)) 1 5) },
  { originalId := 6, type := (.function (.product (.reference (.bound 0)) .integer) .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 98, 548⟩, kind := (.function ⟨2, (.product (.reference (.bound 0)) .integer)⟩ 6) },
  { originalId := 7, type := (.function (.product (.reference (.bound 0)) .integer) .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 179, 189⟩, kind := (.variable 3) },
  { originalId := 8, type := (.reference (.bound 0)), effects := [], source := some ⟨1, 1, 191, 192⟩, kind := (.variable 4) },
  { originalId := 9, type := .integer, effects := [], source := some ⟨1, 1, 194, 195⟩, kind := (.integer (7)) },
  { originalId := 10, type := (.product (.reference (.bound 0)) .integer), effects := [], source := some ⟨1, 1, 190, 196⟩, kind := (.tuple [9, 10]) },
  { originalId := 11, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 179, 196⟩, kind := (.apply 8 11) },
  { originalId := 12, type := (.function .unit .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 157, 202⟩, kind := (.function ⟨5, .unit⟩ 12) },
  { originalId := 13, type := .boolean, effects := [], source := some ⟨1, 1, 243, 247⟩, kind := (.boolean true) },
  { originalId := 14, type := .unit, effects := [(.user 0 [])], source := some ⟨1, 1, 225, 247⟩, kind := (.request (.user 0 []) 0 14) },
  { originalId := 15, type := .boolean, effects := [], source := some ⟨1, 1, 287, 292⟩, kind := (.boolean false) },
  { originalId := 16, type := .unit, effects := [(.user 0 [])], source := some ⟨1, 1, 269, 292⟩, kind := (.request (.user 0 []) 0 16) },
  { originalId := 17, type := (.function (.product (.reference (.bound 0)) .integer) .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 301, 311⟩, kind := (.variable 3) },
  { originalId := 18, type := (.reference (.bound 0)), effects := [], source := some ⟨1, 1, 313, 314⟩, kind := (.variable 4) },
  { originalId := 19, type := .integer, effects := [], source := some ⟨1, 1, 316, 318⟩, kind := (.integer (99)) },
  { originalId := 20, type := (.product (.reference (.bound 0)) .integer), effects := [], source := some ⟨1, 1, 312, 319⟩, kind := (.tuple [19, 20]) },
  { originalId := 21, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 301, 319⟩, kind := (.apply 18 21) },
  { originalId := 22, type := .unit, effects := [(.user 0 []), (.cell (.bound 0))], source := some ⟨1, 1, 256, 292⟩, kind := (.bind ⟨6, .unit⟩ 17 22) },
  { originalId := 23, type := .unit, effects := [(.user 0 []), (.cell (.bound 0))], source := some ⟨1, 1, 213, 247⟩, kind := (.bind ⟨7, .unit⟩ 15 23) },
  { originalId := 24, type := (.function .unit .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 157, 202⟩, kind := (.variable 8) },
  { originalId := 25, type := .unit, effects := [], source := some ⟨1, 1, 157, 202⟩, kind := .unit },
  { originalId := 26, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 157, 202⟩, kind := (.apply 25 26) },
  { originalId := 27, type := .unit, effects := [(.user 0 []), (.cell (.bound 0))], source := some ⟨1, 1, 148, 326⟩, kind := (.cleanup ⟨8, (.function .unit .unit [(.cell (.bound 0))])⟩ 27 24) },
  { originalId := 28, type := .unit, effects := [(.user 0 []), (.cell (.bound 0))], source := some ⟨1, 1, 157, 202⟩, kind := (.bind ⟨8, (.function .unit .unit [(.cell (.bound 0))])⟩ 13 28) },
  { originalId := 29, type := .boolean, effects := [], source := some ⟨1, 1, 366, 370⟩, kind := (.variable 9) },
  { originalId := 30, type := .unit, effects := [], source := some ⟨1, 1, 434, 436⟩, kind := .unit },
  { originalId := 31, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 427, 436⟩, kind := (.resume 0 0 .consumed 31) },
  { originalId := 32, type := (.function (.product (.reference (.bound 0)) .integer) .unit [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 453, 463⟩, kind := (.variable 3) },
  { originalId := 33, type := (.reference (.bound 0)), effects := [], source := some ⟨1, 1, 465, 466⟩, kind := (.variable 4) },
  { originalId := 34, type := .integer, effects := [], source := some ⟨1, 1, 468, 470⟩, kind := (.integer (11)) },
  { originalId := 35, type := (.product (.reference (.bound 0)) .integer), effects := [], source := some ⟨1, 1, 464, 471⟩, kind := (.tuple [34, 35]) },
  { originalId := 36, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 453, 471⟩, kind := (.apply 33 36) },
  { originalId := 37, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 411, 436⟩, kind := (.bind ⟨10, .unit⟩ 32 37) },
  { originalId := 38, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 507, 514⟩, kind := (.discard 0 0 .consumed) },
  { originalId := 39, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 360, 524⟩, kind := (.matchCases 30 [⟨(.boolean true), 38⟩, ⟨(.boolean false), 39⟩]) },
  { originalId := 40, type := .unit, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 141, 530⟩, kind := (.handler 0 (.user 0 []) 29 [⟨0, (.binder ⟨9, .boolean⟩), 0, 40⟩]) },
  { originalId := 41, type := (.function (.reference (.bound 0)) .integer [(.cell (.bound 0))]), effects := [], source := some ⟨1, 1, 535, 544⟩, kind := (.variable 11) },
  { originalId := 42, type := (.reference (.bound 0)), effects := [], source := some ⟨1, 1, 545, 546⟩, kind := (.variable 4) },
  { originalId := 43, type := .integer, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 535, 546⟩, kind := (.apply 42 43) },
  { originalId := 44, type := .integer, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 127, 530⟩, kind := (.bind ⟨12, .unit⟩ 41 44) },
  { originalId := 45, type := .integer, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 98, 548⟩, kind := (.bind ⟨3, (.function (.product (.reference (.bound 0)) .integer) .unit [(.cell (.bound 0))])⟩ 7 45) },
  { originalId := 46, type := .integer, effects := [(.cell (.bound 0))], source := some ⟨1, 1, 98, 548⟩, kind := (.bind ⟨11, (.function (.reference (.bound 0)) .integer [(.cell (.bound 0))])⟩ 4 46) },
  { originalId := 47, type := .integer, effects := [], source := some ⟨1, 1, 98, 548⟩, kind := (.resource 0 ⟨4, (.reference (.bound 0))⟩ 1 47) },
  { originalId := 49, type := .integer, effects := [], source := some ⟨1, 1, 69, 548⟩, kind := (.matchCases 0 [⟨.unit, 48⟩]) },
  { originalId := 50, type := (.function .unit .integer []), effects := [], source := some ⟨1, 1, 88, 548⟩, kind := (.function ⟨0, .unit⟩ 49) },
  { originalId := 51, type := (.function .unit .integer []), effects := [], source := some ⟨1, 1, 69, 73⟩, kind := (.variable 13) },
  { originalId := 52, type := .unit, effects := [], source := some ⟨1, 1, 69, 73⟩, kind := .unit },
  { originalId := 53, type := .integer, effects := [], source := some ⟨1, 1, 69, 73⟩, kind := (.apply 51 52) },
  { originalId := 54, type := .integer, effects := [], source := some ⟨1, 1, 0, 549⟩, kind := (.recursiveBind [⟨⟨13, (.function .unit .integer [])⟩, 50⟩] 53) }
  ], 54⟩

def identityManifest : List String := ["binder 0 generated:0", "binder 1 source:0:10", "binder 10 source:0:7", "binder 11 source:0:9", "binder 12 source:0:8", "binder 13 source:0:0", "binder 2 source:0:12", "binder 3 source:0:11", "binder 4 source:0:1", "binder 5 source:0:2", "binder 6 source:0:4", "binder 7 source:0:3", "binder 8 source:0:5", "binder 9 source:0:6", "binder-origin 0 generated FunctionLowering (related (source ⟨1, 1, 88, 548⟩) [⟨1, 1, 69, 548⟩, ⟨1, 1, 69, 87⟩, ⟨1, 1, 76, 87⟩, ⟨1, 1, 98, 548⟩])", "binder-origin 1 generated FunctionLowering (source ⟨1, 1, 98, 548⟩)", "binder-origin 10 generated BindingLowering (source ⟨1, 1, 415, 424⟩)", "binder-origin 11 source ⟨1, 1, 98, 548⟩", "binder-origin 12 generated BindingLowering (source ⟨1, 1, 131, 138⟩)", "binder-origin 13 generated BindingLowering (source ⟨1, 1, 69, 73⟩)", "binder-origin 2 generated FunctionLowering (source ⟨1, 1, 98, 548⟩)", "binder-origin 3 source ⟨1, 1, 98, 548⟩", "binder-origin 4 source ⟨1, 1, 115, 116⟩", "binder-origin 5 generated FunctionLowering (source ⟨1, 1, 160, 167⟩)", "binder-origin 6 generated BindingLowering (source ⟨1, 1, 260, 266⟩)", "binder-origin 7 generated BindingLowering (source ⟨1, 1, 217, 222⟩)", "binder-origin 8 generated BindingLowering (source ⟨1, 1, 157, 202⟩)", "binder-origin 9 generated BindingLowering (source ⟨1, 1, 352, 356⟩)", "cell 0 api=cell:1 handle=4 methods=[11, 3] provider=source:0:0 span=⟨1, 1, 98, 548⟩", "clause operation=0 body=39 source ⟨1, 1, 344, 524⟩", "cleanup 8 scope=⟨1, 1, 148, 326⟩ action=⟨1, 1, 157, 202⟩", "effect 0 source:0:0 []", "match-arm body=37 source ⟨1, 1, 385, 485⟩", "match-arm body=38 source ⟨1, 1, 498, 514⟩", "match-arm body=47 source ⟨1, 1, 88, 548⟩", "node-origin 0 generated TypeChecking (related (source ⟨1, 1, 119, 120⟩) [⟨1, 1, 119, 120⟩])", "node-origin 1 generated TypeChecking (related (source ⟨1, 1, 98, 548⟩) [⟨1, 1, 98, 548⟩])", "node-origin 10 generated TypeChecking (source ⟨1, 1, 190, 196⟩)", "node-origin 11 generated TypeChecking (related (source ⟨1, 1, 179, 196⟩) [⟨1, 1, 179, 189⟩, ⟨1, 1, 190, 196⟩])", "node-origin 12 generated FunctionLowering (related (source ⟨1, 1, 157, 202⟩) [⟨1, 1, 160, 167⟩, ⟨1, 1, 169, 202⟩])", "node-origin 13 generated TypeChecking (related (source ⟨1, 1, 243, 247⟩) [⟨1, 1, 233, 234⟩])", "node-origin 14 source ⟨1, 1, 225, 247⟩", "node-origin 15 generated TypeChecking (related (source ⟨1, 1, 287, 292⟩) [⟨1, 1, 277, 278⟩])", "node-origin 16 source ⟨1, 1, 269, 292⟩", "node-origin 17 source ⟨1, 1, 301, 311⟩", "node-origin 18 source ⟨1, 1, 313, 314⟩", "node-origin 19 source ⟨1, 1, 316, 318⟩", "node-origin 2 generated TypeChecking (source ⟨1, 1, 98, 548⟩)", "node-origin 20 generated TypeChecking (source ⟨1, 1, 312, 319⟩)", "node-origin 21 related (source ⟨1, 1, 301, 319⟩) [⟨1, 1, 301, 311⟩, ⟨1, 1, 312, 319⟩]", "node-origin 22 generated BindingLowering (related (source ⟨1, 1, 256, 292⟩) [⟨1, 1, 269, 292⟩])", "node-origin 23 generated BindingLowering (related (source ⟨1, 1, 213, 247⟩) [⟨1, 1, 225, 247⟩])", "node-origin 24 source ⟨1, 1, 157, 202⟩", "node-origin 25 generated TypeChecking (source ⟨1, 1, 157, 202⟩)", "node-origin 26 related (source ⟨1, 1, 157, 202⟩) [⟨1, 1, 157, 202⟩, ⟨1, 1, 157, 202⟩]", "node-origin 27 source ⟨1, 1, 148, 326⟩", "node-origin 28 generated BindingLowering (related (source ⟨1, 1, 157, 202⟩) [⟨1, 1, 157, 202⟩])", "node-origin 29 source ⟨1, 1, 366, 370⟩", "node-origin 3 generated FunctionLowering (source ⟨1, 1, 98, 548⟩)", "node-origin 30 generated TypeChecking (related (source ⟨1, 1, 434, 436⟩) [⟨1, 1, 427, 436⟩])", "node-origin 31 source ⟨1, 1, 427, 436⟩", "node-origin 32 source ⟨1, 1, 453, 463⟩", "node-origin 33 source ⟨1, 1, 465, 466⟩", "node-origin 34 source ⟨1, 1, 468, 470⟩", "node-origin 35 generated TypeChecking (source ⟨1, 1, 464, 471⟩)", "node-origin 36 generated TypeChecking (related (related (source ⟨1, 1, 453, 471⟩) [⟨1, 1, 453, 463⟩, ⟨1, 1, 464, 471⟩]) [⟨1, 1, 344, 524⟩])", "node-origin 37 generated BindingLowering (related (source ⟨1, 1, 411, 436⟩) [⟨1, 1, 427, 436⟩])", "node-origin 38 generated TypeChecking (related (source ⟨1, 1, 507, 514⟩) [⟨1, 1, 344, 524⟩])", "node-origin 39 source ⟨1, 1, 360, 524⟩", "node-origin 4 generated TypeChecking (related (source ⟨1, 1, 98, 548⟩) [⟨1, 1, 98, 548⟩])", "node-origin 40 source ⟨1, 1, 141, 530⟩", "node-origin 41 source ⟨1, 1, 535, 544⟩", "node-origin 42 generated TypeChecking (source ⟨1, 1, 545, 546⟩)", "node-origin 43 related (source ⟨1, 1, 535, 546⟩) [⟨1, 1, 535, 544⟩, ⟨1, 1, 545, 546⟩]", "node-origin 44 generated BindingLowering (related (source ⟨1, 1, 127, 530⟩) [⟨1, 1, 141, 530⟩])", "node-origin 45 source ⟨1, 1, 98, 548⟩", "node-origin 46 source ⟨1, 1, 98, 548⟩", "node-origin 47 generated TypeChecking (related (source ⟨1, 1, 98, 548⟩) [⟨1, 1, 84, 87⟩])", "node-origin 48 source ⟨1, 1, 69, 548⟩", "node-origin 49 source ⟨1, 1, 69, 548⟩", "node-origin 5 generated TypeChecking (source ⟨1, 1, 98, 548⟩)", "node-origin 50 generated FunctionLowering (related (source ⟨1, 1, 88, 548⟩) [⟨1, 1, 69, 548⟩, ⟨1, 1, 69, 87⟩, ⟨1, 1, 76, 87⟩, ⟨1, 1, 98, 548⟩])", "node-origin 51 source ⟨1, 1, 69, 73⟩", "node-origin 52 generated TypeChecking (related (source ⟨1, 1, 69, 73⟩) [⟨1, 1, 76, 80⟩])", "node-origin 53 related (source ⟨1, 1, 69, 73⟩) [⟨1, 1, 69, 73⟩, ⟨1, 1, 69, 73⟩]", "node-origin 54 generated RecursiveBindingLowering (source ⟨1, 1, 0, 549⟩)", "node-origin 6 generated FunctionLowering (source ⟨1, 1, 98, 548⟩)", "node-origin 7 source ⟨1, 1, 179, 189⟩", "node-origin 8 source ⟨1, 1, 191, 192⟩", "node-origin 9 source ⟨1, 1, 194, 195⟩", "owner 0 ResumeId(0)", "pattern .boolean source ⟨1, 1, 352, 356⟩", "pattern .boolean source ⟨1, 1, 385, 389⟩", "pattern .boolean source ⟨1, 1, 498, 503⟩", "pattern .unit source ⟨1, 1, 93, 95⟩", "resource 0 source:0:0", "signature (.cell (.bound 0)) 0 (.function (.reference (.bound 0)) .integer []) source ⟨0, 0, 55, 59⟩", "signature (.cell (.bound 0)) 1 (.function (.product (.reference (.bound 0)) .integer) .unit []) source ⟨0, 0, 79, 84⟩", "signature (.user 0 []) 0 (.function .boolean .unit []) source ⟨1, 1, 44, 51⟩", "source 0 module=cell:1 path=cell:1", "source 1 module=source:0 path=docs/design/direct-effects/one-shot/fixtures/core-cleanup-restored-clause-suffix.ash"]

example : graph.nodes.length = 55 := rfl
example : checkShape graph = .ok () := rfl
example : (CoreTranslation.translate graph).isOk = true := rfl

end Ash.OneShot.CoreExportedFixture
