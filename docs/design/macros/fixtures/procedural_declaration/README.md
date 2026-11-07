# Supplemental procedural declaration fixture

This focused source graph supplements I16 in the
[integration corpus](../README.md). It uses accepted but unimplemented
[CP-0034](../../../../proposals/CP-0034-top-level-declaration-macros.md)
syntax. Its existence does not claim a passing macro test.

`main.ash` captures one complete declaration. Its checked Ash transformer
reads that fragment, returns its structured syntax through the existing host,
and the public driver admits and checks the generated declaration. It must
return `42 : Int`, as does the handwritten `control.ash`. This is the early
procedural declaration gate for S4.

`rejected.ash` invokes the separate authored rejection. It must report
`declaration rejected` with the invocation origin and publish no generated
`answer`. Both definitions are admitted even though each caller invokes only
one.

These cases do not replace I16's indexed derive, real consumer after host
teardown, foreign-handle mutation, independent Core validation or supported
build/image checks. Those remain connected acceptance at V3 and the final
gates.
