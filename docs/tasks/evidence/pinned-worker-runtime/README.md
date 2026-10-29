# Pinned worker connected runtime evidence

These are focused development receipts from the source snapshot whose
[before](before.sha256) and [after](after.sha256) manifests both hash to
`9cfdcad9724e2781b49fb9ca5de40119eea0e36b1dde0c9d681d1047433fc62a`.
They precede final delivery assembly and warning/format cleanup. They are not
a full workspace gate for this checkout or proof that every current input equals
that snapshot. The final assembled candidate requires its own fresh gate.

The [public copied-byte test](public.log) passed end to end (1/1).
The [focused diagnostic](focus.log) reconstructs the processing cut and genuine
End route. The [64 KiB regression](stack.log), [tainted carry refusal](tainted.log),
[escape and suffix refusals](escape.log), and [End controls](end.log) passed.
The [build output](build.log) records that snapshot's compilation.

The original native process exited successfully, with three tests passed;
[its session receipt](native-session-34390.json) records the exact immutable
binary and filter. The [native log](native.log) contains interleaved diagnostics
from a briefly duplicated process that was stopped. It is not a clean separate
per-test receipt. The final fresh workspace gate must supply current results.

Two earlier snapshots supply distinct required runtime controls:
[Message-copy provider failure](provider.log) at manifest
`1631acbc80277daa8a8e9fc68aec27190a8a7c4129164b62ec22c623e446187f`
and [capacity-one feedback with actual producing cleanup](feedback.log) at
`5661a9d5d1a5f2c4f6b0dbad43c62923e895fcca8efaf035df6664b7b4551b73`.
The first retains/restores the reserved FIFO head on selected host allocator
work exhaustion. The second checks ordinary returns cannot authorize settlement;
it does not establish bidirectional owner settlement. These logs are scoped
observations, not equality receipts for the later candidate.

The separately retained [modeled source gate](../pinned-one-way-proof/README.md)
and [trusted implementation mapping](../../../design/retained-control/one-way-completion-correspondence.md)
have separate scopes. None of these receipts alone closes N2 or M4.
