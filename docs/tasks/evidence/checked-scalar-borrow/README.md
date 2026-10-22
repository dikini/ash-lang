# Static scalar checked Borrow

The first genuine source fixture prepares Read<H,R> as a nonconsuming opaque
Current Borrow with one guarded operand, scalar result, exact host/formals and
Callee plus automatic assumptions. Its explicit checked-profile resolution then
rejects Read with ForeignContract / InvalidLibrary at the existing role gate.
The default profile also rejects. The test-first command passes two controls
and fails the expected-positive binding control; no connected source/summary/
Core positive is claimed.

[Test-first receipts](test-first/scalar-borrow-binding.receipt.json) retain the
raw result and equal before/after 585-input maps, compact sorted-key JSON SHA-256
`7dec4a35db7ef3c1e68bbba228b081a99aa9ea1e17001f1d5baa0aee5fae502d`.
No product code changed before this red. Runtime/native/image execution, byte/
window/Access capabilities, owner dependencies, general helper transport, whole
F3 and F-core remain excluded.
