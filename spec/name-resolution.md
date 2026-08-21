# Name Resolution

Name resolution gives each definition and parameter a stable lexical identity
and connects every occurrence to exactly one such identity. Later phases use
identity, not spelling, to distinguish shadowed binders.

## Global scope

Global definitions are sequential and nonrecursive. A definition can refer to
earlier globals. Its own name and the names of later globals are not in scope in
its body. The new global enters scope only after its complete definition.

Two globals cannot have the same name. In an equational definition, the name in
the external interface must equal the name at the equation head.

## Local scope

A block resolves its bindings from left to right. A local initializer uses the
scope before its binder, so the binding is nonrecursive. The binder is visible
in later bindings and in the block result. A local may shadow an earlier local
or global. The stable identities keep the two definitions distinct.

A function parameter is visible only in its body and may shadow an outer
binder. Parentheses and other grouping syntax do not introduce a scope.

## Unresolved names

Every occurrence must resolve. The executable test
`resolution_unknown_name_example_has_its_documented_reason` checks that this
file is rejected with `resolve.unknown-name`:

```ash
missing 1
```

A diagnostic may suggest an in-scope name only when its spelling justifies that
suggestion. Suggestions do not change resolution.
