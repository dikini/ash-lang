# Name Resolution

Name resolution gives each definition and parameter a stable lexical identity
and connects every occurrence to exactly one such identity. Later phases use
identity, not spelling, to distinguish shadowed binders.

## Type and constructor scope

All nominal type declarations in one file are mutually visible, including in
their own and earlier constructor payloads. Resolution allocates each nominal
identity in source order before resolving any payload type. Two type
declarations cannot share a spelling.

Every constructor receives a stable identity under its owning nominal type.
Constructors form one file-wide term namespace and must have distinct spellings
across all declarations. Constructor names do not conflict with ordinary
lowercase term names because the lexical classes are separate. A type
occurrence must name a file type, an in-scope type parameter, or one of `Int`,
`Bool`, and `Unit`; an uppercase term or pattern occurrence must name a
constructor.

A parameterized nominal declaration allocates distinct type-parameter
identities in source order. Those parameters are visible throughout that
declaration's constructor payloads and nowhere else. A declaration cannot
repeat a parameter spelling. A parameter shadows a same-spelled nominal type
inside its declaration. Because every parameter has kind `Type`, applying it
as a type constructor is rejected with `resolve.type-kind`. A nominal type
application must supply exactly the declaration's arity; bare and partially
applied nominal constructors are rejected with
`resolve.type-argument-count`.

## Global scope

All global function names in one file form a simultaneous scope. Each global
body can refer to itself, an earlier global, or a later global. The file result
uses the same complete global scope.

Each global interface implicitly binds its free uppercase type names in
first-occurrence order. Those type parameters scope over that global's header,
patterns, and body. They do not enter another global interface or the file
result. Thus `identity : A -> A` declares one rank-1 type parameter without
adding source type-parameter punctuation to the function name.

Two globals cannot have the same name. In an equational definition, the name in
the external interface must equal the name at the equation head.

## Local scope

A block resolves its bindings from left to right. A local initializer uses the
scope before its binder, so the binding is nonrecursive. The binder is visible
in later bindings and in the block result. A local may shadow an earlier local
or global. The stable identities keep the two definitions distinct.

A `let rec ... and ...` group allocates every member identity before resolving
any initializer. Every initializer therefore sees all members, and all members
remain visible in the following block remainder. A member may shadow an outer
binder, but two members of one group cannot have the same spelling.

A function parameter is visible only in its body and may shadow an outer
binder. Parentheses and other grouping syntax do not introduce a scope.

Pattern binders enter scope together after the complete pattern resolves. A
spelling cannot occur twice in one pattern. Match-arm binders are visible only
in that arm body. Equation-pattern binders are visible only in their clause
body. A local `let` pattern contributes its binders to the later block
remainder, not to its initializer.

Forward references exist only among file globals and members of one explicit
local recursive group. An ordinary `let` does not see itself or a later local
declaration.

The executable test `resolution_global_recursive_scope_example_is_executable`
checks mutual visibility across the two global presentations:

```ash
first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let retain : Unit -> Int = fn(value) {
        first value
    }
    42
}

first ()
```

## Unresolved names

Every occurrence must resolve. The executable test
`resolution_unknown_name_example_has_its_documented_reason` checks that this
file is rejected with `resolve.unknown-name`:

```ash
missing 1
```

A diagnostic may suggest an in-scope name only when its spelling justifies that
suggestion. Suggestions do not change resolution.
