# DN-0047: ECS and Open Heterogeneous Stores

- ID: `DN-0047`
- Status: exploring
- Related: [DN-0018: Runtime-Established Static Evidence](DN-0018-runtime-established-static-evidence.md),
  [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md),
  [DN-0035: Region Memory Management and Verified Providers](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0038: Resource Properties and Mutable Variable Usage](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [DN-0042: Native Interaction and Efficient Data](DN-0042-native-interaction-and-efficient-data.md),
  [DN-0045: Native Compilation and Interactive Execution](DN-0045-native-compilation-and-interactive-execution.md)

> This design note is informative. ECS supplies a stress case for Ash design;
> the note defines no current semantics, accepts no implementation, and
> authorizes no compiler or library development. Costs are theoretical. No ECS
> implementation or performance measurement is part of this discussion.

## Question

Can Ash express typed component stores, composable queries and generic systems
with ordinary libraries? Where would an open heterogeneous registry require
additional compiler support, and can that support later share existential
packaging and type-equality facilities rather than duplicate them?

Entity component systems are a vehicle for finding useful general mechanisms.
UI applications motivated the discussion, but the particular application is
irrelevant to the comparison. The designs should also inform other programs
that group values by type, compose typed operations and retain immutable state.

The intended outcome is a basis for future design and development. It is not a
selection of an ECS framework, storage layout, backend or development schedule.

## Context

### Current Ash

The [current specification](../../spec/README.md) supplies nominal data,
structural tuples, rank-1 generic functions, fixed higher-kinded parameters,
method-local interface parameters and multi-parameter interfaces. Implementations
are selected statically and evidence lowers to ordinary callable code. There
is no runtime interface-implementation registry.

[Type equality](../../spec/static-semantics.md) preserves nominal declaration
identity and compares structural types and type applications structurally.
Distinct `newtype` declarations remain distinct even when their representations
match. Their checked conversions erase, so runtime representation alone cannot
identify the nominal type.

[Implementation admission](../../spec/static-semantics.md#implementations)
rejects overlap and requires non-ground prerequisites to decrease structurally.
A determination edge does not introduce an associated type, type projection,
equality witness or fallback instance search. Ordinary source fields cannot
store polymorphic schemes, and ordinary recursion is not polymorphic recursion.

Current Ash has no source existential pack/unpack, general type reflection,
authenticated type keys or checked recovery of an arbitrary hidden value.
Effect execution retains type instantiation for exact effect matching; that
metadata is not a source type-reflection API.

[Scoped cells](../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
store integers; native buffers expose checked bytes. These facilities do not
establish arbitrary typed mutable component arrays. Ordinary immutable values
are duplicable subject to inferred resource dependencies. Dependency checking
follows retained handles, captures, selected methods and operation metadata,
even when the exposed value type hides the acquisition identity.

[Ordinary construction](../../spec/dynamic-semantics.md#tuples-constructors-and-matches)
allocates tuples and ADT values in the semantic heap. This does not promise a
contiguous layout, fixed-width integers, specialization, stack placement or a
particular reclamation policy. The efficient-data and backend questions in
DN-0042 and DN-0045 remain exploratory.

### Logical model and physical representation

An entity has an identifier. A component type describes one kind of value; a
store associates entity identifiers with values of that type. A world groups
stores. A query selects entities and returns typed rows; a system reads those
rows and produces updates or performs separately declared effects.

Three choices must remain separate:

- The component schema may be a statically described product or an open
  collection of stores hidden behind typed access.
- Entity membership is runtime data. A fixed component schema still permits
  entities to gain and lose components.
- Storage may use lists, trees, sparse sets, columns or archetypes. A logical
  heterogeneous product does not require a physical list.

HList is an example of a type-indexed encoding. It is not a requirement that
all heterogeneous structures have linked-list storage. Likewise, an open
registry of stores does not require one individually boxed entry per entity.

## Constraints

- Recover values at their original types without relying on serialization or
  a closed sum enumerating all possible payload types.
- Keep library expressibility, new semantic requirements and possible compiler
  optimizations distinct.
- Preserve nominal type equality through erased representations and import
  aliases. Equal hashes or names alone must not authorize recovery.
- Preserve stored resource dependencies through every packaging and lookup
  operation. Hiding a type grants no lifetime or ownership authority.
- Keep query result types and required interface evidence explicit. Runtime
  lookup must not manufacture implementation evidence for an unknown type.
- Compare source and compilation costs as well as runtime costs. Do not assume
  specialization eliminates abstraction overhead.
- Use ECS to test general facilities. Do not introduce privileged ECS syntax,
  entity identity semantics or query planning without separate evidence.
- Limit this exploration to statically linked, sequential programs and
  theoretical costs. Persistence across builds, serialization, dynamic loading,
  concurrent scheduling and performance measurements are outside its scope.

## Candidate directions

### Typed immutable stores and generic systems

A world can be a nominal product of typed stores, for example a position store
and a velocity store. `Store<C>` is a library abstraction over an immutable
entity map, not a current builtin collection. Adding or removing a component
changes membership in a store; it does not change the world's type.

An access interface can abstract over the world representation. The following
signature sketch uses current interface features; the store representation and
world implementations are deliberately unspecified.

```ash
interface StoreAccess<W, C> {
    component_store : W -> Store<C>
    replace_store : (W, Store<C>) -> W
}
```

Both parameters occur in every method type. No determination edge is needed:
one world normally has several component types, so `W -> C` would describe the
wrong relationship. A generic system can require `StoreAccess<W, Position>`
and `StoreAccess<W, Velocity>` while remaining independent of the concrete
world layout.

Queries can similarly describe their result types explicitly. One ordinary
functional encoding is a `Query<W, R>` containing a monomorphic function from
`W` to entity-tagged rows of `R`. Joining queries for `A` and `B` can return
rows of `(A, B)` by matching entity identifiers. These are library operations;
the signature does not supply an efficient join algorithm or storage layout.
Queries and systems can compose as ordinary functions when their world and
result types agree. Effects remain explicit when a system performs them.

This direction avoids runtime type recovery. It gives static rejection of
missing access requirements and supports persistent snapshots. Its weaknesses
are explicit world schemas, access evidence and update allocation. Evidence
may introduce calls until an optimizer removes them. Replacing a nested world
field may rebuild an enclosing path, and repeated small component updates may
create many persistent nodes. Batched store replacement is worth comparing
with one world replacement per entity.

An effect-based access API is another candidate: a parameterized effect family
can describe reads and writes of `C`. Expressing that API does not provide
arbitrary typed mutable storage, uniqueness or borrowing. Its interpretation
and storage authority would need their own design. The immutable direction
therefore supplies a useful comparison without depending on those additions.

### Static heterogeneous schemas

Nominal products can describe heterogeneous collections today. A literal
HList-style encoding uses `HNil` and `HCons<H, T>`. Explicit path types avoid
overlapping implementations that try to match the head type and otherwise
search the tail.

The following fragment is a current-language encoding. It gives access by
path; it does not claim an automatically inferred type-level search.

```ash
type HNil = HNil
type HCons<H, T> = HCons(H, T)
type Here = Here
type Next<I> = Next(I)

interface At<L, I, A> {
    get_at : (L, I) -> A
    set_at : (L, I, A) -> L
}

impl<H, T> At<HCons<H, T>, Here, H> {
    get_at (HCons(head, tail), Here) = head
    set_at (HCons(head, tail), Here, value) = HCons(value, tail)
}

impl<H, T, I, A> At<HCons<H, T>, Next<I>, A> where At<T, I, A> {
    get_at (HCons(head, tail), Next(index)) = get_at(tail, index)
    set_at (HCons(head, tail), Next(index), value) = {
        HCons(head, set_at(tail, index, value))
    }
}
```

The recursive prerequisite decreases in the list and path arguments. Ordinary
recursive interface evidence thus supplies traversal across different tail
types without requiring ordinary polymorphic recursion.

Adding the edge `(L, I) -> A` to this exact encoding is not admitted. In the
recursive head, `A` occurs only in the dependent position and is absent from
the determinant arguments. The determination-coverage rule rejects it; the
prerequisite cannot act as an associated-type computation that repairs that
coverage. Keeping all three parameters in the selection key avoids that claim.

The same logical relationship could use a tree, nested tuple or generated
product. A literal `HCons` chain has access depth `d` and rebuilds a path of
length `d` on replacement. A balanced representation can change path depth.
Flattening or eliminating a chosen representation is a separate compiler
optimization, not a consequence of the word HList.

### Current safe keys with a closed payload

Current Ash can couple a tag to a typed projector when the payload universe is
explicit. This fragment illustrates the shape; key construction would be
hidden behind an opaque module boundary in a library.

```ash
type Option<A> = None
    | Some(A)
type Position = Position(Int)
type Velocity = Velocity(Int)
type Payload = PositionPayload(Position)
    | VelocityPayload(Velocity)
type ClosedKey<C> = ClosedKey(Int, Payload -> Option<C>)
```

A position key carries a function that matches `PositionPayload` and returns
`Option<Position>`. Registry search can compare the integer tag before invoking
the projector. A tag collision may break lookup behavior, but the typed
projector cannot reinterpret a velocity value as a position value.

This is safe projection from a closed sum, not evidence that two arbitrary
types are equal. Adding a new payload type requires changing the sum. A generic
tagged representation with encoders and decoders could remove that enumeration,
but would reconstruct values and introduce conversion contracts. It does not
satisfy the direct-value registry explored below.

### Open registry with authenticated type keys

The candidate extension introduces an opaque `TypeKey<A>` and an opaque
`Packed` value. Keys carry stable symbols for complete types; boxes retain
their original typed payloads. The proposed API shapes are:

```text
symbol<A> : TypeKey<A> -> Symbol
pack<A> : (TypeKey<A>, A) -> Packed
project<A> : (TypeKey<A>, Packed) -> Option<A>

insert<A> : (Registry, TypeKey<A>, A) -> Registry
lookup<A> : (Registry, TypeKey<A>) -> Option<A>
```

These are not current builtin declarations. `Registry` can remain library code
over entries containing a symbol and a box. Insertion requires the same `A`
for the key and value. Lookup's result type comes from the key. A registry of
component stores uses keys for `Store<C>` and stores whole typed stores, keeping
boxing and registry search outside the per-entity processing loop.

Let `id(A)` denote the identity assigned to `A`. Sound recovery requires
`id(A) = id(B)` to imply Ash type equality `A ≡ B`. Reliable lookup also
requires equal types to receive equal identities. Nominal declarations,
complete arguments and structural type information participate, including
function computation types and effect rows. Representation equality is
insufficient. The key for one `newtype` must differ from another's even if
both erase to `Int`.

The initial stability requirement is identity throughout one linked program,
across aliases, modules and repeated uses. Current
[module identity](../../spec/name-resolution.md#module-paths-and-identity)
is stable within a compilation. Persistence across builds is not implied.
Symbols may lower to interned tokens. Hashes can accelerate search, but hash
collisions must be resolved by exact identity before recovery.

This candidate uses stable type identity, rather than GHC-style object identity.
GHC's [`Type.Reflection`](https://hackage-content.haskell.org/package/base-4.20.0.0/docs/Type-Reflection.html)
provides the closer comparison: indexed representations and checked type
equality. A type-level string, including one reified through
[`KnownSymbol`](https://downloads.haskell.org/~ghc/9.8.1/docs/libraries/base-4.19.0.0-b67a/GHC-TypeLits.html),
would require an authenticated injective relationship to component types before
string equality could justify recovery.

For the smallest first increment, the compiler can issue keys for closed
monotypes whose identities have module scope. Generic functions take explicit
keys. No universal implicit key provider is required. Local nominal and
resource-indexed keys remain a separate scope decision.

The proposed rules below use `GAMMA` for the typing environment and `epsilon`
for evaluation effects. `key[A]` is notation for compiler issuance, not current
source syntax. An admissible type initially means a closed kind-`Type` monotype
with module-scoped identities. Packing and projection add no effects beyond
evaluating their operands; storing a function does not invoke it.

```sequent
family heterogeneous-storage:
  T-Key :=
    A is an admissible closed monotype of kind Type
    id(A) is authenticated by the compiler
    ===>
    GAMMA |- key[A] ⇒ TypeKey<A> ! {}

  T-Pack :=
    GAMMA |- key ⇒ TypeKey<A> ! epsilon_key
    GAMMA |- value ⇐ A ! epsilon_value
    ===>
    GAMMA |- pack(key, value) ⇒ Packed ! (epsilon_key union epsilon_value)

  T-Project :=
    GAMMA |- key ⇒ TypeKey<A> ! epsilon_key
    GAMMA |- boxed ⇒ Packed ! epsilon_boxed
    ===>
    GAMMA |- project(key, boxed) ⇒ Option<A> ! (epsilon_key union epsilon_boxed)
```

Conceptually, `Packed` contains `exists B. (TypeKey<B>, B)`. Projection compares
the stored key with the requested key. Failure returns `None`; successful exact
comparison establishes `A ≡ B` internally and returns the stored value at `A`.
General source existentials and public equality witnesses need not be exposed
for this restricted operation.

Projection checks the key retained inside the box even if an index already
found a matching external symbol. Incorrect source-level associations between
symbols and boxes must produce failed lookup rather than authorize a cast.
A Boolean symbol comparison in current source code does not refine rigid type
variables into equality. That checked recovery bridge is new compiler support.

The compiler boundary is narrower than a builtin ECS or runtime implementation
registry. The proposed facilities require the following contracts:

| Boundary | Additional support |
| --- | --- |
| Key issuance | Authenticate complete type identities and reject construction from arbitrary source symbols. |
| Packing | Retain the original typed value and its matching key in one opaque package. |
| Projection | Recover a value only after exact key equality; return ordinary typed failure otherwise. |
| Analysis | Propagate actual stored dependencies and relevant callable relationships through packaging and recovery. |
| Core validation | Independently authenticate key origins, type arguments, payload relationships and dependency behavior after transforms. |

The ordinary type checker can enforce the shared `A` in the proposed signatures;
it cannot supply the trusted dynamic recovery implementation by source interface
code alone. Type keys remain invariant in their index: there is no conversion
from `TypeKey<A>` to `TypeKey<B>` based on matching representations. The
[existing validation boundary](../../spec/elaboration.md#validation-boundary)
is the precedent for checking new operations independently rather than trusting
a construction API or an elaborator assertion.

### Generic key composition

Generic code should be able to derive `TypeKey<Store<A>>` from `TypeKey<A>`.
The additional input is authenticated identity for the `Store` constructor.
If `Store` has kind `Type -> Type`, bare `TypeKey<Store>` is ill-kinded for
`TypeKey<A : Type>`; a constructor witness can represent that input separately.

One proposed unary application API is:

```text
store_constructor_key : ConstructorKey<Store>
apply_key<F: Type -> Type, A> :
    (ConstructorKey<F>, TypeKey<A>) -> TypeKey<F<A>>
```

`ConstructorKey` and `apply_key` are proposed authenticated facilities. The
following interface uses current higher-kinded and method-local parameters
to organize them; it is not executable against current Ash without those
facilities.

```ash
interface KeyLift<F: Type -> Type> {
    lift_key<A> : TypeKey<A> -> TypeKey<F<A>>
}

impl KeyLift<Store> {
    lift_key element_key = {
        apply_key(store_constructor_key, element_key)
    }
}

store_key<A> : TypeKey<A> -> TypeKey<Store<A>>
store_key element_key = lift_key(element_key)
```

The implementation can reside in the module defining `Store`. Existing
[evidence lowering](../../spec/elaboration.md#interface-evidence-lowering)
already admits the method's polymorphism in authenticated generated evidence
positions. It need not become an ordinary stored polymorphic function.

The key-application rule below permits a generic `A`: the argument key supplies
its runtime identity. `F` has kind `Type -> Type`, `A` has kind `Type`, and both
operand witnesses must retain authenticated origins.

```sequent
T-Key-Application :=
  GAMMA |- constructor ⇒ ConstructorKey<F> ! epsilon_constructor
  GAMMA |- argument ⇒ TypeKey<A> ! epsilon_argument
  ===>
  GAMMA |- apply_key(constructor, argument) ⇒ TypeKey<F<A>> ! (epsilon_constructor union epsilon_argument)
```

Conceptually the descriptor is `Application(descriptor(F), descriptor(A))`.
Direct compiler issuance for `Store<Position>` and composition from its two
witnesses must produce equal keys. One canonical identity mechanism must serve
both routes. Constructing a hash and relabeling it as `TypeKey<F<A>>` would not
establish that relationship.

A first compiler interface could generate a `store_key` operation for each
eligible constructor, all lowering to one internal application mechanism.
Exposing the generalized constructor-witness API is a separate surface choice.
The unary sketch does not assume kind polymorphism or define all higher-arity,
structural and effect-row descriptor operations.

Current interfaces can also derive keys through explicit prerequisites. This
fragment is conditional on the proposed key facilities:

```ash
interface Keyed<A> {
    type_key : Unit -> TypeKey<A>
}

impl<A> Keyed<Store<A>> where Keyed<A> {
    type_key () = {
        let element_key : TypeKey<A> = type_key ()
        store_key(element_key)
    }
}
```

The prerequisite decreases from `Store<A>` to `A`, and the head contains the
nominal `Store` constructor. This needs no new interface-selection semantics.
Automatically generating such implementations, or introducing a universal
compiler-supplied key requirement, would be additional features. Explicit
key parameters remain the smallest generic calling convention.

### Packaging, dependencies and future existentials

The proposed separation is type identity, packaging and library indexing.
These responsibilities should not become independent registry-specific
reflection or ownership systems.

With suitable future existential types, an opaque library wrapper could
implement `Packed` as `exists A. (TypeKey<A>, A)`. Its public packing and
projection signatures could remain unchanged. Opening the package introduces
an abstract `B` shared by its key and payload. It does not prove `B ≡ A` for
the type requested by the caller.

A future shared equality API might have the illustrative shape below.
`TypeEq<A, B>` would require unforgeable introduction and an elimination rule
that permits substitution of equal types. An ordinary phantom ADT called
`TypeEq` would not provide that rule.

```text
same_type<A, B> :
    (TypeKey<A>, TypeKey<B>) -> Option<TypeEq<A, B>>
```

Projection could then be library code: open the package, compare the keys,
return `None` on failure, and use successful equality evidence to return
`Some` of the recovered value. Existentials alone do not eliminate the checked
equality requirement. DN-0018 explores the broader introduction and preservation
of runtime-established evidence; it does not accept that mechanism.

| Initial facility | Possible future implementation |
| --- | --- |
| Authenticated type-key issuance and composition | Retain one shared type-identity service. |
| Restricted opaque packing | Use general existential introduction behind the wrapper. |
| Restricted checked projection | Use existential opening and shared equality elimination. |
| Registry indexing and query preparation | Remain library code. |

Keep restricted compiler handling behind a small lowering boundary so generic
existential operations can replace it. Do not implement a general existential
calculus in advance of its design. The compatibility claim is conditional on
future opening and equality rules, not a guarantee of unchanged Core nodes or
source syntax.

Packing must retain the actual payload's resource dependencies, including
captures whose types hide an owner. Projection must preserve dependencies of
the recovered value. A conservative implementation can retain the dependencies
of all candidate entries; finer entry tracking may accept more programs.
Replacement or deletion must not assume dependencies disappear without a
justified analysis. Returning a box, registry or recovered closure across a
closing resource remains checked by the existing lifetime contract.

Keys for local nominals and acquisition identities need an explicit descriptor
scope and escape policy. Refusing those keys initially bounds that question;
general existential packaging may later choose a broader rule. Type equality
still grants no ownership transfer or longer resource lifetime. Recovered
functions remain monomorphic, and lookup supplies no runtime interface evidence.

### Query and storage alternatives

Typed sparse stores can drive a query from a small candidate entity set and
look up the other requested components. Sorted entity sequences can support
merge joins. Archetypes can group entities by component membership and scan
matching groups, while charging structural changes for migration between groups.
These are alternative algorithms and representations, not current Ash features
or a consequence of choosing an open registry.

An open registry can resolve each requested `Store<C>` once while preparing a
query, then run an ordinary typed join. It need not compare type symbols for
every entity. A static world can similarly extract stores once instead of
traversing its product on each row. Query caching requires an invalidation
contract when membership or storage changes; no cache behavior is selected here.

## Theoretical performance

Let `k` be the number of registered stores, `d` an access-path depth, `q` the
number of queried component types, and `m` the number of candidate entities.
The following costs are conditional algorithmic models, not measured Ash costs.

| Operation or choice | Potential cost and governing assumption |
| --- | --- |
| Literal product/HList access | `O(d)` traversal; persistent replacement rebuilds `O(d)` path nodes. |
| Linked registry search | `O(k)` key comparisons for one requested store. |
| Balanced registry tree | `O(log k)` search and update paths, given a suitable ordering contract. |
| Hash registry | Expected constant-time search under hashing assumptions; collisions, growth and worst cases remain. |
| Key composition | Descriptor construction or interning; combining interned child tokens can avoid rescanning a complete type. |
| Sparse-store query | Candidate iteration plus lookups in the other stores; `O(m q)` assumes constant-time lookups. |
| Two sorted stores | Merge join can take `O(n_a + n_b)` with suitable identifier comparison and iteration. |
| Archetype scan | Group matching and row iteration; structural membership changes may copy or migrate data. |
| Immutable entity updates | Persistent paths and result allocation; batching can share work but does not imply in-place mutation. |

Current mathematical integers do not establish fixed-width identifier or hash
costs. A pointer-shaped semantic value does not establish contiguous component
storage. Cache locality, boxing layout, dictionary calls and vectorization need
backend and collection contracts before they support concrete performance claims.

An open registry may add per-store descriptor storage, boxing allocation and
checked projection. A successful projection recovers the original value without
serialization. Immutable update can share unchanged values. The abstract box
does not require a separate allocation if a later layout can preserve its
contract by another representation.

Generic key arguments and interface evidence may add calls or retained values.
Specialization can potentially precompute concrete keys and remove access
adapters, but that is an optimization opportunity rather than a language
guarantee. A future native backend must preserve nominal identity even when
newtype conversions and value representations erase.

Compilation costs include type/constraint processing, recursive evidence
construction, descriptor construction and independent validation. A large static
schema can move work from runtime search into compilation without making it
free. Explicit keys avoid a universal reification constraint on every generic
call; automatic derivation changes that tradeoff.

## Evidence and experiments

The present evidence is semantic comparison and theoretical cost analysis from
the discussion. It establishes candidate boundaries and questions, not measured
performance or a completed implementation. Illustrative fragments that depend
on proposed facilities are not current executable Ash examples.

Documentation validation with the existing Ash executable checked the current
HList fragment by reading and replacing two integer fields, yielding `40`.
The closed-key fragment, completed with a position projector, yielded `42`.
Adding `(L, I) -> A` to the HList interface was rejected with
`impl.determination-coverage`, as required by the specification. These checks
validate source examples; they implement no ECS and measure no performance.

Future work can use the following discriminating cases. Source checking of
current-language fragments is documentation validation, not an ECS benchmark.

| Case | Required observation | Failure or contrary evidence |
| --- | --- | --- |
| Static world and query composition | Generic systems preserve world and row types; dynamic membership remains ordinary data. | Schema changes require runtime recovery, or query composition loses its result type. |
| Heterogeneous paths | Explicit paths select and replace the intended field with decreasing evidence. | Overlap, accidental determination coverage or ordinary polymorphic recursion is required. |
| Open extension | A new component module adds a store without editing a closed payload sum or registry traversal. | Payload enumeration or serialization remains necessary. |
| Nominal identity | Equal representations with distinct nominal identities have distinct keys. | Erasure or spelling collapses different types. |
| Aliases and composition | Aliased and directly issued/composed keys for one type compare equal. | Different routes create incompatible identity spaces. |
| Forgery and collisions | Incorrect symbols or hash collisions cannot recover a mismatched payload. | An index result or unauthenticated tag authorizes a cast. |
| Generic calls | Explicit keys permit composition without implicit universal evidence. | A generic body depends on unavailable erased metadata. |
| Resource captures | Packaging and lookup preserve actual stored dependencies. | A hidden closure or operation identity escapes its owner. |
| Existential migration | General packaging can replace the restricted wrapper while retaining shared equality. | A second type-identity, equality or ownership mechanism is necessary. |
| Compiler transformations | Independent validation rejects substituted keys, payloads or stale dependencies. | Construction APIs or backend metadata become the only authority. |

Any later disposable prototype must name the question and candidate comparison,
separate semantic checks from performance measurements, and record unsupported
cases. Retain design evidence only if the relevant identities, typing,
dependencies and validation obligations survive abstraction. Discard shortcuts
that assume universal casts, resource-free payloads without enforcing that
restriction, or a closed payload universe. Experimental code is not product
implementation; production changes need a semantic proposal and authorized task.

The [HList paper](https://okmij.org/ftp/Haskell/HList-ext.pdf) supplies a reference
for statically typed heterogeneous products. GHC's Type.Reflection supplies a
reference for indexed type representations, application structure and checked
equality. Neither establishes that all of those languages' mechanisms are
available or required in Ash.

## Open questions

- Which ECS cases actually need an open registry rather than a typed immutable
  world or static heterogeneous schema?
- What query descriptions and generic system requirements remain usable without
  associated types, overlapping instances or stored polymorphic schemes?
- Should the first key API expose constructor witnesses, generate per-constructor
  lifting functions, or use an explicitly constrained reification interface?
- Which monotypes are initially keyable, and how are structural types, effect
  rows, partial applications and local identities added without separate identity
  mechanisms?
- Can descriptor application and exact comparison remain small while preserving
  canonical identity and compiler resource budgets?
- How precisely must stored dependencies be tracked through opaque registries
  for useful resource-bearing programs to be admitted?
- What existential opening and equality-elimination rules allow the restricted
  packaging implementation to become library code?
- Which collection, mutation and representation contracts are needed before
  sparse sets, archetypes or contiguous columns offer an Ash-specific benefit?
- When later measurement is authorized, which workloads distinguish access,
  joining, structural changes, persistence, allocation and compilation costs?
