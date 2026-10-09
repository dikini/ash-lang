# DN-0040: Floating-Point Semantics and Representation

- ID: `DN-0040`
- Status: exploring
- Related: [DN-0019](DN-0019-primitive-feature-composition.md),
  [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [AD-0004](../decisions/AD-0004-small-step-semantic-method.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note plans a floating-point language addition intended to become
> normative through the proposal and implementation workflow. It defines no current
> Float type or arithmetic rules, accepts no representation architecture,
> and authorizes no implementation. It does not change DN-0036's scope.

## Question

What minimal floating-point value, syntax, operations and representation
contracts should Ash specify to support real foreign libraries and typed
data-processing pipelines? How can those semantics remain consistent across
source checking, Core validation, interpretation, constant folding and later
backends while avoiding unnecessary boxing and type-related metadata?

## Context

Current [static semantics](../../spec/static-semantics.md) provide `Int`,
`Bool` and `Unit` as primitive scalar types. The
[dynamic semantics](../../spec/dynamic-semantics.md) give `Int` arbitrary
precision. There is no normative floating-point type, implicit numerical
coercion regime or general host ABI guarantee.

[DN-0019](DN-0019-primitive-feature-composition.md) retains a Float composition
experiment on a separate branch. It demonstrates cross-stage integration
pressure and maintenance techniques; it explicitly accepts neither Float
semantics nor a feature-composition architecture. Transfer its locality and
validation questions, not its provisional arithmetic or spelling.

The copying values recorded in the provider
[execution record](provider-experiments/execution.md) show experimental
`Bytes`/`String` integration and foreign conversion pressure. They do not add
Float to current Ash. [DN-0041](DN-0041-typed-serialization-and-data-pipelines.md)
needs numerical contracts across JSON, YAML, CSV, TOML and BSON, including
processing rather than merely retaining number text.

BSON defines both a 64-bit binary floating-point scalar and a separate
128-bit decimal scalar. Those representations are distinct.
[BSON specification](https://bsonspec.org/spec.html)

## Constraints

- Add normative semantics through a change proposal, implementation and
  specification updates together. A design note or host `f64` field cannot
  establish the language contract.
- Preserve mathematical `Int` semantics. Foreign integer widths and numerical
  conversions must not silently introduce wrapping or precision loss.
- Preserve explicit typed Core, causal origins and independent validation.
  A scalar addition must compose with both Pure and Effect execution.
- Keep numerical values distinct from an Ash memory ABI, foreign ABI types,
  serialized byte order and the interpreter's physical value representation.
- Keep the first library API small. Full mathematics, vectors, SIMD, decimal
  arithmetic, configurable rounding environments and numerical optimization
  libraries are outside the first addition.
- Do not make all parsed format numbers floats. Integer, binary floating point
  and exact decimal/lexical representations answer different questions.

## Candidate directions

### Scalar scope

| Candidate | Benefit | Cost or limitation |
| --- | --- | --- |
| `Float64` first | One specified binary64 value and operation family; suitable for common host-double and format use. | Narrower host float contracts still need explicit conversion; decimal exactness remains separate. |
| `Float32` and `Float64` together | Direct width choices for more foreign interfaces and storage. | More literal, conversion, operation and cross-width rounding contracts in the first delivery. |
| Binary and decimal arithmetic together | Direct support for both numerical domains. | Substantially more arithmetic and representation obligations before the first executable scalar. |

Recommend `Float64` first, with the source name still a proposal choice. Use
IEEE 754 binary64 as the numerical format. Its finite values, subnormals,
signed zeros, infinities and NaNs need explicit behavior; naming the standard
does not decide every Ash observation or host-environment interaction.
[IEEE format description](https://docs.oracle.com/cd/E77782_01/html/E77791/z4000ac019878.html)

`Float32` can follow when a concrete FFI or storage consumer needs it. Decimal
formats may initially retain an exact library representation or reject an
unsupported conversion; binary64 is not an exact-decimal substitute.

### Minimal numerical contract

The first proposal must resolve the following choices. These are candidate
requirements, not current rules.

| Concern | Recommended starting direction |
| --- | --- |
| Value type | One primitive of kind `Type`; type equality remains ordinary primitive type equality. |
| Basic arithmetic | Addition, subtraction, multiplication, division and negation with binary64 results. |
| Rounding | Round to nearest, ties to even, with a specified result precision for every primitive operation. |
| Underflow | Gradual underflow with subnormals; specify rounding to signed zero instead of depending on host flush-to-zero settings. |
| Overflow and invalid arithmetic | IEEE results, including infinity and NaN, without implicit Ash effects or host traps. |
| Numerical comparison | IEEE equality and ordered comparisons; NaN is unordered and signed zeros compare numerically equal. |
| Classification | Small operations to distinguish finite values, infinities, NaN and the sign where needed. |
| Conversion | Explicit operations with documented rounding or failure; no automatic `Int`/Float coercion. |
| Optimization | Preserve specified rounding and observable special values; no implicit reassociation or multiply-add contraction. |

Numerical equality is not bit identity. NaN prevents ordinary equality from
being a reflexive equivalence; signed zero has equal numerical comparison but
can yield different arithmetic results. Generic equality, ordering and hashing
interfaces must choose their law rather than assume the integer laws transfer.
Total ordering and hashing can be later library facilities with explicit rules.

The first proposal must settle NaN observability. Prefer a portable arithmetic
contract that does not expose signaling behavior, and specify the NaN results
it produces. Decide whether arithmetic canonicalizes NaNs, whether foreign
imports preserve payloads, and whether bit inspection is available. Do not claim
bit-preserving NaN serialization unless that observation is actually supported.
A format-specific raw scalar can retain uninterpreted bits independently of
numerical operations when lossless transport is needed.

Host floating-point environment changes are a foreign-boundary issue. Specify
how the implementation establishes the rounding, subnormal and trap behavior
required by Ash. Calling a foreign function must not silently change later pure
Ash numerical results. Record any target assumptions and evidence.

### Literals and operations

Decimal fractional and exponent forms should produce the new type. Keep
ordinary integer literals as `Int`; specify decimal-to-binary rounding once for
source literals and again by reference for equivalent library parsing. Resolve
leading minus, token boundaries, invalid exponents and any future width suffix
before writing the grammar. Hexadecimal float literals are not needed initially.

Recommend diagnosing overflowing decimal source literals rather than silently
turning them into infinity. Arithmetic may still produce infinity under its
declared rule. Specify underflowing literals and explicit special-value
construction. Text-format acceptance is a separate parser policy.

Compare typed functions for arithmetic with overloaded existing operators.
Typed functions can provide the first executable API without requiring a new
general numerical-overloading mechanism. Any operator notation must elaborate
to the same checked operation and leave existing integer programs unchanged.
No literal or operator spelling is accepted by this note.

An unambiguous fractional/exponent literal can determine its scalar type under
the selected grammar. Ordinary inference can then propagate that type through
calls and aggregates. Rounding policy, foreign width and numerical conversion
intent remain explicit contracts; type inference must not choose a lossy
conversion merely to make a mixed expression type-check.

Explicit `Int` conversion needs both a precision policy and resource behavior.
An integer-to-float operation can round or reject inexact/out-of-range input,
but its name and result type must state which. Float-to-`Int` conversion must
reject nonfinite input and state whether fractional input is truncated or
rejected. Since Ash `Int` is arbitrary precision, do not invent machine-width
overflow for a valid finite conversion; runtime work/allocation limits remain
separate. Foreign-width conversion adds its own range check.

### Parsing, printing and formats

The minimal library needs fallible decimal parsing and deterministic printing
for pipeline use. Specify accepted syntax, full-input versus prefix parsing,
range failures, special values and signed zero. Separate the grammar of an Ash
literal from JSON, YAML, CSV and TOML grammars.

For finite values, target a printing rule whose output parses back to the same
binary64 value, preserving signed zero if that is the selected observation.
This does not promise recovery of the original decimal spelling or exact
decimal mathematical value. NaN needs its separately stated round-trip law.

JSON excludes NaN and infinity and permits numbers outside binary64's range or
precision. A decode requesting `Float64` therefore needs explicit range and
rounding behavior; an integer or lossless-number decode need not use that route.
[JSON number rules](https://www.rfc-editor.org/rfc/rfc8259.html#section-6)

Format libraries own syntax and unsupported-value policy. They must not add
JSON/YAML-specific decisions to the primitive evaluator. Binary codecs specify
their own byte order and width; no native memory image is implied.

## Semantics, Core and proof obligations

Describe the scalar through every owning boundary before implementation:

1. Lexing and parsing retain literal spelling and source origin, then produce
   one checked numerical value under the declared conversion rule.
2. Resolution/kinding and typing admit the primitive type, constants and exact
   operation signatures. Mixed numerical domains require explicit conversion.
3. Elaboration retains a typed scalar constant and operation or authenticated
   intrinsic call. It does not disguise a Float as an unchecked `Int` payload.
4. Independent Core validation checks constant representation, operation arity,
   input/output types, dialect admission and provenance. Text deserialization
   and transformed Core cross the same boundary.
5. The small-step semantics extend the runtime-value domain and primitive
   transition account, retaining existing operand evaluation order. State the
   mathematical binary64 operation relation or the precise trusted numerical
   model it uses, including special values.
6. Transformations preserve the same primitive observations. Folded and unfolded
   programs agree under the selected NaN and signed-zero policy.
7. Body-free module summaries, diagnostics and runtime result rendering retain
   the new type and value without depending on a serialization format.

Record the required semantic delta to
[syntax](../../spec/syntax.md),
[static semantics](../../spec/static-semantics.md),
[elaboration](../../spec/elaboration.md) and
[dynamic semantics](../../spec/dynamic-semantics.md). Representation decisions
also follow the accepted typed-Core and evaluator boundaries.

Required proof work includes typing of primitives, preservation/progress for
their admitted operand cases, correspondence of interpreter operations to the
selected numerical model, and transformation preservation. A NaN result is a
value, not a typing contradiction. Differential tests against a numerical
oracle support correspondence; they do not prove all IEEE behavior.

## Representation and cost experiment

Compare an immediate scalar with representations that box or allocate it when
stored in generic aggregates. Measure scalar payload bytes, tags, alignment,
heap objects, argument passing and storage in repeated records. Binary64's
semantic width does not prove that the interpreter stores each value in eight
physical bytes.

Pure type erasure and `newtype` erasure already provide comparison baselines.
Track whether numerical wrappers and generic interface calls add allocations
or retained metadata. Necessary aggregate/variant representation is distinct
from overhead attributable only to static types. Compare generic and concrete
Ash programs before attributing a difference against a native implementation
to the type system.

Arena layout and foreign conversion are separate consumers. Add Float layout
evidence only through the arena's admitted representation contract; do not
infer layout from the scalar's name. A host `double` bridge requires its exact
ABI profile. No Ash ABI is introduced.

## Evidence and delivery order

Develop feature batches, with e2e/integration evidence at each usable boundary.
Use focused numerical tests where rounding and special-value regressions need
them; do not substitute per-helper tests for source-to-runtime programs.

| Delivery | Executable evidence |
| --- | --- |
| N-0: proposal contract | Literal, arithmetic, conversion, NaN/environment and printing choices are resolved with their semantic delta and required evidence. |
| N-1: source scalar | Imported modules accept, type-check, independently validate and run Float constants through the ordinary CLI and both relevant Core dialects. |
| N-2: numerical processing | Generic and concrete Ash helpers perform arithmetic, comparisons and checked conversions on real inputs. |
| N-3: text bridge | Decimal parse/print composes with the first serialization formats, including range errors and signed zero. |
| N-4: representation consumers | A separately admitted foreign-double bridge and arena layout exercise actual typed storage and conversion. |

Include normal, subnormal and boundary values, halfway rounding, cancellation,
overflow, division by zero, NaN comparisons, signed zero and integer conversions
beyond exact binary64 precision. Negative cases reject malformed literals,
implicit mixed arithmetic, invalid primitive Core and nonfinite integer
conversion. Compare execution before/after retained transformations.

Use numerical processing in JSON/YAML and BSON programs as acceptance evidence,
not just scalar demonstrations. Record unchanged configured resource limits,
allocation/copy costs, compiler maintenance locality and build/checker costs.
The retained Float experiment is an integration comparison, not an oracle for
the new semantics.

## Retention and adoption

A bounded prototype, if separately tasked, tests whether the minimal scalar
contract composes through the existing pipeline and libraries with controlled
representation costs. Retain useful implementation/evidence only after contract
review; revise or reject choices that depend on unspecified host behavior.

Normative adoption requires a language proposal and task, implementation,
positive/negative evidence, applicable proofs, updated specification and a
verified product integration checkpoint. Do not import the historical Float
branch as current truth or merge an unsuccessful numerical experiment.

## Open questions

- Is `Float64` the preferred source name, and which operator notation is useful
  without expanding the first numerical API?
- What NaN payload, signaling and bit-level observations should Ash expose?
- What literal underflow and parse range policies should the first proposal use?
- Which explicit integer conversion variants are necessary for the first
  processing pipelines?
- Which numerical model and implementation oracle establish portable rounding
  correspondence on the supported targets?
- Which measured costs justify immediate/unboxed storage or generic-call
  optimization, and where must runtime representation remain observable?
