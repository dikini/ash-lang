# DN-0034: One-Shot Control Kernel Soundness and Practicality Assessment

- ID: `DN-0034`
- Status: evaluating
- Related: [DN-0033](DN-0033-direct-effects-and-continuation-capabilities.md)

> This note evaluates the soundness and practicality of the one-shot control
> kernel formalization governed by DN-0033. It defines no current Ash semantics,
> accepts no architecture, and authorizes no implementation. The assessment
> below is based on the evidence in
> [direct-effects/one-shot](direct-effects/one-shot/README.md) and its
> [mathematical companion](direct-effects/one-shot/KERNEL.md).

## Question

What is the current soundness guarantee of the one-shot control kernel
formalization, and how practical is it for aiding Ash development by making
its proofs available?

This note addresses the specific request for a top-level evaluation without
approving changes, focusing on whether and how the formalization can support
Ash's ongoing development.

## Assessment Summary

The one-shot control kernel is **sound within its defined scope** and
**practically promising** for Ash development. The formalization provides a
rigorous direct operational foundation that aligns closely with Ash's
existing specification. Making its proofs available can immediately begin
aiding Ash development through static analysis, test generation, and
specification validation, even as the remaining proof obligations mature.

| Dimension | Status | Confidence |
| --- | --- | --- |
| Mathematical soundness (current scope) | Substantial | High |
| Alignment with Ash semantics | Strong | High |
| Proof completeness | Partial (M0-M3 mostly complete, M4 open) | Medium |
| Development aid readiness | High (with packaging) | High |
| Long-term maintainability | Moderate | Medium |

## Soundness Evaluation

### Direct Semantic Alignment

The calculus achieves **strong alignment** with Ash's dynamic semantics:

- **No computation wrappers**: Uses ordinary values, lexical binding, operation
  requests, and handler boundaries. This matches
  [spec/dynamic-semantics.md](../../spec/dynamic-semantics.md):
  > the selected boundary moves into the capture and returns around resumed
  > computation, above remaining clause work

- **Exact effect instance matching**: Requests select the nearest exact
  interpretation, matching Ash's requirement for exact parameterized effect
  identities.

- **Result-preserving handlers**: Normal body return passes its value through
  without transformation, preserving Ash's result-preserving handler semantics.

- **Hidden capability consumption**: Each normally completing clause path
  consumes the capability exactly once, matching the spec's hidden capability
  requirement.

The presence of `Bind` in current Core is compatible with this account; it
represents sequential local binding syntax and evaluation, not a distinct
computation model.

### Structural Integrity

The formalization establishes **core structural properties** through proved
theorems:

1. **Ownership accounting**: The multiset equation
   `owners(before) + created = owners(after) + discharged` holds for all 21
   raw constructors. This prevents duplicate ownership and ensures every
   acquired resource is tracked.

2. **Capture safety**: The `CaptureOK` and `Discardable` judgments prevent unsafe
   abandonment. The structural theorem `consuming_suffix_blocks_discard` proves
   that a free suffix ticket owned outside a cut prohibits disposal, directly
   supporting Ash's continuation safety requirements.

3. **Interpretation preservation**: The `SameRequests` judgment and
   `close_plan_preserves_interpretation` theorem ensure that every planned
   invocation retains the same exact interpreter activation, preserving
   handler selection semantics across disposal and resumption.

4. **Finite execution**: `Run.finite_prefix` constructs actual steps for any
   fuel bound with `terminal_accounting` proving no duplicate completions.

### Progress Theorems

| Milestone | Status | Coverage |
| --- | --- | --- |
| M0: Structural resource admission | Complete | Full |
| M1: 32 transition families | 31/32 connected | Capture remains in transition |
| M2: Initial source admission | Complete | For lexical `InstallationState` |
| M3: Combined constructive preservation | Complete | Every applicable request has valid successor |
| M4: Progress, reachable safety, terminal ownership | **Open** | Full safety theorem remains |

The **M3 result** is particularly significant: it establishes that every
applicable request has a valid successor using source-selected metadata,
providing constructive preservation for the current result fragment.

### Explicit Scope Boundaries

The formalization maintains **clear documentation** of its limitations:

- **Excluded features**: Multishot, escaping continuations, suspension, and
  asynchronous integration are explicitly out of scope.

- **Open obligations**: Approximately 100 explicit "remain open" items are tracked
  in KERNEL.md, each with clear dependencies.

- **Counterexamples**: Known gaps are formalized as explicit counterexamples
  (e.g., model counterexample with wrong continuation input type), not hidden
  defects.

This transparency reduces the risk of false confidence in the formalization's
coverage.

### Core Correspondence

| Area | Status | Risk |
| --- | --- | --- |
| Exact handler selection and full-prefix resume | Aligned, unproved | Low |
| Fresh resource activation | Repeated-call counterexample fixed | Low |
| Nonempty capture payload | Fixture alignment verified (`17 : Int`) | Low |
| Types and declaration admission | Partial (monomorphic fragment) | Medium |
| Runtime capture annotations | Model counterexample identified | Medium |
| Disposal, cleanup and completion | Runtime coverage proved, unproved | Medium |
| Failure and divergence observations | Unproved | High |

**No demonstrated semantic disagreements** have been identified. The comparison
classifies the direct-argument failure as a Core construction limitation,
not a semantic mismatch. However, **no general simulation theorem** has been
established, and alignment changes are not authorized.

## Practicality Evaluation

### Ash Alignment

The calculus **directly implements** Ash's operational semantics:

- **Handler selection**: Nearest exact match, moves segment through boundary
- **Resumption**: Reinstalls frames above remaining clause work (deep resumption)
- **Disposal**: Executes close protocol in structural inner-to-outer order
- **Cleanup**: Distinguishes armed actions from running actions

There is **no architectural mismatch** requiring Core changes. The approach
rejects wrappers, transformer stacks, and model conversions that would
complicate integration.

### Current Proof Asset Inventory

The formalization consists of **754 Lean files** organized into coherent
modules:

| Module Category | Count | Purpose |
| --- | --- | --- |
| Structural judgments | ~50 | `Control`, `Frame`, `Owner`, `Kind` definitions |
| Execution layers | ~100 | `Execution.lean`, `Access.lean`, `Typing.lean`, `Usage.lean` |
| Annotated runtime | ~200 | `SourceAnnotatedStored*.lean` files |
| Proof transports | ~200 | Substitution, rechecking, preservation |
| Fixtures and examples | ~100 | Test cases, counterexamples, bridges |
| Interface and bridges | ~104 | Connections between layers |

This represents a **substantial proof asset** with reusable lemmas:
- `capture_wellFormed`, `resume_wellFormed`
- `close_plan_checks`, `close_plan_preserves_interpretation`
- `raw_step_preserves_access`
- `terminal_accounting`

### Development Aid Potential

#### Immediate Applications (Ready Now)

1. **Static analysis tool**: Extract the structural usage checker (`Usage.lean`)
   - Detect continuation capture issues in Ash code
   - Flag potential discard-safety violations
   - Integrate with `ash-doc` for developer feedback

2. **Test generation**: Use fixture alignment results
   - Generate Ash test cases from formal counterexamples
   - Verify Ash behavior against formal expectations
   - Catch regressions in handler selection and resumption

3. **Specification validation**: Use annotated runtime state
   - Formalize ambiguous spec sections (e.g., cleanup ordering)
   - Validate proposed semantic changes before implementation
   - Resolve edge cases in disposal and escape handling

#### Near-term Applications (Require Packaging)

1. **Proof health monitoring**: Add to Ash CI
   - Verify all "complete" theorems still type-check
   - Track connected constructor count (currently 20/21)
   - Monitor open obligation count as a metric

2. **Regression detection**: Leverage the fixture parity table
   - Current alignment: outer-handle-capture-payload.ash returns `17` in both
   - Extend to additional test cases
   - Flag behavioral divergence early

### Integration Complexity

| Factor | Assessment | Mitigation |
| --- | --- | --- |
| Proof size (754 files) | Large surface area | Modularize by feature, not by proof |
| Lean toolchain dependency | Additional requirement | Containerized builds, version pinning |
| Proof brittleness | Medium risk | Automated proof health checks |
| Expertise requirement | High for contribution | Provide abstraction layers for users |
| Maintenance overhead | Moderate | Automate where possible |

### Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
| --- | --- | --- | --- |
| Proof brittleness under Core changes | Medium | High | Automated proof health checks in CI |
| Lean toolchain maintenance burden | Low | Medium | Containerized builds, documented setup |
| Incomplete coverage leading to false confidence | Medium | High | Explicit scope boundaries, gap tracking |
| Integration complexity discouraging use | High | Medium | Usable tools, not just raw proofs |
| Open obligations growing uncontrollably | Medium | Medium | Milestone-based completion criteria |

## Recommendations

### For Making Proofs Available (Immediate Priority)

**Phase 1: Package the Artifact (Start Now)**

1. Create a stable release with:
   - Machine-readable proof index mapping theorems to status, dependencies,
     and Ash relevance
   - Cross-reference links from DN-0033 sections to specific Lean files
   - Fixture parity table showing Ash test cases with formal counterparts

2. Establish proof navigation aids:
   - Feature-aligned module organization (handlers, resources, cleanup, etc.)
   - Dependency graph visualization
   - Status dashboard for the ~100 open obligations

**Phase 2: Integrate with Ash Workflow (Start Now)**

1. Add proof health check to Ash CI:
   - Verify all "complete" theorems type-check
   - Flag regression in connected constructor count
   - Track open obligation count

2. Extract the structural usage checker as a developer tool:
   - Standalone analysis for continuation safety
   - Integration with `ash-doc` for inline warnings
   - GitHub Action for PR review

**Phase 3: Bridge to Core (Near-term)**

1. Prioritize Core correspondence proofs:
   - Start with exact handler selection (already aligned)
   - Complete fresh resource activation (counterexample fixed)
   - Document known gaps as formal markers

2. Develop proof adaptation infrastructure:
   - Tools to update structural equalities when Core changes
   - Automated flagging of affected theorems
   - Skeleton proof generation for new features

### For Ash Development Aid

**High-value Extracts (Ready for Implementation)**

1. **Continuation safety checker**:
   - Input: Ash source code
   - Output: Warnings about potential discard-safety violations
   - Based on: `consuming_suffix_blocks_discard` theorem

2. **Handler selection validator**:
   - Input: Ash effect definitions and handlers
   - Output: Verification of exact instance matching
   - Based on: `SameRequests` and selection theorems

3. **Resource lifetime analyzer**:
   - Input: Ash resource acquisition and usage patterns
   - Output: Lifetime dependency graph and potential leaks
   - Based on: Ownership accounting multiset equations

**Medium-term Developments**

1. **Complete M4 milestone**:
   - Full one-shot safety theorem
   - Reachable safety and terminal ownership
   - Requires: General initial-term admission

2. **Expand feature coverage**:
   - Multishot continuation capabilities
   - Escaping continuations
   - Suspension (requires architectural decisions)

3. **Enhance type system coverage**:
   - Full polymorphism support
   - Kind system integration
   - Row/lacks constraint handling

### For Long-term Sustainability

1. **Modularize the Formalization**:
   - Restructure files into feature-aligned modules
   - Create abstraction layers hiding proof details
   - Provide tutorial documentation for users

2. **Automate Proof Maintenance**:
   - Develop proof adaptation tools
   - Automated regression detection
   - Skeleton proof generation

3. **Build Community Capacity**:
   - Documentation for non-experts
   - Contribution guidelines
   - Mentoring pathways

## Conclusion

The one-shot control kernel formalization is **sound within its defined scope**
and **highly practical** for aiding Ash development. The alignment with Ash
semantics is strong, the proof structure is robust, and the immediate
applications are compelling.

**Making the proofs available now is recommended.** With proper packaging and
selective extraction of usable components, this formalization can immediately
begin supporting Ash development while the remaining proof obligations
mature. The identified risks are manageable with appropriate infrastructure
and processes.

The work represents a **significant asset** for Ash. The gaps are well-understood
and documented, not hidden. The path forward is clear: package, integrate, and
extract value while continuing to complete the formalization.

## Appendix: Proof Status Reference

This assessment references the following evidence from the one-shot
formalization:

- [README.md](direct-effects/one-shot/README.md): Current proof status and
  evidence register
- [KERNEL.md](direct-effects/one-shot/KERNEL.md): Mathematical companion with
  structural judgments and proof dependencies
- [OneShot.lean](direct-effects/one-shot/OneShot.lean): Core definitions and
  structural lemmas
- [SourceAnnotatedStored*.lean](direct-effects/one-shot/): Joint preservation
  theorems and runtime connections

The milestone numbering (M0-M4) follows the conventions established in
KERNEL.md and referenced throughout the formalization.
