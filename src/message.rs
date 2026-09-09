//! Typed compile-time messages and embedded translations.
//!
//! This allocating formatter is not the runtime resource-failure reporter.

use fluent_bundle::{FluentArgs, FluentBundle, FluentResource};
use std::{borrow::Cow, path::Path};

/// Supported embedded diagnostic languages.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Locale {
    /// English, including the final fallback.
    English,
    /// Bulgarian.
    Bulgarian,
}

impl Locale {
    /// Resolves a locale name, accepting POSIX spelling and parent fallback.
    #[must_use]
    pub fn from_name(name: &str) -> Self {
        let normalized = name
            .split(['.', '@'])
            .next()
            .unwrap_or("")
            .replace('_', "-");
        match normalized.parse::<unic_langid::LanguageIdentifier>() {
            Ok(locale) if locale.language.as_str() == "bg" => Self::Bulgarian,
            _ => Self::English,
        }
    }
}

/// A checked message borrowing phase facts. Private fields restrict construction
/// to declared keys and named arguments. Presentation keys are not JSON reasons.
///
/// Missing arguments and wrong value types fail to compile:
/// ```compile_fail
/// use ash::message::Message;
/// let _ = Message::binding_initializer("Bool");
/// ```
/// ```compile_fail
/// use ash::message::Message;
/// let _ = Message::initializer(42);
/// ```
/// Grammar descriptions must come from typed parser facts, not English text:
/// ```compile_fail
/// use ash::message::Message;
/// let _ = Message::parse_expected("an expression");
/// ```
/// ```compile_fail
/// use ash::{message::Message, parser::ExpectedForm};
/// let _ = Message::parse_found(ExpectedForm::Expression);
/// ```
/// Resource quantities are checked integers, not preformatted descriptions:
/// ```compile_fail
/// use ash::message::Message;
/// let _ = Message::syntax_depth("source.ash", "128");
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Message<'a> {
    key: &'static str,
    arguments: Vec<(&'static str, Cow<'a, str>)>,
}

impl<'a> Message<'a> {
    fn parts(&self) -> (&'static str, &[(&'static str, Cow<'a, str>)]) {
        (self.key, &self.arguments)
    }
}

// Only retained argument types participate; catalogue values borrow compiler facts.
trait Argument<'a> {
    fn value(self) -> Cow<'a, str>;
}

impl<'a> Argument<'a> for &'a str {
    fn value(self) -> Cow<'a, str> {
        Cow::Borrowed(self)
    }
}

impl Argument<'_> for crate::parser::ExpectedForm {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(self.diagnostic_name())
    }
}

impl Argument<'_> for crate::parser::FoundToken {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(self.diagnostic_name())
    }
}

impl<'a> Argument<'a> for &'a Path {
    fn value(self) -> Cow<'a, str> {
        self.to_string_lossy()
    }
}

impl Argument<'_> for std::io::ErrorKind {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(crate::module::io_kind_name(self))
    }
}

impl Argument<'_> for usize {
    fn value(self) -> Cow<'static, str> {
        // Resource limits are exact decimal quantities, not floating-point counts.
        Cow::Owned(self.to_string())
    }
}

impl Argument<'_> for crate::module::ModuleResource {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(self.diagnostic_name())
    }
}

impl Argument<'_> for crate::parser::InternalReason {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(self.diagnostic_name())
    }
}

impl Argument<'_> for crate::resolve::ResolveIdentitySpace {
    fn value(self) -> Cow<'static, str> {
        Cow::Borrowed(self.diagnostic_name())
    }
}

// One declaration supplies typed constructors and exhaustive test examples.
// The concrete carrier remains visible to the source ownership inventory.
macro_rules! messages {
    ($( $(#[$doc:meta])* $constructor:ident => $key:literal { $($argument:ident: $ty:ty = $example:expr),* } ),* $(,)?) => {
        impl<'a> Message<'a> {
            $(
                $(#[$doc])*
                #[must_use]
                pub fn $constructor($($argument: $ty),*) -> Self {
                    Self { key: $key, arguments: vec![$((stringify!($argument), $argument.value())),*] }
                }
            )*

            #[cfg(test)]
            fn examples() -> Vec<Message<'static>> {
                vec![$(Message::$constructor($($example),*)),*]
            }
        }
    };
}

messages! {
    /// Kind validation failed while checking evidence at this use.
    evidence_kind_use => "evidence-kind-use" {},
    elaboration_kind_use => "elaboration-kind-use" {},
    resolve_kind_use => "resolve-kind-use" {},
    /// The compiler retained a constructor scheme referring to a variable outside its owner parameters.
    kind_internal_body_free_constructor_owner => "kind-internal-body-free-constructor-owner" {},
    /// The compiler has no canonical parameter kinds for an interface occurrence checked without a body.
    kind_internal_body_free_interface_kind => "kind-internal-body-free-interface-kind" {},
    /// The compiler retained a checked constructor scheme whose resulting kind is not Type.
    kind_internal_body_free_constructor_kind => "kind-internal-body-free-constructor-kind" {},
    /// The compiler retained a function-type component with the wrong kind during body-free checking.
    kind_internal_body_free_function_kind => "kind-internal-body-free-function-kind" {},
    /// The compiler retained an interface application with the wrong argument count during body-free checking.
    kind_internal_body_free_interface_arity => "kind-internal-body-free-interface-arity" {},
    /// The compiler retained an interface argument with the wrong kind during body-free checking.
    kind_internal_body_free_interface_argument => "kind-internal-body-free-interface-argument" {},
    /// The compiler retained an empty or all-parameter determinant seed for a checked interface.
    kind_internal_body_free_determinant_seed => "kind-internal-body-free-determinant-seed" {},
    /// The compiler retained a checked interface method whose resulting kind is not Type.
    kind_internal_body_free_method_kind => "kind-internal-body-free-method-kind" {},
    /// The compiler retained a checked interface method with an empty required-parameter seed.
    kind_internal_body_free_required_seed => "kind-internal-body-free-required-seed" {},
    /// The compiler retained a checked interface method without a function type.
    kind_internal_body_free_method_function => "kind-internal-body-free-method-function" {},
    /// The compiler retained a checked interface method that omits a required parameter.
    kind_internal_body_free_missing_parameter => "kind-internal-body-free-missing-parameter" {},
    /// The compiler retained a duplicate type parameter in a checked interface method.
    kind_internal_body_free_method_duplicate_parameter => "kind-internal-body-free-method-duplicate-parameter" {},
    /// The compiler retained a duplicate type parameter in a checked interface.
    kind_internal_body_free_interface_duplicate_parameter => "kind-internal-body-free-interface-duplicate-parameter" {},
    /// The compiler retained an interface parameter seed that is not a unique subset in declaration order.
    kind_internal_body_free_seed_order => "kind-internal-body-free-seed-order" {},
    /// The compiler retained a checked monotype with the wrong canonical kind.
    kind_internal_body_free_monotype_kind => "kind-internal-body-free-monotype-kind" {},
    /// The compiler retained a tuple element with the wrong kind during body-free checking.
    kind_internal_body_free_tuple_kind => "kind-internal-body-free-tuple-kind" {},
    /// The compiler retained a type application with the wrong argument kind during body-free checking.
    kind_internal_body_free_application_argument => "kind-internal-body-free-application-argument" {},
    /// The compiler retained a type application whose operator does not have a function kind.
    kind_internal_body_free_non_function_kind => "kind-internal-body-free-non-function-kind" {},
    /// The compiler retained a checked value scheme whose resulting kind is not Type.
    kind_internal_body_free_value_kind => "kind-internal-body-free-value-kind" {},
    /// The compiler tried to retain a source diagnostic while checking kinds without source bodies.
    kind_internal_body_free_source_diagnostic => "kind-internal-body-free-source-diagnostic" {},
    /// The compiler retained a lexical newtype referring to a missing canonical constructor.
    kind_internal_lookup_lexical_constructor => "kind-internal-lookup-lexical-constructor" {},
    /// The compiler has no canonical parameter records for a lexical nominal type.
    kind_internal_lookup_lexical_parameters => "kind-internal-lookup-lexical-parameters" {},
    /// The compiler retained a lexical nominal marker referring to a missing canonical record.
    kind_internal_lookup_lexical_nominal => "kind-internal-lookup-lexical-nominal" {},
    /// The compiler has no canonical parameter records for a local nominal type.
    kind_internal_lookup_nominal_parameters => "kind-internal-lookup-nominal-parameters" {},
    /// The compiler retained a newtype referring to a missing canonical constructor.
    kind_internal_lookup_newtype_constructor => "kind-internal-lookup-newtype-constructor" {},
    /// The compiler has no declaration-ordered payload provenance for a nominal type.
    kind_internal_lookup_payload_provenance => "kind-internal-lookup-payload-provenance" {},
    /// The compiler retained a nominal type referring to a missing canonical constructor.
    kind_internal_lookup_nominal_constructor => "kind-internal-lookup-nominal-constructor" {},
    /// The compiler's declaration order contains an invalid effect index.
    kind_internal_lookup_effect_index => "kind-internal-lookup-effect-index" {},
    /// The compiler's declaration order contains an invalid global-definition index.
    kind_internal_lookup_global_index => "kind-internal-lookup-global-index" {},
    /// The compiler's declaration order contains an invalid implementation index.
    kind_internal_lookup_implementation_index => "kind-internal-lookup-implementation-index" {},
    /// The compiler's declaration order contains an invalid interface index.
    kind_internal_lookup_interface_index => "kind-internal-lookup-interface-index" {},
    /// The compiler's declaration order contains an invalid nominal-type index.
    kind_internal_lookup_nominal_index => "kind-internal-lookup-nominal-index" {},
    /// The compiler has no canonical kind for a type binder.
    kind_internal_missing_canonical_binder => "kind-internal-missing-canonical-binder" {},
    /// The compiler retained a declaration binder that conflicts with its canonical registry record.
    kind_internal_conflicting_declaration_binder => "kind-internal-conflicting-declaration-binder" {},
    /// The compiler has no canonical registry record for a declaration binder.
    kind_internal_missing_declaration_binder => "kind-internal-missing-declaration-binder" {},
    /// The compiler passed a polymorphic scheme to global determination discovery, which requires a monotype.
    kind_internal_scheme_in_determination => "kind-internal-scheme-in-determination" {},
    /// The compiler passed a polymorphic scheme to resolved monotype kind checking.
    kind_internal_scheme_in_monotype => "kind-internal-scheme-in-monotype" {},
    /// The compiler retained an empty explicit method binder list.
    kind_internal_empty_method_binders => "kind-internal-empty-method-binders" {},
    /// The compiler has no canonical interface-kind entry for a resolved interface application.
    kind_internal_missing_interface_kind => "kind-internal-missing-interface-kind" {},
    /// The compiler retained a resolved interface without type parameters.
    kind_internal_empty_interface_parameters => "kind-internal-empty-interface-parameters" {},
    /// The compiler has no canonical kind for a resolved type variable.
    kind_internal_missing_variable_kind => "kind-internal-missing-variable-kind" {},
    /// The compiler retained a resource identity whose kind is not Type.
    kind_internal_resource_identity_kind => "kind-internal-resource-identity-kind" {},
    /// The compiler retained a determinant position outside its complete interface application.
    kind_internal_determinant_position => "kind-internal-determinant-position" {},
    /// The compiler retained an invalid determination key in authenticated source data.
    kind_internal_source_determination_key => "kind-internal-source-determination-key" {},
    /// The compiler retained an invalid determination key in an authenticated summary.
    kind_internal_summary_determination_key => "kind-internal-summary-determination-key" {},
    /// The compiler retained an effect-row argument with the wrong canonical kind.
    kind_internal_effect_argument_kind => "kind-internal-effect-argument-kind" {},
    /// The compiler retained an effect-row instance with the wrong canonical argument count.
    kind_internal_effect_argument_count => "kind-internal-effect-argument-count" {},
    /// The compiler retained an effect row referring to an effect without a canonical checked declaration.
    kind_internal_missing_row_effect => "kind-internal-missing-row-effect" {},
    /// The compiler retained an effect-row tail that is not bound by its owner.
    kind_internal_non_owner_row_tail => "kind-internal-non-owner-row-tail" {},
    /// The compiler retained an effect-row tail whose kind is not EffectRow.
    kind_internal_row_tail_kind => "kind-internal-row-tail-kind" {},
    /// The compiler has no canonical binder kind for an effect-row tail.
    kind_internal_missing_row_binder_kind => "kind-internal-missing-row-binder-kind" {},
    /// The compiler has no fixed inference kind for an effect-row tail.
    kind_internal_missing_row_inference_kind => "kind-internal-missing-row-inference-kind" {},
    /// The compiler retained an EffectRow parameter on an implementation owner that cannot bind one.
    kind_internal_implementation_row_binder => "kind-internal-implementation-row-binder" {},
    /// The compiler observed different interface-application argument counts between kind preflight passes.
    kind_internal_preflight_arity_changed => "kind-internal-preflight-arity-changed" {},
    /// The compiler retained an EffectRow parameter on an interface method that cannot bind one.
    kind_internal_method_row_binder => "kind-internal-method-row-binder" {},
    /// The compiler encountered row inference during global determination discovery.
    kind_internal_row_inference_determination => "kind-internal-row-inference-determination" {},
    /// The compiler retained constructor payload provenance that disagrees with the moved payload.
    kind_internal_constructor_moved_provenance => "kind-internal-constructor-moved-provenance" {},
    /// The compiler retained a canonical constructor owned by a different nominal type.
    kind_internal_constructor_owner => "kind-internal-constructor-owner" {},
    /// The compiler retained the wrong number of outer provenance records for a constructor payload.
    kind_internal_payload_cardinality => "kind-internal-payload-cardinality" {},
    /// The compiler paired constructor payload provenance with the wrong constructor identity.
    kind_internal_payload_identity => "kind-internal-payload-identity" {},
    /// The compiler retained different numbers of nominal constructors and payload provenance records.
    kind_internal_nominal_payload_provenance => "kind-internal-nominal-payload-provenance" {},
    /// The compiler retained an ordinary constructor payload for a newtype constructor.
    kind_internal_newtype_payload => "kind-internal-newtype-payload" {},
    /// The compiler retained a newtype without exactly one constructor identity.
    kind_internal_newtype_constructor_count => "kind-internal-newtype-constructor-count" {},
    /// The compiler retained a newtype without exactly one representation provenance record.
    kind_internal_newtype_representation_count => "kind-internal-newtype-representation-count" {},
    /// The compiler failed to retain a newtype's canonical representation.
    kind_internal_newtype_representation => "kind-internal-newtype-representation" {},
    /// The compiler retained a newtype representation without exactly one field provenance record.
    kind_internal_newtype_field_provenance => "kind-internal-newtype-field-provenance" {},
    /// The compiler retained a lexical nominal record that is not a lexical newtype.
    kind_internal_lexical_nominal => "kind-internal-lexical-nominal" {},
    /// The compiler retained a lexical newtype constructor with invalid ownership or an ordinary payload.
    kind_internal_lexical_newtype_constructor => "kind-internal-lexical-newtype-constructor" {},
    /// The compiler retained a lexical newtype without exactly one constructor identity.
    kind_internal_lexical_newtype_count => "kind-internal-lexical-newtype-count" {},
    /// The compiler failed to retain a lexical newtype's canonical representation.
    kind_internal_lexical_newtype_representation => "kind-internal-lexical-newtype-representation" {},
    /// The compiler failed to retain representation provenance for a lexical newtype.
    kind_internal_lexical_newtype_provenance => "kind-internal-lexical-newtype-provenance" {},
    /// The compiler retained an imported nominal type whose parameter records disagree with its parameter count.
    kind_internal_imported_nominal_parameters => "kind-internal-imported-nominal-parameters" {},
    /// The compiler retained a payload constructor scheme without an outer function type.
    kind_internal_payload_scheme_function => "kind-internal-payload-scheme-function" {},
    /// The compiler retained duplicate or out-of-order declaration indices.
    kind_internal_declaration_order => "kind-internal-declaration-order" {},
    /// The compiler's declaration order omits local declarations.
    kind_internal_declaration_coverage => "kind-internal-declaration-coverage" {},
    /// The compiler encountered an invalid global-definition index during interface-application kind preflight.
    kind_internal_kind_preflight_global => "kind-internal-kind-preflight-global" {},
    /// The compiler encountered an invalid implementation index during interface-application kind preflight.
    kind_internal_kind_preflight_implementation => "kind-internal-kind-preflight-implementation" {},
    /// The compiler encountered an invalid global-definition index during interface-application preflight.
    kind_internal_preflight_global => "kind-internal-preflight-global" {},
    /// The compiler encountered an invalid implementation index during interface-application preflight.
    kind_internal_preflight_implementation => "kind-internal-preflight-implementation" {},
    /// The compiler retained invalid source provenance for a resolved type.
    kind_internal_invalid_type_provenance => "kind-internal-invalid-type-provenance" {},
    /// The compiler paired a resolved type with source provenance belonging to a different owner.
    kind_internal_type_provenance_owner => "kind-internal-type-provenance-owner" {},
    /// The compiler attached composite-type provenance to an atomic resolved type.
    kind_internal_atomic_type_provenance => "kind-internal-atomic-type-provenance" {},
    /// The compiler paired a resolved type application with provenance for a different type form.
    kind_internal_application_provenance => "kind-internal-application-provenance" {},
    /// The compiler paired a resolved function type with provenance for a different type form.
    kind_internal_function_provenance => "kind-internal-function-provenance" {},
    /// The compiler paired a resolved tuple type with provenance for a different type form.
    kind_internal_tuple_provenance => "kind-internal-tuple-provenance" {},
    /// The compiler retained incomplete source provenance for a resolved tuple type.
    kind_internal_incomplete_tuple_provenance => "kind-internal-incomplete-tuple-provenance" {},
    /// The compiler retained incomplete element provenance for a resolved tuple type.
    kind_internal_tuple_child_provenance => "kind-internal-tuple-child-provenance" {},
    /// The compiler paired an effect-bearing type with provenance belonging to a different owner.
    kind_internal_effect_type_provenance_owner => "kind-internal-effect-type-provenance-owner" {},
    /// The compiler paired an effect-bearing type with provenance for a different type structure.
    kind_internal_effect_type_provenance_shape => "kind-internal-effect-type-provenance-shape" {},
    /// The compiler retained provenance that does not match the elements of an effect-bearing tuple type.
    kind_internal_effect_tuple_provenance => "kind-internal-effect-tuple-provenance" {},
    /// The compiler retained incomplete provenance for an effectful function type.
    kind_internal_effect_function_provenance => "kind-internal-effect-function-provenance" {},
    /// The compiler retained effect-argument provenance for a pure computation.
    kind_internal_pure_computation_provenance => "kind-internal-pure-computation-provenance" {},
    /// The compiler retained a computation row with a missing or invalid effect-argument provenance record.
    kind_internal_computation_missing_arguments => "kind-internal-computation-missing-arguments" {},
    /// The compiler retained surplus effect-argument provenance records for a computation row.
    kind_internal_computation_surplus_arguments => "kind-internal-computation-surplus-arguments" {},
    /// The compiler retained too few argument provenance records for an effect row.
    kind_internal_row_missing_arguments => "kind-internal-row-missing-arguments" {},
    /// The compiler retained surplus argument provenance records for an effect row.
    kind_internal_row_surplus_arguments => "kind-internal-row-surplus-arguments" {},
    /// The compiler retained a hook argument without its source occurrence.
    kind_internal_hook_argument_source => "kind-internal-hook-argument-source" {},
    /// The compiler retained different numbers of hook arguments and argument provenance records.
    kind_internal_hook_argument_provenance => "kind-internal-hook-argument-provenance" {},
    /// The compiler has no canonical effect declaration for a hook target.
    kind_internal_hook_missing_effect => "kind-internal-hook-missing-effect" {},
    /// The compiler retained different binder counts in the source and checked implementation head.
    kind_internal_implementation_binder_count => "kind-internal-implementation-binder-count" {},
    /// The compiler retained different binder identities in the source and checked implementation head.
    kind_internal_implementation_binder_identity => "kind-internal-implementation-binder-identity" {},
    /// The compiler retained different binder counts in a linked source scheme and its checked scheme.
    kind_internal_scheme_binder_count => "kind-internal-scheme-binder-count" {},
    /// The compiler retained different binder identities in a linked source scheme and its checked scheme.
    kind_internal_scheme_binder_identity => "kind-internal-scheme-binder-identity" {},
    /// The compiler retained a binder kind that disagrees with its canonical registry entry.
    kind_internal_retained_binder_kind => "kind-internal-retained-binder-kind" {},
    /// The compiler retained an unused rigid binder in a linked implementation head.
    kind_internal_unused_implementation_binder => "kind-internal-unused-implementation-binder" {},
    /// The compiler retained an unused owner binder in a linked value scheme.
    kind_internal_unused_scheme_binder => "kind-internal-unused-scheme-binder" {},
    /// The compiler retained an invalid allowance for dependent-only binders in a linked global definition.
    kind_internal_invalid_dependent_allowance => "kind-internal-invalid-dependent-allowance" {},
    /// The compiler retained a linked source type that disagrees with its checked value type.
    kind_internal_linked_value_type => "kind-internal-linked-value-type" {},
    /// The compiler retained a source computation row that disagrees with its checked row.
    kind_internal_linked_computation_row => "kind-internal-linked-computation-row" {},
    /// The compiler retained two mirrors for one linked constructor domain.
    kind_internal_duplicate_constructor_mirror => "kind-internal-duplicate-constructor-mirror" {},
    /// The compiler has no canonical kind for a nominal type.
    kind_internal_missing_nominal_kind => "kind-internal-missing-nominal-kind" {},
    /// The compiler registered more than one canonical kind for a nominal type.
    kind_internal_duplicate_nominal_kind => "kind-internal-duplicate-nominal-kind" {},
    /// The compiler has no fixed kind for an inference variable.
    kind_internal_missing_inference_kind => "kind-internal-missing-inference-kind" {},
    /// The compiler registered more than one fixed kind for an inference variable.
    kind_internal_duplicate_inference_kind => "kind-internal-duplicate-inference-kind" {},
    /// The compiler has no canonical parameter records for an interface.
    kind_internal_missing_interface_parameters => "kind-internal-missing-interface-parameters" {},
    /// The compiler retained conflicting canonical parameter counts for an interface.
    kind_internal_interface_parameter_count => "kind-internal-interface-parameter-count" {},
    /// The compiler retained conflicting canonical parameter records for an interface.
    kind_internal_interface_parameter_records => "kind-internal-interface-parameter-records" {},
    /// The compiler has no canonical registry entry for a local effect.
    kind_internal_missing_effect => "kind-internal-missing-effect" {},
    /// The compiler retained a duplicate identity in the checked effect registry.
    kind_internal_duplicate_effect => "kind-internal-duplicate-effect" {},
    /// The compiler retained EffectRow beneath a kind arrow, where it is not admitted.
    kind_internal_nested_effect_row => "kind-internal-nested-effect-row" {},
    /// The compiler retained a duplicate type-variable identity in an owner's binder list.
    kind_internal_duplicate_binder => "kind-internal-duplicate-binder" {},
    /// The compiler retained an EffectRow parameter for an owner that cannot bind one.
    kind_internal_owner_effect_row => "kind-internal-owner-effect-row" {},
    /// The compiler has no canonical registry entry for a linked owner binder.
    kind_internal_missing_owner_binder => "kind-internal-missing-owner-binder" {},
    /// The compiler ran out of resources while checking type kinds.
    kind_resources => "kind-resources" {},
    /// The compiler ran out of resources while resolving types.
    resolve_type_resources => "resolve-type-resources" {},
    /// The compiler ran out of resources while resolving interfaces and constraints.
    resolve_constraint_resources => "resolve-constraint-resources" {},
    /// Wrong Core dialect, retaining the arena-local node number.
    core_validation_dialect_node => "core-validation-dialect-node" { node: usize = 42 },
    /// Invalid Core root, retaining the arena-local node number.
    core_validation_root_node => "core-validation-root-node" { node: usize = 42 },
    /// Cyclic Core graph, retaining the arena-local node number.
    core_validation_cycle_node => "core-validation-cycle-node" { node: usize = 42 },
    /// Unreachable Core node, retaining the arena-local node number.
    core_validation_unreachable_node => "core-validation-unreachable-node" { node: usize = 42 },
    core_validation_missing_child => "core-validation-missing-child" {},
    core_validation_missing_child_node => "core-validation-missing-child-node" { node: usize = 42 },
    core_validation_foreign_arena => "core-validation-foreign-arena" {},
    core_validation_foreign_arena_node => "core-validation-foreign-arena-node" { node: usize = 42 },
    core_validation_missing_node => "core-validation-missing-node" {},
    core_validation_missing_node_node => "core-validation-missing-node-node" { node: usize = 42 },
    core_validation_identity_range => "core-validation-identity-range" {},
    core_validation_identity_range_node => "core-validation-identity-range-node" { node: usize = 42 },
    core_validation_empty_match => "core-validation-empty-match" {},
    core_validation_empty_match_node => "core-validation-empty-match-node" { node: usize = 42 },
    core_validation_redundant_arm => "core-validation-redundant-arm" { arm: usize = 2 },
    core_validation_redundant_arm_node => "core-validation-redundant-arm-node" { arm: usize = 2, node: usize = 42 },
    core_validation_non_exhaustive => "core-validation-non-exhaustive" {},
    core_validation_non_exhaustive_node => "core-validation-non-exhaustive-node" { node: usize = 42 },
    core_validation_missing_origin => "core-validation-missing-origin" {},
    core_validation_missing_origin_node => "core-validation-missing-origin-node" { node: usize = 42 },
    core_validation_origin_depth => "core-validation-origin-depth" {},
    core_validation_origin_depth_node => "core-validation-origin-depth-node" { node: usize = 42 },
    core_validation_related_origin_source => "core-validation-related-origin-source" {},
    core_validation_related_origin_source_node => "core-validation-related-origin-source-node" { node: usize = 42 },
    core_validation_unadmitted_origin_source => "core-validation-unadmitted-origin-source" {},
    core_validation_unadmitted_origin_source_node => "core-validation-unadmitted-origin-source-node" { node: usize = 42 },
    core_validation_origin_range => "core-validation-origin-range" { start: usize = 3, end: usize = 9, length: usize = 6 },
    core_validation_origin_range_node => "core-validation-origin-range-node" { start: usize = 3, end: usize = 9, length: usize = 6, node: usize = 42 },
    core_validation_origin_code_point => "core-validation-origin-code-point" { offset: usize = 1 },
    core_validation_origin_code_point_node => "core-validation-origin-code-point-node" { offset: usize = 1, node: usize = 42 },
    core_validation_origin_text_limit => "core-validation-origin-text-limit" {},
    core_validation_origin_text_limit_node => "core-validation-origin-text-limit-node" { node: usize = 42 },
    core_validation_origin_index => "core-validation-origin-index" {},
    core_validation_origin_index_node => "core-validation-origin-index-node" { node: usize = 42 },
    core_validation_empty_recursive_group => "core-validation-empty-recursive-group" {},
    core_validation_empty_recursive_group_node => "core-validation-empty-recursive-group-node" { node: usize = 42 },
    core_validation_recursive_function_initializer => "core-validation-recursive-function-initializer" {},
    core_validation_recursive_function_initializer_node => "core-validation-recursive-function-initializer-node" { node: usize = 42 },
    core_validation_recursive_type_abstraction => "core-validation-recursive-type-abstraction" {},
    core_validation_recursive_type_abstraction_node => "core-validation-recursive-type-abstraction-node" { node: usize = 42 },
    core_validation_recursive_type_parameters => "core-validation-recursive-type-parameters" {},
    core_validation_recursive_type_parameters_node => "core-validation-recursive-type-parameters-node" { node: usize = 42 },
    core_validation_recursive_function_body => "core-validation-recursive-function-body" {},
    core_validation_recursive_function_body_node => "core-validation-recursive-function-body-node" { node: usize = 42 },
    core_validation_recursive_value_type => "core-validation-recursive-value-type" {},
    core_validation_recursive_value_type_node => "core-validation-recursive-value-type-node" { node: usize = 42 },
    core_validation_recursive_unknown_constructor => "core-validation-recursive-unknown-constructor" {},
    core_validation_recursive_unknown_constructor_node => "core-validation-recursive-unknown-constructor-node" { node: usize = 42 },
    core_validation_recursive_constructor_owner => "core-validation-recursive-constructor-owner" {},
    core_validation_recursive_constructor_owner_node => "core-validation-recursive-constructor-owner-node" { node: usize = 42 },
    core_validation_recursive_missing_payload => "core-validation-recursive-missing-payload" {},
    core_validation_recursive_missing_payload_node => "core-validation-recursive-missing-payload-node" { node: usize = 42 },
    core_validation_recursive_unexpected_payload => "core-validation-recursive-unexpected-payload" {},
    core_validation_recursive_unexpected_payload_node => "core-validation-recursive-unexpected-payload-node" { node: usize = 42 },
    core_validation_recursive_data_root => "core-validation-recursive-data-root" {},
    core_validation_recursive_data_root_node => "core-validation-recursive-data-root-node" { node: usize = 42 },
    core_validation_recursive_payload_call => "core-validation-recursive-payload-call" {},
    core_validation_recursive_payload_call_node => "core-validation-recursive-payload-call-node" { node: usize = 42 },
    core_validation_recursive_payload_form => "core-validation-recursive-payload-form" {},
    core_validation_recursive_payload_form_node => "core-validation-recursive-payload-form-node" { node: usize = 42 },
    core_validation_foreign_binder_arena => "core-validation-foreign-binder-arena" {},
    core_validation_foreign_binder_arena_node => "core-validation-foreign-binder-arena-node" { node: usize = 42 },
    core_validation_duplicate_binder => "core-validation-duplicate-binder" {},
    core_validation_duplicate_binder_node => "core-validation-duplicate-binder-node" { node: usize = 42 },
    core_validation_unknown_variable_binder => "core-validation-unknown-variable-binder" {},
    core_validation_unknown_variable_binder_node => "core-validation-unknown-variable-binder-node" { node: usize = 42 },
    core_validation_non_lexical_scope_owner => "core-validation-non-lexical-scope-owner" {},
    core_validation_non_lexical_scope_owner_node => "core-validation-non-lexical-scope-owner-node" { node: usize = 42 },
    core_validation_unknown_scope_owner => "core-validation-unknown-scope-owner" {},
    core_validation_unknown_scope_owner_node => "core-validation-unknown-scope-owner-node" { node: usize = 42 },
    core_validation_local_scope_type => "core-validation-local-scope-type" {},
    core_validation_local_scope_type_node => "core-validation-local-scope-type-node" { node: usize = 42 },
    core_validation_local_scope_effects => "core-validation-local-scope-effects" {},
    core_validation_local_scope_effects_node => "core-validation-local-scope-effects-node" { node: usize = 42 },
    core_validation_incomplete_scope_analysis => "core-validation-incomplete-scope-analysis" {},
    core_validation_incomplete_scope_analysis_node => "core-validation-incomplete-scope-analysis-node" { node: usize = 42 },
    core_validation_unbound_core_binder => "core-validation-unbound-core-binder" {},
    core_validation_unbound_core_binder_node => "core-validation-unbound-core-binder-node" { node: usize = 42 },
    core_validation_unbound_local_nominal => "core-validation-unbound-local-nominal" {},
    core_validation_unbound_local_nominal_node => "core-validation-unbound-local-nominal-node" { node: usize = 42 },
    core_validation_unexpected_local_scope => "core-validation-unexpected-local-scope" {},
    core_validation_unexpected_local_scope_node => "core-validation-unexpected-local-scope-node" { node: usize = 42 },
    core_validation_duplicate_local_scope => "core-validation-duplicate-local-scope" {},
    core_validation_duplicate_local_scope_node => "core-validation-duplicate-local-scope-node" { node: usize = 42 },
    core_validation_missing_local_scope => "core-validation-missing-local-scope" {},
    core_validation_missing_local_scope_node => "core-validation-missing-local-scope-node" { node: usize = 42 },
    core_validation_missing_capture_requirement => "core-validation-missing-capture-requirement" {},
    core_validation_missing_capture_requirement_node => "core-validation-missing-capture-requirement-node" { node: usize = 42 },
    core_validation_missing_root_requirements => "core-validation-missing-root-requirements" {},
    core_validation_missing_root_requirements_node => "core-validation-missing-root-requirements-node" { node: usize = 42 },
    core_validation_missing_node_requirements => "core-validation-missing-node-requirements" {},
    core_validation_missing_node_requirements_node => "core-validation-missing-node-requirements-node" { node: usize = 42 },
    /// The compiler stored a Core node from a different dialect than the selected program.
    core_validation_dialect => "core-validation-dialect" {},
    /// The compiler selected a root node that is not valid in this Core arena.
    core_validation_root => "core-validation-root" {},
    /// The compiler constructed a cycle in the Core expression graph.
    core_validation_cycle => "core-validation-cycle" {},
    /// The compiler retained a Core node that cannot be reached from the program root.
    core_validation_unreachable => "core-validation-unreachable" {},
    /// The compiler selected an implementation unavailable at this use.
    evidence_unavailable_implementation => "evidence-unavailable-implementation" {},
    /// The compiler ran out of resources for type checking and type construction.
    compiler_type_resources => "compiler-type-resources" {},
    /// The compiler ran out of resources for interface and constraint processing.
    compiler_constraint_resources => "compiler-constraint-resources" {},
    /// The compiler tried to lower effect syntax through its pure Core path.
    effect_core_unavailable => "effect-core-unavailable" {},
    /// Pattern coverage analysis reached the compiler's state limit.
    coverage_state_limit => "coverage-state-limit" {},
    /// The compiler could not complete pattern coverage analysis within its work resources.
    coverage_work_limit => "coverage-work-limit" {},
    /// The compiler has exhausted its Core arena identities.
    core_build_arena_id_exhausted => "core-build-arena-id-exhausted" {},
    /// The compiler has exhausted the node identities in this Core arena.
    core_build_node_id_exhausted => "core-build-node-id-exhausted" {},
    /// The compiler has exhausted its Core binder identities.
    core_build_binder_id_exhausted => "core-build-binder-id-exhausted" {},
    /// The compiler reserved the same resolved binder identity more than once.
    core_build_duplicate_binder_reservation => "core-build-duplicate-binder-reservation" {},
    /// The compiler tried to reserve resolved binder identities after Core binder construction had begun.
    core_build_binder_reservation_phase_started => "core-build-binder-reservation-phase-started" {},
    /// The compiler tried to construct a Core binder without reserving its resolved identity.
    core_build_unreserved_resolved_binder => "core-build-unreserved-resolved-binder" {},
    /// The compiler tried to construct a resolved Core binder more than once.
    core_build_duplicate_resolved_binder => "core-build-duplicate-resolved-binder" {},
    /// The compiler used a binder from a different Core arena.
    core_build_foreign_binder => "core-build-foreign-binder" {},
    /// A type exceeds the compiler's Core type nesting limit.
    core_build_type_depth_exceeded => "core-build-type-depth-exceeded" {},
    /// Core construction exhausted the compiler's type-work budget.
    core_build_type_work_exceeded => "core-build-type-work-exceeded" {},
    /// Source-origin metadata exceeds the compiler's Core nesting limit.
    core_build_origin_depth_exceeded => "core-build-origin-depth-exceeded" {},
    /// A pattern exceeds the compiler's Core pattern nesting limit.
    core_build_pattern_depth_exceeded => "core-build-pattern-depth-exceeded" {},
    /// The compiler encountered inconsistent state while rebuilding a Core payload.
    core_build_invalid_payload => "core-build-invalid-payload" {},
    /// The compiler requested a root node that does not belong to this Core arena.
    core_build_invalid_node_id => "core-build-invalid-node-id" {},
    /// These requirements have the same determining arguments but different dependent arguments.
    determination_requirement_conflict => "determination-requirement-conflict" {},
    /// These prerequisites have the same determining arguments but different dependent arguments.
    determination_prerequisite_conflict => "determination-prerequisite-conflict" {},
    /// The known key fixes an expected dependent tuple, which conflicts with the found tuple.
    determination_improvement_conflict => "determination-improvement-conflict" { key: &'a str = "(Unit)", expected: &'a str = "(Int)", found: &'a str = "(Bool)" },
    /// This earlier requirement fixes different dependent arguments for the same determining arguments.
    determination_earlier_requirement => "determination-earlier-requirement" {},
    /// This earlier prerequisite fixes different dependent arguments for the same determining arguments.
    determination_earlier_prerequisite => "determination-earlier-prerequisite" {},
    /// This source fixes the expected dependent tuple.
    determination_expected_source => "determination-expected-source" {},
    /// The determining side must contain at least one interface parameter.
    determination_empty_determinant => "determination-empty-determinant" {},
    /// The dependent side must contain at least one interface parameter.
    determination_empty_dependent => "determination-empty-dependent" {},
    /// An interface parameter cannot occur on both sides of a determination.
    determination_both_sides => "determination-both-sides" {},
    /// The determination must include every interface parameter.
    determination_omitted => "determination-omitted" {},
    /// This parameter is repeated on the same side of the determination.
    determination_repeated => "determination-repeated" {},
    /// Parameters on each side of a determination must follow their interface declaration order.
    determination_order => "determination-order" {},
    /// This parameter also occurs on the determining side.
    determination_key_occurrence => "determination-key-occurrence" {},
    /// This interface parameter is missing from the determination.
    determination_missing_parameter => "determination-missing-parameter" {},
    /// The parameter already occurs here on this side.
    determination_earlier_occurrence => "determination-earlier-occurrence" {},
    /// This preceding occurrence is out of declaration order with the highlighted parameter.
    determination_preceding_occurrence => "determination-preceding-occurrence" {},
    /// Method type parameters must be explicitly declared in the method's parameter list.
    method_implicit_parameters => "method-implicit-parameters" {},
    /// This method type must mention every interface parameter.
    method_missing_interface_parameter => "method-missing-interface-parameter" {},
    /// This method type must mention every determining interface parameter.
    method_missing_determinant => "method-missing-determinant" {},
    /// An interface parameter is declared here.
    interface_parameter_declaration => "interface-parameter-declaration" {},
    /// This required interface parameter is absent from the method type.
    missing_method_parameter => "missing-method-parameter" {},
    /// This dependent argument uses a type variable that does not occur in the implementation's determining arguments.
    impl_determination_coverage => "impl-determination-coverage" {},
    /// This dependent type variable is declared here.
    dependent_variable => "dependent-variable" {},
    /// This determining argument does not contain the dependent type variable.
    determinant_missing_variable => "determinant-missing-variable" {},
    /// A type variable in this requirement's selection key is absent from the definition's value type. It cannot be determined from that type.
    undetermined_parameter => "undetermined-parameter" {},
    /// This type parameter does not occur in the definition's value type.
    requirement_only_parameter => "requirement-only-parameter" {},
    /// This implementation can match the same interface application as an earlier available implementation.
    impl_overlap => "impl-overlap" {},
    /// These implementations can match the same determining arguments but require incompatible dependent arguments.
    impl_determination_conflict => "impl-determination-conflict" {},
    /// The earlier implementation is defined here.
    earlier_implementation => "earlier-implementation" {},
    /// This import made the earlier implementation available.
    earlier_implementation_import => "earlier-implementation-import" {},
    /// The later implementation is defined here.
    later_implementation => "later-implementation" {},
    /// This import made the later implementation available.
    later_implementation_import => "later-implementation-import" {},
    /// An interface application's argument count differs from its declaration.
    interface_argument_count => "interface-argument-count" { expected: usize = 2, found: usize = 1 },
    /// The interface parameter list fixes its arity.
    interface_parameters => "interface-parameters" {},
    /// No available evidence satisfies this interface requirement.
    constraint_unsatisfied => "constraint-unsatisfied" {},
    /// The types in this interface requirement are not sufficiently determined to select evidence.
    constraint_ambiguous => "constraint-ambiguous" {},
    /// Selecting evidence for this requirement returns to a requirement whose selection is already in progress.
    constraint_cycle => "constraint-cycle" {},
    /// This declaration introduced the interface requirement.
    selection_declaration => "selection-declaration" {},
    /// This import made the declaration available.
    selection_import => "selection-import" {},
    /// This interface participates in the failing evidence selection.
    selection_interface => "selection-interface" {},
    /// Evidence selection followed this implementation.
    selection_implementation => "selection-implementation" {},
    /// This implementation method supplies the selected evidence.
    selection_method => "selection-method" {},
    /// This import made the selected implementation available.
    selection_implementation_import => "selection-implementation-import" {},
    /// An implementation must be owned through its interface or selection key.
    impl_orphan => "impl-orphan" {},
    /// The interface selected by an orphan implementation is foreign.
    impl_foreign_interface => "impl-foreign-interface" {},
    /// This public definition exposes a private interface in its requirements.
    constraint_private_interface => "constraint-private-interface" {},
    /// A public implementation must use public interfaces both for its head and for its prerequisites.
    impl_private_interface => "impl-private-interface" {},
    /// This exact interface requirement is declared more than once.
    duplicate_requirement => "duplicate-requirement" {},
    /// This interface is declared private here.
    private_interface_declaration => "private-interface-declaration" {},
    /// The earlier identical requirement is here.
    earlier_requirement => "earlier-requirement" {},
    /// An implementation's selection key cannot consist only of bare type variables.
    impl_variable_head => "impl-variable-head" {},
    /// This prerequisite uses a type variable that does not occur in the implementation head.
    impl_prerequisite_variable => "impl-prerequisite-variable" {},
    /// This generic prerequisite does not have a strictly smaller selection key than the implementation head.
    impl_prerequisite_decrease => "impl-prerequisite-decrease" {},
    /// This is the interface being implemented.
    impl_selected_interface => "impl-selected-interface" {},
    /// Every prerequisite type variable must occur in this implementation head.
    impl_head_variables => "impl-head-variables" {},
    /// Each prerequisite key argument must equal or be a strict syntactic subterm of its corresponding head argument, with at least one strict decrease.
    impl_head_decrease => "impl-head-decrease" {},
    /// An interface method must have a function type with a top-level arrow.
    interface_method_function => "interface-method-function" {},
    /// This method signature is declared here.
    interface_method_declaration => "interface-method-declaration" {},
    /// This implementation does not supply a required interface method.
    impl_missing_method => "impl-missing-method" {},
    /// This implementation supplies the same interface method more than once.
    impl_duplicate_method => "impl-duplicate-method" {},
    /// This method is not declared by the implemented interface.
    impl_extra_method => "impl-extra-method" {},
    /// The implemented interface is declared here.
    impl_interface => "impl-interface" {},
    /// This evidence declaration needs an active local nominal type in its selection key: the determinant arguments, or all arguments when there is no determination edge.
    evidence_local_key => "evidence-local-key" {},
    /// An active evidence declaration already supplies this exact interface application.
    evidence_duplicate => "evidence-duplicate" {},
    /// These evidence declarations have the same determining arguments but different dependent arguments.
    evidence_determination_conflict => "evidence-determination-conflict" {},
    /// This evidence declaration does not supply a required interface method.
    evidence_missing_method => "evidence-missing-method" {},
    /// This evidence declaration supplies the same method more than once.
    evidence_duplicate_method => "evidence-duplicate-method" {},
    /// This method does not belong to the interface supplied by this evidence declaration.
    evidence_extra_method => "evidence-extra-method" {},
    /// The earlier active evidence declaration is here.
    evidence_earlier => "evidence-earlier" {},
    /// This interface method must be supplied.
    evidence_required_method => "evidence-required-method" {},
    /// This method was already supplied here.
    evidence_earlier_method => "evidence-earlier-method" {},
    /// The supplied interface is declared here.
    evidence_interface => "evidence-interface" {},
    /// A recursive call changes its required instantiation.
    type_polymorphic_recursion => "type-polymorphic-recursion" { expected: &'a str = "A", found: &'a str = "(A, A)" },
    /// The recursive function keeps one instantiation.
    recursive_function => "recursive-function" {},
    /// The application supplies a recursive argument.
    recursive_application => "recursive-application" {},
    /// Ordinary handlers require an explicitly present exact effect instance.
    missing_handled_effect => "missing-handled-effect" {},
    /// Ash cannot prove that this continuation can be discarded without skipping required completion.
    discard_unknown => "discard-unknown" {},
    /// This discard would skip a clause that still requires completion.
    discard_clause => "discard-clause" {},
    /// This discard would skip a cleanup action that must complete.
    discard_cleanup => "discard-cleanup" {},
    /// This request or call can capture the continuation.
    discard_request => "discard-request" {},
    /// This clause still requires completion.
    discard_clause_owner => "discard-clause-owner" {},
    /// This cleanup action must complete.
    discard_cleanup_owner => "discard-cleanup-owner" {},
    /// The cleanup effects do not satisfy the required effect row.
    effect_row_cleanup_requirement => "effect-row-cleanup-requirement" {},
    /// Ash cannot determine the effect row remaining after this handler removes its exact effect instance.
    effect_row_removal => "effect-row-removal" {},
    /// This expression combines effect rows that have no most general union.
    effect_row_union => "effect-row-union" {},
    /// This function would require an infinite effect row.
    effect_row_infinite_function => "effect-row-infinite-function" {},
    /// This function body's effects do not match its function type.
    effect_row_function_mismatch => "effect-row-function-mismatch" {},
    /// This function body requests effects outside its declared effect row.
    effect_row_function_outside_declared => "effect-row-function-outside-declared" {},
    /// Ash cannot infer a most general effect row for this cleanup action.
    effect_row_cleanup_inference => "effect-row-cleanup-inference" {},
    /// This cleanup action requests effects outside its expected effect row.
    effect_row_cleanup_outside_expected => "effect-row-cleanup-outside-expected" {},
    /// The effects of this discard do not match the cleanup actions it owns.
    effect_row_discard_cleanup => "effect-row-discard-cleanup" {},
    /// An effect instance has the wrong number of type arguments.
    handler_argument_count => "handler-argument-count" {},
    /// An operation identity belongs to another effect declaration.
    handler_operation_owner => "handler-operation-owner" {},
    /// A handler has the wrong number of clauses.
    handler_clause_count => "handler-clause-count" {},
    /// An operation identity is outside its effect declaration.
    handler_operation_index => "handler-operation-index" {},
    /// A handler repeats an operation clause.
    handler_duplicate_operation => "handler-duplicate-operation" {},
    /// All equations must consume the same positive number of patterns.
    equation_pattern_count => "equation-pattern-count" {},
    /// An equation consumes more arrows than its declared type provides.
    equation_declared_arrows => "equation-declared-arrows" {},
    /// Hooks and registrations require one declared endomorphic publish operation.
    hook_api => "hook-api" {},
    /// An anonymous function lacks an expected function type.
    function_needs_context => "function-needs-context" {},
    /// An unannotated binding requires its initializer to infer a type.
    function_context_binding => "function-context-binding" {},
    /// A program result requires type synthesis.
    function_context_result => "function-context-result" {},
    /// An application requires the function expression to infer a type.
    function_context_application => "function-context-application" {},
    /// An operator requires the operand to infer a type.
    function_context_operator => "function-context-operator" {},
    /// The general checking rule compares required and synthesized types.
    type_mismatch => "type-mismatch" { expected: &'a str = "Int", found: &'a str = "Bool" },
    /// An outward type or effect row retains a local nominal identity.
    local_nominal_escape => "local-nominal-escape" {},
    /// The scope that owns the escaping local nominal identity.
    local_nominal_scope => "local-nominal-scope" {},
    /// An outward value, type or effect retains a resource dependency.
    resource_escape => "resource-escape" {},
    /// The acquisition that owns the escaping resource dependency.
    resource_acquisition => "resource-acquisition" {},
    /// A recursive function member requires a direct anonymous function.
    recursion_initializer => "recursion-initializer" {},
    /// A recursive data member requires a constructor root.
    recursion_root => "recursion-root" {},
    /// The enclosing simultaneous recursive group.
    recursion_group => "recursion-group" {},
    /// The recursive member's declared type.
    recursion_member_annotation => "recursion-member-annotation" {},
    /// Newtype representations form a forbidden cycle.
    newtype_representation_cycle => "newtype-representation-cycle" {},
    /// A declaration participating in the representation cycle.
    newtype_cycle_member => "newtype-cycle-member" {},
    /// Discard removes an interpreter required by cleanup.
    cleanup_context => "cleanup-context" {},
    /// The cleanup action that requires the abandoned interpreter.
    cleanup_required_action => "cleanup-required-action" {},
    /// The handler removed by discard.
    cleanup_abandoned_handler => "cleanup-abandoned-handler" {},
    /// First-order inference would construct an infinite type.
    type_infinite => "type-infinite" {},
    /// Inference cannot determine a complete type at this source location.
    type_ambiguous => "type-ambiguous" {},
    /// A recursive occurrence crosses a forcing or transporting expression.
    recursion_unguarded_use => "recursion-unguarded-use" {},
    /// A path can finish without consuming its continuation.
    continuation_not_consumed => "continuation-not-consumed" {},
    /// A path consumes its continuation more than once.
    continuation_already_consumed => "continuation-already-consumed" {},
    /// A nested scope captures an enclosing clause's completion capability.
    continuation_capture => "continuation-capture" {},
    /// A pattern disagrees with the type of the value being matched.
    pattern_type_mismatch => "pattern-type-mismatch" { expected: &'a str = "Bool" },
    /// A constructor occurrence has the wrong payload shape.
    pattern_constructor_payload => "pattern-constructor-payload" {},
    /// A constructor pattern names another nominal type.
    pattern_constructor_owner => "pattern-constructor-owner" {},
    /// An uncovered value proves that a binding pattern can fail.
    pattern_refutable_binding => "pattern-refutable-binding" { witness: &'a str = "false" },
    /// An uncovered value proves that a function domain pattern can fail.
    pattern_refutable_function => "pattern-refutable-function" { witness: &'a str = "false" },
    /// An uncovered value proves that an operation clause pattern can fail.
    pattern_refutable_handler => "pattern-refutable-handler" { witness: &'a str = "false" },
    /// A match or equation group leaves a value uncovered.
    coverage_non_exhaustive => "coverage-non-exhaustive" { witness: &'a str = "false" },
    /// A match contains no arms.
    coverage_empty_match => "coverage-empty-match" {},
    /// A case has no input not already covered by preceding cases.
    coverage_redundant_case => "coverage-redundant-case" {},
    /// A finite compiler identifier space cannot represent another identity.
    resolve_identity_exhausted => "resolve-identity-exhausted" { space: crate::resolve::ResolveIdentitySpace = crate::resolve::ResolveIdentitySpace::TermBinder },
    /// A written row repeats a canonically identical effect instance.
    resolve_duplicate_effect => "resolve-duplicate-effect" {},
    /// The first written occurrence of the same exact instance.
    first_effect_instance => "first-effect-instance" {},
    /// An operation signature requires a pure outer arrow, with no explicit row.
    resolve_operation_shape => "resolve-operation-shape" {},
    /// Source implementations/evidence cannot introduce builtin resource providers.
    resolve_sealed_provider => "resolve-sealed-provider" {},
    /// Acquisition requires the corresponding direct builtin import.
    resolve_builtin_required => "resolve-builtin-required" { builtin: &'a str = "@builtin.cell" },
    /// Resume or discard occurs outside an operation clause.
    resolve_continuation_outside => "resolve-continuation-outside" { operation: &'a str = "resume" },
    /// An interface occupies a value-type position.
    resolve_type_kind => "resolve-type-kind" { name: &'a str = "Marker" },
    /// An interface position contains a known non-interface name.
    resolve_interface_kind => "resolve-interface-kind" { name: &'a str = "Thing" },
    /// An effect position contains a known non-effect name.
    resolve_effect_kind => "resolve-effect-kind" { name: &'a str = "Thing" },
    /// An implicit parameter has incompatible type and row-tail roles.
    resolve_mixed_type_row_roles => "resolve-mixed-type-row-roles" { name: &'a str = "R" },
    /// The occurrence uses a name in an incompatible role.
    incompatible_name_role => "incompatible-name-role" {},
    /// A function body does not match its required result type.
    type_definition_result => "type-definition-result" { expected: &'a str = "Int", found: &'a str = "Bool" },
    /// A primitive operand must be Int.
    type_operator_operand => "type-operator-operand" { found: &'a str = "Bool" },
    /// An argument does not match the function's domain.
    type_argument => "type-argument" { expected: &'a str = "Int", found: &'a str = "Bool" },
    /// An application's function position has a non-function type.
    type_not_applicable => "type-not-applicable" { found: &'a str = "Int" },
    /// An equation's signature provides no function domain.
    type_equation_signature => "type-equation-signature" { found: &'a str = "Int" },
    /// The type at the causal source occurrence.
    type_found => "type-found" { found: &'a str = "Bool" },
    /// The signature requires this function result type.
    type_result_annotation => "type-result-annotation" { expected: &'a str = "Int" },
    /// The primitive operator requires integer operands.
    type_operator_requirement => "type-operator-requirement" {},
    /// The function requires this argument type.
    type_function_domain => "type-function-domain" { expected: &'a str = "Int" },
    /// The containing application supplies this argument or requires a function.
    type_application => "type-application" {},
    /// The equation head requires a function signature.
    type_equation_head => "type-equation-head" {},
    /// The entry module must supply a local entry point.
    entry_missing_main => "entry-missing-main" {},
    /// The entry point cannot quantify type parameters.
    entry_polymorphic => "entry-polymorphic" {},
    /// The entry point must accept Unit.
    entry_domain => "entry-domain" {},
    /// The entry invocation cannot require effects from its caller.
    entry_effects => "entry-effects" {},
    /// The entry result must be closed, including nested effect-row tails.
    entry_open_result => "entry-open-result" {},
    /// The entry caller supplies no interface evidence.
    entry_constrained => "entry-constrained" {},
    /// The source module where a local main is required.
    entry_module => "entry-module" {},
    /// The local main declaration that violates the entry contract.
    entry_main => "entry-main" {},
    /// A value-type position contains a type constructor or effect row.
    kind_expected_type => "kind-expected-type" { found: &'a str = "Type -> Type" },
    /// A type application applies something without an arrow kind.
    kind_not_applicable => "kind-not-applicable" { found: &'a str = "Type" },
    /// A type, interface or effect argument has the wrong kind.
    kind_argument => "kind-argument" { expected: &'a str = "Type -> Type", found: &'a str = "Type" },
    /// The kind of the causal source occurrence.
    kind_found => "kind-found" { found: &'a str = "Type" },
    /// A declaration fixes the actual kind of the source occurrence.
    kind_found_declaration => "kind-found-declaration" { found: &'a str = "Type" },
    /// A declaration determines the required argument kind.
    kind_required_declaration => "kind-required-declaration" { expected: &'a str = "Type -> Type" },
    /// An ordinary type lookup failed.
    resolve_unknown_type => "resolve-unknown-type" { name: &'a str = "Missing" },
    /// An effect-row parameter lookup failed.
    resolve_unknown_row_parameter => "resolve-unknown-row-parameter" { name: &'a str = "Missing" },
    /// A determination names no parameter of its owning interface.
    resolve_unknown_interface_parameter => "resolve-unknown-interface-parameter" { name: &'a str = "Missing" },
    /// No constructor is available in this scope.
    resolve_unknown_constructor => "resolve-unknown-constructor" { name: &'a str = "Missing" },
    /// No interface is available in this scope.
    resolve_unknown_interface => "resolve-unknown-interface" { name: &'a str = "Missing" },
    /// No effect is available in this scope.
    resolve_unknown_effect => "resolve-unknown-effect" { name: &'a str = "Missing" },
    /// The selected module exports no effect with this name.
    resolve_unexported_effect => "resolve-unexported-effect" { name: &'a str = "Missing" },
    /// Ordinary term lookup found no binding.
    resolve_unknown_term => "resolve-unknown-term" { name: &'a str = "missing" },
    /// The selected effect declares no operation with this spelling.
    resolve_unknown_operation => "resolve-unknown-operation" { name: &'a str = "missing" },
    /// A checked name occurrence carrying an unresolved lookup.
    unresolved_name => "unresolved-name" {},
    /// A term or operation name conflicts in its declaration scope.
    resolve_duplicate_global => "resolve-duplicate-global" { name: &'a str = "value" },
    /// Nominal types, interfaces and effects share a declaration namespace.
    resolve_duplicate_type => "resolve-duplicate-type" { name: &'a str = "Thing" },
    /// Two constructors have the same name.
    resolve_duplicate_constructor => "resolve-duplicate-constructor" { name: &'a str = "Same" },
    /// Two qualified imports bind the same alias.
    resolve_duplicate_alias => "resolve-duplicate-alias" { name: &'a str = "Cell" },
    /// A type parameter conflicts with an earlier parameter in scope.
    resolve_duplicate_parameter => "resolve-duplicate-parameter" { name: &'a str = "A" },
    /// A pattern binds one name twice.
    resolve_duplicate_binder => "resolve-duplicate-binder" { name: &'a str = "value" },
    /// A recursive group contains two members with the same name.
    resolve_duplicate_recursive_member => "resolve-duplicate-recursive-member" { name: &'a str = "same" },
    /// The conflicting occurrence of a declaration name.
    duplicate_name => "duplicate-name" {},
    /// The earlier declaration causing the conflict.
    first_declaration => "first-declaration" {},
    /// The complete earlier global definition, distinct from its name site.
    first_definition => "first-definition" {},
    /// The equation and its declared signature have different names.
    resolve_equation_name => "resolve-equation-name" { name: &'a str = "other", expected: &'a str = "value" },
    /// A newtype constructor must repeat the type's name.
    resolve_newtype_name => "resolve-newtype-name" { name: &'a str = "Other", expected: &'a str = "Wrapper" },
    /// An explicit parameter has no occurrence in its declaration header.
    resolve_unused_parameter => "resolve-unused-parameter" { name: &'a str = "A" },
    /// A file-wide binding conflicts with an import or existing namespace entry.
    resolve_import_conflict => "resolve-import-conflict" { name: &'a str = "Cell" },
    /// An opaque type does not expose its constructor to this module.
    resolve_opaque_constructor => "resolve-opaque-constructor" { name: &'a str = "Box" },
    /// The defining module retained a private declaration.
    resolve_private_export => "resolve-private-export" { name: &'a str = "hidden" },
    /// An import or qualified reference found no available declaration.
    resolve_missing_export => "resolve-missing-export" { name: &'a str = "absent" },
    /// A qualified reference names no imported module alias.
    resolve_missing_module_alias => "resolve-missing-module-alias" { name: &'a str = "Missing" },
    /// A name differs from the spelling required by its declaration.
    incorrect_name => "incorrect-name" {},
    /// A parameter is absent from the declaration header.
    unused_parameter => "unused-parameter" {},
    /// A binding conflicts with a file-wide name.
    conflicting_binding => "conflicting-binding" {},
    /// An imported name is unavailable at this occurrence.
    inaccessible_name => "inaccessible-name" {},
    /// The declaration that determines the required spelling.
    required_name_declaration => "required-name-declaration" {},
    /// The original private or opaque declaration.
    inaccessible_declaration => "inaccessible-declaration" {},
    /// A retained canonical module path has no parent directory.
    module_missing_parent => "module-missing-parent" {},
    /// A projected import has no module-name segments.
    module_missing_segments => "module-missing-segments" {},
    /// Syntax-recovery information crossed the checked projection boundary.
    projection_recovery => "projection-recovery" { path: &'a str = "source.ash" },
    /// A retained concrete-syntax invariant failed.
    projection_malformed => "projection-malformed" { path: &'a str = "source.ash", cause: crate::parser::InternalReason = crate::parser::InternalReason::UnexpectedShape },
    /// Span construction failed after source admission.
    source_unrepresentable_span => "source-unrepresentable-span" { path: &'a Path = Path::new("source.ash") },
    /// Source identity allocation is exhausted.
    source_ids => "source-ids" { path: &'a Path = Path::new("source.ash") },
    /// The display path exceeds source model limits.
    source_path_limit => "source-path-limit" { path: &'a Path = Path::new("source.ash") },
    /// Source text exceeds the representable byte length.
    source_text_limit => "source-text-limit" { path: &'a Path = Path::new("source.ash") },
    /// The line count exceeds the representable range.
    source_line_limit => "source-line-limit" { path: &'a Path = Path::new("source.ash") },
    /// A line exceeds the representable column range.
    source_column_limit => "source-column-limit" { path: &'a Path = Path::new("source.ash") },
    /// An internal byte range exceeds source bounds.
    source_range => "source-range" { path: &'a Path = Path::new("source.ash"), start: usize = 3, end: usize = 9, length: usize = 4 },
    /// An internal span belongs to another source.
    source_foreign_span => "source-foreign-span" { path: &'a Path = Path::new("source.ash"), expected: usize = 1, found: usize = 2 },
    /// An internal offset exceeds source bounds.
    source_offset => "source-offset" { path: &'a Path = Path::new("source.ash"), offset: usize = 9, length: usize = 4 },
    /// An internal offset is not a UTF-8 boundary.
    source_code_point => "source-code-point" { path: &'a Path = Path::new("source.ash"), offset: usize = 3 },
    /// The source line index is internally inconsistent.
    source_line_state => "source-line-state" { path: &'a Path = Path::new("source.ash") },
    /// A shared localized explanation of a retained I/O category.
    io_cause => "io-cause" { kind: std::io::ErrorKind = std::io::ErrorKind::PermissionDenied },
    /// A configured root cannot be resolved, with a retained I/O cause.
    module_root_io => "module-root-io" { path: &'a Path = Path::new("library"), root: &'a str = "std", kind: std::io::ErrorKind = std::io::ErrorKind::PermissionDenied },
    /// A configured root could not be admitted as a directory.
    module_root_unavailable => "module-root-unavailable" { path: &'a Path = Path::new("library"), root: &'a str = "std" },
    /// Resource exhaustion in a specific module-loader operation.
    module_resource => "module-resource" { resource: crate::module::ModuleResource = crate::module::ModuleResource::Sources },
    /// A configured root attempts to replace a compiler-owned root.
    module_reserved_root => "module-reserved-root" { root: &'a str = "builtin" },
    /// One root name appears more than once in the invocation.
    module_duplicate_root => "module-duplicate-root" { root: &'a str = "std" },
    /// A root name fails the existing identifier check.
    module_invalid_root_name => "module-invalid-root-name" { root: &'a str = "Bad" },
    /// An absolute import selects an unconfigured root.
    module_unknown_root => "module-unknown-root" { root: &'a str = "std" },
    /// No compiler-owned module matches the selected builtin path.
    module_unknown_builtin => "module-unknown-builtin" {},
    /// Canonicalization reported that the imported file does not exist.
    module_not_found => "module-not-found" { path: &'a Path = Path::new("missing.ash") },
    /// An import reaches a module active in the current traversal.
    module_import_cycle => "module-import-cycle" { path: &'a Path = Path::new("entry.ash") },
    /// A canonical target lies outside at least one retained owning root.
    module_path_escape => "module-path-escape" { path: &'a Path = Path::new("outside.ash") },
    /// Compiler protection for syntax nesting stopped parsing.
    syntax_depth => "syntax-depth" { path: &'a str = "source.ash", limit: usize = 128 },
    /// Cumulative retained syntax work reached the compiler budget.
    syntax_work => "syntax-work" { path: &'a str = "source.ash", limit: usize = 1_500_000 },
    /// An input read failure with its native target path and I/O category.
    input_read => "input-read" { path: &'a Path = Path::new("input.ash"), kind: std::io::ErrorKind = std::io::ErrorKind::NotFound },
    /// Input bytes do not encode UTF-8 source text.
    input_invalid_utf8 => "input-invalid-utf8" { path: &'a Path = Path::new("input.ash") },
    /// The import that selected a failed target.
    import_target => "import-target" {},
    /// The operator needs a right operand.
    parse_operand => "parse-operand" {},
    /// This opening parenthesis has no matching ).
    parse_unclosed_group => "parse-unclosed-group" {},
    /// Equality comparisons cannot be chained without parentheses.
    parse_repeated_equality => "parse-repeated-equality" {},
    /// A recursive binding member is required here.
    parse_recursive_member => "parse-recursive-member" {},
    /// and is allowed only within a recursive binding group.
    parse_unexpected_and => "parse-unexpected-and" {},
    /// Ash does not support semicolons.
    parse_semicolon => "parse-semicolon" {},
    /// This token is not allowed at this grammar position.
    parse_unexpected_token => "parse-unexpected-token" {},
    /// Parsing continues from this position.
    parse_recovery => "parse-recovery" {},
    /// Parsing resumes at this boundary.
    parse_synchronization => "parse-synchronization" {},
    /// A binding initializer disagrees with its annotation.
    binding_initializer => "binding-initializer" { expected: &'a str = "expected", found: &'a str = "found" },
    /// The initializer's actual type.
    initializer => "initializer" { found: &'a str = "found" },
    /// The annotated type requirement.
    binding_annotation => "binding-annotation" { expected: &'a str = "expected" },
    /// The grammar form required at this position.
    parse_expected => "parse-expected" { expected: crate::parser::ExpectedForm = crate::parser::ExpectedForm::Expression },
    /// The token category or fixed spelling encountered by the parser.
    parse_found => "parse-found" { found: crate::parser::FoundToken = crate::parser::FoundToken::EndOfFile },
    /// A carriage return without its required line feed.
    lex_bare_carriage_return => "lex-bare-carriage-return" {},
    /// An excluded byte order mark.
    lex_byte_order_mark => "lex-byte-order-mark" {},
    /// Non-ASCII identifier characters.
    lex_unicode_identifier => "lex-unicode-identifier" {},
    /// Comment syntax is excluded.
    lex_comment => "lex-comment" {},
    /// Negative literal syntax is excluded.
    lex_negative_literal => "lex-negative-literal" {},
    /// An invalid decimal spelling.
    lex_invalid_integer_literal => "lex-invalid-integer-literal" {},
    /// An invalid identifier spelling.
    lex_invalid_identifier => "lex-invalid-identifier" {},
    /// A character with no token interpretation.
    lex_unknown_character => "lex-unknown-character" {},
}

/// A defect in an embedded catalogue or its message contract.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CatalogueError {
    /// Invalid resource syntax or duplicate definitions.
    InvalidResource,
    /// A required message or its value is absent.
    MissingMessage,
    /// The template could not format the declared arguments.
    InvalidArguments,
}

/// An initialized compile-time formatter for one embedded locale.
pub struct Catalogue {
    bundle: FluentBundle<FluentResource>,
}

impl Catalogue {
    /// Loads one embedded catalogue, without accessing the filesystem.
    ///
    /// # Errors
    /// Returns a catalogue defect; callers must retain the original diagnostic.
    pub fn new(locale: Locale) -> Result<Self, CatalogueError> {
        let (name, source) = match locale {
            Locale::English => ("en-US", include_str!("../locales/en-US.ftl")),
            Locale::Bulgarian => ("bg", include_str!("../locales/bg.ftl")),
        };
        let lang = name.parse().map_err(|_| CatalogueError::InvalidResource)?;
        let resource = FluentResource::try_new(source.to_owned())
            .map_err(|_| CatalogueError::InvalidResource)?;
        let mut bundle = FluentBundle::new(vec![lang]);
        // Both retained locales are left-to-right. Source values are kept
        // verbatim; later terminal escaping belongs to the presentation layer.
        bundle.set_use_isolating(false);
        bundle
            .add_resource(resource)
            .map_err(|_| CatalogueError::InvalidResource)?;
        Ok(Self { bundle })
    }

    /// Formats a checked message using retained diagnostic facts.
    ///
    /// # Errors
    /// Returns a missing template or argument defect, never a generic message.
    pub fn format(&self, message: &Message<'_>) -> Result<String, CatalogueError> {
        let (key, values) = message.parts();
        let mut args = FluentArgs::new();
        for (name, value) in values {
            args.set(*name, value.as_ref());
        }
        let message = self
            .bundle
            .get_message(key)
            .ok_or(CatalogueError::MissingMessage)?;
        let pattern = message.value().ok_or(CatalogueError::MissingMessage)?;
        let mut errors = Vec::new();
        let text = self
            .bundle
            .format_pattern(pattern, Some(&args), &mut errors);
        if errors.is_empty() {
            Ok(text.into_owned())
        } else {
            Err(CatalogueError::InvalidArguments)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fluent_syntax::ast::{Entry, Expression, InlineExpression, Pattern, PatternElement};
    use std::collections::{BTreeMap, BTreeSet};

    fn variables<'a>(
        pattern: &'a Pattern<&'a str>,
        patterns: &BTreeMap<&'a str, &'a Pattern<&'a str>>,
        active: &mut BTreeSet<&'a str>,
        result: &mut BTreeSet<&'a str>,
    ) -> bool {
        for element in &pattern.elements {
            match element {
                PatternElement::TextElement { .. } => {}
                PatternElement::Placeable {
                    expression: Expression::Inline(InlineExpression::StringLiteral { .. }),
                } => {}
                PatternElement::Placeable {
                    expression: Expression::Inline(InlineExpression::VariableReference { id }),
                } => {
                    result.insert(id.name);
                }
                PatternElement::Placeable {
                    expression:
                        Expression::Inline(InlineExpression::MessageReference {
                            id,
                            attribute: None,
                        }),
                } => {
                    let Some(referenced) = patterns.get(id.name) else {
                        return false;
                    };
                    if !active.insert(id.name) {
                        return false;
                    }
                    if !variables(referenced, patterns, active, result) {
                        return false;
                    }
                    active.remove(id.name);
                }
                PatternElement::Placeable {
                    expression: Expression::Select { selector, variants },
                } => {
                    if let InlineExpression::VariableReference { id } = selector {
                        result.insert(id.name);
                    } else {
                        return false;
                    }
                    for variant in variants {
                        if !variables(&variant.value, patterns, active, result) {
                            return false;
                        }
                    }
                }
                _ => {
                    return false;
                }
            }
        }
        true
    }

    fn contract_matches(source: &str) -> bool {
        let Ok(resource) = fluent_syntax::parser::parse(source) else {
            return false;
        };
        let expected: BTreeMap<_, BTreeSet<_>> = Message::examples()
            .into_iter()
            .map(|message| {
                let (key, values) = message.parts();
                (key, values.iter().map(|(name, _)| *name).collect())
            })
            .collect();
        let mut patterns = BTreeMap::new();
        for entry in &resource.body {
            if let Entry::Message(message) = entry {
                let Some(pattern) = &message.value else {
                    return false;
                };
                if !message.attributes.is_empty() {
                    return false;
                }
                if patterns.insert(message.id.name, pattern).is_some() {
                    return false;
                }
            }
        }
        let mut actual = BTreeMap::new();
        for (&key, pattern) in &patterns {
            let mut names = BTreeSet::new();
            if !variables(pattern, &patterns, &mut BTreeSet::from([key]), &mut names) {
                return false;
            }
            actual.insert(key, names);
        }
        actual == expected
    }

    #[test]
    fn both_catalogues_cover_every_retained_message_and_argument() {
        assert!(contract_matches(include_str!("../locales/en-US.ftl")));
        assert!(contract_matches(include_str!("../locales/bg.ftl")));
        for locale in [Locale::English, Locale::Bulgarian] {
            let catalogue = Catalogue::new(locale).unwrap();
            for message in Message::examples() {
                assert!(!catalogue.format(&message).unwrap().is_empty());
            }
        }
    }

    #[test]
    fn catalogue_contract_detects_missing_extra_and_misspelled_arguments() {
        let english = include_str!("../locales/en-US.ftl");
        assert!(!contract_matches(&english.replace("{ $expected }", "Bool")));
        assert!(!contract_matches(&english.replace("$expected", "$expectd")));
        assert!(!contract_matches(&format!(
            "{english}\nextra = Extra message.\n"
        )));
        assert!(!contract_matches(
            &english.replace("initializer =", "unused =")
        ));
    }

    #[test]
    fn catalogue_references_preserve_transitive_arguments_and_reject_cycles() {
        let english = include_str!("../locales/en-US.ftl");
        assert!(contract_matches(english));
        assert!(!contract_matches(
            &english.replace("{ io-cause }", "{ missing-cause }")
        ));
        assert!(!contract_matches(
            &english.replace("{ io-cause }", "{ input-read }")
        ));
        assert!(!contract_matches(
            &english.replace("{ io-cause }", "{ module-root-io }")
        ));
        assert!(!contract_matches(&english.replace("$kind", "$unknown")));
        assert!(!contract_matches(
            &english.replace("{ io-cause }", "unavailable")
        ));
    }

    #[test]
    fn wording_changes_preserve_message_arguments_and_machine_facts() {
        let message = Message::initializer("Int");
        let before = message.parts();
        let text = include_str!("../locales/en-US.ftl")
            .replace("This initializer has type", "The initial value has type");
        assert!(contract_matches(&text));
        let mut bundle = FluentBundle::new(vec!["en-US".parse().unwrap()]);
        bundle.set_use_isolating(false);
        bundle
            .add_resource(FluentResource::try_new(text).unwrap())
            .unwrap();
        assert_eq!(
            Catalogue { bundle }.format(&message).unwrap(),
            "The initial value has type `Int`."
        );
        assert_eq!(message.parts(), before);
    }
}
