//! Coordinates for immutable checked foreign builtins, not authority tokens.
//!
//! A consumer must additionally authenticate the original BuiltinForeign module,
//! declaration shapes, ordered formals and provenance. Matching these numbers or
//! a string in ordinary source cannot grant host or checked codec authority.

use super::{FOREIGN_SOURCE, ModuleFailure, ModuleReason, ModuleResource};
use crate::{
    source::{ByteRange, SourceFile, Span},
    surface::{
        SurfaceDeclarationIndex, SurfaceEffectDeclaration, SurfaceModule, SurfaceName,
        SurfaceTypeParameter,
    },
    syntax_resource::{ResourceFailure, SyntaxBudget},
};

/// The only compiler-owned foreign host effect; it has no request operations.
pub(crate) const FOREIGN_NATIVE_HOST_LOCAL: u32 = 0;

/// Appended nominal roles in the immutable Foreign module.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub(crate) enum ForeignCheckedNominalRole {
    NativeStatus = 6,
    NativeFact = 7,
    DiagnosticAbsence = 8,
    Diagnostic = 9,
    BoundaryRecord = 10,
    BoundaryFailure = 11,
    CheckedCall = 12,
    FinishResult = 13,
    CheckedFinish = 14,
    CheckedCompletion = 15,
    CheckedScope = 16,
    ViolationCause = 17,
}

impl ForeignCheckedNominalRole {
    pub(crate) const fn local(self) -> u32 {
        self as u32
    }

    pub(crate) const fn constructor_count(self) -> usize {
        match self {
            Self::NativeStatus | Self::Diagnostic | Self::FinishResult | Self::CheckedScope => 2,
            Self::NativeFact => 4,
            Self::DiagnosticAbsence => 6,
            Self::BoundaryRecord => 1,
            Self::BoundaryFailure
            | Self::CheckedCall
            | Self::CheckedFinish
            | Self::CheckedCompletion => 3,
            Self::ViolationCause => 5,
        }
    }

    #[cfg(test)]
    const fn declaration(self) -> &'static str {
        match self {
            Self::NativeStatus => "pub type NativeStatus =",
            Self::NativeFact => "pub type NativeFact =",
            Self::DiagnosticAbsence => "pub type DiagnosticAbsence =",
            Self::Diagnostic => "pub type Diagnostic =",
            Self::BoundaryRecord => "pub type BoundaryRecord =",
            Self::BoundaryFailure => "pub type BoundaryFailure =",
            Self::CheckedCall => "pub type CheckedCall<T> =",
            Self::FinishResult => "pub type FinishResult<E> =",
            Self::CheckedFinish => "pub type CheckedFinish<S, E> =",
            Self::CheckedCompletion => "pub type CheckedCompletion<E> =",
            Self::CheckedScope => "pub type CheckedScope<A, I, E> =",
            Self::ViolationCause => "pub type ViolationCause =",
        }
    }
}

fn complete_source(source: Span) -> bool {
    source.range().start() == 0
        && usize::try_from(source.range().end()).ok() == Some(FOREIGN_SOURCE.len())
}

fn range(start: usize, end: usize) -> Option<ByteRange> {
    ByteRange::new(u32::try_from(start).ok()?, u32::try_from(end).ok()?).ok()
}

/// Canonical declaration coordinates only; callers authenticate original roles.
#[cfg(test)]
pub(crate) fn foreign_checked_nominal_range(
    source: Span,
    role: ForeignCheckedNominalRole,
) -> Option<ByteRange> {
    if !complete_source(source) {
        return None;
    }
    let start = FOREIGN_SOURCE.find(role.declaration())?;
    let rest = &FOREIGN_SOURCE[start..];
    let end = rest
        .find("\npub ")
        .or_else(|| rest.find("\nnative_host_metadata :"))
        .unwrap_or(rest.len());
    range(start, start + rest[..end].trim_end().len())
}

/// Full source anchor, name and H coordinates for synthesized builtin metadata.
pub(crate) fn foreign_native_host_ranges(
    source: Span,
) -> Option<(ByteRange, ByteRange, ByteRange)> {
    if !complete_source(source) {
        return None;
    }
    let start = FOREIGN_SOURCE.find("pub effect NativeHost<H>")?;
    let name = start + "pub effect ".len();
    let formal = name + "NativeHost<".len();
    Some((
        source.range(),
        range(name, name + "NativeHost".len())?,
        range(formal, formal + 1)?,
    ))
}

// These canonical headers deliberately preserve legacy TypeVariableId locals
// 0..13 even though resolution prepares nominal formals before global formals.
const FORMALS: &[(&str, &[u32])] = &[
    ("pub type Call<T>", &[0]),
    ("pub type Output<T>", &[1]),
    ("pub type Nullable<T>", &[2]),
    ("pub type Disposition<T>", &[3]),
    ("pub opaque type Extent<V>", &[4]),
    ("pub byte_read<S>", &[5]),
    ("pub byte_write<S>", &[6]),
    ("pub data_of<S, D>", &[7, 8]),
    ("pub replace_data<S, D>", &[9, 10]),
    ("pub copy_bytes<V>", &[11]),
    ("pub copy_nul<V>", &[12]),
    ("pub extent_value<V>", &[13]),
    ("pub type CheckedCall<T>", &[14]),
    ("pub type FinishResult<E>", &[15]),
    ("pub type CheckedFinish<S, E>", &[16, 17]),
    ("pub type CheckedCompletion<E>", &[18]),
    ("pub type CheckedScope<A, I, E>", &[19, 20, 21]),
    ("pub effect NativeHost<H>", &[22]),
];

/// Exact formal-name coordinates to reserved builtin locals; not a role grant.
pub(crate) fn foreign_type_formal_local(source: Span, formal: Span) -> Option<u32> {
    if !complete_source(source) || source.source() != formal.source() {
        return None;
    }
    for (header, locals) in FORMALS {
        let start = FOREIGN_SOURCE.find(header)?;
        let parameters = header.find('<')? + 1;
        for (position, local) in locals.iter().enumerate() {
            // Every immutable canonical formal is one ASCII letter, separated
            // by comma-space. This is not parsing of caller-provided spelling.
            let offset = start + parameters + position * 3;
            if formal.range() == range(offset, offset + 1)? {
                return Some(*local);
            }
        }
    }
    None
}

/// Prepay retained synthetic nodes and copied names on the existing syntax meter.
pub(super) fn charge_host(work: &mut SyntaxBudget) -> Result<(), ResourceFailure> {
    for _ in 0..("NativeHost".len() + "H".len() + 3) {
        work.charge()?;
    }
    Ok(())
}

fn name(text: &str, span: Span) -> Result<SurfaceName, ModuleFailure> {
    let mut owned = String::new();
    owned
        .try_reserve_exact(text.len())
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    owned.push_str(text);
    Ok(SurfaceName { text: owned, span })
}

/// Called only by reserved builtin admission after parsing its immutable bytes.
pub(super) fn append_host(
    module: super::ModuleId,
    source: &SourceFile,
    surface: &mut SurfaceModule,
) -> Result<(), ModuleFailure> {
    if !module.is_builtin_foreign()
        || source.text().as_bytes() != FOREIGN_SOURCE.as_bytes()
        || source.id() != surface.span.source()
        || !complete_source(surface.span)
        || !surface.effects.is_empty()
    {
        return Err(ModuleFailure::source(
            ModuleReason::UnknownBuiltin,
            surface.span,
            None,
        ));
    }
    let (declaration, identifier, formal) = foreign_native_host_ranges(surface.span)
        .expect("immutable Foreign source contains its host metadata coordinates");
    let declaration = source.span(declaration).expect("canonical host span");
    let identifier = source.span(identifier).expect("canonical host name span");
    let formal = source.span(formal).expect("canonical host formal span");
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    parameters.push(SurfaceTypeParameter {
        name: name("H", formal)?,
        kind: None,
        span: formal,
    });
    let effect = SurfaceEffectDeclaration {
        public: true,
        name: name("NativeHost", identifier)?,
        parameters,
        operations: Vec::new(),
        span: declaration,
    };
    surface
        .effects
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    surface
        .declaration_order
        .try_reserve(1)
        .map_err(|_| ModuleFailure::resource(ModuleResource::Sources))?;
    // No fallible step separates the new declaration and its order coordinate.
    surface.effects.push(effect);
    surface
        .declaration_order
        .push(SurfaceDeclarationIndex::Effect(
            FOREIGN_NATIVE_HOST_LOCAL as usize,
        ));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::*;

    fn admitted() -> StagedModule {
        let source = SourceFile::new("importer", "import @builtin.foreign as Foreign\n").unwrap();
        let mut budget = GraphBudget::default();
        let mut staged = Vec::new();
        let mut order = Vec::new();
        admit_builtin_foreign(
            17,
            source.span(ByteRange::new(0, 1).unwrap()).unwrap(),
            &mut budget,
            &mut staged,
            &mut order,
        )
        .unwrap();
        staged.pop().unwrap()
    }

    #[test]
    fn checked_foreign_inventory_appends_without_changing_legacy_ordinals() {
        let module = admitted();
        let names: Vec<_> = module
            .surface
            .type_declarations
            .iter()
            .map(|value| value.name.text.as_str())
            .collect();
        assert_eq!(
            names,
            [
                "ConversionError",
                "Call",
                "Output",
                "Nullable",
                "Disposition",
                "Extent",
                "NativeStatus",
                "NativeFact",
                "DiagnosticAbsence",
                "Diagnostic",
                "BoundaryRecord",
                "BoundaryFailure",
                "CheckedCall",
                "FinishResult",
                "CheckedFinish",
                "CheckedCompletion",
                "CheckedScope",
                "ViolationCause"
            ]
        );
        assert_eq!(module.surface.definitions.len(), 11);
        assert!(!module.surface.definitions[10].public);
        let crate::surface::SurfaceDefinitionKind::Equational(metadata) =
            &module.surface.definitions[10].kind
        else {
            panic!("canonical metadata global");
        };
        assert_eq!(metadata.interface.name.text, "native_host_metadata");
        assert!(metadata.interface.type_parameters.is_none());
        let host = module
            .surface
            .effects
            .first()
            .expect("canonical host effect");
        assert_eq!(host.name.text, "NativeHost");
        assert!(host.public && host.operations.is_empty());
        assert_eq!(host.parameters.len(), 1);
        assert_eq!(host.parameters[0].name.text, "H");
        assert!(host.parameters[0].kind.is_none());
        assert_eq!(
            module.surface.declaration_order.last(),
            Some(&SurfaceDeclarationIndex::Effect(0))
        );
        assert!(module.id.is_builtin_foreign());
        assert_ne!(module.id, ModuleId::from(module.source.id()));
    }

    #[test]
    fn checked_foreign_coordinates_preserve_all_canonical_formal_locals() {
        let module = admitted();
        let source = module.surface.span;
        for (index, expected) in [(1, 0), (2, 1), (3, 2), (4, 3), (5, 4)] {
            assert_eq!(
                foreign_type_formal_local(
                    source,
                    module.surface.type_declarations[index].parameters[0]
                        .name
                        .span
                ),
                Some(expected)
            );
        }
        let globals: [(&str, &[u32]); 10] = [
            ("checked_i64", &[]),
            ("checked_size_t", &[]),
            ("byte_read", &[5]),
            ("byte_write", &[6]),
            ("checked_nul", &[]),
            ("data_of", &[7, 8]),
            ("replace_data", &[9, 10]),
            ("copy_bytes", &[11]),
            ("copy_nul", &[12]),
            ("extent_value", &[13]),
        ];
        for (definition, (name, expected)) in module.surface.definitions.iter().zip(globals) {
            let crate::surface::SurfaceDefinitionKind::Equational(value) = &definition.kind else {
                panic!("canonical equational preflight");
            };
            assert_eq!(value.interface.name.text, name);
            let locals = value
                .interface
                .type_parameters
                .as_deref()
                .unwrap_or(&[])
                .iter()
                .map(|formal| foreign_type_formal_local(source, formal.name.span).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(locals, expected);
        }
        let mut seen = Vec::new();
        let formals = module
            .surface
            .type_declarations
            .iter()
            .flat_map(|item| item.parameters.iter())
            .chain(module.surface.definitions.iter().flat_map(|definition| {
                let crate::surface::SurfaceDefinitionKind::Equational(value) = &definition.kind
                else {
                    panic!("canonical equational preflight");
                };
                value
                    .interface
                    .type_parameters
                    .as_deref()
                    .unwrap_or(&[])
                    .iter()
            }))
            .chain(module.surface.effects[0].parameters.iter());
        for formal in formals {
            seen.push(
                foreign_type_formal_local(source, formal.name.span)
                    .expect("every original formal has a reserved local"),
            );
        }
        seen.sort_unstable();
        assert_eq!(seen, (0..23).collect::<Vec<_>>());
        let (_, name, formal) = foreign_native_host_ranges(source).unwrap();
        assert_eq!(module.surface.effects[0].name.span.range(), name);
        assert_eq!(
            module.surface.effects[0].parameters[0].name.span.range(),
            formal
        );
        assert_eq!(
            foreign_type_formal_local(source, module.surface.effects[0].parameters[0].name.span),
            Some(22)
        );
        assert_eq!(module.surface.effects[0].span, source);
        let other = SourceFile::new("other", FOREIGN_SOURCE).unwrap();
        assert!(foreign_type_formal_local(source, other.span(formal).unwrap()).is_none());
    }

    #[test]
    fn checked_foreign_nominal_coordinates_match_original_inventory() {
        let module = admitted();
        let roles = [
            ForeignCheckedNominalRole::NativeStatus,
            ForeignCheckedNominalRole::NativeFact,
            ForeignCheckedNominalRole::DiagnosticAbsence,
            ForeignCheckedNominalRole::Diagnostic,
            ForeignCheckedNominalRole::BoundaryRecord,
            ForeignCheckedNominalRole::BoundaryFailure,
            ForeignCheckedNominalRole::CheckedCall,
            ForeignCheckedNominalRole::FinishResult,
            ForeignCheckedNominalRole::CheckedFinish,
            ForeignCheckedNominalRole::CheckedCompletion,
            ForeignCheckedNominalRole::CheckedScope,
            ForeignCheckedNominalRole::ViolationCause,
        ];
        for role in roles {
            let declaration = &module.surface.type_declarations[role.local() as usize];
            assert_eq!(declaration.constructors.len(), role.constructor_count());
            assert_eq!(
                Some(declaration.span.range()),
                foreign_checked_nominal_range(module.surface.span, role)
            );
        }
        let expected = [
            ["HiddenConversionError"].as_slice(),
            &["Returned", "ConversionFailed"],
            &["Unreadable", "Readable"],
            &["Null", "NonNull"],
            &["Consumed", "Retained", "BlockedDependent"],
            &["HiddenExtent"],
        ];
        for (declaration, constructors) in module.surface.type_declarations.iter().zip(expected) {
            assert_eq!(
                declaration
                    .constructors
                    .iter()
                    .map(|value| value.name.text.as_str())
                    .collect::<Vec<_>>(),
                constructors
            );
        }
    }

    #[test]
    fn checked_foreign_host_metadata_requires_exact_bytes_and_reserves_before_publication() {
        let path = std::path::Path::new("ordinary");
        let (source, mut surface) = parse_surface_module(
            path,
            FOREIGN_SOURCE.to_owned(),
            None,
            &mut SyntaxBudget::default(),
        )
        .unwrap();
        assert!(
            surface.effects.is_empty(),
            "ordinary syntax cannot declare the metadata effect"
        );
        let mut short = SyntaxBudget::with_limit("NativeHost".len() + "H".len() + 2);
        assert!(charge_host(&mut short).is_err());
        assert!(surface.effects.is_empty());
        for _ in 0..2 {
            let mut exact = SyntaxBudget::with_limit("NativeHost".len() + "H".len() + 3);
            charge_host(&mut exact).unwrap();
        }
        let altered = SourceFile::new(
            "ordinary",
            FOREIGN_SOURCE.replace("no operations", "no authority!"),
        )
        .unwrap();
        assert!(
            append_host(
                ModuleId::builtin_foreign_for_test(7),
                &altered,
                &mut surface
            )
            .is_err()
        );
        assert!(surface.effects.is_empty());
        assert!(append_host(ModuleId::from(source.id()), &source, &mut surface).is_err());
        assert!(surface.effects.is_empty());
        append_host(ModuleId::builtin_foreign_for_test(7), &source, &mut surface).unwrap();
        assert!(append_host(ModuleId::builtin_foreign_for_test(7), &source, &mut surface).is_err());
        assert_eq!(surface.effects.len(), 1);
    }

    #[test]
    fn checked_foreign_builtin_admission_exact_work_and_one_short_publish_atomically() {
        let importer = SourceFile::new("importer", "import @builtin.foreign as Foreign\n").unwrap();
        let span = importer.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let run = |limit| {
            let mut budget = GraphBudget {
                syntax_work: SyntaxBudget::with_limit(limit),
                ..GraphBudget::default()
            };
            let mut staged = Vec::new();
            let mut order = Vec::new();
            let result = admit_builtin_foreign(17, span, &mut budget, &mut staged, &mut order);
            (result, staged, order, budget.syntax_work.consumed())
        };
        let (result, _, _, required) = run(crate::syntax_resource::SYNTAX_WORK_LIMIT);
        assert!(result.is_ok());
        for limit in [required - 1, required, required] {
            let (result, staged, order, _) = run(limit);
            if limit < required {
                let Err(LoadGraphError::Syntax(failure)) = result else {
                    panic!("one-short admission must refuse syntax work");
                };
                assert!(failure.resource.is_some());
                assert!(staged.is_empty() && order.is_empty());
            } else {
                assert!(result.is_ok());
                assert_eq!(staged.len(), 1);
                assert_eq!(order.len(), 1);
                assert_eq!(staged[0].surface.effects.len(), 1);
            }
        }
    }
}
