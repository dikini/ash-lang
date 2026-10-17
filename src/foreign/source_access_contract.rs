//! Passive access-family facts. Preparation supplies no live window or pointer.

use super::{
    ForeignContractError, ForeignContractReason, PreparedForeignLibrary, PreparedForeignParameter,
    PreparedForeignSymbol, PreparedOwnerApplication, PreparedOwnerArgument, SurfaceForeignLibrary,
    SurfaceForeignMember, SurfaceType, SurfaceTypeKind, TypeWorkBudget, charge, failure,
    local_reference, names_equal, owner_application_from_parameters, owner_source_path,
    prepare_parameters, project_arguments, reserve, source_path, text,
};
use crate::{
    source::{Origin, Span},
    surface::{
        SurfaceForeignAccess, SurfaceForeignExtent, SurfaceForeignOutputRoleKind,
        SurfaceForeignSourcePosition,
    },
    types::Kind,
};

/// The authored initialized-memory convention, without an executable address.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedForeignExtent {
    Bytes,
    Nul,
}

/// Original family, fresh-window role, owner projection and preserving members.
/// Coordinates refer only to this immutable defining library.
#[derive(Debug)]
pub struct PreparedForeignAccess {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) parameters: Vec<PreparedForeignParameter>,
    pub(crate) window_parameter: usize,
    pub(crate) window_span: Span,
    pub(crate) owner: PreparedOwnerApplication,
    pub(crate) extent: PreparedForeignExtent,
    pub(crate) extent_span: Span,
    pub(crate) preserving_members: Vec<(usize, Span)>,
    pub(crate) origin: Origin,
}

impl PreparedForeignAccess {
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub fn parameters(&self) -> &[PreparedForeignParameter] {
        &self.parameters
    }
    #[must_use]
    pub const fn window_parameter(&self) -> usize {
        self.window_parameter
    }
    #[must_use]
    pub const fn window_span(&self) -> Span {
        self.window_span
    }
    #[must_use]
    pub const fn owner(&self) -> &PreparedOwnerApplication {
        &self.owner
    }
    #[must_use]
    pub const fn extent(&self) -> PreparedForeignExtent {
        self.extent
    }
    #[must_use]
    pub const fn extent_span(&self) -> Span {
        self.extent_span
    }
    #[must_use]
    pub fn preserving_members(&self) -> &[(usize, Span)] {
        &self.preserving_members
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

pub(super) fn prepare(
    library: &PreparedForeignLibrary,
    written: &SurfaceForeignLibrary,
    member_index: usize,
    source: &SurfaceForeignAccess,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignAccess, ForeignContractError> {
    let parameters = prepare_parameters(&source.parameters, source.span, work)?;
    let mut window = None;
    for (index, parameter) in parameters.iter().enumerate() {
        if names_equal(
            parameter.name(),
            &source.window.text,
            source.window.span,
            work,
        )? {
            if parameter.kind() != &Kind::Type {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    source.window.span,
                ));
            }
            window = Some(index);
        }
    }
    let window_parameter = window
        .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, source.window.span))?;
    let owner = owner_application_from_parameters(library, &parameters, &source.owner, work)?;
    // A window is fresh independently of every owner identity. Its formal cannot
    // be reused as an owner's declared argument, even when kinds coincide.
    charge(work, owner.arguments().len(), source.owner.span)?;
    if owner
        .arguments()
        .iter()
        .any(|argument| argument.parameter() == window_parameter)
    {
        return Err(failure(
            ForeignContractReason::InvalidParameters,
            source.owner.span,
        ));
    }
    let (extent, extent_span) = match source.extent {
        SurfaceForeignExtent::Bytes(span) => (PreparedForeignExtent::Bytes, span),
        SurfaceForeignExtent::Nul(span) => (PreparedForeignExtent::Nul, span),
    };
    let mut preserving_members: Vec<(usize, Span)> = Vec::new();
    reserve(&mut preserving_members, source.preserves.len(), source.span)?;
    for reference in &source.preserves {
        let spelling = local_reference(reference)?;
        let mut member = None;
        for (index, value) in written.members.iter().enumerate() {
            charge(work, 1, reference.span)?;
            if let SurfaceForeignMember::Symbol(symbol) = value
                && names_equal(&symbol.name.text, spelling, reference.span, work)?
            {
                member = Some(index);
            }
        }
        let member =
            member.ok_or_else(|| failure(ForeignContractReason::UnknownMember, reference.span))?;
        charge(work, preserving_members.len(), reference.span)?;
        if preserving_members
            .iter()
            .any(|(previous, _)| *previous == member)
        {
            return Err(failure(
                ForeignContractReason::DuplicateMember,
                reference.span,
            ));
        }
        preserving_members.push((member, reference.span));
    }
    Ok(PreparedForeignAccess {
        member_index,
        name: text(&source.name.text, source.name.span, work)?,
        parameters,
        window_parameter,
        window_span: source.window.span,
        owner,
        extent,
        extent_span,
        preserving_members,
        origin: Origin::Source(source.span),
    })
}

/// Preservation retains original member coordinates. Runtime compatibility still
/// checks the selected family's owner/dependency arguments and full call context;
/// parameter spellings in separate declarations have no authority.
pub(super) fn validate_preserving_symbols(
    library: &PreparedForeignLibrary,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    for access in library.accesses() {
        for (member, span) in access.preserving_members() {
            charge(work, library.symbols().len(), *span)?;
            let symbol = library
                .symbols()
                .iter()
                .find(|symbol| symbol.member_index() == *member)
                .ok_or_else(|| failure(ForeignContractReason::UnknownMember, *span))?;
            if matches!(symbol.call(), super::PreparedForeignCall::Owner(call)
                if !matches!(call, super::PreparedOwnerCall::Borrow { .. }))
            {
                return Err(failure(ForeignContractReason::OperandRole, *span));
            }
        }
    }
    Ok(())
}

/// A complete kind-tagged application of one original access family.
#[derive(Debug)]
pub struct PreparedAccessApplication {
    pub(crate) family: usize,
    pub(crate) arguments: Vec<PreparedOwnerArgument>,
    pub(crate) span: Span,
}
impl PreparedAccessApplication {
    #[must_use]
    pub const fn family(&self) -> usize {
        self.family
    }
    #[must_use]
    pub fn arguments(&self) -> &[PreparedOwnerArgument] {
        &self.arguments
    }
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }
}

/// The passive output role. Only independent binding and a live direct window
/// can turn its coordinates into view/extent authority.
#[derive(Debug)]
pub enum PreparedAccessResult {
    View {
        application: PreparedAccessApplication,
        keys: Vec<Vec<usize>>,
        span: Span,
    },
    Extent {
        application: PreparedAccessApplication,
        view: Vec<usize>,
        keys: Vec<Vec<usize>>,
        span: Span,
    },
}
impl PreparedAccessResult {
    #[must_use]
    pub const fn application(&self) -> &PreparedAccessApplication {
        match self {
            Self::View { application, .. } | Self::Extent { application, .. } => application,
        }
    }
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::View { span, .. } | Self::Extent { span, .. } => *span,
        }
    }
}

fn application(
    library: &PreparedForeignLibrary,
    symbol: &PreparedForeignSymbol,
    ty: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<PreparedAccessApplication, ForeignContractError> {
    let SurfaceTypeKind::Application {
        constructor,
        arguments,
    } = &ty.kind
    else {
        return Err(failure(ForeignContractReason::OutputRole, ty.span));
    };
    if constructor.qualifier().is_some() {
        return Err(failure(ForeignContractReason::UnknownMember, ty.span));
    }
    let mut selected = None;
    for (index, access) in library.accesses().iter().enumerate() {
        if names_equal(access.name(), &constructor.member().text, ty.span, work)? {
            selected = Some(index);
        }
    }
    let family = selected.ok_or_else(|| failure(ForeignContractReason::UnknownMember, ty.span))?;
    let access = &library.accesses()[family];
    let arguments = project_arguments(
        symbol.parameters(),
        arguments,
        access.parameters(),
        ty.span,
        work,
    )?;
    charge(work, access.preserving_members().len(), ty.span)?;
    if !access
        .preserving_members()
        .iter()
        .any(|(member, _)| *member == symbol.member_index())
    {
        return Err(failure(ForeignContractReason::OperandRole, ty.span));
    }
    Ok(PreparedAccessApplication {
        family,
        arguments,
        span: ty.span,
    })
}

fn scalar_keys(
    positions: &[SurfaceForeignSourcePosition],
    domain: &SurfaceType,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<Vec<Vec<usize>>, ForeignContractError> {
    charge(work, positions.len(), span)?;
    let mut keys = Vec::new();
    reserve(&mut keys, positions.len(), span)?;
    for position in positions {
        keys.push(source_path(position, domain, work)?);
    }
    Ok(keys)
}

pub(super) fn prepare_result(
    library: &PreparedForeignLibrary,
    symbol: &PreparedForeignSymbol,
    role: &SurfaceForeignOutputRoleKind,
    domain: &SurfaceType,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<PreparedAccessResult, ForeignContractError> {
    match role {
        SurfaceForeignOutputRoleKind::View { ty, keys } => Ok(PreparedAccessResult::View {
            application: application(library, symbol, ty, work)?,
            keys: scalar_keys(keys, domain, span, work)?,
            span,
        }),
        SurfaceForeignOutputRoleKind::ExtentOf { view, keys } => {
            let (view, ty) = owner_source_path(view, domain, work)?;
            Ok(PreparedAccessResult::Extent {
                application: application(library, symbol, ty, work)?,
                view,
                keys: scalar_keys(keys, domain, span, work)?,
                span,
            })
        }
        _ => Err(failure(ForeignContractReason::OutputRole, span)),
    }
}

pub(super) fn access_owner(
    library: &PreparedForeignLibrary,
    application: &PreparedAccessApplication,
    work: &mut TypeWorkBudget,
) -> Result<(usize, Vec<PreparedOwnerArgument>), ForeignContractError> {
    let access = library
        .accesses()
        .get(application.family())
        .ok_or_else(|| failure(ForeignContractReason::UnknownMember, application.span()))?;
    charge(work, access.owner().arguments().len(), application.span())?;
    let mut arguments = Vec::new();
    reserve(
        &mut arguments,
        access.owner().arguments().len(),
        application.span(),
    )?;
    for argument in access.owner().arguments() {
        let actual = application
            .arguments()
            .get(argument.parameter())
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, application.span()))?;
        if !matches!(
            (argument, actual),
            (
                PreparedOwnerArgument::Type(_),
                PreparedOwnerArgument::Type(_)
            ) | (
                PreparedOwnerArgument::EffectRow(_),
                PreparedOwnerArgument::EffectRow(_)
            )
        ) {
            return Err(failure(
                ForeignContractReason::InvalidParameters,
                application.span(),
            ));
        }
        arguments.push(*actual);
    }
    Ok((access.owner().owner(), arguments))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{module::ModuleId, surface::SurfaceModule};

    const ACCESS: &str = r#"foreign library Native {
    profile "x86_64-unknown-linux-gnu"
    repr Address = opaque
    repr CInt = signed(32)
    owner State<C> {
        representation Address
        owned C
        teardown Destroy
    }
    access View<W, C> {
        window W
        owner State<C>
        extent bytes
        preserves Query
    }
    symbol Query<C> : State<C> -> Foreign.Call<Int> {
        name "query"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Destroy<C> : State<C> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "destroy"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}
"#;

    fn source(text: &str) -> (ModuleId, SurfaceModule) {
        let source = crate::source::SourceFile::new("access.ash", text).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        let module = crate::parser::project_module(&source, &tree).unwrap();
        (ModuleId::from(source.id()), module)
    }

    #[test]
    fn access_preparation_keeps_original_window_owner_and_preserving_coordinates() {
        let (id, module) = source(ACCESS);
        let prepared =
            super::super::prepare_foreign_library(id, &module.foreign_libraries[0]).unwrap();
        let access = &prepared.accesses()[0];
        assert_eq!(access.name(), "View");
        assert_eq!(access.member_index(), 4);
        assert_eq!(access.window_parameter(), 0);
        assert_eq!(access.owner().owner(), 0);
        assert_eq!(
            access.owner().arguments(),
            &[PreparedOwnerArgument::Type(1)]
        );
        assert_eq!(access.extent(), PreparedForeignExtent::Bytes);
        assert_eq!(access.preserving_members()[0].0, 5);
        assert_eq!(
            access.origin().primary_span().source(),
            prepared.origin().primary_span().source()
        );
        let renamed = ACCESS
            .replace("symbol Query<C>", "symbol Query<Other>")
            .replace(
                "State<C> -> Foreign.Call<Int>",
                "State<Other> -> Foreign.Call<Int>",
            );
        let (id, module) = source(&renamed);
        super::super::prepare_foreign_library(id, &module.foreign_libraries[0]).unwrap();
    }

    #[test]
    fn access_preparation_rejects_window_owner_aliases_and_unrelated_preservation() {
        for changed in [
            ACCESS.replace("window W", "window Missing"),
            ACCESS.replace("View<W, C>", "View<W : EffectRow, C>"),
            ACCESS.replace("owner State<C>", "owner State<W>"),
            ACCESS.replace("owner State<C>", "owner Missing<C>"),
            ACCESS.replace("preserves Query", "preserves Query, Query"),
            ACCESS.replace("preserves Query", "preserves Destroy"),
            ACCESS.replace("preserves Query", "preserves Address"),
        ] {
            let (id, module) = source(&changed);
            assert!(
                super::super::prepare_foreign_library(id, &module.foreign_libraries[0]).is_err(),
                "{changed}"
            );
        }
    }

    pub(crate) fn view_source() -> String {
        ACCESS.replace("preserves Query", "preserves Query, Column, Length")
            .replace("    symbol Query", r#"    symbol Column<W, C> : (State<C>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<View<W, C>>>> {
        name "column"
        abi (pointer(Address), CInt) -> pointer(AddressBytes)
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(View<W, C>, 1)
        outcome otherwise { readable result }
    }
    symbol Length<W, C> : (State<C>, Int, View<W, C>) -> Foreign.Call<Foreign.Extent<View<W, C>>> {
        name "length"
        abi (pointer(Address), CInt) -> CInt
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as extent_of(2, 1)
        outcome otherwise { readable result }
    }
    symbol Query"#)
            .replace("repr Address = opaque", "repr Address = opaque\n    repr AddressBytes = bytes")
    }

    #[test]
    fn view_and_extent_results_keep_full_family_arguments_and_scalar_key_paths() {
        let (id, module) = source(&view_source());
        let prepared =
            super::super::prepare_foreign_library(id, &module.foreign_libraries[0]).unwrap();
        let column = prepared
            .symbols()
            .iter()
            .find(|symbol| symbol.name() == "Column")
            .unwrap();
        let Some(PreparedAccessResult::View {
            application, keys, ..
        }) = column.access_result()
        else {
            panic!("view role");
        };
        assert_eq!(application.family(), 0);
        assert_eq!(
            application.arguments(),
            &[
                PreparedOwnerArgument::Type(0),
                PreparedOwnerArgument::Type(1)
            ]
        );
        assert_eq!(keys, &[vec![1]]);
        let length = prepared
            .symbols()
            .iter()
            .find(|symbol| symbol.name() == "Length")
            .unwrap();
        let Some(PreparedAccessResult::Extent {
            application,
            view,
            keys,
            ..
        }) = length.access_result()
        else {
            panic!("extent role");
        };
        assert_eq!(application.family(), 0);
        assert_eq!(view, &[2]);
        assert_eq!(keys, &[vec![1]]);
        assert_eq!(
            access_owner(&prepared, application, &mut TypeWorkBudget::default()).unwrap(),
            (0, vec![PreparedOwnerArgument::Type(1)])
        );
    }

    #[test]
    fn view_result_preparation_refuses_unlisted_roles_wrong_owner_and_noninteger_keys() {
        let original = view_source();
        for changed in [
            original.replace("preserves Query, Column, Length", "preserves Query, Length"),
            original.replace("as view(View<W, C>, 1)", "as view(View<C, W>, 1)"),
            original.replace("as view(View<W, C>, 1)", "as view(View<W, C>, 0)"),
            original.replace("as extent_of(2, 1)", "as extent_of(0, 1)"),
            original.replace("as extent_of(2, 1)", "as extent_of(2, 2)"),
            original.replace("-> pointer(AddressBytes)", "-> pointer(Address)"),
            original.replace(
                "as view(View<W, C>, 1)",
                "as view(View<W, C>, 1)\n        output result as scalar",
            ),
        ] {
            let (id, module) = source(&changed);
            assert!(
                super::super::prepare_foreign_library(id, &module.foreign_libraries[0]).is_err(),
                "{changed}"
            );
        }
    }

    #[test]
    fn access_preparation_exact_short_prefix_and_fresh_retry_do_not_publish_partial_facts() {
        let (id, module) = source(&view_source());
        let written = &module.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        super::super::prepare_foreign_library_with_budget(id, written, &mut measured).unwrap();
        let exact = measured.used();
        for prefix in [0, 13] {
            for _ in 0..2 {
                let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    super::super::prepare_foreign_library_with_budget(id, written, &mut short)
                        .unwrap_err()
                        .reason(),
                    ForeignContractReason::WorkExhausted
                );
                let mut work = TypeWorkBudget::with_limit(prefix + exact);
                work.charge(prefix).unwrap();
                let result =
                    super::super::prepare_foreign_library_with_budget(id, written, &mut work)
                        .unwrap();
                assert_eq!(work.used(), prefix + exact);
                assert_eq!(result.accesses()[0].preserving_members().len(), 3);
            }
        }
    }
}
