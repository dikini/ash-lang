//! Passive checked-profile construction: exact resident source is reparsed and
//! reprepared, then all ABI and checked projection bytes must correspond.
use super::*;
use crate::foreign::source_contract::{CheckedNativeAssumption, PreparedForeignLibrary};

fn contract_failure(error: crate::foreign::source_contract::ForeignContractError) -> ImageFailure {
    if error.is_resource_exhaustion() {
        ImageFailure::Resource
    } else {
        ImageFailure::RegistryAdmission
    }
}
fn source_origin(
    origin: &crate::source::Origin,
    library: crate::source::Span,
    writer: &mut WireWriter<'_>,
) -> Result<(), ImageFailure> {
    charge(writer.work, 1)?;
    let crate::source::Origin::Source(span) = origin else {
        return Err(ImageFailure::InvalidRecord);
    };
    if span.source() != library.source()
        || span.range().start() < library.range().start()
        || span.range().end() > library.range().end()
    {
        return Err(ImageFailure::InvalidRecord);
    }
    span.range().start().write(writer)?;
    span.range().end().write(writer)
}
fn text(text: &str, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
    index(text.len())?.write(writer)?;
    writer.bytes(text.as_bytes())
}
fn premise(value: CheckedNativeAssumption) -> u8 {
    use CheckedNativeAssumption::*;
    match value {
        CompilerAndRuntimeIntegrity => 0,
        AuthorizedBuildCorrespondence => 1,
        ExecutorIntegrity => 2,
        NativeAbiAndOutcomeTruth => 3,
        NativeInputIntervalValidity => 4,
        NativeInputNonRetention => 5,
        NativeIndependentInputCopy => 6,
        NativeAliasingAndNonInterference => 7,
        NativeOutputIntervalValidity => 8,
        NativeOwnerLifetimeAndDisposition => 9,
        SerializedNativeAccess => 10,
    }
}
fn write_projection(
    library: &PreparedForeignLibrary,
    writer: &mut WireWriter<'_>,
) -> Result<(), ImageFailure> {
    let checked = library
        .checked_contract()
        .ok_or(ImageFailure::InvalidRecord)?;
    let span = library.origin().primary_span();
    1u8.write(writer)?; // Explicit normalized checked-projection schema.
    index(checked.assumptions().len())?.write(writer)?;
    for value in checked.assumptions() {
        index(value.member_index())?.write(writer)?;
        text(value.name(), writer)?;
        text(value.description(), writer)?;
        source_origin(value.origin(), span, writer)?;
    }
    index(checked.owners().len())?.write(writer)?;
    for value in checked.owners() {
        index(value.member_index())?.write(writer)?;
        index(value.host_parameter())?.write(writer)?;
    }
    index(checked.symbols().len())?.write(writer)?;
    for value in checked.symbols() {
        index(value.member_index())?.write(writer)?;
        index(value.host_parameter())?.write(writer)?;
        index(value.assumption_members().len())?.write(writer)?;
        for member in value.assumption_members() {
            index(*member)?.write(writer)?;
        }
        index(value.minimum_assumptions().len())?.write(writer)?;
        for minimum in value.minimum_assumptions() {
            premise(*minimum).write(writer)?;
        }
    }
    Ok(())
}
impl Encoder<'_> {
    pub(super) fn checked_prepared_projection(
        &mut self,
        original: &PreparedForeignLibrary,
    ) -> Result<Option<Slice>, ImageFailure> {
        if original.checked_contract().is_none() {
            return Ok(None);
        }
        let mut writer = WireWriter {
            output: WireOutput::Encoded(Vec::new()),
            work: self.work,
        };
        write_projection(original, &mut writer)?;
        let WireOutput::Encoded(bytes) = writer.output else {
            unreachable!()
        };
        Ok(Some(append(&mut self.image.bytes, &bytes, self.work)?))
    }
}
impl Decoder<'_> {
    pub(super) fn restore_prepared_record(
        &mut self,
        record: PreparedLibraryRecord,
    ) -> Result<PreparedForeignLibrary, ImageFailure> {
        let parts = self.prepared_parts(record)?;
        let Some(projection) = record.checked else {
            // Historical normalized legacy reconstruction retains all its guards.
            return crate::foreign::source_contract::restore_prepared_library(parts, self.work)
                .map_err(contract_failure);
        };
        let source = get(&self.sources, record.module)?;
        charge(self.work, 3)?;
        if *get(&self.modules, record.module)? != parts.module || source.id() != parts.span.source()
        {
            return Err(ImageFailure::InvalidRecord);
        }
        // Pay actual lex/parse consumption on failure before inspecting the tree.
        charge(self.work, source.text().len())?;
        let mut syntax = crate::syntax_resource::SyntaxBudget::loan(self.work.remaining());
        let parsed = crate::lexer::lex_with_budget(source, &mut syntax)
            .map(|lexed| crate::parser::parse_with_budget(lexed, &mut syntax));
        charge(self.work, syntax.consumed())?;
        let tree = parsed.map_err(|_| ImageFailure::SourceAdmission)?;
        if tree.resource_failure().is_some() {
            return Err(ImageFailure::Resource);
        }
        if tree.malformed.is_some()
            || !tree.lexical_diagnostics().is_empty()
            || !tree.parse_diagnostics().is_empty()
        {
            return Err(ImageFailure::SourceAdmission);
        }
        // Charge the full bounded projection input before validating/projecting.
        charge(self.work, tree.tokens.len())?;
        let mut pending = Vec::new();
        if let Some(root) = tree.root() {
            push(&mut pending, root, self.work)?;
        }
        while let Some(node) = pending.pop() {
            charge(
                self.work,
                node.children
                    .len()
                    .checked_mul(2)
                    .ok_or(ImageFailure::Resource)?,
            )?;
            for element in &node.children {
                if let crate::parser::ConcreteElement::Node(child) = element {
                    push(&mut pending, child, self.work)?;
                }
            }
        }
        let surface =
            crate::parser::project_module(source, &tree).map_err(|error| match error {
                crate::parser::ProjectionError::ResourceLimit(_) => ImageFailure::Resource,
                _ => ImageFailure::SourceAdmission,
            })?;
        let mut selected = None;
        for library in &surface.foreign_libraries {
            charge(self.work, 1)?;
            if library.span == parts.span && selected.replace(library).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        let written = selected.ok_or(ImageFailure::SourceAdmission)?;
        if written.checked.is_none() {
            return Err(ImageFailure::InvalidRecord);
        }
        let fresh = crate::foreign::source_contract::prepare_checked_foreign_library_with_budget(
            parts.module,
            written,
            self.work,
        )
        .map_err(contract_failure)?;
        let expected = projection.get(&self.image.bytes)?;
        let mut writer = WireWriter {
            output: WireOutput::Expected {
                bytes: expected,
                offset: 0,
            },
            work: self.work,
        };
        write_projection(&fresh, &mut writer)?;
        charge(writer.work, 1)?;
        let WireOutput::Expected { bytes, offset } = writer.output else {
            unreachable!()
        };
        if offset != bytes.len() {
            return Err(ImageFailure::InvalidRecord);
        }
        if !crate::foreign::source_contract::same_prepared_library_parts_after_checked_source(
            &fresh, &parts, self.work,
        )
        .map_err(contract_failure)?
        {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(fresh) // Caller publishes one shared Arc only after all comparisons.
    }
}

#[cfg(test)]
fn projection_offsets(data: &[u8]) -> (usize, usize, usize) {
    let mut work = TypeWorkBudget::default();
    let mut reader = WireReader {
        bytes: data,
        offset: 0,
        work: &mut work,
    };
    assert_eq!(u8::read(&mut reader).unwrap(), 1);
    let assumptions = u32::read(&mut reader).unwrap();
    for _ in 0..assumptions {
        u32::read(&mut reader).unwrap();
        for _ in 0..2 {
            let len = u32::read(&mut reader).unwrap();
            reader.bytes(len as usize).unwrap();
        }
        u32::read(&mut reader).unwrap();
        u32::read(&mut reader).unwrap();
    }
    let owners = u32::read(&mut reader).unwrap();
    assert!(owners > 0);
    let mut owner_host = None;
    for _ in 0..owners {
        u32::read(&mut reader).unwrap();
        owner_host.get_or_insert(reader.offset);
        u32::read(&mut reader).unwrap();
    }
    let symbols = u32::read(&mut reader).unwrap();
    assert!(symbols > 0);
    u32::read(&mut reader).unwrap();
    let symbol_host = reader.offset;
    u32::read(&mut reader).unwrap();
    let members = u32::read(&mut reader).unwrap();
    assert!(members > 0);
    (owner_host.unwrap(), symbol_host, reader.offset)
}

#[cfg(test)]
pub(super) fn checked_projection_hostile_controls(image: &PureImage) {
    let mut work = TypeWorkBudget::default();
    let bytes = image.encode_bytes(&mut work).unwrap();
    let decode = || PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
    let slot = image
        .prepared_libraries
        .iter()
        .position(|p| p.checked.is_some())
        .expect("actual checked library");
    // Whole canonical restore already succeeded in the caller; do it here too
    // before every independent prepared-projection mutation is credited.
    decode()
        .restore_effect(&mut TypeWorkBudget::default())
        .unwrap();
    for mutation in 0..7 {
        let mut hostile = decode();
        let projection = hostile.prepared_libraries[slot].checked.unwrap();
        match mutation {
            0 => hostile.prepared_libraries[slot].checked = None,
            1 => hostile.bytes[projection.start as usize] ^= 1, // Projection version.
            2 => {
                let data = projection.get(&hostile.bytes).unwrap();
                let needle =
                    b"the admitted native owner, initialized interval and view contracts hold";
                let offset = data
                    .windows(needle.len())
                    .position(|w| w == needle)
                    .expect("actual original Callee description");
                hostile.bytes[projection.start as usize + offset] ^= 1;
            }
            3 => {
                // Genuine source/module donor, retaining the original library span.
                let donor = hostile
                    .sources
                    .iter()
                    .position(|s| matches!(s.role, ModuleRoleRecord::BuiltinForeign))
                    .unwrap();
                assert_ne!(
                    hostile.prepared_libraries[slot].module,
                    index(donor).unwrap()
                );
                hostile.prepared_libraries[slot].module = index(donor).unwrap();
            }
            4..=6 => {
                let data = projection.get(&hostile.bytes).unwrap();
                let (owner_host, symbol_host, member) = projection_offsets(data);
                let offset = match mutation {
                    4 => owner_host,
                    5 => symbol_host,
                    _ => member,
                };
                hostile.bytes[projection.start as usize + offset] ^= 1;
            }
            _ => unreachable!(),
        }
        let error = match hostile.restore_effect(&mut TypeWorkBudget::default()) {
            Ok(_) => panic!("hostile prepared facts accepted"),
            Err(error) => error,
        };
        match error {
            ImageFailure::Resource => panic!("no Resource rejection credit"),
            ImageFailure::Validation(error) => {
                assert_ne!(error.reason(), crate::core::ValidationReason::Resource)
            }
            ImageFailure::Unsupported(feature) => {
                panic!("unsupported is missing coverage: {feature:?}")
            }
            ImageFailure::CoreAdmission(error) => {
                panic!("builder setup is not semantic evidence: {error:?}")
            }
            _ => {}
        }
    }
}

#[cfg(test)]
pub(super) fn zero_assumption_scalar_controls(
    program: &crate::core::ValidatedEffectProgram,
    provenance: &[(ModuleId, Arc<SourceFile>)],
) {
    let mut encoding = TypeWorkBudget::default();
    let encoder = encode_program(
        program,
        provenance,
        &mut encoding,
        true,
        |_| Ok(()),
        |encoder, kind| encoder.encode_effect_node(kind),
    )
    .expect("actual zero-assumption checked scalar program encodes");
    let bytes = encoder
        .image
        .encode_bytes(&mut TypeWorkBudget::default())
        .unwrap();
    let decode = || PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
    let canonical = decode();
    let slot = canonical
        .prepared_libraries
        .iter()
        .position(|record| record.checked.is_some())
        .expect("actual checked scalar library retained");
    let projection = canonical.prepared_libraries[slot].checked.unwrap();
    let mut reader_work = TypeWorkBudget::default();
    let mut reader = WireReader {
        bytes: projection.get(&canonical.bytes).unwrap(),
        offset: 0,
        work: &mut reader_work,
    };
    assert_eq!(u8::read(&mut reader).unwrap(), 1);
    assert_eq!(
        u32::read(&mut reader).unwrap(),
        0,
        "no declared assumptions mask profile erasure"
    );
    assert_eq!(
        u32::read(&mut reader).unwrap(),
        0,
        "scalar fixture has no owner"
    );
    assert_eq!(u32::read(&mut reader).unwrap(), 1);
    u32::read(&mut reader).unwrap(); // Original symbol member.
    u32::read(&mut reader).unwrap(); // Host position.
    assert_eq!(u32::read(&mut reader).unwrap(), 0);
    let minimum_count = reader.offset;
    let minimum = u32::read(&mut reader).unwrap();
    assert!(
        minimum > 0,
        "automatic native premises remain without named assumptions"
    );
    let minimum_value = reader.offset;
    canonical
        .restore_effect(&mut TypeWorkBudget::default())
        .expect("whole zero-assumption checked scalar image re-admits first");
    for mutation in 0..3 {
        let mut hostile = decode();
        match mutation {
            0 => hostile.prepared_libraries[slot].checked = None,
            1 => hostile.bytes[projection.start as usize + minimum_count] = 0,
            2 => hostile.bytes[projection.start as usize + minimum_value] ^= 1,
            _ => unreachable!(),
        }
        let error = match hostile.restore_effect(&mut TypeWorkBudget::default()) {
            Ok(_) => panic!("checked profile/minimum-premise mutation {mutation} accepted"),
            Err(error) => error,
        };
        match error {
            ImageFailure::Resource => panic!("no Resource credit for mutation {mutation}"),
            ImageFailure::Validation(error) => {
                assert_ne!(error.reason(), crate::core::ValidationReason::Resource)
            }
            ImageFailure::Unsupported(feature) => panic!("missing static coverage: {feature:?}"),
            ImageFailure::CoreAdmission(error) => panic!("builder setup failure: {error:?}"),
            _ => {}
        }
    }
}
