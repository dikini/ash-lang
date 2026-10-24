//! Deterministic producer observations, not approval or an executable capability.
//! The existing producer cannot establish the full checked/native/tool/context
//! closure. Missing fields stay explicit, including on otherwise matching data.
use crate::types::TypeWorkBudget;
use sha2::{Digest, Sha256};
#[cfg(unix)]
use std::fs::File;
use std::{io::Read, path::Path};

const MAGIC: &[u8; 8] = b"ASHRCP01";
const FIELDS: usize = 16;
const RECORD_BYTES: usize = 42;

/// Explicit opt-in bounds. These do not change ordinary build preparation limits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProducerReceiptLimits {
    pub artifact_bytes: usize,
    pub receipt_bytes: usize,
    pub records: usize,
    pub work: usize,
}

/// No variant grants protected approval or immutable execution authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReceiptFailure {
    Resource,
    Malformed,
    Version,
    Association,
    Input,
    IncompleteClosure,
    ProtectedAuthorityUnavailable,
}

/// An observation of exact bytes. A digest is not a trust decision.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArtifactPin {
    pub bytes: u64,
    pub sha256: [u8; 32],
}

/// Field identities are versioned wire data, not a second semantic registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum ReceiptField {
    ProgramImage,
    ExpectedFacts,
    GeneratedRust,
    OriginalMappings,
    RuntimeFingerprint,
    BuildConfiguration,
    DeclaredNativeInputs,
    FinalElf,
    CheckedContracts,
    RuntimeClosure,
    NativeClosure,
    HeaderClosure,
    ToolClosure,
    Policy,
    Premises,
    Context,
}

/// Producer role is descriptive wire data, not permission to run an artifact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProducerRole {
    ExistingNative,
    CheckedPreparation,
}

/// Independently decoded producer data. ExistingNative observes ordinary builds;
/// CheckedPreparation describes a private static preparation role. Neither
/// supplies protected approval or checked execution authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProducerReceipt {
    role: ProducerRole,
    limits: ProducerReceiptLimits,
    fields: [Option<ArtifactPin>; FIELDS],
}

fn pay(work: &mut TypeWorkBudget, amount: usize) -> Result<(), ReceiptFailure> {
    work.charge(amount).map_err(|()| ReceiptFailure::Resource)
}
pub(super) fn pin(bytes: &[u8], work: &mut TypeWorkBudget) -> Result<ArtifactPin, ReceiptFailure> {
    pay(work, bytes.len())?;
    Ok(ArtifactPin {
        bytes: u64::try_from(bytes.len()).map_err(|_| ReceiptFailure::Resource)?,
        sha256: Sha256::digest(bytes).into(),
    })
}

impl ProducerReceipt {
    // Producer DATA completion only: the six previously absent claim pins can
    // be attached without changing any original/native/root/image association.
    // The request assembler independently decodes all bodies after this join.
    pub(super) fn with_closure_data(
        &self,
        closures: [ArtifactPin; 6],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ReceiptFailure> {
        pay(work, FIELDS * RECORD_BYTES + 6 * RECORD_BYTES)?;
        if self.role != ProducerRole::CheckedPreparation {
            return Err(ReceiptFailure::Association);
        }
        let mut data = self.clone();
        for (field, observed) in [ReceiptField::NativeClosure, ReceiptField::HeaderClosure,
            ReceiptField::ToolClosure, ReceiptField::RuntimeClosure,
            ReceiptField::Premises, ReceiptField::Context].into_iter().zip(closures)
        {
            if data.fields[field as usize].replace(observed).is_some() {
                return Err(ReceiptFailure::Association);
            }
        }
        Ok(data)
    }
    #[cfg(test)]
    pub(super) fn substituted_configuration_data_for_test(&self, pin: ArtifactPin) -> Self {
        let mut data = self.clone();
        data.fields[ReceiptField::BuildConfiguration as usize] = Some(pin);
        data
    }
    #[cfg(test)]
    pub(super) fn substituted_pin_data_for_test(
        &self,
        field: ReceiptField,
        pin: ArtifactPin,
    ) -> Self {
        let mut data = self.clone();
        data.fields[field as usize] = Some(pin);
        data
    }
    // Independently match the final observation chain before comparing its
    // earlier native sidecar. This cloned data grants no applicability/authority.
    pub(super) fn before_root_link(
        &self,
        bytes: &[u8],
        limits: super::checked_link::Limits,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ReceiptFailure> {
        let prior = super::checked_link::matches(bytes, limits, self, work)?;
        let mut receipt = self.clone();
        receipt.fields[ReceiptField::BuildConfiguration as usize] = Some(prior);
        Ok(receipt)
    }

    pub fn role(&self) -> ProducerRole {
        self.role
    }
    pub fn declared_limits(&self) -> ProducerReceiptLimits {
        self.limits
    }

    pub fn pin(&self, field: ReceiptField) -> Option<ArtifactPin> {
        self.fields[field as usize]
    }

    /// Strict bounded independent decoding. Unknown versions, fields, duplicate
    /// or reordered records, trailing bytes and noncanonical missing pins refuse.
    pub fn decode(bytes: &[u8], limits: ProducerReceiptLimits) -> Result<Self, ReceiptFailure> {
        Self::decode_with_work(bytes, limits, &mut TypeWorkBudget::with_limit(limits.work))
    }
    /// Reads at most the configured receipt bound plus one refusal byte. This
    /// does not establish protected ownership of the reader or its source.
    pub fn read(
        reader: &mut impl Read,
        limits: ProducerReceiptLimits,
    ) -> Result<Self, ReceiptFailure> {
        let mut work = TypeWorkBudget::with_limit(limits.work);
        let mut bytes = Vec::new();
        let mut buffer = [0_u8; 8192];
        loop {
            let remaining = limits
                .receipt_bytes
                .checked_sub(bytes.len())
                .ok_or(ReceiptFailure::Resource)?;
            let requested = remaining.clamp(1, buffer.len());
            pay(&mut work, requested)?;
            let count = reader
                .read(&mut buffer[..requested])
                .map_err(|_| ReceiptFailure::Input)?;
            if count == 0 {
                break;
            }
            if count > remaining {
                return Err(ReceiptFailure::Resource);
            }
            pay(&mut work, count)?;
            bytes
                .try_reserve_exact(count)
                .map_err(|_| ReceiptFailure::Resource)?;
            bytes.extend_from_slice(&buffer[..count]);
        }
        Self::decode_with_work(&bytes, limits, &mut work)
    }
    pub(super) fn decode_with_work(
        bytes: &[u8],
        limits: ProducerReceiptLimits,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ReceiptFailure> {
        pay(work, 2)?;
        if bytes.len() > limits.receipt_bytes || limits.records < FIELDS {
            return Err(ReceiptFailure::Resource);
        }
        pay(work, bytes.len())?;
        let mut cursor = Cursor { bytes, at: 0 };
        if cursor.take(8)? != MAGIC {
            return Err(ReceiptFailure::Malformed);
        }
        if cursor.take(4)? != 1_u32.to_le_bytes() {
            return Err(ReceiptFailure::Version);
        }
        // role=existing-native, mode=existing-profile. Neither asserts static
        // closure or reinterprets ordinary shared-library builds as checked.
        let role = match cursor.take(2)? {
            [0, 0] => ProducerRole::ExistingNative,
            [1, 0] => ProducerRole::CheckedPreparation,
            _ => return Err(ReceiptFailure::Association),
        };
        let target_len = cursor.u32()? as usize;
        if cursor.take(target_len)? != super::host::NATIVE_TARGET.as_bytes() {
            return Err(ReceiptFailure::Association);
        }
        if cursor.u32()? as usize != FIELDS {
            return Err(ReceiptFailure::Malformed);
        }
        let mut declared = [0_usize; 4];
        for limit in &mut declared {
            *limit = usize::try_from(u64::from_le_bytes(
                cursor
                    .take(8)?
                    .try_into()
                    .map_err(|_| ReceiptFailure::Malformed)?,
            ))
            .map_err(|_| ReceiptFailure::Resource)?;
            if *limit == 0 {
                return Err(ReceiptFailure::Malformed);
            }
        }
        let declared = ProducerReceiptLimits {
            artifact_bytes: declared[0],
            receipt_bytes: declared[1],
            records: declared[2],
            work: declared[3],
        };
        if declared.artifact_bytes > limits.artifact_bytes
            || declared.receipt_bytes > limits.receipt_bytes
            || declared.records > limits.records
            || declared.work > limits.work
        {
            return Err(ReceiptFailure::Resource);
        }
        if bytes.len() > declared.receipt_bytes || declared.records < FIELDS {
            return Err(ReceiptFailure::Resource);
        }
        let mut fields = [None; FIELDS];
        for (index, field) in fields.iter_mut().enumerate() {
            pay(work, 1)?;
            if cursor.take(1)? != [index as u8] {
                return Err(ReceiptFailure::Malformed);
            }
            let present = cursor.take(1)?[0];
            let size = u64::from_le_bytes(
                cursor
                    .take(8)?
                    .try_into()
                    .map_err(|_| ReceiptFailure::Malformed)?,
            );
            let digest: [u8; 32] = cursor
                .take(32)?
                .try_into()
                .map_err(|_| ReceiptFailure::Malformed)?;
            *field = match present {
                0 if size == 0 && digest == [0; 32] => None,
                1 if size
                    <= u64::try_from(declared.artifact_bytes)
                        .map_err(|_| ReceiptFailure::Resource)? =>
                {
                    Some(ArtifactPin {
                        bytes: size,
                        sha256: digest,
                    })
                }
                1 => return Err(ReceiptFailure::Resource),
                _ => return Err(ReceiptFailure::Malformed),
            };
        }
        if cursor.at != bytes.len() {
            return Err(ReceiptFailure::Malformed);
        }
        // Producer-required observations cannot be erased to make a smaller
        // purported receipt. FinalElf may be absent during preparation only.
        if fields[..6].iter().any(Option::is_none) {
            return Err(ReceiptFailure::Association);
        }
        if role == ProducerRole::CheckedPreparation
            && (fields[ReceiptField::CheckedContracts as usize].is_none()
                || fields[ReceiptField::Policy as usize].is_none())
        {
            return Err(ReceiptFailure::Association);
        }
        Ok(Self {
            role,
            fields,
            limits: declared,
        })
    }
    pub(super) fn encode(
        &self,
        work: &mut TypeWorkBudget,
        limits: ProducerReceiptLimits,
    ) -> Result<Vec<u8>, ReceiptFailure> {
        let target = super::host::NATIVE_TARGET.as_bytes();
        let size = 54_usize
            .checked_add(target.len())
            .and_then(|n| n.checked_add(FIELDS * RECORD_BYTES))
            .ok_or(ReceiptFailure::Resource)?;
        pay(work, 2)?;
        if size > limits.receipt_bytes || limits.records < FIELDS {
            return Err(ReceiptFailure::Resource);
        }
        pay(work, size)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(size)
            .map_err(|_| ReceiptFailure::Resource)?;
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&1_u32.to_le_bytes());
        bytes.extend_from_slice(&[
            match self.role {
                ProducerRole::ExistingNative => 0,
                ProducerRole::CheckedPreparation => 1,
            },
            0,
        ]);
        bytes.extend_from_slice(&(target.len() as u32).to_le_bytes());
        bytes.extend_from_slice(target);
        bytes.extend_from_slice(&(FIELDS as u32).to_le_bytes());
        for limit in [
            self.limits.artifact_bytes,
            self.limits.receipt_bytes,
            self.limits.records,
            self.limits.work,
        ] {
            bytes.extend_from_slice(
                &u64::try_from(limit)
                    .map_err(|_| ReceiptFailure::Resource)?
                    .to_le_bytes(),
            );
        }
        for (index, field) in self.fields.iter().enumerate() {
            pay(work, 1)?;
            bytes.push(index as u8);
            bytes.push(u8::from(field.is_some()));
            let field = field.unwrap_or(ArtifactPin {
                bytes: 0,
                sha256: [0; 32],
            });
            if field.bytes
                > u64::try_from(limits.artifact_bytes).map_err(|_| ReceiptFailure::Resource)?
            {
                return Err(ReceiptFailure::Resource);
            }
            bytes.extend_from_slice(&field.bytes.to_le_bytes());
            bytes.extend_from_slice(&field.sha256);
        }
        Ok(bytes)
    }
    /// Compares independently decoded data under explicit work bounds. The
    /// expected value is another claim, not an approval or protected context.
    pub fn matches_expected(
        &self,
        expected: &Self,
        limits: ProducerReceiptLimits,
    ) -> Result<(), ReceiptFailure> {
        let mut work = TypeWorkBudget::with_limit(limits.work);
        pay(&mut work, FIELDS * RECORD_BYTES + 32)?;
        if self != expected {
            return Err(ReceiptFailure::Association);
        }
        Ok(())
    }
    /// Checks independent policy bytes against this receipt's exact image/facts
    /// pins. Both sides remain producer claims; successful matching is not approval.
    pub fn matches_checked_policy(
        &self,
        bytes: &[u8],
        limits: ProducerReceiptLimits,
    ) -> Result<(), ReceiptFailure> {
        let mut work = TypeWorkBudget::with_limit(limits.work);
        if self.role != ProducerRole::CheckedPreparation || bytes.len() > limits.artifact_bytes {
            return Err(ReceiptFailure::Association);
        }
        let observed = pin(bytes, &mut work)?;
        if self.pin(ReceiptField::Policy) != Some(observed) {
            return Err(ReceiptFailure::Association);
        }
        super::checked_producer::decode_policy(
            bytes,
            self.pin(ReceiptField::ProgramImage)
                .ok_or(ReceiptFailure::Association)?,
            self.pin(ReceiptField::ExpectedFacts)
                .ok_or(ReceiptFailure::Association)?,
            &mut work,
        )?;
        Ok(())
    }

    /// Existing-profile producer records lack checked required closure. Matching
    /// claim hashes cannot fill absent originals, headers, tools or premises.
    pub fn check_checked_applicability(&self) -> Result<(), ReceiptFailure> {
        Err(ReceiptFailure::IncompleteClosure)
    }
    /// No protected context/store constructor exists in this slice. Same-UID
    /// receipt files and exact claim matches remain untrusted producer data.
    pub fn activate(&self) -> Result<std::convert::Infallible, ReceiptFailure> {
        Err(ReceiptFailure::ProtectedAuthorityUnavailable)
    }
}

struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Cursor<'a> {
    fn take(&mut self, count: usize) -> Result<&'a [u8], ReceiptFailure> {
        let end = self
            .at
            .checked_add(count)
            .ok_or(ReceiptFailure::Malformed)?;
        let bytes = self
            .bytes
            .get(self.at..end)
            .ok_or(ReceiptFailure::Malformed)?;
        self.at = end;
        Ok(bytes)
    }
    fn u32(&mut self) -> Result<u32, ReceiptFailure> {
        Ok(u32::from_le_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| ReceiptFailure::Malformed)?,
        ))
    }
}

#[derive(Debug)]
pub(super) struct ReceiptSeed {
    receipt: ProducerReceipt,
    limits: ProducerReceiptLimits,
    work: TypeWorkBudget,
    configuration: Option<[ArtifactPin; 3]>,
}
impl ReceiptSeed {
    pub(super) fn receipt(&self) -> &ProducerReceipt {
        &self.receipt
    }
    pub(super) fn from_emission(
        build: &super::image::NativeBuildImage,
        program: &crate::core::ValidatedEffectProgram,
        provenance: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
        emission: &super::emit::NativeHostEmission,
        configuration: &[u8],
        limits: ProducerReceiptLimits,
    ) -> Result<Self, ReceiptFailure> {
        Self::from_emission_kind(
            build,
            program,
            provenance,
            emission,
            configuration,
            limits,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn from_checked_emission(
        build: &super::image::NativeBuildImage,
        program: &crate::core::ValidatedEffectProgram,
        provenance: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
        emission: &super::emit::NativeHostEmission,
        configuration: &[u8],
        limits: ProducerReceiptLimits,
        policy: crate::foreign::source_runtime::CheckedOwnerLimits,
    ) -> Result<Self, ReceiptFailure> {
        Self::from_emission_kind(
            build,
            program,
            provenance,
            emission,
            configuration,
            limits,
            Some(policy),
        )
    }

    /// Root code identity is independently derived from closed code/config
    /// inputs. The full producer-codec/original re-admission remains exactly
    /// the existing checked path; this changes only the runtime DATA pin.
    pub(super) fn from_root_emission(
        build: &super::image::NativeBuildImage,
        program: &crate::core::ValidatedEffectProgram,
        provenance: &[(crate::module::ModuleId, std::sync::Arc<crate::source::SourceFile>)],
        emission: &super::emit::NativeHostEmission,
        configuration: &[u8],
        limits: ProducerReceiptLimits,
        root: (&super::checked_root_identity::RootCodeIdentity, crate::foreign::source_runtime::CheckedOwnerLimits),
    ) -> Result<Self, ReceiptFailure> {
        let mut seed = Self::from_checked_emission(build, program, provenance, emission, configuration, limits, root.1)?;
        seed.receipt.fields[ReceiptField::RuntimeFingerprint as usize] = Some(pin(root.0.bytes(), &mut seed.work)?);
        Ok(seed)
    }

    #[allow(clippy::too_many_arguments)]
    fn from_emission_kind(
        build: &super::image::NativeBuildImage,
        program: &crate::core::ValidatedEffectProgram,
        provenance: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
        emission: &super::emit::NativeHostEmission,
        configuration: &[u8],
        limits: ProducerReceiptLimits,
        policy: Option<crate::foreign::source_runtime::CheckedOwnerLimits>,
    ) -> Result<Self, ReceiptFailure> {
        let mut work = TypeWorkBudget::with_limit(limits.work);
        let (image, facts) = emission.payloads.bytes();
        let applicability = super::checked_admission::Applicability {
            version: 1,
            mode: super::checked_admission::Mode::InProcess,
            target: super::host::NATIVE_TARGET,
            runtime: super::runtime_fingerprint(),
            native_closure: [0; 32],
            premises: [0; 32],
            context: None,
            limits: super::checked_admission::Limits {
                image: limits.artifact_bytes,
                facts: limits.artifact_bytes,
                bridges: limits.records,
                metadata: limits.receipt_bytes,
            },
        };
        let admit = if policy.is_some() {
            super::checked_admission::PassivePlan::admit_checked_preparation
        } else {
            super::checked_admission::PassivePlan::admit
        };
        admit(
            build,
            program,
            provenance,
            image,
            facts,
            &applicability,
            &mut work,
        )
        .map_err(|error| {
            if error == super::checked_admission::Failure::Resource {
                ReceiptFailure::Resource
            } else {
                ReceiptFailure::Association
            }
        })?;
        let mut fields = [None; FIELDS];
        for (field, bytes) in [
            (ReceiptField::ProgramImage, image),
            (ReceiptField::ExpectedFacts, facts),
            (ReceiptField::GeneratedRust, emission.rust_source.as_bytes()),
            (
                ReceiptField::RuntimeFingerprint,
                &super::runtime_fingerprint()[..],
            ),
            (ReceiptField::BuildConfiguration, configuration),
        ] {
            if bytes.len() > limits.artifact_bytes {
                return Err(ReceiptFailure::Resource);
            }
            fields[field as usize] = Some(pin(bytes, &mut work)?);
        }
        // Full ABI/source facts and typed wrapper source are separately pinned
        // above. Preserve ordered emitted wire coordinates without a new registry.
        pay(
            &mut work,
            build
                .libraries
                .len()
                .checked_add(build.bridges.len())
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        let count = build
            .libraries
            .iter()
            .try_fold(2_usize, |n, l| {
                n.checked_add(4)?.checked_add(l.members.len())
            })
            .and_then(|n| {
                build
                    .bridges
                    .len()
                    .checked_mul(5)
                    .and_then(|b| n.checked_add(b))
            })
            .and_then(|n| n.checked_mul(8))
            .ok_or(ReceiptFailure::Resource)?;
        if count > limits.artifact_bytes {
            return Err(ReceiptFailure::Resource);
        }
        pay(&mut work, count)?;
        let mut mappings = Vec::new();
        mappings
            .try_reserve_exact(count)
            .map_err(|_| ReceiptFailure::Resource)?;
        let mut number = |n: usize| -> Result<(), ReceiptFailure> {
            mappings.extend_from_slice(
                &u64::try_from(n)
                    .map_err(|_| ReceiptFailure::Resource)?
                    .to_le_bytes(),
            );
            Ok(())
        };
        number(build.libraries.len())?;
        number(build.bridges.len())?;
        for library in &build.libraries {
            for n in [
                library.image_library as usize,
                library.module as usize,
                library.ordinal as usize,
                library.members.len(),
            ] {
                number(n)?;
            }
            for &member in &library.members {
                number(member)?;
            }
        }
        for bridge in &build.bridges {
            for n in [
                bridge.image_symbol,
                bridge.symbol_index,
                bridge.operation_module,
                bridge.operation_effect,
                bridge.operation_local,
            ] {
                number(n as usize)?;
            }
        }
        fields[ReceiptField::OriginalMappings as usize] = Some(pin(&mappings, &mut work)?);
        let role = if let Some(policy) = policy {
            let actual = emission
                .payloads
                .checked_policy()
                .ok_or(ReceiptFailure::Association)?;
            let expected = super::checked_producer::policy_bytes(
                program,
                fields[ReceiptField::ProgramImage as usize].ok_or(ReceiptFailure::Association)?,
                fields[ReceiptField::ExpectedFacts as usize].ok_or(ReceiptFailure::Association)?,
                policy,
                &mut work,
            )?;
            pay(&mut work, actual.len())?;
            if actual != expected {
                return Err(ReceiptFailure::Association);
            }
            fields[ReceiptField::Policy as usize] = Some(pin(actual, &mut work)?);
            // Bind the complete encoded checked originals/Type/Row/source/copy
            // mappings, not a reduced semantic registry or an accepted digest.
            let count = image
                .len()
                .checked_add(facts.len())
                .and_then(|n| n.checked_add(16))
                .ok_or(ReceiptFailure::Resource)?;
            if count > limits.artifact_bytes {
                return Err(ReceiptFailure::Resource);
            }
            pay(&mut work, count)?;
            let mut sha = Sha256::new();
            sha.update((image.len() as u64).to_le_bytes());
            sha.update(image);
            sha.update((facts.len() as u64).to_le_bytes());
            sha.update(facts);
            fields[ReceiptField::CheckedContracts as usize] = Some(ArtifactPin {
                bytes: count as u64,
                sha256: sha.finalize().into(),
            });
            ProducerRole::CheckedPreparation
        } else {
            if emission.payloads.checked_policy().is_some() {
                return Err(ReceiptFailure::Association);
            }
            ProducerRole::ExistingNative
        };
        let receipt = ProducerReceipt {
            role,
            fields,
            limits,
        };
        // Admit storage/wire bounds now, before any native tool can run.
        let _ = receipt.encode(&mut work, limits)?;
        Ok(Self {
            receipt,
            limits,
            work,
            configuration: None,
        })
    }
    pub(super) fn observe_native_inputs(
        &mut self,
        inputs: &[super::host::NativeLinkInput],
    ) -> Result<(), ReceiptFailure> {
        let mut combined = Sha256::new();
        pay(&mut self.work, inputs.len())?;
        let mut total = 0_usize;
        for input in inputs {
            let path = input.path().as_os_str().as_encoded_bytes();
            total = total
                .checked_add(49)
                .and_then(|n| n.checked_add(path.len()))
                .ok_or(ReceiptFailure::Resource)?;
            if total > self.limits.artifact_bytes {
                return Err(ReceiptFailure::Resource);
            }
            pay(
                &mut self.work,
                path.len().checked_add(8).ok_or(ReceiptFailure::Resource)?,
            )?;
            combined.update(
                u64::try_from(path.len())
                    .map_err(|_| ReceiptFailure::Resource)?
                    .to_le_bytes(),
            );
            combined.update(path);
            let observed = observe_file(input.path(), self.limits.artifact_bytes, &mut self.work)?;
            pay(&mut self.work, 41)?;
            combined.update([match input {
                super::host::NativeLinkInput::StaticArchive(_) => 0,
                super::host::NativeLinkInput::SharedLibrary(_) => 1,
            }]);
            combined.update(observed.bytes.to_le_bytes());
            combined.update(observed.sha256);
        }
        self.receipt.fields[ReceiptField::DeclaredNativeInputs as usize] = Some(ArtifactPin {
            bytes: u64::try_from(total).map_err(|_| ReceiptFailure::Resource)?,
            sha256: combined.finalize().into(),
        });
        Ok(())
    }
    pub(super) fn verify_native_inputs(
        &mut self,
        inputs: &[super::host::NativeLinkInput],
    ) -> Result<(), ReceiptFailure> {
        let previous = self.receipt.pin(ReceiptField::DeclaredNativeInputs);
        self.observe_native_inputs(inputs)?;
        let observed = self.receipt.pin(ReceiptField::DeclaredNativeInputs);
        self.receipt.fields[ReceiptField::DeclaredNativeInputs as usize] = previous;
        if previous != observed {
            return Err(ReceiptFailure::Association);
        }
        Ok(())
    }
    pub(super) fn verify_emitted_files(
        &mut self,
        paths: &[std::path::PathBuf; 3],
    ) -> Result<(), ReceiptFailure> {
        for (path, field) in paths.iter().zip([
            ReceiptField::GeneratedRust,
            ReceiptField::ProgramImage,
            ReceiptField::ExpectedFacts,
        ]) {
            let observed = observe_file(path, self.limits.artifact_bytes, &mut self.work)?;
            pay(&mut self.work, 40)?;
            if Some(observed) != self.receipt.pin(field) {
                return Err(ReceiptFailure::Association);
            }
        }
        if self.receipt.role == ProducerRole::CheckedPreparation {
            let path = paths[1]
                .parent()
                .ok_or(ReceiptFailure::Input)?
                .join("checked-policy.bin");
            let observed = observe_file(&path, self.limits.artifact_bytes, &mut self.work)?;
            pay(&mut self.work, 40)?;
            if Some(observed) != self.receipt.pin(ReceiptField::Policy) {
                return Err(ReceiptFailure::Association);
            }
        }
        Ok(())
    }
    pub(super) fn observe_configuration(
        &mut self,
        paths: &[std::path::PathBuf; 3],
    ) -> Result<(), ReceiptFailure> {
        let pins = [
            observe_file(&paths[0], self.limits.artifact_bytes, &mut self.work)?,
            observe_file(&paths[1], self.limits.artifact_bytes, &mut self.work)?,
            observe_file(&paths[2], self.limits.artifact_bytes, &mut self.work)?,
        ];
        self.configuration = Some(pins);
        Ok(())
    }
    pub(super) fn verify_configuration(
        &mut self,
        paths: &[std::path::PathBuf; 3],
    ) -> Result<(), ReceiptFailure> {
        let before = self.configuration.ok_or(ReceiptFailure::Association)?;
        self.observe_configuration(paths)?;
        let after = self.configuration.ok_or(ReceiptFailure::Association)?;
        self.configuration = Some(before);
        // Cargo may add its generated root package to Cargo.lock. Preserve both
        // seed and resolved lock observations; manifest/toolchain must match.
        if before[..2] != after[..2] {
            return Err(ReceiptFailure::Association);
        }
        let mut sha = Sha256::new();
        pay(&mut self.work, 40 * 7)?;
        for entry in std::iter::once(
            self.receipt
                .pin(ReceiptField::BuildConfiguration)
                .ok_or(ReceiptFailure::Association)?,
        )
        .chain(before)
        .chain(after)
        {
            sha.update(entry.bytes.to_le_bytes());
            sha.update(entry.sha256);
        }
        self.receipt.fields[ReceiptField::BuildConfiguration as usize] = Some(ArtifactPin {
            bytes: 40 * 7,
            sha256: sha.finalize().into(),
        });
        Ok(())
    }
    /// The artifact-root lock is already settled and its full BuildData is the
    /// configuration field. Reobserve all three actual files without replacing
    /// that closed binding with the legacy seven-pin lock-settling fold.
    pub(super) fn verify_settled_configuration(
        &mut self,
        paths: &[std::path::PathBuf; 3],
    ) -> Result<(), ReceiptFailure> {
        let before = self.configuration.ok_or(ReceiptFailure::Association)?;
        self.observe_configuration(paths)?;
        let after = self.configuration.ok_or(ReceiptFailure::Association)?;
        self.configuration = Some(before);
        pay(&mut self.work, 40 * 3)?;
        if before != after { return Err(ReceiptFailure::Association); }
        Ok(())
    }
    pub(super) fn bind_native_build(
        &mut self,
        bytes: &[u8],
        limits: super::checked_native_build::Limits,
    ) -> Result<(), ReceiptFailure> {
        let (before, observed) =
            super::checked_native_build::binding(bytes, limits, &mut self.work)?;
        if self.receipt.role != ProducerRole::CheckedPreparation
            || self.receipt.pin(ReceiptField::BuildConfiguration) != Some(before)
        {
            return Err(ReceiptFailure::Association);
        }
        self.receipt.fields[ReceiptField::BuildConfiguration as usize] = Some(
            super::checked_native_build::configuration_binding(before, observed, &mut self.work)?,
        );
        Ok(())
    }
    pub(super) fn bind_root_link(
        &mut self,
        bytes: &[u8],
        limits: super::checked_link::Limits,
    ) -> Result<(), ReceiptFailure> {
        if self.receipt.role != ProducerRole::CheckedPreparation {
            return Err(ReceiptFailure::Association);
        }
        let (before, record) =
            super::checked_link::binding(bytes, limits, &self.receipt, &mut self.work)?;
        self.receipt.fields[ReceiptField::BuildConfiguration as usize] = Some(
            super::checked_link::configuration_binding(before, record, &mut self.work)?,
        );
        Ok(())
    }
    pub(super) fn finalize(self, file: &Path) -> Result<Vec<u8>, ReceiptFailure> {
        self.finalize_with_root_link(file, None)
    }
    pub(super) fn finalize_with_root_link(
        mut self,
        file: &Path,
        root_link: Option<(&[u8], super::checked_link::Limits)>,
    ) -> Result<Vec<u8>, ReceiptFailure> {
        if self.configuration.is_none()
            || self
                .receipt
                .pin(ReceiptField::DeclaredNativeInputs)
                .is_none()
        {
            return Err(ReceiptFailure::Association);
        }
        self.receipt.fields[ReceiptField::FinalElf as usize] =
            Some(if self.receipt.role == ProducerRole::CheckedPreparation {
                observe_object(file, self.limits.artifact_bytes, &mut self.work, true, true)?
            } else {
                observe_elf(file, self.limits.artifact_bytes, &mut self.work)?
            });
        if let Some((bytes, limits)) = root_link {
            self.receipt
                .before_root_link(bytes, limits, &mut self.work)?;
        }
        self.receipt.encode(&mut self.work, self.limits)
    }
}

/// A bounded observation of one opened regular object. No immutable-file,
/// compilation/link correspondence or future pathname identity is asserted.
#[cfg(unix)]
pub(super) fn observe_file(
    path: &Path,
    cap: usize,
    work: &mut TypeWorkBudget,
) -> Result<ArtifactPin, ReceiptFailure> {
    observe_object(path, cap, work, false, false)
}
/// Reuse strict bounded same-object ELF inspection for the separate launcher
/// transaction. This is an observed file pin, never executable approval.
pub(super) fn observe_static_image(path: &Path, cap: usize, work: &mut TypeWorkBudget)
    -> Result<ArtifactPin, ReceiptFailure> {
    observe_object(path, cap, work, true, true)
}
#[cfg(unix)]
fn observe_elf(
    path: &Path,
    cap: usize,
    work: &mut TypeWorkBudget,
) -> Result<ArtifactPin, ReceiptFailure> {
    observe_object(path, cap, work, true, false)
}
#[cfg(not(unix))]
pub(super) fn observe_file(_: &Path, _: usize, _: &mut TypeWorkBudget) -> Result<ArtifactPin, ReceiptFailure> {
    Err(ReceiptFailure::Input)
}
#[cfg(not(unix))]
fn observe_elf(_: &Path, _: usize, _: &mut TypeWorkBudget) -> Result<ArtifactPin, ReceiptFailure> {
    Err(ReceiptFailure::Input)
}
#[cfg(not(unix))]
fn observe_object(
    _: &Path,
    _: usize,
    _: &mut TypeWorkBudget,
    _: bool,
    _: bool,
) -> Result<ArtifactPin, ReceiptFailure> {
    Err(ReceiptFailure::Input)
}

#[cfg(unix)]
fn observe_object(
    path: &Path,
    cap: usize,
    work: &mut TypeWorkBudget,
    elf: bool,
    strict: bool,
) -> Result<ArtifactPin, ReceiptFailure> {
    use std::os::unix::fs::MetadataExt;
    pay(work, 3)?;
    let named = std::fs::symlink_metadata(path).map_err(|_| ReceiptFailure::Input)?;
    if !named.is_file() {
        return Err(ReceiptFailure::Input);
    }
    let mut file = File::open(path).map_err(|_| ReceiptFailure::Input)?;
    let before = file.metadata().map_err(|_| ReceiptFailure::Input)?;
    let identity = |m: &std::fs::Metadata| {
        (
            m.dev(),
            m.ino(),
            m.len(),
            m.mode(),
            m.mtime(),
            m.mtime_nsec(),
            m.ctime(),
            m.ctime_nsec(),
        )
    };
    if !before.is_file() || identity(&named) != identity(&before) {
        return Err(ReceiptFailure::Input);
    }
    if before.len() > cap as u64 {
        return Err(ReceiptFailure::Resource);
    }
    let mut sha = Sha256::new();
    let mut total = 0_usize;
    let mut buffer = [0_u8; 8192];
    let mut header = [0_u8; 64];
    let mut header_len = 0;
    let mut prefix = Vec::new();
    if strict {
        pay(work, 4096)?;
        prefix
            .try_reserve_exact(4096)
            .map_err(|_| ReceiptFailure::Resource)?;
    }
    loop {
        // Charge the bounded attempted read before I/O; no refunds on failure.
        let allowed = cap
            .checked_sub(total)
            .ok_or(ReceiptFailure::Resource)?
            .min(buffer.len());
        let count = allowed.max(1);
        pay(work, count)?;
        let read = file
            .read(&mut buffer[..count])
            .map_err(|_| ReceiptFailure::Input)?;
        if read == 0 {
            break;
        }
        total = total.checked_add(read).ok_or(ReceiptFailure::Resource)?;
        if total > cap {
            return Err(ReceiptFailure::Resource);
        }
        let header_part = read.min(header.len() - header_len);
        header[header_len..header_len + header_part].copy_from_slice(&buffer[..header_part]);
        header_len += header_part;
        if strict {
            let extra = read.min(4096 - prefix.len());
            pay(work, extra)?;
            prefix.extend_from_slice(&buffer[..extra]);
        }
        sha.update(&buffer[..read]);
    }
    pay(work, 1)?;
    let after = file.metadata().map_err(|_| ReceiptFailure::Input)?;
    if identity(&before) != identity(&after) || total as u64 != before.len() {
        return Err(ReceiptFailure::Association);
    }
    if elf {
        pay(work, header.len())?;
        if header_len != 64
            || &header[..7] != b"\x7fELF\x02\x01\x01"
            || !matches!(u16::from_le_bytes([header[16], header[17]]), 2 | 3)
            || u16::from_le_bytes([header[18], header[19]]) != 62
            || u32::from_le_bytes(
                header[20..24]
                    .try_into()
                    .map_err(|_| ReceiptFailure::Input)?,
            ) != 1
            || u16::from_le_bytes([header[52], header[53]]) != 64
        {
            return Err(ReceiptFailure::Input);
        }
    }
    if strict {
        inspect_static_elf(&prefix, total, work)?;
    }
    Ok(ArtifactPin {
        bytes: total as u64,
        sha256: sha.finalize().into(),
    })
}

/// Passive same-open-object ELF framing, not loading/ABI/native conformance proof.
fn inspect_static_elf(
    prefix: &[u8],
    total: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    pay(work, 64)?;
    if prefix.len() < 64 || u16::from_le_bytes([prefix[16], prefix[17]]) != 2 {
        return Err(ReceiptFailure::Input);
    }
    let u64at = |offset: usize| -> Result<u64, ReceiptFailure> {
        Ok(u64::from_le_bytes(
            prefix
                .get(offset..offset + 8)
                .ok_or(ReceiptFailure::Input)?
                .try_into()
                .map_err(|_| ReceiptFailure::Input)?,
        ))
    };
    let offset = usize::try_from(u64at(32)?).map_err(|_| ReceiptFailure::Resource)?;
    let size = u16::from_le_bytes([prefix[54], prefix[55]]) as usize;
    let count = u16::from_le_bytes([prefix[56], prefix[57]]) as usize;
    if offset < 64 || size != 56 || count == 0 || count > 64 {
        return Err(ReceiptFailure::Input);
    }
    let end = count
        .checked_mul(size)
        .and_then(|n| n.checked_add(offset))
        .ok_or(ReceiptFailure::Resource)?;
    let table = prefix.get(offset..end).ok_or(ReceiptFailure::Input)?;
    let entry = u64at(24)?;
    let mut loads = 0usize;
    let mut executable_entry = false;
    for row in table.chunks_exact(56) {
        pay(work, 56)?;
        let kind = u32::from_le_bytes(row[..4].try_into().map_err(|_| ReceiptFailure::Input)?);
        if matches!(kind, 2 | 3) {
            return Err(ReceiptFailure::Input);
        }
        if kind == 1 {
            loads += 1;
            let word = |at: usize| -> Result<u64, ReceiptFailure> {
                Ok(u64::from_le_bytes(
                    row[at..at + 8]
                        .try_into()
                        .map_err(|_| ReceiptFailure::Input)?,
                ))
            };
            let start = word(16)?;
            let memory = word(40)?;
            let files = word(32)?;
            if files > memory
                || word(8)?
                    .checked_add(files)
                    .is_none_or(|end| end > total as u64)
            {
                return Err(ReceiptFailure::Input);
            }
            let end = start.checked_add(memory).ok_or(ReceiptFailure::Input)?;
            if row[4] & 1 != 0 && start <= entry && entry < end {
                executable_entry = true;
            }
        }
    }
    if loads == 0 || !executable_entry {
        return Err(ReceiptFailure::Input);
    }
    Ok(())
}

#[cfg(test)]
#[path = "checked_receipt_tests.rs"]
mod tests;
