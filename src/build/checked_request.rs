//! Bounded applicability request DATA. Neither parsing nor a claimed review status
//! establishes protected applicability or gives access to an execution API.
use super::checked_receipt::{
    ArtifactPin, ProducerReceipt, ProducerReceiptLimits, ProducerRole, ReceiptFailure,
    ReceiptField, pin,
};
use crate::types::TypeWorkBudget;
use serde::{Deserialize, Serialize};

/// Explicit request parsing/storage bounds, separate from legacy build work.
#[derive(Clone, Copy, Debug)]
pub struct RequestLimits {
    pub bytes: usize,
    pub work: usize,
}
impl Default for RequestLimits {
    fn default() -> Self {
        Self {
            bytes: 8 * 1024 * 1024,
            work: 128 * 1024 * 1024,
        }
    }
}
const CLOSURES: [ReceiptField; 6] = [
    ReceiptField::NativeClosure,
    ReceiptField::HeaderClosure,
    ReceiptField::ToolClosure,
    ReceiptField::RuntimeClosure,
    ReceiptField::Premises,
    ReceiptField::Context,
];
// Versioned request text instantiates AD16's finite review domains. Proposed
// status is retained explicitly; these strings are not an independent review.
const PREMISES: [&str; 6] = [
    "AD16/1 allocation-lifetime: allocation is null or has the declared valid extent/alignment and live lifetime; teardown receives the exact compatible still-live pointer once with declared disposition. Initialized bytes require the exact supported operation promise, not malloc or opaque State.",
    "AD16/1 allocator: pinned allocator/runtime conforms through initialization, arenas, TLS, locking, reentrancy, failure/diagnostics and abort. No unreviewed allocator plugin/debug/tunable configuration is applicable; native memory integrity remains trusted.",
    "AD16/1 lifecycle: prepaid guard precedes acquisition; returned ownership/disposition commits before fallible source delivery. Null/partial/report refusal, abandoned continuation, panic/unwind/drop and pending cleanup are reviewed. Native return is not source completion; local discharge is not physical free.",
    "AD16/1 runtime: exact _start/_init/_fini, preinit/init/fini arrays, IFUNC/TLS, libc/Rust startup, constructors, signals/thread entries, registered cleanup and error/IO/allocation/panic/unwind/shutdown conform. Unknown callbacks/registrations and source/native callback facilities are excluded.",
    "AD16/1 strict-loading: built-in C locale remains global and per-thread; direct/indirect module loading, plugins, NSS dispatch, arbitrary charset conversion and locale replacement are excluded. Structural ELF facts or retained loader names do not prove this premise. Independent finite conformity review is required, not a formal whole-libc proof.",
    "AD16/1 shared-host: address space, credentials, supplementary groups and ordinary authority remain shared; faults, aborts, corruption and nonreturning native calls can lose the host. This is the in-process trusted closure, not isolation.",
];
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Premise {
    id: u32,
    text: String,
    status: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Part {
    id: u32,
    bytes: Vec<u8>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    version: u32,
    target: String,
    mode: String,
    role: String,
    linked: bool,
    parts: Vec<Part>,
    premises: Vec<Premise>,
    native_limits: Option<super::checked_native_build::Limits>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    root_build: Option<super::checked_root_project::BuildData>,
}
// Closed supported conformity addendum DATA. It carries the actual admitted
// originals and validated native/root records, not an arbitrary digest body.
// Reviewed-claim strings still need the separate protected per-image approval.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ConformityAddendum {
    version: u32,
    category: String,
    profile: String,
    program: Vec<u8>,
    facts: Vec<u8>,
    policy: Vec<u8>,
    native_build: Vec<u8>,
    root_link: Vec<u8>,
    premises: Vec<Premise>,
    context: Vec<u8>,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContextIdentity {
    device: u64,
    inode: u64,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContextData {
    version: u32,
    uid: u32,
    gid: u32,
    groups: Vec<u32>,
    user_namespace: ContextIdentity,
    mount_namespace: ContextIdentity,
    uid_map_sha256: String,
    mountinfo_sha256: String,
    store: String,
    store_identity: ContextIdentity,
    stdio: String,
    context_version: u32,
    premise_version: u32,
    launch_version: u32,
    request_bytes: usize,
    request_work: usize,
    image_bytes: usize,
    image_work: usize,
    program_headers: usize,
}
fn context_data(bytes: &[u8], work: &mut TypeWorkBudget) -> Result<(), ReceiptFailure> {
    if bytes.len() > 65536 {
        return Err(ReceiptFailure::Resource);
    }
    pay(
        work,
        bytes.len().checked_mul(4).ok_or(ReceiptFailure::Resource)?,
    )?;
    let c: ContextData = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    let hash = |s: &str| {
        s.len() == 64
            && s.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    };
    if c.version != 1 || c.context_version != 1 || c.premise_version != 1 || c.launch_version != 1 {
        return Err(ReceiptFailure::Version);
    }
    if c.uid == 0
        || c.gid == 0
        || c.groups.len() > 128
        || c.groups.windows(2).any(|p| p[0] >= p[1])
        || c.stdio != "null-read-null-write-v1"
        || !hash(&c.uid_map_sha256)
        || !hash(&c.mountinfo_sha256)
        || !std::path::Path::new(&c.store).is_absolute()
        || c.store.len() > 4096
        || c.store.as_bytes().contains(&0)
        || std::path::Path::new(&c.store).components().any(|p| {
            matches!(
                p,
                std::path::Component::ParentDir | std::path::Component::CurDir
            )
        })
        || [&c.user_namespace, &c.mount_namespace, &c.store_identity]
            .iter()
            .any(|i| i.device == 0 || i.inode == 0)
    {
        return Err(ReceiptFailure::Association);
    }
    if c.request_bytes == 0
        || c.request_bytes > 64 * 1024 * 1024
        || c.request_work == 0
        || c.request_work > 1024 * 1024 * 1024
        || c.image_bytes == 0
        || c.image_bytes > 2usize.pow(31)
        || c.image_work == 0
        || c.image_work > 16 * 1024 * 1024 * 1024
        || c.program_headers == 0
        || c.program_headers > 4096
    {
        return Err(ReceiptFailure::Resource);
    }
    Ok(())
}
fn conformity_data(
    raw: &[u8],
    category: usize,
    slots: &[Option<&[u8]>; 14],
    premises: &[Premise],
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    pay(
        work,
        raw.len().checked_mul(4).ok_or(ReceiptFailure::Resource)?,
    )?;
    let c: ConformityAddendum =
        serde_json::from_slice(raw).map_err(|_| ReceiptFailure::Malformed)?;
    if c.version != 1 {
        return Err(ReceiptFailure::Version);
    }
    let names = ["native", "header", "tool", "runtime"];
    if c.category != names[category]
        || c.profile != "linux-x86_64-gnu-static-initialized8-owner-v1"
        || c.premises != premises
    {
        return Err(ReceiptFailure::Association);
    }
    for (actual, slot) in [
        (c.program.as_slice(), 1),
        (c.facts.as_slice(), 2),
        (c.policy.as_slice(), 3),
        (c.native_build.as_slice(), 5),
        (c.root_link.as_slice(), 6),
        (c.context.as_slice(), 13),
    ] {
        pay(work, actual.len())?;
        if Some(actual) != slots[slot] {
            return Err(ReceiptFailure::Association);
        }
    }
    Ok(())
}

/// Independent request summary. All fields describe untrusted data; even a
/// complete request needs the separate independently protected approval.
#[derive(Debug)]
pub struct ApplicabilityRequest {
    request: ArtifactPin,
    receipt: ArtifactPin,
    image: Option<ArtifactPin>,
    premises: ArtifactPin,
    linked: bool,
    missing: Vec<ReceiptField>,
    proposed: bool,
    context: Option<ArtifactPin>,
}
impl ApplicabilityRequest {
    pub fn decode(bytes: &[u8], limits: RequestLimits) -> Result<Self, ReceiptFailure> {
        decode_with_work(bytes, limits, &mut TypeWorkBudget::with_limit(limits.work))
    }
    pub fn request_pin(&self) -> ArtifactPin {
        self.request
    }
    pub fn receipt_pin(&self) -> ArtifactPin {
        self.receipt
    }
    pub fn final_image_pin(&self) -> Option<ArtifactPin> {
        self.image
    }
    pub fn premise_pin(&self) -> ArtifactPin {
        self.premises
    }
    pub fn context_pin(&self) -> Option<ArtifactPin> {
        self.context
    }
    pub fn linked(&self) -> bool {
        self.linked
    }
    pub fn missing_fields(&self) -> &[ReceiptField] {
        &self.missing
    }
    /// Completeness DATA only; this never grants approval or opens a guard.
    pub fn check_complete(&self) -> Result<(), ReceiptFailure> {
        if !self.linked || !self.missing.is_empty() || self.proposed {
            Err(ReceiptFailure::IncompleteClosure)
        } else {
            Ok(())
        }
    }
}
fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), ReceiptFailure> {
    work.charge(n).map_err(|()| ReceiptFailure::Resource)
}
fn image_error(e: super::image::ImageFailure) -> ReceiptFailure {
    use super::image::ImageFailure;
    match e {
        ImageFailure::Resource
        | ImageFailure::CoreAdmission(crate::core::BuildError::TypeWorkExceeded) => {
            ReceiptFailure::Resource
        }
        ImageFailure::Validation(error)
            if error.reason() == crate::core::ValidationReason::Resource =>
        {
            ReceiptFailure::Resource
        }
        _ => ReceiptFailure::Association,
    }
}
pub(super) fn native_image_error(error: super::image::NativeImageFailure) -> ReceiptFailure {
    match error {
        super::image::NativeImageFailure::Image(error) => image_error(error),
        super::image::NativeImageFailure::Bridge(error) if error.is_resource() => {
            ReceiptFailure::Resource
        }
        _ => ReceiptFailure::Association,
    }
}
pub(super) fn emission_error(error: super::emit::EmissionFailure) -> ReceiptFailure {
    match error {
        super::emit::EmissionFailure::Image(error) => image_error(error),
        super::emit::EmissionFailure::Resource => ReceiptFailure::Resource,
        super::emit::EmissionFailure::Bridge(error) if error.is_resource() => {
            ReceiptFailure::Resource
        }
        _ => ReceiptFailure::Association,
    }
}
fn decode_with_work(
    bytes: &[u8],
    limits: RequestLimits,
    work: &mut TypeWorkBudget,
) -> Result<ApplicabilityRequest, ReceiptFailure> {
    if limits.bytes == 0 || limits.bytes > 64 * 1024 * 1024 || bytes.len() > limits.bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(
        work,
        bytes.len().checked_mul(8).ok_or(ReceiptFailure::Resource)?,
    )?;
    let record: Record = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    if !matches!((record.version, record.root_build.is_some()), (1, false) | (2, true)) {
        return Err(ReceiptFailure::Version);
    }
    if record.target != super::host::NATIVE_TARGET
        || record.mode != "checked-inprocess-static"
        || record.role != "checked-preparation"
    {
        return Err(ReceiptFailure::Association);
    }
    if record.parts.len() < 5 || record.parts.len() > 14 || record.premises.len() != PREMISES.len()
    {
        return Err(ReceiptFailure::Malformed);
    }
    let mut slots: [Option<&[u8]>; 14] = [None; 14];
    for part in &record.parts {
        pay(work, 1)?;
        let index = usize::try_from(part.id)
            .map_err(|_| ReceiptFailure::Malformed)?
            .checked_sub(1)
            .ok_or(ReceiptFailure::Malformed)?;
        if index >= slots.len() || slots[index].replace(&part.bytes).is_some() {
            return Err(ReceiptFailure::Malformed);
        }
    }
    let mut proposed = false;
    for (index, premise) in record.premises.iter().enumerate() {
        pay(work, premise.text.len() + premise.status.len() + 1)?;
        if premise.id != index as u32 + 1
            || premise.text != PREMISES[index]
            || !matches!(premise.status.as_str(), "proposed" | "reviewed-claim")
        {
            return Err(ReceiptFailure::Association);
        }
        proposed |= premise.status == "proposed";
    }
    let receipt_bytes = slots[0].ok_or(ReceiptFailure::Malformed)?;
    let receipt_limits = ProducerReceiptLimits {
        artifact_bytes: 2usize.pow(31),
        receipt_bytes: 4096,
        records: 64,
        // Historical producer allowance is untrusted bounded metadata; actual
        // decoding still consumes the single smaller caller request meter.
        work: 64 * 1024 * 1024 * 1024,
    };
    let receipt = ProducerReceipt::decode_with_work(receipt_bytes, receipt_limits, work)?;
    if receipt.role() != ProducerRole::CheckedPreparation {
        return Err(ReceiptFailure::Association);
    }
    for (index, field) in [
        (1, ReceiptField::ProgramImage),
        (2, ReceiptField::ExpectedFacts),
        (3, ReceiptField::Policy),
        (4, ReceiptField::GeneratedRust),
    ] {
        if receipt.pin(field) != Some(pin(slots[index].ok_or(ReceiptFailure::Malformed)?, work)?) {
            return Err(ReceiptFailure::Association);
        }
    }
    let image =
        super::image::PureImage::decode_bytes(slots[1].unwrap(), work).map_err(image_error)?;
    image
        .admit_expected_native_facts(slots[2].unwrap(), work)
        .map_err(image_error)?;
    let restored = image.restore_effect(work).map_err(image_error)?;
    let capacities = super::checked_producer::decode_policy(
        slots[3].unwrap(),
        receipt.pin(ReceiptField::ProgramImage).unwrap(),
        receipt.pin(ReceiptField::ExpectedFacts).unwrap(),
        work,
    )?;
    let regenerated = super::checked_producer::policy_bytes(
        &restored.program,
        receipt.pin(ReceiptField::ProgramImage).unwrap(),
        receipt.pin(ReceiptField::ExpectedFacts).unwrap(),
        capacities,
        work,
    )?;
    pay(work, regenerated.len())?;
    if regenerated != slots[3].unwrap() {
        return Err(ReceiptFailure::Association);
    }
    // Reuse the full encoder/bridge planner from independently restored source
    // originals. Never accept a reduced mapping hash as semantic authority.
    let (rebuilt, provenance) = restored
        .reencode_checked_data(work)
        .map_err(native_image_error)?;
    let mut root_identity = None;
    let emission = if let Some(data) = &record.root_build {
        let root = super::emit::checked_root_host(&rebuilt, &restored.program, capacities, work).map_err(emission_error)?;
        root_identity = Some(data.reconstruct(&root.leaf.source, &root.host.rust_source, work).map_err(|error| match error {
            super::checked_root_identity::Failure::Resource => ReceiptFailure::Resource,
            _ => ReceiptFailure::Association,
        })?);
        let upper = bytes.len().checked_mul(8).ok_or(ReceiptFailure::Resource)?;
        pay(work, upper)?;
        let configuration = serde_json::to_vec(data).map_err(|_| ReceiptFailure::Resource)?;
        if configuration.len() > upper || receipt.pin(ReceiptField::BuildConfiguration) != Some(pin(&configuration, work)?) { return Err(ReceiptFailure::Association); }
        root.host
    } else {
        super::emit::checked_native_host(&rebuilt, &restored.program, capacities, &super::runtime_fingerprint(), work).map_err(emission_error)?
    };
    let (reimage, refacts) = emission.payloads.bytes();
    pay(
        work,
        reimage
            .len()
            .checked_add(refacts.len())
            .ok_or(ReceiptFailure::Resource)?,
    )?;
    if reimage != slots[1].unwrap() || refacts != slots[2].unwrap() {
        return Err(ReceiptFailure::Association);
    }
    pay(work, emission.rust_source.len())?;
    if emission.rust_source.as_bytes() != slots[4].unwrap() {
        return Err(ReceiptFailure::Association);
    }
    let seed_limit = super::gas::preparation(&provenance, restored.program.node_count())
        .map_err(|_| ReceiptFailure::Resource)?
        .limit();
    pay(work, seed_limit)?;
    let seed_limits = ProducerReceiptLimits {
        work: seed_limit,
        ..receipt_limits
    };
    let fresh = if let Some(identity) = &root_identity {
        super::checked_receipt::ReceiptSeed::from_root_emission(
            &rebuilt, &restored.program, &provenance, &emission,
            b"request-independent-root-data", seed_limits, (identity, capacities),
        )?
    } else {
        super::checked_receipt::ReceiptSeed::from_checked_emission(
            &rebuilt, &restored.program, &provenance, &emission,
            b"request-independent-data", seed_limits, capacities,
        )?
    };
    for field in [
        ReceiptField::OriginalMappings,
        ReceiptField::CheckedContracts,
        ReceiptField::RuntimeFingerprint,
    ] {
        pay(work, 42)?;
        if fresh.receipt().pin(field) != receipt.pin(field) {
            return Err(ReceiptFailure::Association);
        }
    }
    if record.linked {
        let native_limits = record.native_limits.ok_or(ReceiptFailure::Malformed)?;
        native_limits.link.validate()?;
        if native_limits.record_bytes == 0
            || native_limits.record_bytes > 4 * 1024 * 1024
            || native_limits.paths == 0
            || native_limits.paths > 4096
            || native_limits.output_bytes == 0
            || native_limits.output_bytes > 4 * 1024 * 1024
            || native_limits.file_bytes == 0
            || native_limits.file_bytes > 2usize.pow(31)
            || native_limits.total_bytes == 0
            || native_limits.total_bytes > 8 * 1024 * 1024 * 1024
            || native_limits.command_seconds == 0
            || native_limits.command_seconds > 120
        {
            return Err(ReceiptFailure::Resource);
        }
        let prior = receipt.before_root_link(
            slots[6].ok_or(ReceiptFailure::Malformed)?,
            native_limits.link,
            work,
        )?;
        super::checked_native_build::matches(
            slots[5].ok_or(ReceiptFailure::Malformed)?,
            &prior,
            native_limits,
            work,
        )?;
        if receipt.pin(ReceiptField::FinalElf).is_none() {
            return Err(ReceiptFailure::Association);
        }
    } else if slots[5].is_some() || slots[6].is_some() || record.native_limits.is_some() {
        return Err(ReceiptFailure::Malformed);
    }
    if slots[7].is_some() {
        return Err(ReceiptFailure::Malformed);
    }
    let mut missing = Vec::new();
    pay(work, CLOSURES.len())?;
    for (i, field) in CLOSURES.into_iter().enumerate() {
        match (receipt.pin(field), slots[8 + i]) {
            (None, None) => missing.push(field),
            (Some(expected), Some(raw)) if pin(raw, work)? == expected => match i {
                0..=3 => conformity_data(raw, i, &slots, &record.premises, work)?,
                4 => {
                    pay(work, raw.len())?;
                    let p: Vec<Premise> =
                        serde_json::from_slice(raw).map_err(|_| ReceiptFailure::Malformed)?;
                    if p != record.premises {
                        return Err(ReceiptFailure::Association);
                    }
                }
                5 => context_data(raw, work)?,
                _ => unreachable!(),
            },
            _ => return Err(ReceiptFailure::Association),
        }
    }
    let premise_bytes =
        serde_json::to_vec(&record.premises).map_err(|_| ReceiptFailure::Resource)?;
    if let Some(expected) = receipt.pin(ReceiptField::Premises)
        && pin(&premise_bytes, work)? != expected
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(ApplicabilityRequest {
        request: pin(bytes, work)?,
        receipt: pin(receipt_bytes, work)?,
        image: receipt.pin(ReceiptField::FinalElf),
        premises: pin(&premise_bytes, work)?,
        linked: record.linked,
        missing,
        proposed,
        context: receipt.pin(ReceiptField::Context),
    })
}
fn encode_kind(
    parts: [&[u8]; 5],
    native: Option<(&[u8], &[u8], super::checked_native_build::Limits)>,
    root_build: Option<super::checked_root_project::BuildData>,
    limits: RequestLimits,
    work: &mut TypeWorkBudget,
) -> Result<Vec<u8>, ReceiptFailure> {
    let mut raw = parts
        .iter()
        .try_fold(0usize, |a, p| a.checked_add(p.len()))
        .ok_or(ReceiptFailure::Resource)?;
    if let Some((n, l, _)) = native {
        raw = raw
            .checked_add(n.len())
            .and_then(|v| v.checked_add(l.len()))
            .ok_or(ReceiptFailure::Resource)?;
    }
    if let Some(root) = &root_build {
        raw = [&root.manifest, &root.build_configuration, &root.settled_lock, &root.leaf_manifest, &root.leaf, &root.shim].iter()
            .try_fold(raw, |n, bytes| n.checked_add(bytes.len()))
            .and_then(|n| n.checked_add(root.project_root.as_os_str().len())).ok_or(ReceiptFailure::Resource)?;
    }
    let upper = raw
        .checked_mul(4)
        .and_then(|n| n.checked_add(32768))
        .ok_or(ReceiptFailure::Resource)?;
    if upper > limits.bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(work, upper)?;
    let mut record = Record {
        version: if root_build.is_some() { 2 } else { 1 },
        target: super::host::NATIVE_TARGET.into(),
        mode: "checked-inprocess-static".into(),
        role: "checked-preparation".into(),
        linked: native.is_some(),
        parts: parts
            .into_iter()
            .enumerate()
            .map(|(i, b)| Part {
                id: i as u32 + 1,
                bytes: b.to_vec(),
            })
            .collect(),
        premises: PREMISES
            .iter()
            .enumerate()
            .map(|(i, t)| Premise {
                id: i as u32 + 1,
                text: (*t).into(),
                status: "proposed".into(),
            })
            .collect(),
        native_limits: native.map(|(_, _, l)| l),
        root_build,
    };
    if let Some((n, l, _)) = native {
        record.parts.push(Part {
            id: 6,
            bytes: n.to_vec(),
        });
        record.parts.push(Part {
            id: 7,
            bytes: l.to_vec(),
        });
    }
    let bytes = serde_json::to_vec(&record).map_err(|_| ReceiptFailure::Resource)?;
    decode_with_work(&bytes, limits, work)?;
    Ok(bytes)
}
fn encode(
    parts: [&[u8]; 5], native: Option<(&[u8], &[u8], super::checked_native_build::Limits)>,
    limits: RequestLimits, work: &mut TypeWorkBudget,
) -> Result<Vec<u8>, ReceiptFailure> { encode_kind(parts,native,None,limits,work) }

/// Root request DATA reuses the same full independent admission, with a closed
/// independently reconstructed code/configuration identity instead of accepting
/// a caller-supplied replacement runtime pin.
pub(super) fn encode_root(
    parts: [&[u8]; 5], native: Option<(&[u8], &[u8], super::checked_native_build::Limits)>,
    root: super::checked_root_project::BuildData, limits: RequestLimits, work: &mut TypeWorkBudget,
) -> Result<Vec<u8>, ReceiptFailure> { encode_kind(parts,native,Some(root),limits,work) }

#[cfg(test)]
fn encode_preparation(parts: [&[u8]; 5], limits: RequestLimits) -> Result<Vec<u8>, ReceiptFailure> {
    encode(
        parts,
        None,
        limits,
        &mut TypeWorkBudget::with_limit(limits.work),
    )
}
/// Same-transaction producer request. No raw claim/status is promoted to approval.
pub(super) fn from_linked_files(
    project: &std::path::Path,
    receipt: &[u8],
    native: super::checked_native_build::Limits,
) -> Result<Vec<u8>, ReceiptFailure> {
    use std::io::Read;
    let limits = RequestLimits::default();
    let mut used = receipt.len();
    let mut work = TypeWorkBudget::with_limit(limits.work);
    let mut read = |name: &str| -> Result<Vec<u8>, ReceiptFailure> {
        let mut file =
            std::fs::File::open(project.join(name)).map_err(|_| ReceiptFailure::Input)?;
        let meta = file.metadata().map_err(|_| ReceiptFailure::Input)?;
        if !meta.is_file() || meta.len() > limits.bytes as u64 {
            return Err(ReceiptFailure::Resource);
        }
        let mut bytes = Vec::new();
        let mut buffer = [0u8; 8192];
        loop {
            let count = buffer
                .len()
                .min(limits.bytes.saturating_sub(bytes.len()).saturating_add(1));
            pay(&mut work, count)?;
            let n = file
                .read(&mut buffer[..count])
                .map_err(|_| ReceiptFailure::Input)?;
            if n == 0 {
                break;
            }
            if bytes.len().checked_add(n).is_none_or(|v| v > limits.bytes) {
                return Err(ReceiptFailure::Resource);
            }
            bytes.try_reserve(n).map_err(|_| ReceiptFailure::Resource)?;
            bytes.extend_from_slice(&buffer[..n]);
        }
        used = used
            .checked_add(bytes.len())
            .ok_or(ReceiptFailure::Resource)?;
        if used > limits.bytes {
            return Err(ReceiptFailure::Resource);
        }
        Ok(bytes)
    };
    let image = read("src/program-image.bin")?;
    let facts = read("src/expected-facts.bin")?;
    let policy = read("src/checked-policy.bin")?;
    let rust = read("src/main.rs")?;
    let n = read("native-provenance.json")?;
    let l = read("link-provenance.json")?;
    encode(
        [receipt, &image, &facts, &policy, &rust],
        Some((&n, &l, native)),
        limits,
        &mut work,
    )
}
// These cfg(test) claim mutations are untrusted request DATA. They never mint
// protected context, approval, complete closure truth, or a PreparedImage.
#[cfg(test)]
pub(super) fn exercise_linked_request_data_for_test(bytes: &[u8]) {
    let limits = RequestLimits::default();
    let actual = ApplicabilityRequest::decode(bytes, limits).unwrap();
    assert!(actual.linked());
    assert_eq!(actual.missing_fields().len(), 6);
    assert_eq!(
        actual.check_complete(),
        Err(ReceiptFailure::IncompleteClosure)
    );
    let base: Record = serde_json::from_slice(bytes).unwrap();
    let receipt_limits = ProducerReceiptLimits {
        artifact_bytes: 2usize.pow(31),
        receipt_bytes: 4096,
        records: 64,
        work: 64 * 1024 * 1024 * 1024,
    };
    let rebind = |record: &mut Record, id: u32, raw: Vec<u8>| {
        let field = CLOSURES[usize::try_from(id - 9).unwrap()];
        assert!(raw.len() <= limits.bytes);
        let mut pin_work = TypeWorkBudget::with_limit(raw.len());
        let bound = pin(&raw, &mut pin_work).unwrap();
        assert_eq!(pin_work.used(), raw.len());
        let receipt = ProducerReceipt::decode(&record.parts[0].bytes, receipt_limits)
            .unwrap()
            .substituted_pin_data_for_test(field, bound);
        record.parts[0].bytes = receipt
            .encode(&mut TypeWorkBudget::default(), receipt_limits)
            .unwrap();
        if let Some(part) = record.parts.iter_mut().find(|part| part.id == id) {
            part.bytes = raw;
        } else {
            record.parts.push(Part { id, bytes: raw });
        }
    };
    let context = serde_json::to_vec(&serde_json::json!({
        "version": 1, "uid": 1000, "gid": 1000, "groups": [],
        "user_namespace": {"device": 1, "inode": 2},
        "mount_namespace": {"device": 1, "inode": 3},
        "uid_map_sha256": "0".repeat(64), "mountinfo_sha256": "0".repeat(64),
        "store": "/untrusted-request-data/store", "store_identity": {"device": 1, "inode": 4},
        "stdio": "null-read-null-write-v1", "context_version": 1,
        "premise_version": 1, "launch_version": 1,
        "request_bytes": limits.bytes, "request_work": limits.work,
        "image_bytes": 2usize.pow(31), "image_work": 16 * 1024 * 1024 * 1024usize,
        "program_headers": 64
    }))
    .unwrap();
    for (category, name) in ["native", "header", "tool", "runtime"]
        .into_iter()
        .enumerate()
    {
        let id = category as u32 + 9;
        let mut canonical = base.clone();
        let claim = ConformityAddendum {
            version: 1,
            category: name.into(),
            profile: "linux-x86_64-gnu-static-initialized8-owner-v1".into(),
            program: base.parts.iter().find(|p| p.id == 2).unwrap().bytes.clone(),
            facts: base.parts.iter().find(|p| p.id == 3).unwrap().bytes.clone(),
            policy: base.parts.iter().find(|p| p.id == 4).unwrap().bytes.clone(),
            native_build: base.parts.iter().find(|p| p.id == 6).unwrap().bytes.clone(),
            root_link: base.parts.iter().find(|p| p.id == 7).unwrap().bytes.clone(),
            premises: base.premises.clone(),
            context: context.clone(),
        };
        rebind(&mut canonical, id, serde_json::to_vec(&claim).unwrap());
        rebind(
            &mut canonical,
            13,
            serde_json::to_vec(&base.premises).unwrap(),
        );
        rebind(&mut canonical, 14, context.clone());
        let summary =
            ApplicabilityRequest::decode(&serde_json::to_vec(&canonical).unwrap(), limits).unwrap();
        assert_eq!(summary.missing_fields().len(), 3);
        assert_eq!(
            summary.check_complete(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        for change in 0..10 {
            let mut donor = canonical.clone();
            let mut typed = claim.clone();
            let expected = match change {
                0 => {
                    typed.version = 2;
                    ReceiptFailure::Version
                }
                1 => {
                    typed.category.push('!');
                    ReceiptFailure::Association
                }
                2 => {
                    typed.root_link.push(0);
                    ReceiptFailure::Association
                }
                3 => {
                    let mut unknown = serde_json::to_value(&claim).unwrap();
                    unknown["accepted"] = true.into();
                    rebind(&mut donor, id, serde_json::to_vec(&unknown).unwrap());
                    ReceiptFailure::Malformed
                }
                4 => {
                    let mut omitted = serde_json::to_value(&claim).unwrap();
                    omitted.as_object_mut().unwrap().remove("root_link");
                    rebind(&mut donor, id, serde_json::to_vec(&omitted).unwrap());
                    ReceiptFailure::Malformed
                }
                5 => {
                    donor.parts.retain(|p| p.id != id);
                    ReceiptFailure::Association
                }
                6 => {
                    donor
                        .parts
                        .push(donor.parts.iter().find(|p| p.id == id).unwrap().clone());
                    ReceiptFailure::Malformed
                }
                7 | 8 => {
                    let mut changed: serde_json::Value = serde_json::from_slice(&context).unwrap();
                    if change == 7 {
                        changed["context_version"] = 2.into();
                    } else {
                        changed["store_identity"]["inode"] = 0.into();
                    }
                    typed.context = serde_json::to_vec(&changed).unwrap();
                    rebind(&mut donor, 14, typed.context.clone());
                    if change == 7 {
                        ReceiptFailure::Version
                    } else {
                        ReceiptFailure::Association
                    }
                }
                _ => {
                    let mut changed = base.premises.clone();
                    changed[0].status = "reviewed-claim".into();
                    rebind(&mut donor, 13, serde_json::to_vec(&changed).unwrap());
                    ReceiptFailure::Association
                }
            };
            if matches!(change, 0..=2 | 7..=8) {
                rebind(&mut donor, id, serde_json::to_vec(&typed).unwrap());
            }
            assert_eq!(
                ApplicabilityRequest::decode(&serde_json::to_vec(&donor).unwrap(), limits)
                    .unwrap_err(),
                expected,
                "category {name}, mutation {change}"
            );
        }
    }
    let mut measured = TypeWorkBudget::with_limit(limits.work);
    decode_with_work(bytes, limits, &mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        decode_with_work(bytes, limits, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        assert!(decode_with_work(bytes, limits, &mut exact).is_err());
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            decode_with_work(bytes, limits, &mut short).unwrap_err(),
            ReceiptFailure::Resource
        );
        assert!(decode_with_work(bytes, limits, &mut short).is_err());
        decode_with_work(bytes, limits, &mut TypeWorkBudget::with_limit(cost)).unwrap();
    }
    ApplicabilityRequest::decode(
        bytes,
        RequestLimits {
            bytes: bytes.len(),
            ..limits
        },
    )
    .unwrap();
    assert_eq!(
        ApplicabilityRequest::decode(
            bytes,
            RequestLimits {
                bytes: bytes.len() - 1,
                ..limits
            }
        )
        .unwrap_err(),
        ReceiptFailure::Resource
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn resource_adapters_preserve_actual_bridge_emission_and_validation_cuts() {
        use super::super::{
            emit::EmissionFailure,
            image::{ImageFailure, NativeImageFailure},
        };
        let validation_resource = || match crate::core::validate::DeclarationCoordinateLoan::new(
            &[],
            &[],
            &mut TypeWorkBudget::with_limit(0),
        ) {
            Err(error) => error,
            Ok(_) => panic!("zero work must refuse before coordinate storage"),
        };
        assert_eq!(
            validation_resource().reason(),
            crate::core::ValidationReason::Resource
        );
        assert_eq!(
            image_error(ImageFailure::Validation(validation_resource())),
            ReceiptFailure::Resource
        );
        assert_eq!(
            emission_error(EmissionFailure::Image(ImageFailure::Validation(
                validation_resource()
            ))),
            ReceiptFailure::Resource
        );
        assert_eq!(
            image_error(ImageFailure::CoreAdmission(
                crate::core::BuildError::TypeWorkExceeded
            )),
            ReceiptFailure::Resource
        );
        for error in [
            ImageFailure::InvalidRecord,
            ImageFailure::CoreAdmission(crate::core::BuildError::TypeDepthExceeded),
            ImageFailure::CoreAdmission(crate::core::BuildError::ForeignBinder),
        ] {
            assert_eq!(image_error(error), ReceiptFailure::Association);
        }
        assert_eq!(
            emission_error(EmissionFailure::Resource),
            ReceiptFailure::Resource
        );
        let (program, provenance) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        let mut construction =
            super::super::gas::preparation(&provenance, program.node_count()).unwrap();
        let build = super::super::image::encode_checked_preparation(
            &program,
            &provenance,
            super::super::host::NATIVE_TARGET,
            &mut construction,
        )
        .unwrap();
        let plan = &build.bridges.first().unwrap().plan;
        let bridge_resource = plan
            .authenticate_in_program(
                super::super::host::NATIVE_TARGET,
                &program,
                &mut TypeWorkBudget::with_limit(0),
            )
            .unwrap_err();
        assert!(bridge_resource.is_resource());
        assert_eq!(
            native_image_error(NativeImageFailure::Bridge(bridge_resource)),
            ReceiptFailure::Resource
        );
        assert_eq!(
            emission_error(EmissionFailure::Bridge(bridge_resource)),
            ReceiptFailure::Resource
        );
        let foreign_target = plan
            .authenticate_in_program("unrelated-target", &program, &mut TypeWorkBudget::default())
            .unwrap_err();
        assert!(!foreign_target.is_resource());
        assert_eq!(
            native_image_error(NativeImageFailure::Bridge(foreign_target)),
            ReceiptFailure::Association
        );
        assert_eq!(
            emission_error(EmissionFailure::Bridge(foreign_target)),
            ReceiptFailure::Association
        );
        let policy = crate::foreign::source_runtime::CheckedOwnerLimits {
            groups: 1,
            owners: 1,
            pending: 1,
            observations: 5,
            history: 6,
            continuations: 1,
        };
        // This is the existing request decoder allowance, not a startup claim.
        let mut measured = TypeWorkBudget::with_limit(RequestLimits::default().work);
        let canonical = super::super::emit::checked_native_host(
            &build,
            &program,
            policy,
            &super::super::runtime_fingerprint(),
            &mut measured,
        )
        .unwrap();
        assert!(!canonical.rust_source.is_empty());
        let cost = measured.used();
        for limit in [0, cost - 1] {
            let error = super::super::emit::checked_native_host(
                &build,
                &program,
                policy,
                &super::super::runtime_fingerprint(),
                &mut TypeWorkBudget::with_limit(limit),
            )
            .expect_err("actual emission work cut must refuse");
            assert_eq!(emission_error(error), ReceiptFailure::Resource);
        }
    }

    #[test]
    fn root_request_reconstructs_genuine_originals_and_refuses_rebound_code_data() {
        let (program, provenance) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        let limits = RequestLimits::default();
        let mut construction = TypeWorkBudget::with_limit(limits.work);
        let build = super::super::image::encode_checked_preparation(&program,&provenance,super::super::host::NATIVE_TARGET,&mut construction).unwrap();
        let policy=crate::foreign::source_runtime::CheckedOwnerLimits {groups:1,owners:1,pending:1,observations:5,history:6,continuations:1};
        let root=super::super::emit::checked_root_host(&build,&program,policy,&mut construction).unwrap();
        // A closed lock DATA fixture, not an actual Cargo/native build or
        // installed protected image. Its graph is fully independently checked.
        let data=super::super::checked_root_project::fixture_data(&root.leaf.source,&root.host.rust_source,&mut construction);
        let identity=data.reconstruct(&root.leaf.source,&root.host.rust_source,&mut construction).unwrap();
        let configuration=serde_json::to_vec(&data).unwrap();
        let receipt_limits=ProducerReceiptLimits {artifact_bytes:limits.bytes,receipt_bytes:4096,records:64,work:limits.work};
        let seed=super::super::checked_receipt::ReceiptSeed::from_root_emission(&build,&program,&provenance,&root.host,&configuration,receipt_limits,(&identity,policy)).unwrap();
        let receipt=seed.receipt().encode(&mut construction,receipt_limits).unwrap();
        let (image,facts)=root.host.payloads.bytes();
        let parts=[receipt.as_slice(),image,facts,root.host.payloads.checked_policy().unwrap(),root.host.rust_source.as_bytes()];
        let bytes=encode_root(parts,None,data,limits,&mut TypeWorkBudget::with_limit(limits.work)).unwrap();
        // Fresh restores allocate new process-local originals and pay actual
        // comparisons/name construction. Canonical bytes are exact; total work
        // need not repeat bit-for-bit. Never turn one measured run into credit
        // for a different reconstruction or add a margin to product limits.
        for prefix in [0,7] {
            for _ in 0..2 {
                let mut work=TypeWorkBudget::with_limit(limits.work);
                work.charge(prefix).unwrap();
                assert_eq!(work.used(),prefix);
                let summary=decode_with_work(&bytes,limits,&mut work).unwrap();
                assert!(!summary.linked()); assert_eq!(summary.missing_fields().len(),6);
                assert_eq!(summary.check_complete(),Err(ReceiptFailure::IncompleteClosure));
                assert_eq!(work.limit(),limits.work);
                assert!(work.used()>=prefix+bytes.len()*8 && work.used()<=limits.work);
            }
        }
        let mut spent=TypeWorkBudget::with_limit(limits.work);
        spent.charge(limits.work).unwrap();
        assert!(matches!(decode_with_work(&bytes,limits,&mut spent),Err(ReceiptFailure::Resource)));
        assert_eq!(spent.used(),limits.work);
        // The framing bound is deterministic; exact bytes admit and one byte
        // short refuses before parse/reconstruction. Component work exact/short
        // controls remain in root identity/configuration/reconstruction units.
        let exact_bytes=RequestLimits {bytes:bytes.len(),..limits};
        assert!(ApplicabilityRequest::decode(&bytes,exact_bytes).is_ok());
        let mut short=TypeWorkBudget::with_limit(limits.work);
        assert!(matches!(decode_with_work(&bytes,RequestLimits{bytes:bytes.len()-1,..limits},&mut short),Err(ReceiptFailure::Resource)));
        assert_eq!(short.used(),0);
        let canonical:Record=serde_json::from_slice(&bytes).unwrap();
        for index in 0..8 {
            let mut donor=canonical.clone();
            let data=donor.root_build.as_mut().unwrap();
            match index {
                0=>data.manifest.push(b' '),1=>data.leaf.push(b' '),2=>data.shim.push(b' '),
                3=>data.settled_lock=b"version = 3".to_vec(),4=>data.version=2,
                5=>data.project_root="/tmp/donor".into(),
                6=>{let mut config:serde_json::Value=serde_json::from_slice(&data.build_configuration).unwrap();config["environment"]["rustc"]=serde_json::json!("/tmp/donor-rustc");data.build_configuration=serde_json::to_vec(&config).unwrap();},
                _=>{let mut config:serde_json::Value=serde_json::from_slice(&data.build_configuration).unwrap();config["unknown"]=serde_json::json!(true);data.build_configuration=serde_json::to_vec(&config).unwrap();},
            }
            // Rebind the outer receipt configuration: rejection must come
            // from independent closed reconstruction, not a stale outer pin.
            let raw=serde_json::to_vec(data).unwrap();
            let bound=pin(&raw,&mut TypeWorkBudget::with_limit(raw.len())).unwrap();
            donor.parts[0].bytes=ProducerReceipt::decode(&donor.parts[0].bytes,receipt_limits).unwrap()
                .substituted_pin_data_for_test(ReceiptField::BuildConfiguration,bound)
                .encode(&mut TypeWorkBudget::default(),receipt_limits).unwrap();
            let raw=serde_json::to_vec(&donor).unwrap();
            assert!(matches!(ApplicabilityRequest::decode(&raw,limits),Err(ReceiptFailure::Association)));
        }
    }

    #[test]
    fn request_genuine_eight_byte_preparation_and_rebound_refusals() {
        let (program, provenance) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        let mut work = super::super::gas::preparation(&provenance, program.node_count()).unwrap();
        let build = super::super::image::encode_checked_preparation(
            &program,
            &provenance,
            super::super::host::NATIVE_TARGET,
            &mut work,
        )
        .unwrap();
        let policy = crate::foreign::source_runtime::CheckedOwnerLimits {
            groups: 1,
            owners: 1,
            pending: 1,
            observations: 5,
            history: 6,
            continuations: 1,
        };
        let emission = super::super::emit::checked_native_host(
            &build,
            &program,
            policy,
            &super::super::runtime_fingerprint(),
            &mut work,
        )
        .unwrap();
        let limits = ProducerReceiptLimits {
            artifact_bytes: 1024 * 1024,
            receipt_bytes: 4096,
            records: 64,
            work: 128 * 1024 * 1024,
        };
        let seed = super::super::checked_receipt::ReceiptSeed::from_checked_emission(
            &build,
            &program,
            &provenance,
            &emission,
            b"request-unit",
            limits,
            policy,
        )
        .unwrap();
        let receipt = seed.receipt().encode(&mut work, limits).unwrap();
        let (image, facts) = emission.payloads.bytes();
        let parts = [
            receipt.as_slice(),
            image,
            facts,
            emission.payloads.checked_policy().unwrap(),
            emission.rust_source.as_bytes(),
        ];
        let encoded = encode_preparation(parts, RequestLimits::default()).unwrap();
        let summary = ApplicabilityRequest::decode(&encoded, RequestLimits::default()).unwrap();
        assert!(!summary.linked());
        assert_eq!(summary.missing_fields().len(), 6);
        assert_eq!(
            summary.check_complete(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        let record: Record = serde_json::from_slice(&encoded).unwrap();
        for change in 0..5 {
            let mut donor = record.clone();
            match change {
                0 => donor.parts[1].bytes[0] ^= 1,
                1 => donor.parts[2].bytes[0] ^= 1,
                2 => donor.parts[3].bytes[0] ^= 1,
                3 => donor.premises[0].text.push('!'),
                _ => donor.target.push('!'),
            }
            let bytes = serde_json::to_vec(&donor).unwrap();
            assert!(ApplicabilityRequest::decode(&bytes, RequestLimits::default()).is_err());
        }
        // Rebind the changed part's receipt pin so each case reaches the
        // intended inner parser/original association, not the shallow hash gate.
        for (part, field, offset) in [
            (1, ReceiptField::ProgramImage, 0),
            (2, ReceiptField::ExpectedFacts, 0),
            (3, ReceiptField::Policy, 92),
        ] {
            let mut donor = record.clone();
            donor.parts[part].bytes[offset] ^= 1;
            let changed = pin(&donor.parts[part].bytes, &mut TypeWorkBudget::default()).unwrap();
            let bound = ProducerReceipt::decode(&donor.parts[0].bytes, limits)
                .unwrap()
                .substituted_pin_data_for_test(field, changed);
            donor.parts[0].bytes = bound
                .encode(&mut TypeWorkBudget::default(), limits)
                .unwrap();
            assert_eq!(
                ApplicabilityRequest::decode(
                    &serde_json::to_vec(&donor).unwrap(),
                    RequestLimits::default()
                )
                .unwrap_err(),
                if field == ReceiptField::Policy {
                    ReceiptFailure::Resource
                } else {
                    ReceiptFailure::Association
                }
            );
        }
        let mut changed = record.clone();
        let original = ProducerReceipt::decode(&changed.parts[0].bytes, limits).unwrap();
        let mut bad = original.pin(ReceiptField::CheckedContracts).unwrap();
        bad.sha256[0] ^= 1;
        changed.parts[0].bytes = original
            .substituted_pin_data_for_test(ReceiptField::CheckedContracts, bad)
            .encode(&mut TypeWorkBudget::default(), limits)
            .unwrap();
        assert_eq!(
            ApplicabilityRequest::decode(
                &serde_json::to_vec(&changed).unwrap(),
                RequestLimits::default()
            )
            .unwrap_err(),
            ReceiptFailure::Association
        );
        let mut duplicate = record.clone();
        duplicate.parts.push(record.parts[0].clone());
        assert_eq!(
            ApplicabilityRequest::decode(
                &serde_json::to_vec(&duplicate).unwrap(),
                RequestLimits::default()
            )
            .unwrap_err(),
            ReceiptFailure::Malformed
        );
        let mut omitted = record;
        omitted.parts.remove(2);
        assert_eq!(
            ApplicabilityRequest::decode(
                &serde_json::to_vec(&omitted).unwrap(),
                RequestLimits::default()
            )
            .unwrap_err(),
            ReceiptFailure::Malformed
        );
        let mut meter = TypeWorkBudget::with_limit(RequestLimits::default().work);
        decode_with_work(&encoded, RequestLimits::default(), &mut meter).unwrap();
        let exact = meter.used();
        let mut exact_work = TypeWorkBudget::with_limit(exact);
        decode_with_work(&encoded, RequestLimits::default(), &mut exact_work).unwrap();
        let mut short = TypeWorkBudget::with_limit(exact - 1);
        assert_eq!(
            decode_with_work(&encoded, RequestLimits::default(), &mut short).unwrap_err(),
            ReceiptFailure::Resource
        );
        assert!(decode_with_work(&encoded, RequestLimits::default(), &mut short).is_err());
        let mut fresh = TypeWorkBudget::with_limit(exact);
        decode_with_work(&encoded, RequestLimits::default(), &mut fresh).unwrap();
        let mut bounds = RequestLimits {
            bytes: encoded.len(),
            ..RequestLimits::default()
        };
        ApplicabilityRequest::decode(&encoded, bounds).unwrap();
        bounds.bytes -= 1;
        assert_eq!(
            ApplicabilityRequest::decode(&encoded, bounds).unwrap_err(),
            ReceiptFailure::Resource
        );
    }
    #[test]
    fn closed_conformity_schema_rejects_rebound_unknown_opaque_and_donor_data() {
        let premises: Vec<_> = PREMISES
            .iter()
            .enumerate()
            .map(|(i, text)| Premise {
                id: i as u32 + 1,
                text: (*text).into(),
                status: "proposed".into(),
            })
            .collect();
        // Slot values here are predicate inputs only, not native/closure truth.
        let slots: [Option<&[u8]>; 14] = [
            None,
            Some(b"image"),
            Some(b"facts"),
            Some(b"policy"),
            None,
            Some(b"native"),
            Some(b"root"),
            None,
            None,
            None,
            None,
            None,
            None,
            Some(b"context"),
        ];
        let c = ConformityAddendum {
            version: 1,
            category: "native".into(),
            profile: "linux-x86_64-gnu-static-initialized8-owner-v1".into(),
            program: b"image".to_vec(),
            facts: b"facts".to_vec(),
            policy: b"policy".to_vec(),
            native_build: b"native".to_vec(),
            root_link: b"root".to_vec(),
            premises: premises.clone(),
            context: b"context".to_vec(),
        };
        let raw = serde_json::to_vec(&c).unwrap();
        conformity_data(&raw, 0, &slots, &premises, &mut TypeWorkBudget::default()).unwrap();
        let mut donor = c.clone();
        donor.native_build.push(0);
        assert_eq!(
            conformity_data(
                &serde_json::to_vec(&donor).unwrap(),
                0,
                &slots,
                &premises,
                &mut TypeWorkBudget::default()
            ),
            Err(ReceiptFailure::Association)
        );
        let mut unknown = serde_json::to_value(&c).unwrap();
        unknown["accepted"] = true.into();
        assert_eq!(
            conformity_data(
                &serde_json::to_vec(&unknown).unwrap(),
                0,
                &slots,
                &premises,
                &mut TypeWorkBudget::default()
            ),
            Err(ReceiptFailure::Malformed)
        );
        let mut missing = serde_json::to_value(&c).unwrap();
        missing.as_object_mut().unwrap().remove("root_link");
        assert_eq!(
            conformity_data(
                &serde_json::to_vec(&missing).unwrap(),
                0,
                &slots,
                &premises,
                &mut TypeWorkBudget::default()
            ),
            Err(ReceiptFailure::Malformed)
        );
        assert_eq!(
            conformity_data(
                b"opaque",
                0,
                &slots,
                &premises,
                &mut TypeWorkBudget::default()
            ),
            Err(ReceiptFailure::Malformed)
        );
        assert_eq!(
            conformity_data(
                &raw,
                0,
                &slots,
                &premises,
                &mut TypeWorkBudget::with_limit(1)
            ),
            Err(ReceiptFailure::Resource)
        );
    }
}
