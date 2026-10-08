// Required additive reader inside impl CheckedProviderContracts, provider.rs.
// Caller charges resource_count before this bounded declaration lookup.
pub(crate) fn family_handler_certificate(
    &self,
    definition: crate::resolved::ResourceDefinitionId,
) -> Option<&crate::core::validate::CheckedHandlerContractCertificate> {
    let family = self.declarations.iter()
        .find(|entry| entry.fact.id == definition)?.family.as_ref()?;
    (family.identity.definition == definition).then_some(&family.handlers)
}
