//! Semantic payloads and defining formal ownership of a retained registry.

use super::*;
use crate::core::validate::semantic_type_variables::UnusedVariables;

impl ResolvedRegistry {
    pub(crate) fn visit_semantic_type_variables(
        &self,
        uses: &mut UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.charge(self.nominals.len() + self.lexical_nominals.len())?;
        for nominal in self.nominals.iter().chain(self.lexical_nominals.iter()) {
            if let Some(ty) = &nominal.representation {
                uses.ty(ty)?;
            }
        }
        uses.charge(self.constructors.len() + self.lexical_constructors.len())?;
        for constructor in self
            .constructors
            .iter()
            .chain(self.lexical_constructors.iter())
        {
            if let Some(ty) = &constructor.payload {
                uses.ty(ty)?;
            }
        }
        uses.charge(self.effects.len())?;
        for effect in &self.effects {
            uses.charge(effect.parameters.len() + effect.operations.len())?;
            for parameter in &effect.parameters {
                uses.id(parameter.id)?;
            }
            for operation in &effect.operations {
                uses.ty(&operation.annotation.ty)?;
            }
        }
        uses.charge(
            self.nominal_parameters.len()
                + self.owner_definitions.len()
                + self.global_parameter_rows.len(),
        )?;
        for parameters in self.nominal_parameters.values() {
            uses.charge(parameters.len())?;
            for parameter in parameters {
                uses.id(parameter.id)?;
            }
        }
        for owner in &self.owner_definitions {
            uses.charge(owner.parameters.len())?;
            for parameter in owner.parameters.iter() {
                uses.id(parameter.id)?;
            }
        }
        for global in &self.global_parameter_rows {
            uses.charge(global.parameters.len())?;
            for parameter in &global.parameters {
                uses.id(*parameter)?;
            }
        }
        uses.charge(self.source_resource_facts.len())?;
        for fact in self.source_resource_facts.values() {
            uses.source_header(fact)?;
        }
        uses.charge(self.native_symbols.len() + self.source_foreign_nominals.len())?;
        for symbol in self.native_symbols.values() {
            uses.ty(symbol.source_signature())?;
            uses.charge(symbol.parameter_ids().len())?;
            for parameter in symbol.parameter_ids() {
                uses.id(*parameter)?;
            }
        }
        uses.charge(self.scalar_preflights.len())?;
        for preflight in self.scalar_preflights.values() {
            uses.ty(preflight.signature())?;
            uses.ty(preflight.core_signature())?;
        }
        for nominal in &self.source_foreign_nominals {
            uses.charge(nominal.parameters.len())?;
            for parameter in nominal.parameters.iter() {
                uses.id(parameter.id)?;
            }
        }
        uses.charge(self.provider_contracts.len())?;
        for contract in self.provider_contracts.values() {
            uses.charge(contract.resource_count())?;
            for (_, _, fact) in contract.resource_contracts() {
                uses.ordinary_header(fact)?;
            }
            // The private canonical owner rows are definitions. They are
            // authenticated by the certificate, independent of public aliases.
            contract.visit_semantic_type_variables(uses)?;
        }
        Ok(())
    }
}

impl UnusedVariables<'_> {
    pub(crate) fn scheme(&mut self, scheme: &ConstrainedScheme) -> Result<(), ()> {
        self.charge(scheme.type_parameters.len() + scheme.requirements.len())?;
        for (parameter, _) in &scheme.type_parameters {
            self.id(*parameter)?;
        }
        for requirement in &scheme.requirements {
            self.application(&requirement.application)?;
        }
        self.ty(&scheme.value_type)
    }

    pub(crate) fn interface_fact(&mut self, fact: &CheckedInterfaceFact) -> Result<(), ()> {
        self.charge(fact.parameters.len() + fact.methods.len())?;
        for parameter in fact.parameters.iter() {
            self.id(parameter.id)?;
        }
        for method in &fact.methods {
            self.ty(method.value_type())?;
            self.charge(
                method.type_parameters().len() + method.authoritative_type_parameters().len(),
            )?;
            for parameter in method
                .type_parameters()
                .iter()
                .chain(method.authoritative_type_parameters())
            {
                self.id(parameter.id)?;
            }
        }
        Ok(())
    }

    pub(crate) fn implementation_fact(
        &mut self,
        fact: &CheckedImplementationFact,
    ) -> Result<(), ()> {
        self.application(fact.application())?;
        self.charge(fact.head_parameters.len() + fact.prerequisites.len() + fact.methods.len())?;
        for parameter in &fact.head_parameters {
            self.id(parameter.id)?;
        }
        for requirement in &fact.prerequisites {
            self.application(&requirement.application)?;
        }
        for method in &fact.methods {
            self.scheme(&method.scheme)?;
            method.capture.visit_semantic_type_variables(self)?;
        }
        Ok(())
    }
    pub(crate) fn resolved_application(
        &mut self,
        application: &ResolvedInterfaceApplication,
    ) -> Result<(), ()> {
        self.charge(application.arguments.len())?;
        for argument in &application.arguments {
            self.argument(&argument.ty)?;
        }
        Ok(())
    }

    pub(crate) fn source_header(&mut self, fact: &SourceResourceTypeFact) -> Result<(), ()> {
        self.charge(fact.parameters.len() + fact.interpreted.len() + fact.windows.len())?;
        for parameter in &fact.parameters {
            self.id(parameter.id)?;
        }
        self.id(fact.answer.id)?;
        for ty in [
            &fact.input,
            &fact.state,
            &fact.data,
            &fact.acquisition,
            &fact.completion,
            &fact.result,
        ] {
            self.ty(&ty.ty)?;
        }
        self.resolved_application(&fact.provider)?;
        self.instance(&fact.provided.instance)?;
        for effect in &fact.interpreted {
            self.instance(&effect.instance)?;
        }
        for window in &fact.windows {
            self.id(window.identity)?;
        }
        Ok(())
    }

    pub(crate) fn ordinary_header(&mut self, fact: &ResourceTypeFact) -> Result<(), ()> {
        self.charge(fact.parameters.len())?;
        for parameter in &fact.parameters {
            self.id(parameter.id)?;
        }
        self.id(fact.answer.id)?;
        for ty in [&fact.input, &fact.state, &fact.result] {
            self.ty(&ty.ty)?;
        }
        self.resolved_application(&fact.provider)?;
        self.application(&fact.provider_application)?;
        self.instance(&fact.provided.instance)?;
        self.instance(&fact.interpreted.instance)?;
        if let Some(family) = &fact.family_template {
            self.id(family.parameter.id)?;
            self.resolved_application(&family.provider)?;
            self.application(&family.provider_application)?;
            self.instance(&family.provided.instance)?;
            self.instance(&family.interpreted.instance)?;
            self.charge(family.requirements.len())?;
            for requirement in &family.requirements {
                self.resolved_application(requirement)?;
            }
        }
        Ok(())
    }
}

impl ProviderExternalFacts<'_> {
    pub(crate) fn visit_semantic_type_variables(
        &self,
        uses: &mut UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.charge(
            self.imported.globals.len()
                + self.imported.interfaces.len()
                + self.imported.implementations.len(),
        )?;
        for global in self.imported.globals.values() {
            uses.scheme(&global.scheme)?;
            global.capture.visit_semantic_type_variables(uses)?;
            if let Some(preflight) = &global.scalar_preflight {
                uses.ty(preflight.signature())?;
                uses.ty(preflight.core_signature())?;
            }
        }
        for interface in &self.imported.interfaces {
            uses.interface_fact(&interface.fact)?;
        }
        for implementation in &self.imported.implementations {
            uses.implementation_fact(&implementation.fact)?;
        }
        if let Some(defining) = self.defining {
            uses.charge(
                defining.globals.len() + defining.interfaces.len() + defining.implementations.len(),
            )?;
            for global in &defining.globals {
                uses.scheme(&global.scheme)?;
                global.capture.visit_semantic_type_variables(uses)?;
            }
            for interface in &defining.interfaces {
                uses.interface_fact(interface)?;
            }
            for implementation in &defining.implementations {
                uses.implementation_fact(implementation)?;
            }
        }
        Ok(())
    }
}
