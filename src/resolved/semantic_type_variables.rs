//! Semantic payloads and defining formal ownership of a retained registry.

use super::*;
use crate::core::validate::semantic_type_variables::UnusedVariables;

impl ResolvedRegistry {
    /// Source generative binders cannot also define private interface formals.
    /// Keep those owner records behind the registry's borrowed check.
    pub(crate) fn source_parameters_disjoint_from_private_formals(
        &self,
        parameters: &HashSet<TypeVariableId>,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        for (_, formals) in self.image_interface_owner_definitions() {
            work.charge(formals.len())?;
            if formals.iter().any(|formal| parameters.contains(&formal.id)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

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
        uses.charge(self.native_symbols.len())?;
        for symbol in self.native_symbols.values() {
            uses.ty(symbol.source_signature())?;
            uses.charge(symbol.parameter_ids().len())?;
            for parameter in symbol.parameter_ids() {
                uses.id(*parameter)?;
            }
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

impl CheckedImplementationFact {
    pub(crate) fn visit_semantic_type_variables(
        &self,
        uses: &mut UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.application(self.application())?;
        uses.charge(self.head_parameters.len() + self.prerequisites.len() + self.methods.len())?;
        for parameter in &self.head_parameters {
            uses.id(parameter.id)?;
        }
        for requirement in &self.prerequisites {
            uses.application(&requirement.application)?;
        }
        for method in &self.methods {
            uses.scheme(&method.scheme)?;
            method.capture.visit_semantic_type_variables(uses)?;
        }
        Ok(())
    }
}
