//! Check-once source indexing for dependency-ordered local body admission.

use super::TypeError;
use super::{
    CheckedImplementationFactBuffer, CoreElaborator, CoreLoweringFamily, ModuleBodyChecking,
    invalid_state, resolved_build_error, selection_failure, type_resource,
};
use crate::{
    core::NodeId,
    interface::EvidenceSelection,
    resolved::{
        BinderId, CheckedGlobalScheme, ResolvedBlock, ResolvedDeclarationIndex,
        ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModule,
    },
    source::Span,
    types::TypeWorkBudget,
};
use std::collections::{HashMap, HashSet};
use std::primitive::{u64, usize};

/// Scalar completion proof. The source arrays define all indexes; completed
/// bodies may be checked in another order without changing publication order.
pub(super) struct ModuleBodySchedule {
    global_count: usize,
    implementation_count: usize,
    completed: Vec<u64>,
    globals: HashMap<BinderId, usize>,
    implementations: HashMap<crate::interface::ImplId, usize>,
    implementation_methods: HashMap<BinderId, usize>,
}

impl ModuleBodySchedule {
    pub(super) fn new(
        module: &ResolvedModule,
        schemes: &[CheckedGlobalScheme],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, TypeError> {
        let global_count = module.definitions().len();
        let implementation_count = module.implementations().len();
        if global_count != schemes.len() {
            return Err(invalid_state());
        }
        let count = global_count
            .checked_add(implementation_count)
            .ok_or_else(type_resource)?;
        let words = count.checked_add(63).ok_or_else(type_resource)? / 64;
        work.charge(count.checked_add(words).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let mut completed = Vec::new();
        completed
            .try_reserve_exact(words)
            .map_err(|_| type_resource())?;
        completed.resize(words, 0);
        let mut globals = HashMap::new();
        globals
            .try_reserve(global_count)
            .map_err(|_| type_resource())?;
        for (position, scheme) in schemes.iter().enumerate() {
            if globals.insert(scheme.binder, position).is_some() {
                return Err(invalid_state());
            }
        }
        let mut implementations = HashMap::new();
        implementations
            .try_reserve(implementation_count)
            .map_err(|_| type_resource())?;
        for (position, implementation) in module.implementations().iter().enumerate() {
            if implementations
                .insert(implementation.id, position)
                .is_some()
            {
                return Err(invalid_state());
            }
        }
        let method_count =
            module
                .implementations()
                .iter()
                .try_fold(0usize, |count, implementation| {
                    count
                        .checked_add(implementation.method_groups.len())
                        .ok_or_else(type_resource)
                })?;
        work.charge(method_count).map_err(|()| type_resource())?;
        let mut implementation_methods = HashMap::new();
        implementation_methods
            .try_reserve(method_count)
            .map_err(|_| type_resource())?;
        for (position, implementation) in module.implementations().iter().enumerate() {
            for method in &implementation.method_groups {
                work.charge(1).map_err(|()| type_resource())?;
                if implementation_methods
                    .insert(method.binder.id, position)
                    .is_some()
                    || globals.contains_key(&method.binder.id)
                {
                    return Err(invalid_state());
                }
            }
        }
        Ok(Self {
            global_count,
            implementation_count,
            completed,
            globals,
            implementations,
            implementation_methods,
        })
    }

    fn position(&self, declaration: ResolvedDeclarationIndex) -> Result<usize, TypeError> {
        match declaration {
            ResolvedDeclarationIndex::Global(index) if index < self.global_count => Ok(index),
            ResolvedDeclarationIndex::Implementation(index)
                if index < self.implementation_count =>
            {
                self.global_count
                    .checked_add(index)
                    .ok_or_else(invalid_state)
            }
            _ => Err(invalid_state()),
        }
    }

    fn declaration(&self, position: usize) -> Result<ResolvedDeclarationIndex, TypeError> {
        if position < self.global_count {
            return Ok(ResolvedDeclarationIndex::Global(position));
        }
        let implementation = position
            .checked_sub(self.global_count)
            .ok_or_else(invalid_state)?;
        if implementation >= self.implementation_count {
            return Err(invalid_state());
        }
        Ok(ResolvedDeclarationIndex::Implementation(implementation))
    }

    fn binder_declaration(&self, binder: BinderId) -> Result<ResolvedDeclarationIndex, TypeError> {
        if let Some(index) = self.globals.get(&binder) {
            Ok(ResolvedDeclarationIndex::Global(*index))
        } else {
            self.implementation_methods
                .get(&binder)
                .copied()
                .map(ResolvedDeclarationIndex::Implementation)
                .ok_or_else(invalid_state)
        }
    }

    pub(super) fn is_completed(
        &self,
        declaration: ResolvedDeclarationIndex,
    ) -> Result<bool, TypeError> {
        let position = self.position(declaration)?;
        Ok(self
            .completed
            .get(position / 64)
            .ok_or_else(invalid_state)?
            & (1u64 << (position % 64))
            != 0)
    }

    pub(super) fn mark_completed(
        &mut self,
        declaration: ResolvedDeclarationIndex,
    ) -> Result<(), TypeError> {
        let position = self.position(declaration)?;
        let word = self
            .completed
            .get_mut(position / 64)
            .ok_or_else(invalid_state)?;
        let bit = 1u64 << (position % 64);
        if *word & bit != 0 {
            return Err(invalid_state());
        }
        *word |= bit;
        Ok(())
    }

    pub(super) fn global_position(
        &self,
        binder: BinderId,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        self.globals.get(&binder).copied().ok_or_else(invalid_state)
    }

    pub(super) fn restore_source_order(
        &self,
        checking: &mut ModuleBodyChecking,
        implementation_roots: &mut Vec<(BinderId, NodeId)>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        if checking.globals.globals.len() != self.global_count
            || checking.facts.0.len() != self.implementation_count
        {
            return Err(invalid_state());
        }
        for index in 0..self.global_count {
            loop {
                let target =
                    self.global_position(checking.globals.globals[index].binder.id(), work)?;
                if target == index {
                    break;
                }
                if target >= self.global_count {
                    return Err(invalid_state());
                }
                checking.globals.globals.swap(index, target);
            }
        }
        for index in 0..self.implementation_count {
            loop {
                work.charge(1).map_err(|()| type_resource())?;
                let target = *self
                    .implementations
                    .get(&checking.facts.0[index].id)
                    .ok_or_else(invalid_state)?;
                if target == index {
                    break;
                }
                if target >= self.implementation_count {
                    return Err(invalid_state());
                }
                checking.facts.0.swap(index, target);
            }
        }
        let count = implementation_roots.len();
        work.charge(count.checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let mut roots = HashMap::new();
        roots.try_reserve(count).map_err(|_| type_resource())?;
        for (binder, root) in implementation_roots.iter().copied() {
            if roots.insert(binder, root).is_some() {
                return Err(invalid_state());
            }
        }
        let mut ordered = Vec::new();
        ordered
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        for fact in &checking.facts.0 {
            for method in &fact.methods {
                work.charge(1).map_err(|()| type_resource())?;
                ordered.push((
                    method.binder,
                    roots.remove(&method.binder).ok_or_else(invalid_state)?,
                ));
            }
        }
        if !roots.is_empty() || ordered.len() != count {
            return Err(invalid_state());
        }
        *implementation_roots = ordered;
        Ok(())
    }
}

/// A source declaration actually referenced by a completed typed body or by
/// one of its already selected evidence plans. This is an inventory, not a
/// capture fact or permission to check a provider template.
pub(super) struct ModuleBodyDependency {
    pub(super) declaration: ResolvedDeclarationIndex,
    pub(super) completed: bool,
}

pub(super) struct ModuleBodyDependencies {
    entries: Vec<ModuleBodyDependency>,
}

fn mark_dependency(
    schedule: &ModuleBodySchedule,
    declaration: ResolvedDeclarationIndex,
    dependencies: &mut [u64],
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    work.charge(1).map_err(|()| type_resource())?;
    let position = schedule.position(declaration)?;
    let word = dependencies
        .get_mut(position / 64)
        .ok_or_else(invalid_state)?;
    *word |= 1u64 << (position % 64);
    Ok(())
}

fn retain_selected_dependencies(
    schedule: &ModuleBodySchedule,
    module: crate::module::ModuleId,
    selection: &EvidenceSelection,
    dependencies: &mut [u64],
    work: &mut TypeWorkBudget,
) -> Result<(), TypeError> {
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    work.charge(1).map_err(|()| type_resource())?;
    pending.try_reserve(1).map_err(|_| type_resource())?;
    pending.push(selection.root());
    while let Some(node) = pending.pop() {
        work.charge(1).map_err(|()| type_resource())?;
        if visited.contains(&node) {
            continue;
        }
        work.charge(1).map_err(|()| type_resource())?;
        visited.try_reserve(1).map_err(|_| type_resource())?;
        visited.insert(node);
        match selection.node(node).ok_or_else(invalid_state)? {
            crate::interface::EvidenceNode::Implementation {
                implementation,
                prerequisites,
                ..
            } => {
                work.charge(1).map_err(|()| type_resource())?;
                if implementation.module() == module {
                    let index = *schedule
                        .implementations
                        .get(&implementation)
                        .ok_or_else(invalid_state)?;
                    mark_dependency(
                        schedule,
                        ResolvedDeclarationIndex::Implementation(index),
                        dependencies,
                        work,
                    )?;
                }
                work.charge(prerequisites.len())
                    .map_err(|()| type_resource())?;
                pending
                    .try_reserve(prerequisites.len())
                    .map_err(|_| type_resource())?;
                pending.extend(prerequisites.iter().rev().copied());
            }
            crate::interface::EvidenceNode::ProviderFamily { prerequisites, .. } => {
                work.charge(prerequisites.len())
                    .map_err(|()| type_resource())?;
                pending
                    .try_reserve(prerequisites.len())
                    .map_err(|_| type_resource())?;
                pending.extend(prerequisites.iter().rev().copied());
            }
            crate::interface::EvidenceNode::Lexical { .. }
            | crate::interface::EvidenceNode::Abstract { .. }
            | crate::interface::EvidenceNode::NativeLayout { .. } => {}
        }
    }
    Ok(())
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    /// Queries only authentic completed declarations selected by the caller.
    /// This does not imply that their dependencies form a closed component.
    pub(super) fn completed_module_body_dependencies_for(
        &mut self,
        module: &ResolvedModule,
        checking: &ModuleBodyChecking,
        declarations: &[ResolvedDeclarationIndex],
    ) -> Result<ModuleBodyDependencies, TypeError> {
        let roots = self.completed_module_body_roots_for(checking, declarations)?;
        self.module_body_dependencies_from_roots(module, checking, &roots)
            .map(|(dependencies, _)| dependencies)
    }

    /// Keeps the maximal completed subset closed under actual typed and
    /// selected-evidence dependencies. Mutually recursive completed bodies
    /// remain together; an unchecked dependency removes its whole dependent
    /// component without assigning it a capture fact.
    pub(super) fn closed_completed_module_declarations(
        &mut self,
        module: &ResolvedModule,
        checking: &ModuleBodyChecking,
    ) -> Result<Vec<ResolvedDeclarationIndex>, TypeError> {
        let schedule = checking.schedule.as_ref().ok_or_else(invalid_state)?;
        let count = schedule
            .global_count
            .checked_add(schedule.implementation_count)
            .ok_or_else(type_resource)?;
        self.type_work
            .charge(count.checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let mut allowed = Vec::new();
        let mut rows = Vec::new();
        allowed
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        rows.try_reserve_exact(count).map_err(|_| type_resource())?;
        for position in 0..count {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            let declaration = schedule.declaration(position)?;
            let completed = schedule.is_completed(declaration)?;
            allowed.push(completed);
            rows.push(if completed {
                Some(self.completed_module_body_dependencies_for(
                    module,
                    checking,
                    &[declaration],
                )?)
            } else {
                None
            });
        }
        loop {
            let mut changed = false;
            for position in 0..count {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                if !allowed[position] {
                    continue;
                }
                for dependency in &rows[position].as_ref().ok_or_else(invalid_state)?.entries {
                    self.type_work.charge(1).map_err(|()| type_resource())?;
                    if !allowed[schedule.position(dependency.declaration)?] {
                        allowed[position] = false;
                        changed = true;
                        break;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut declarations = Vec::new();
        for (position, admitted) in allowed.into_iter().enumerate() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if admitted {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                declarations.try_reserve(1).map_err(|_| type_resource())?;
                declarations.push(schedule.declaration(position)?);
            }
        }
        Ok(declarations)
    }

    fn module_body_dependencies_from_roots(
        &mut self,
        module: &ResolvedModule,
        checking: &ModuleBodyChecking,
        roots: &[(BinderId, NodeId)],
    ) -> Result<(ModuleBodyDependencies, HashSet<NodeId>), TypeError> {
        let schedule = checking.schedule.as_ref().ok_or_else(invalid_state)?;
        let publication = checking.publication.as_ref().ok_or_else(invalid_state)?;
        let count = schedule
            .global_count
            .checked_add(schedule.implementation_count)
            .ok_or_else(type_resource)?;
        let words = count.checked_add(63).ok_or_else(type_resource)? / 64;
        self.type_work.charge(words).map_err(|()| type_resource())?;
        let mut dependencies = Vec::new();
        dependencies
            .try_reserve_exact(words)
            .map_err(|_| type_resource())?;
        dependencies.resize(words, 0u64);
        self.type_work
            .charge(roots.len())
            .map_err(|()| type_resource())?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(roots.len())
            .map_err(|_| type_resource())?;
        pending.extend(roots.iter().map(|(_, node)| *node));
        let mut visited = HashSet::new();
        while let Some(node) = pending.pop() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if visited.contains(&node) {
                continue;
            }
            self.type_work.charge(1).map_err(|()| type_resource())?;
            visited.try_reserve(1).map_err(|_| type_resource())?;
            visited.insert(node);
            let kind = self
                .builder
                .compiler_node_kind(node)
                .map_err(TypeError::from)?;
            if let Some(crate::core::PureExprKind::Variable(variable)) = F::pure(kind) {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                let binder = variable.binder();
                if let Some(index) = schedule.globals.get(&binder).copied() {
                    mark_dependency(
                        schedule,
                        ResolvedDeclarationIndex::Global(index),
                        &mut dependencies,
                        &mut self.type_work,
                    )?;
                } else if let Some(index) = schedule.implementation_methods.get(&binder).copied() {
                    mark_dependency(
                        schedule,
                        ResolvedDeclarationIndex::Implementation(index),
                        &mut dependencies,
                        &mut self.type_work,
                    )?;
                }
            }
            let child_count = F::child_count(kind);
            self.type_work
                .charge(child_count)
                .map_err(|()| type_resource())?;
            pending
                .try_reserve(child_count)
                .map_err(|_| type_resource())?;
            for index in (0..child_count).rev() {
                pending.push(F::child_at(kind, index).ok_or_else(invalid_state)?);
            }
        }
        for (node, slot, method) in &self.method_capture_uses {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if !visited.contains(node) {
                continue;
            }
            let (selection, _) = publication
                .capture_selection(*slot, Some(*method), &mut self.type_work)
                .map_err(|failure| selection_failure(failure, None))?;
            retain_selected_dependencies(
                schedule,
                module.module(),
                selection,
                &mut dependencies,
                &mut self.type_work,
            )?;
        }
        for (node, _, slot) in &self.global_capture_uses {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if !visited.contains(node) {
                continue;
            }
            let (selection, _) = publication
                .capture_selection(*slot, None, &mut self.type_work)
                .map_err(|failure| selection_failure(failure, None))?;
            retain_selected_dependencies(
                schedule,
                module.module(),
                selection,
                &mut dependencies,
                &mut self.type_work,
            )?;
        }
        let mut entries = Vec::new();
        for position in 0..count {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if dependencies[position / 64] & (1u64 << (position % 64)) == 0 {
                continue;
            }
            let declaration = if position < schedule.global_count {
                ResolvedDeclarationIndex::Global(position)
            } else {
                ResolvedDeclarationIndex::Implementation(position - schedule.global_count)
            };
            let completed = schedule.is_completed(declaration)?;
            self.type_work.charge(1).map_err(|()| type_resource())?;
            entries.try_reserve(1).map_err(|_| type_resource())?;
            entries.push(ModuleBodyDependency {
                declaration,
                completed,
            });
        }
        Ok((ModuleBodyDependencies { entries }, visited))
    }

    /// Exposes actual completed typed roots. It does not regard an unchecked
    /// declaration or an implementation candidate as a dependency fact.
    pub(super) fn completed_module_body_roots(
        &mut self,
        checking: &ModuleBodyChecking,
    ) -> Result<Vec<(BinderId, NodeId)>, TypeError> {
        let count = checking
            .globals
            .globals
            .len()
            .checked_add(self.implementation_capture_roots.len())
            .ok_or_else(type_resource)?;
        self.type_work.charge(count).map_err(|()| type_resource())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        roots.extend(
            checking
                .globals
                .globals
                .iter()
                .map(|body| (body.binder.id(), body.initializer)),
        );
        roots.extend_from_slice(&self.implementation_capture_roots);
        Ok(roots)
    }

    fn completed_module_body_roots_for(
        &mut self,
        checking: &ModuleBodyChecking,
        declarations: &[ResolvedDeclarationIndex],
    ) -> Result<Vec<(BinderId, NodeId)>, TypeError> {
        let schedule = checking.schedule.as_ref().ok_or_else(invalid_state)?;
        self.type_work
            .charge(schedule.completed.len())
            .map_err(|()| type_resource())?;
        let mut selected = Vec::new();
        selected
            .try_reserve_exact(schedule.completed.len())
            .map_err(|_| type_resource())?;
        selected.resize(schedule.completed.len(), 0u64);
        for declaration in declarations {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if !schedule.is_completed(*declaration)? {
                return Err(invalid_state());
            }
            let position = schedule.position(*declaration)?;
            let word = selected.get_mut(position / 64).ok_or_else(invalid_state)?;
            let bit = 1u64 << (position % 64);
            if *word & bit != 0 {
                return Err(invalid_state());
            }
            *word |= bit;
        }
        let mut roots = self.completed_module_body_roots(checking)?;
        let mut output = 0;
        for index in 0..roots.len() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            let declaration = schedule.binder_declaration(roots[index].0)?;
            let position = schedule.position(declaration)?;
            if selected[position / 64] & (1u64 << (position % 64)) != 0 {
                roots.swap(output, index);
                output += 1;
            }
        }
        roots.truncate(output);
        Ok(roots)
    }

    /// Selects completed original occurrences once and joins them without
    /// publication. Later bodies append to this same module transaction.
    pub(super) fn stage_completed_module_body_evidence(
        &mut self,
        checking: &mut ModuleBodyChecking,
    ) -> Result<(), TypeError> {
        let incoming = self.prepare_evidence_publication()?;
        if let Some(publication) = &mut checking.publication {
            publication
                .append(incoming, &mut self.constraint_work)
                .map_err(|failure| selection_failure(failure, None))?;
        } else {
            checking.publication = Some(incoming);
        }
        Ok(())
    }

    /// Reconstructs captures only for an authenticated closed subset. Checked
    /// bodies outside that subset remain stored with their existing state;
    /// none of their incomplete capture facts is offered to template checking.
    pub(super) fn completed_module_provider_facts_for(
        &mut self,
        module: &ResolvedModule,
        schemes: &mut [CheckedGlobalScheme],
        interfaces: &[crate::resolved::SharedCheckedInterfaceFact],
        checking: &mut ModuleBodyChecking,
        declarations: &[ResolvedDeclarationIndex],
    ) -> Result<crate::resolved::ProviderDefiningFacts, TypeError> {
        self.stage_completed_module_body_evidence(checking)?;
        if self.cleanup_rows.is_empty() {
            self.zonk_builder_types().map_err(TypeError::Internal)?;
        } else {
            self.zonk_builder_types_since(None, false)
                .map_err(TypeError::Internal)?;
        }
        let roots = self.completed_module_body_roots_for(checking, declarations)?;
        let (dependencies, reachable) =
            self.module_body_dependencies_from_roots(module, checking, &roots)?;
        let schedule = checking.schedule.as_ref().ok_or_else(invalid_state)?;
        self.type_work
            .charge(declarations.len())
            .map_err(|()| type_resource())?;
        let mut selected = HashSet::new();
        selected
            .try_reserve(declarations.len())
            .map_err(|_| type_resource())?;
        for declaration in declarations {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if !schedule.is_completed(*declaration)?
                || !selected.insert(schedule.position(*declaration)?)
            {
                return Err(invalid_state());
            }
        }
        for dependency in &dependencies.entries {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if !dependency.completed
                || !selected.contains(&schedule.position(dependency.declaration)?)
            {
                return Err(invalid_state());
            }
        }
        // Routes are scalar preparation records. Restrict them to the actual
        // queried graph, then restore the complete module records on success or
        // refusal. Selection and capture reconstruction still use the ordinary
        // engine, including all exact selected prerequisite facts.
        let mut methods = Vec::new();
        let mut globals = Vec::new();
        for record in &self.method_capture_uses {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if reachable.contains(&record.0) {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                methods.try_reserve(1).map_err(|_| type_resource())?;
                methods.push(*record);
            }
        }
        for record in &self.global_capture_uses {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if reachable.contains(&record.0) {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                globals.try_reserve(1).map_err(|_| type_resource())?;
                globals.push(*record);
            }
        }
        let publication = checking.publication.as_ref().ok_or_else(invalid_state)?;
        let all_methods = std::mem::replace(&mut self.method_capture_uses, methods);
        let all_globals = std::mem::replace(&mut self.global_capture_uses, globals);
        let captures =
            self.capture_completed_module_roots(module, &roots, &checking.facts.0, publication);
        self.method_capture_uses = all_methods;
        self.global_capture_uses = all_globals;
        let captures = captures?;
        if captures.len() != roots.len() {
            return Err(invalid_state());
        }
        let mut captures = captures.into_iter();
        let mut positions = Vec::new();
        for (binder, _) in &roots {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if let Some(position) = schedule.globals.get(binder).copied() {
                let scheme = schemes.get_mut(position).ok_or_else(invalid_state)?;
                if scheme.binder != *binder {
                    return Err(invalid_state());
                }
                scheme.capture = captures.next().ok_or_else(invalid_state)?;
                self.type_work.charge(1).map_err(|()| type_resource())?;
                positions.try_reserve(1).map_err(|_| type_resource())?;
                positions.push(position);
            }
        }
        let mut implementation_roots = roots.iter().skip(positions.len());
        let mut retained = CheckedImplementationFactBuffer(Vec::new());
        for fact in &mut checking.facts.0 {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            let source = *schedule
                .implementations
                .get(&fact.id)
                .ok_or_else(invalid_state)?;
            if !selected
                .contains(&schedule.position(ResolvedDeclarationIndex::Implementation(source))?)
            {
                continue;
            }
            for method in &mut fact.methods {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                if implementation_roots.next().map(|(binder, _)| *binder) != Some(method.binder) {
                    return Err(invalid_state());
                }
                method.capture = captures.next().ok_or_else(invalid_state)?;
            }
            self.type_work.charge(1).map_err(|()| type_resource())?;
            retained.0.try_reserve(1).map_err(|_| type_resource())?;
            retained.0.push(
                crate::resolved::clone_checked_implementation_fact(
                    fact,
                    &mut self.type_work,
                    &mut self.constraint_work,
                )
                .map_err(resolved_build_error)?,
            );
        }
        if captures.next().is_some() || implementation_roots.next().is_some() {
            return Err(invalid_state());
        }
        let mut constraints = std::mem::take(&mut self.constraint_work);
        let result = self.prepare_provider_defining_facts_completed(
            positions.iter().map(|position| &schemes[*position]),
            interfaces,
            &retained.0,
            module.imported_facts(),
            &mut constraints,
        );
        self.constraint_work = constraints;
        result
    }
}

/// Detects a local instance from the original resolved body, including bodies
/// nested inside a supplied lexical method. It does not inspect provider
/// definitions or implementation candidates.
pub(super) fn declaration_has_local_provider_instance(
    module: &ResolvedModule,
    declaration: ResolvedDeclarationIndex,
    work: &mut TypeWorkBudget,
) -> Result<bool, TypeError> {
    let pending = declaration_source_items(module, declaration, work)?;
    visit_source_items(pending, work, |expression, _| {
        Ok(matches!(&expression.kind,
        ResolvedExprKind::ProviderResource(resource) if resource.definition.module() == module.module()))
    })
}

/// This gate only avoids retaining a provider environment for ordinary bodies.
/// It supplies no selection, capture, or executable permission.
pub(super) fn declaration_has_provider_instance(
    module: &ResolvedModule,
    declaration: ResolvedDeclarationIndex,
    work: &mut TypeWorkBudget,
) -> Result<bool, TypeError> {
    let pending = declaration_source_items(module, declaration, work)?;
    visit_source_items(pending, work, |expression, _| {
        Ok(matches!(
            &expression.kind,
            ResolvedExprKind::ProviderResource(_)
        ))
    })
}

/// Source coordinates are readiness hints only. Checked typed components and
/// their selected evidence remain the sole capture and original authority.
pub(super) fn declaration_local_provider_requirements(
    module: &ResolvedModule,
    declaration: ResolvedDeclarationIndex,
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::resolved::ResourceDefinitionId>, TypeError> {
    let pending = declaration_source_items(module, declaration, work)?;
    let mut required = Vec::new();
    visit_source_items(pending, work, |expression, work| {
        if let ResolvedExprKind::ProviderResource(resource) = &expression.kind
            && resource.definition.module() == module.module()
        {
            work.charge(required.len().checked_add(1).ok_or_else(type_resource)?)
                .map_err(|()| type_resource())?;
            if !required.contains(&resource.definition) {
                required.try_reserve(1).map_err(|_| type_resource())?;
                required.push(resource.definition);
            }
        }
        Ok(false)
    })?;
    Ok(required)
}

impl ModuleBodySchedule {
    pub(super) fn original_source_dependencies(
        &self,
        definition: &crate::resolved::ResolvedResourceDefinition,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<ResolvedDeclarationIndex>, TypeError> {
        let mut pending = Vec::new();
        push_source(
            &mut pending,
            BodySourceItem::Expression(&definition.acquire),
            work,
            definition.span,
        )?;
        push_source(
            &mut pending,
            BodySourceItem::Expression(&definition.finish),
            work,
            definition.span,
        )?;
        for clause in &definition.handlers {
            push_source(
                &mut pending,
                BodySourceItem::Expression(&clause.body),
                work,
                clause.span,
            )?;
        }
        let mut dependencies = Vec::new();
        visit_source_items(pending, work, |expression, work| {
            let ResolvedExprKind::Occurrence(occurrence) = &expression.kind else {
                return Ok(false);
            };
            let mut retain = |declaration| -> Result<(), TypeError> {
                work.charge(
                    dependencies
                        .len()
                        .checked_add(1)
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
                if !dependencies.contains(&declaration) {
                    dependencies.try_reserve(1).map_err(|_| type_resource())?;
                    dependencies.push(declaration);
                }
                Ok(())
            };
            match occurrence.term {
                crate::resolved::ResolvedTermName::Global(binder) => {
                    if self.globals.contains_key(&binder)
                        || self.implementation_methods.contains_key(&binder)
                    {
                        retain(self.binder_declaration(binder)?)?;
                    }
                }
                crate::resolved::ResolvedTermName::Method(_) => {
                    // Keep the local candidate inventory complete before selecting
                    // an ordinary method. This index never selects an implementation.
                    for index in 0..self.implementation_count {
                        retain(ResolvedDeclarationIndex::Implementation(index))?;
                    }
                }
            }
            Ok(false)
        })?;
        Ok(dependencies)
    }
}

fn declaration_source_items<'a>(
    module: &'a ResolvedModule,
    declaration: ResolvedDeclarationIndex,
    work: &mut TypeWorkBudget,
) -> Result<Vec<BodySourceItem<'a>>, TypeError> {
    let mut pending = Vec::new();
    match declaration {
        ResolvedDeclarationIndex::Global(index) => {
            let definition = module.definitions().get(index).ok_or_else(invalid_state)?;
            match &definition.kind {
                ResolvedDefinitionKind::Equational(global)
                | ResolvedDefinitionKind::ForeignConstant(global) => {
                    for equation in &global.equations {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&equation.body),
                            work,
                            equation.span,
                        )?;
                    }
                }
                ResolvedDefinitionKind::InlineOperational(global) => {
                    push_source(
                        &mut pending,
                        BodySourceItem::Block(&global.body),
                        work,
                        global.body.span,
                    )?;
                }
            }
        }
        ResolvedDeclarationIndex::Implementation(index) => {
            let implementation = module
                .implementations()
                .get(index)
                .ok_or_else(invalid_state)?;
            for method in &implementation.method_groups {
                for equation in &method.equations {
                    push_source(
                        &mut pending,
                        BodySourceItem::Expression(&equation.body),
                        work,
                        equation.span,
                    )?;
                }
            }
        }
        ResolvedDeclarationIndex::Resource(_)
        | ResolvedDeclarationIndex::SourceResource(_)
        | ResolvedDeclarationIndex::Type(_)
        | ResolvedDeclarationIndex::Interface(_)
        | ResolvedDeclarationIndex::Effect(_) => return Ok(pending),
    }
    Ok(pending)
}

#[cfg(test)]
pub(super) fn ordinary_source_occurrences_for_test<'a>(
    body: &'a ResolvedExpr,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a crate::resolved::ResolvedOccurrence>, TypeError> {
    let mut pending = Vec::new();
    push_source(
        &mut pending,
        BodySourceItem::Expression(body),
        work,
        body.span,
    )?;
    let mut occurrences = Vec::new();
    visit_source_items(pending, work, |expression, work| {
        if let ResolvedExprKind::Occurrence(occurrence) = &expression.kind {
            work.charge(1).map_err(|()| type_resource())?;
            occurrences.try_reserve(1).map_err(|_| type_resource())?;
            occurrences.push(occurrence);
        }
        Ok(false)
    })?;
    Ok(occurrences)
}

fn visit_source_items<'a>(
    mut pending: Vec<BodySourceItem<'a>>,
    work: &mut TypeWorkBudget,
    mut visit: impl FnMut(&'a ResolvedExpr, &mut TypeWorkBudget) -> Result<bool, TypeError>,
) -> Result<bool, TypeError> {
    while let Some(item) = pending.pop() {
        work.charge(1).map_err(|()| type_resource())?;
        match item {
            BodySourceItem::Block(block) => {
                push_source(
                    &mut pending,
                    BodySourceItem::Expression(&block.result),
                    work,
                    block.span,
                )?;
                for declaration in &block.declarations {
                    push_source(
                        &mut pending,
                        BodySourceItem::Declaration(declaration),
                        work,
                        block.span,
                    )?;
                }
            }
            BodySourceItem::Declaration(ResolvedLocalDeclaration::Binding(binding)) => {
                push_source(
                    &mut pending,
                    BodySourceItem::Expression(&binding.initializer),
                    work,
                    binding.span,
                )?;
            }
            BodySourceItem::Declaration(ResolvedLocalDeclaration::Recursive(group)) => {
                for member in &group.members {
                    push_source(
                        &mut pending,
                        BodySourceItem::Expression(&member.initializer),
                        work,
                        group.span,
                    )?;
                }
            }
            BodySourceItem::Declaration(ResolvedLocalDeclaration::Evidence(source)) => {
                for method in &source.method_groups {
                    for equation in &method.equations {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&equation.body),
                            work,
                            equation.span,
                        )?;
                    }
                }
            }
            BodySourceItem::Declaration(ResolvedLocalDeclaration::Newtype(_)) => {}
            BodySourceItem::Expression(expression) => {
                if visit(expression, work)? {
                    return Ok(true);
                }
                match &expression.kind {
                    ResolvedExprKind::CopyWindow(window) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&window.body),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&window.state),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::ProviderResource(resource) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&resource.body),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&resource.initializer),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::Block(block) => push_source(
                        &mut pending,
                        BodySourceItem::Block(block),
                        work,
                        expression.span,
                    )?,
                    ResolvedExprKind::Function(function) => push_source(
                        &mut pending,
                        BodySourceItem::Block(&function.body),
                        work,
                        expression.span,
                    )?,
                    ResolvedExprKind::Apply(application) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&application.argument),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&application.function),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::Tuple(elements) => {
                        for element in elements {
                            push_source(
                                &mut pending,
                                BodySourceItem::Expression(element),
                                work,
                                expression.span,
                            )?;
                        }
                    }
                    ResolvedExprKind::Add(binary)
                    | ResolvedExprKind::Multiply(binary)
                    | ResolvedExprKind::Equal(binary) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&binary.left),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&binary.right),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::Match(matched) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&matched.scrutinee),
                            work,
                            expression.span,
                        )?;
                        for arm in &matched.arms {
                            push_source(
                                &mut pending,
                                BodySourceItem::Expression(&arm.body),
                                work,
                                expression.span,
                            )?;
                        }
                    }
                    ResolvedExprKind::Resource(resource) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&resource.body),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&resource.initializer),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::Cleanup(cleanup) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&cleanup.body),
                            work,
                            expression.span,
                        )?;
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&cleanup.action),
                            work,
                            expression.span,
                        )?;
                    }
                    ResolvedExprKind::Perform(request) => push_source(
                        &mut pending,
                        BodySourceItem::Expression(&request.operand),
                        work,
                        expression.span,
                    )?,
                    ResolvedExprKind::Handle(handler) => {
                        push_source(
                            &mut pending,
                            BodySourceItem::Expression(&handler.body),
                            work,
                            expression.span,
                        )?;
                        for clause in &handler.clauses {
                            push_source(
                                &mut pending,
                                BodySourceItem::Expression(&clause.body),
                                work,
                                expression.span,
                            )?;
                        }
                    }
                    ResolvedExprKind::Resume(resume) => push_source(
                        &mut pending,
                        BodySourceItem::Expression(&resume.value),
                        work,
                        expression.span,
                    )?,
                    ResolvedExprKind::String(_)
                    | ResolvedExprKind::Integer(_)
                    | ResolvedExprKind::Boolean(_)
                    | ResolvedExprKind::Unit
                    | ResolvedExprKind::Occurrence(_)
                    | ResolvedExprKind::Constructor(_)
                    | ResolvedExprKind::Discard(_) => {}
                }
            }
        }
    }
    Ok(false)
}

enum BodySourceItem<'a> {
    Expression(&'a ResolvedExpr),
    Block(&'a ResolvedBlock),
    Declaration(&'a ResolvedLocalDeclaration),
}

fn push_source<'a>(
    pending: &mut Vec<BodySourceItem<'a>>,
    item: BodySourceItem<'a>,
    work: &mut TypeWorkBudget,
    _span: Span,
) -> Result<(), TypeError> {
    work.charge(1).map_err(|()| type_resource())?;
    pending.try_reserve(1).map_err(|_| type_resource())?;
    pending.push(item);
    Ok(())
}
