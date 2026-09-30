//! Test-only bounded exporter for the TASK-0032 formal experiment.

use crate::{
    core::{ValidatedEffectProgram, validate_effect_modules},
    elaborate::{EffectElaborator, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/direct-effects/one-shot/fixtures")
        .join(format!("core-cleanup-{name}.ash"))
}

pub(crate) struct CompiledFixture {
    pub(crate) program: ValidatedEffectProgram,
    pub(crate) sources: Vec<(SourceId, ModuleId, String)>,
}

pub(crate) fn effect_program(name: &str) -> CompiledFixture {
    let graph = load_module_graph(&fixture(name), &ModuleRoots::empty()).expect("fixture loads");
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependencies precede importers");
                DependencyExports::new(edge, dependency.exports()).expect("exports authenticate")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("fixture resolves"))
                .expect("fixture checks"),
        );
    }
    let linked = link_modules(checked, graph.entry()).expect("fixture links");
    let linked = validate_interface_evidence(linked).expect("interface evidence authenticates");
    let mut elaborator = EffectElaborator::for_module_program(&linked).expect("builder starts");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("effects lower");
    let core = elaborator.finish(typed.node).expect("Core finishes");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = validate_effect_modules(core, &sources, &module_sources)
        .expect("Core independently validates");
    let sources = graph
        .modules()
        .iter()
        .map(|module| {
            (
                module.source().id(),
                module.id(),
                if module.id().is_builtin_resource() {
                    module_key(module.id())
                } else {
                    module
                        .canonical_path()
                        .strip_prefix(env!("CARGO_MANIFEST_DIR"))
                        .expect("fixture module is in repository")
                        .to_string_lossy()
                        .into_owned()
                },
            )
        })
        .collect();
    CompiledFixture { program, sources }
}

use super::{
    CorePattern, CorePatternKind, EffectExprKind, EffectOperation, NodeId, PureComputation,
    PureExprKind, PureValue, TypedBinder,
};
use crate::{
    module::ModuleId,
    resolved::{BinderId, ResourceApi},
    source::{Origin, SourceId, Span},
    types::{EffectInstance, EffectRow, Type, TypeVariableId},
};
use std::collections::{BTreeMap, HashMap, HashSet};

fn list(items: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", items.into_iter().collect::<Vec<_>>().join(", "))
}

fn module_key(module: ModuleId) -> String {
    let namespace = if module.is_builtin_cell() {
        "cell"
    } else if module.is_builtin_native_buffer() {
        "nativeBuffer"
    } else {
        "source"
    };
    format!("{namespace}:{}", module.value())
}

#[derive(Default)]
struct Exporter {
    slots: HashMap<NodeId, usize>,
    binders: BTreeMap<BinderId, usize>,
    resources: BTreeMap<TypeVariableId, usize>,
    effects: BTreeMap<crate::types::EffectId, usize>,
    sources: HashMap<SourceId, (usize, usize)>,
    owners: HashMap<crate::resolved::ResumeId, usize>,
    manifest: Vec<String>,
}

impl Exporter {
    fn owner(&mut self, id: crate::resolved::ResumeId) -> usize {
        let next = self.owners.len();
        let value = *self.owners.entry(id).or_insert(next);
        self.manifest.push(format!("owner {value} {id:?}"));
        value
    }
    fn binder_id(&mut self, id: BinderId) -> usize {
        if let Some(value) = self.binders.get(&id) {
            return *value;
        }
        let value = self.binders.len();
        self.binders.insert(id, value);
        self.manifest.push(format!(
            "binder {value} {}:{}",
            id.module().map_or_else(|| "generated".into(), module_key),
            id.local()
        ));
        value
    }
    fn resource_id(&mut self, id: TypeVariableId) -> usize {
        if let Some(value) = self.resources.get(&id) {
            return *value;
        }
        let value = self.resources.len();
        self.resources.insert(id, value);
        self.manifest.push(format!(
            "resource {value} {}:{}",
            id.module().map_or_else(|| "generated".into(), module_key),
            id.local()
        ));
        value
    }
    fn source(&mut self, span: Span) -> String {
        let (module, source) = self.sources[&span.source()];
        format!(
            "⟨{module}, {source}, {}, {}⟩",
            span.range().start(),
            span.range().end()
        )
    }
    fn origin(&mut self, origin: &Origin) -> String {
        match origin {
            Origin::Source(span) => format!("source {}", self.source(*span)),
            Origin::Generated { cause, reason } => {
                format!("generated {reason:?} ({})", self.origin(cause))
            }
            Origin::Related { primary, related } => {
                let primary = self.origin(primary);
                let related = list(related.iter().map(|span| self.source(*span)));
                format!("related ({primary}) {related}")
            }
        }
    }
    fn ty(&mut self, ty: &Type) -> Result<String, String> {
        Ok(match ty {
            Type::Unit => ".unit".into(),
            Type::Bool => ".boolean".into(),
            Type::Int => ".integer".into(),
            Type::Tuple(elements) => match elements.as_ref() {
                [left, right] => format!("(.product {} {})", self.ty(left)?, self.ty(right)?),
                _ => return Err("unsupported tuple type".into()),
            },
            Type::Function(left, right) => {
                format!("(.function {} {} [])", self.ty(left)?, self.ty(right)?)
            }
            Type::EffectfulFunction(left, right) => format!(
                "(.function {} {} {})",
                self.ty(left)?,
                self.ty(right.value())?,
                self.row(right.effects())?
            ),
            Type::Application(head, argument) => {
                let (Type::Nominal(nominal), Type::Variable(identity)) =
                    (head.as_ref(), argument.as_ref())
                else {
                    return Err("unsupported type application".into());
                };
                let Some(api) = ResourceApi::for_module(nominal.module()) else {
                    return Err("unsealed reference type".into());
                };
                if api.is_native_buffer()
                    || api.handle() != *nominal
                    || !self.resources.contains_key(identity)
                {
                    return Err("unsealed or unsupported resource handle".into());
                }
                format!("(.reference (.bound {}))", self.resource_id(*identity))
            }
            _ => return Err("unsupported type".into()),
        })
    }
    fn binder(&mut self, binder: &TypedBinder) -> Result<String, String> {
        let id = self.binder_id(binder.id());
        let ty = self.ty(binder.ty())?;
        let origin = self.origin(binder.origin());
        self.manifest.push(format!("binder-origin {id} {origin}"));
        Ok(format!("⟨{id}, {ty}⟩"))
    }
    fn effect(&mut self, instance: &EffectInstance) -> Result<String, String> {
        if let Some(api) = ResourceApi::for_module(instance.effect().module()) {
            if api.is_native_buffer() || instance.effect() != api.ops() {
                return Err("unsupported builtin effect".into());
            }
            let [Type::Variable(identity)] = instance.arguments() else {
                return Err("invalid cell effect arguments".into());
            };
            if !self.resources.contains_key(identity) {
                return Err("unowned cell identity".into());
            }
            return Ok(format!("(.cell (.bound {}))", self.resource_id(*identity)));
        }
        let next = self.effects.len();
        let id = *self.effects.entry(instance.effect()).or_insert(next);
        let mut args = Vec::new();
        for argument in instance.arguments() {
            // This increment accepts the fixture's exact nullary user effects.
            // Other closed arguments need a declared calculus argument encoding.
            match argument {
                Type::Variable(identity) if self.resources.contains_key(identity) => args.push(
                    format!("(.resource (.bound {}))", self.resource_id(*identity)),
                ),
                _ => return Err("unsupported user effect argument".into()),
            }
        }
        self.manifest.push(format!(
            "effect {id} {}:{} {}",
            module_key(instance.effect().module()),
            instance.effect().declaration(),
            list(args.clone())
        ));
        Ok(format!("(.user {id} {})", list(args)))
    }
    fn row(&mut self, row: &EffectRow) -> Result<String, String> {
        if row.tail().is_some() {
            return Err("open effect row".into());
        }
        Ok(list(
            row.known()
                .iter()
                .map(|effect| self.effect(effect))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
    fn pattern(&mut self, pattern: &CorePattern) -> Result<String, String> {
        let ty = self.ty(&pattern.ty)?;
        let origin = self.origin(&pattern.origin);
        self.manifest.push(format!("pattern {ty} {origin}"));
        Ok(match &pattern.kind {
            CorePatternKind::Binder(binder) => format!("(.binder {})", self.binder(binder)?),
            CorePatternKind::Unit => ".unit".into(),
            CorePatternKind::Boolean(value) => format!("(.boolean {value})"),
            _ => return Err("unsupported pattern".into()),
        })
    }
    fn reference(&self, id: NodeId) -> usize {
        self.slots[&id]
    }
    fn signature(
        &mut self,
        program: &ValidatedEffectProgram,
        instance: &EffectInstance,
    ) -> Result<(), String> {
        let declaration = program
            .registry()
            .effect(instance.effect())
            .ok_or("missing effect declaration")?;
        if declaration.parameters.len() != instance.arguments().len() {
            return Err("effect argument arity".into());
        }
        let replacements = declaration
            .parameters
            .iter()
            .zip(instance.arguments())
            .map(|(parameter, argument)| (parameter.id, argument.clone()))
            .collect();
        let effect = self.effect(instance)?;
        for operation in &declaration.operations {
            let ty = crate::types::substitute_type_variables_with(
                &operation.annotation.ty,
                &replacements,
                |_| Ok::<_, String>(()),
                || "signature allocation".into(),
            )?;
            let ty = self.ty(&ty)?;
            let origin = self.origin(&operation.origin);
            self.manifest.push(format!(
                "signature {effect} {} {ty} {origin}",
                operation.id.operation()
            ));
        }
        Ok(())
    }
    fn kind(
        &mut self,
        program: &ValidatedEffectProgram,
        kind: &EffectExprKind,
    ) -> Result<String, String> {
        Ok(match kind {
            EffectExprKind::Pure(PureExprKind::Value(value)) => match value {
                PureValue::Unit(_) => ".unit".into(),
                PureValue::Boolean(value) => format!("(.boolean {})", value.value()),
                PureValue::Integer(value) => format!("(.integer ({}))", value.value()),
                PureValue::Function(function) => format!(
                    "(.function {} {})",
                    self.binder(function.parameter())?,
                    self.reference(function.body())
                ),
                _ => return Err("unsupported value".into()),
            },
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                format!("(.variable {})", self.binder_id(variable.binder()))
            }
            EffectExprKind::Pure(PureExprKind::Computation(computation)) => match computation {
                PureComputation::Bind(bind) => format!(
                    "(.bind {} {} {})",
                    self.binder(bind.binder())?,
                    self.reference(bind.initializer()),
                    self.reference(bind.body())
                ),
                PureComputation::Apply(app) => format!(
                    "(.apply {} {})",
                    self.reference(app.function()),
                    self.reference(app.argument())
                ),
                PureComputation::Tuple(tuple) => {
                    if tuple.elements().len() != 2 {
                        return Err("unsupported tuple".into());
                    }
                    format!(
                        "(.tuple {})",
                        list(
                            tuple
                                .elements()
                                .iter()
                                .map(|id| self.reference(*id).to_string())
                        )
                    )
                }
                PureComputation::Match(matches) => {
                    let mut arms = Vec::new();
                    for arm in matches.arms() {
                        let origin = self.origin(arm.origin());
                        self.manifest
                            .push(format!("match-arm body={} {origin}", arm.body().value()));
                        arms.push(format!(
                            "⟨{}, {}⟩",
                            self.pattern(arm.pattern())?,
                            self.reference(arm.body())
                        ));
                    }
                    let valid = matches!(matches.arms(), [arm] if matches!(arm.pattern().kind, CorePatternKind::Unit))
                        || matches!(matches.arms(), [a,b] if matches!((&a.pattern().kind, &b.pattern().kind), (CorePatternKind::Boolean(x),CorePatternKind::Boolean(y)) if x != y));
                    if !valid {
                        return Err("unsupported match".into());
                    }
                    format!(
                        "(.matchCases {} {})",
                        self.reference(matches.scrutinee()),
                        list(arms)
                    )
                }
                PureComputation::RecursiveBind(group) => {
                    let [member] = group.members() else {
                        return Err("unsupported recursive group".into());
                    };
                    let mut pending = vec![member.initializer()];
                    let mut seen = HashSet::new();
                    while let Some(id) = pending.pop() {
                        if !seen.insert(id) {
                            continue;
                        }
                        let node = program.node(id).ok_or("missing initializer")?;
                        if matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == member.binder().id())
                        {
                            return Err("recursive initializer".into());
                        }
                        pending.extend(
                            (0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)),
                        );
                    }
                    if !matches!(
                        &program
                            .node(member.initializer())
                            .ok_or("missing initializer")?
                            .kind,
                        EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(_)))
                    ) {
                        return Err("unsupported global initializer".into());
                    }
                    format!(
                        "(.recursiveBind [⟨{}, {}⟩] {})",
                        self.binder(member.binder())?,
                        self.reference(member.initializer()),
                        self.reference(group.body())
                    )
                }
                _ => return Err("unsupported computation".into()),
            },
            EffectExprKind::Operation(operation) => match operation {
                EffectOperation::Resource(resource) => {
                    let api = resource.acquisition.api().ok_or("unsealed acquisition")?;
                    if api.is_native_buffer() {
                        return Err("native buffer acquisition".into());
                    }
                    let identity = self.resource_id(resource.acquisition.identity);
                    let handle = self.binder_id(resource.acquisition.handle);
                    let methods = resource
                        .acquisition
                        .methods
                        .iter()
                        .map(|id| self.binder_id(*id))
                        .collect::<Vec<_>>();
                    let span = self.source(resource.acquisition.span);
                    self.manifest.push(format!("cell {identity} api={} handle={handle} methods={methods:?} provider={}:{} span={span}", module_key(resource.acquisition.builtin), module_key(resource.acquisition.provider.module()), resource.acquisition.provider.declaration()));
                    format!(
                        "(.resource {identity} {} {} {})",
                        self.binder(&resource.handle)?,
                        self.reference(resource.initializer()),
                        self.reference(resource.body())
                    )
                }
                EffectOperation::Cleanup(scope) => {
                    let callback = self.binder_id(scope.callback);
                    let span = self.source(scope.span);
                    let action_span = self.source(scope.action_span);
                    self.manifest.push(format!(
                        "cleanup {callback} scope={span} action={action_span}"
                    ));
                    // Recover the authenticated callback occurrence's actual type.
                    let action = program.node(scope.action).ok_or("missing cleanup action")?;
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        app,
                    ))) = &action.kind
                    else {
                        return Err("cleanup action shape".into());
                    };
                    let function = program
                        .node(app.function())
                        .ok_or("missing cleanup function")?;
                    if !matches!(&function.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == scope.callback)
                    {
                        return Err("cleanup callback mismatch".into());
                    }
                    format!(
                        "(.cleanup ⟨{callback}, {}⟩ {} {})",
                        self.ty(&function.ty)?,
                        self.reference(scope.action),
                        self.reference(scope.body)
                    )
                }
                EffectOperation::Request(request) => {
                    self.signature(program, request.effect())?;
                    format!(
                        "(.request {} {} {})",
                        self.effect(request.effect())?,
                        request.operation().operation(),
                        self.reference(request.operand())
                    )
                }
                EffectOperation::Handler(handler) => {
                    if handler.hook_root().is_some() || handler.hook_registration.is_some() {
                        return Err("generated hook handler".into());
                    }
                    self.signature(program, handler.effect())?;
                    let mut clauses = Vec::new();
                    for clause in handler.clauses() {
                        let origin = self.origin(clause.origin());
                        self.manifest.push(format!(
                            "clause operation={} body={} {origin}",
                            clause.operation().operation(),
                            clause.body().value()
                        ));
                        clauses.push(format!(
                            "⟨{}, {}, {}, {}⟩",
                            clause.operation().operation(),
                            self.pattern(clause.pattern())?,
                            self.owner(clause.resume()),
                            self.reference(clause.body())
                        ));
                    }
                    format!(
                        "(.handler {} {} {} {})",
                        handler.id().value(),
                        self.effect(handler.effect())?,
                        self.reference(handler.body()),
                        list(clauses)
                    )
                }
                EffectOperation::Resume(resume) => format!(
                    "(.resume {} {} .{} {})",
                    resume.handler().value(),
                    self.owner(resume.owner()),
                    match resume.use_state() {
                        super::ResumeUse::Available => "available",
                        super::ResumeUse::Consumed => "consumed",
                    },
                    self.reference(resume.value())
                ),
                EffectOperation::Discard(discard) => format!(
                    "(.discard {} {} .{})",
                    discard.handler().value(),
                    self.owner(discard.owner()),
                    match discard.use_state() {
                        super::ResumeUse::Available => "available",
                        super::ResumeUse::Consumed => "consumed",
                    }
                ),
                EffectOperation::Registration(_) => return Err("hook registration".into()),
            },
        })
    }
}

fn export_with_identities(
    program: &ValidatedEffectProgram,
    sources: &[(SourceId, ModuleId, String)],
) -> Result<(String, IdentityMaps), String> {
    let mut exporter = Exporter::default();
    for (source, module, path) in sources {
        let slot = exporter.sources.len();
        exporter.sources.insert(*source, (slot, slot));
        exporter.manifest.push(format!(
            "source {slot} module={} path={path}",
            module_key(*module)
        ));
    }
    let mut order = Vec::new();
    let mut seen = HashSet::new();
    let mut work = vec![(program.root(), false)];
    while let Some((id, visited)) = work.pop() {
        if visited {
            order.push(id);
            continue;
        }
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).ok_or("missing node")?;
        if let EffectExprKind::Operation(EffectOperation::Resource(resource)) = &node.kind {
            exporter.resource_id(resource.acquisition.identity);
        }
        work.push((id, true));
        work.extend(
            (0..node.kind.child_count())
                .rev()
                .filter_map(|i| node.kind.child_at(i))
                .map(|child| (child, false)),
        );
    }
    exporter.slots = order
        .iter()
        .enumerate()
        .map(|(slot, id)| (*id, slot))
        .collect();
    let mut nodes = Vec::new();
    for id in order {
        let node = program.node(id).ok_or("missing node")?;
        let ty = exporter.ty(&node.ty)?;
        let row = exporter.row(node.effects())?;
        let source = exporter.source(node.origin.primary_span());
        let origin = exporter.origin(&node.origin);
        exporter
            .manifest
            .push(format!("node-origin {} {origin}", id.value()));
        let kind = exporter.kind(program, &node.kind)?;
        nodes.push(format!("  {{ originalId := {}, type := {ty}, effects := {row}, source := some {source}, kind := {kind} }}", id.value()));
    }
    exporter.manifest.sort();
    exporter.manifest.dedup();
    let manifest = list(exporter.manifest.iter().map(|line| format!("{:?}", line)));
    let node_count = nodes.len();
    let rendered = format!(
        "import CoreSyntax\nimport CoreTranslation\n\n/-! Generated from independently validated Effect Core by the test-only\nalignment exporter. Regenerate with the ignored Rust regeneration test.\nThe manifest retains static identities and signatures; it is not admission. -/\nnamespace Ash.OneShot.CoreExportedFixture\nopen CoreSyntax\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n\ndef graph : Graph := ⟨[\n{}\n  ], {}⟩\n\ndef identityManifest : List String := {manifest}\n\nexample : graph.nodes.length = {node_count} := rfl\nexample : checkShape graph = .ok () := rfl\nexample : (CoreTranslation.translate graph).isOk = true := rfl\n\nend Ash.OneShot.CoreExportedFixture\n",
        nodes.join(",\n"),
        exporter.reference(program.root())
    );
    Ok((
        rendered,
        IdentityMaps {
            nodes: exporter.slots,
            binders: exporter.binders,
            resources: exporter.resources,
            effects: exporter.effects,
            owners: exporter.owners,
        },
    ))
}

/// Frozen numbering produced by the same traversal that renders the graph.
/// Runtime export fails for missing identities rather than allocating new ones.
pub(crate) struct IdentityMaps {
    pub(crate) nodes: HashMap<NodeId, usize>,
    pub(crate) binders: BTreeMap<BinderId, usize>,
    pub(crate) resources: BTreeMap<TypeVariableId, usize>,
    pub(crate) effects: BTreeMap<crate::types::EffectId, usize>,
    pub(crate) owners: HashMap<crate::resolved::ResumeId, usize>,
}

pub(crate) fn identity_maps(fixture: &CompiledFixture) -> Result<IdentityMaps, String> {
    export_with_identities(&fixture.program, &fixture.sources).map(|(_, identities)| identities)
}

fn export(
    program: &ValidatedEffectProgram,
    sources: &[(SourceId, ModuleId, String)],
) -> Result<String, String> {
    export_with_identities(program, sources).map(|(rendered, _)| rendered)
}

#[test]
fn exports_complete_validated_fixture() {
    let program = effect_program("restored-clause-suffix");
    let exported = export(&program.program, &program.sources).expect("bounded fixture exports");
    assert_eq!(exported.matches("originalId :=").count(), 55);
}

#[test]
fn export_is_stable_across_independent_compilation() {
    let first = effect_program("restored-clause-suffix");
    let second = effect_program("restored-clause-suffix");
    assert_eq!(
        export(&first.program, &first.sources),
        export(&second.program, &second.sources)
    );
}

#[test]
#[ignore = "explicit fixture regeneration writes the checked-in Lean golden"]
fn regenerate_exported_fixture() {
    let fixture = effect_program("restored-clause-suffix");
    let generated = export(&fixture.program, &fixture.sources).expect("fixture exports");
    std::fs::write(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/direct-effects/one-shot/CoreExportedFixture.lean"),
        generated,
    )
    .expect("write golden");
}

#[test]
fn export_matches_checked_in_lean_fixture() {
    let fixture = effect_program("restored-clause-suffix");
    let generated = export(&fixture.program, &fixture.sources).expect("fixture exports");
    let golden = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/direct-effects/one-shot/CoreExportedFixture.lean"),
    )
    .expect("read golden");
    assert_eq!(
        generated, golden,
        "regenerate with cargo test --lib core::alignment_export::regenerate_exported_fixture -- --ignored"
    );
}

#[test]
fn rejects_open_rows_and_unsupported_patterns_without_narrowing() {
    let fixture = effect_program("restored-clause-suffix");
    let node = fixture.program.node(fixture.program.root()).expect("root");
    let mut exporter = Exporter::default();
    let row = EffectRow::open(
        crate::types::EffectRowVariable::rigid(TypeVariableId::generated(999)),
        Box::new([]),
    );
    assert_eq!(exporter.row(&row), Err("open effect row".into()));
    let pattern = CorePattern::new(Type::Unit, node.origin.clone(), CorePatternKind::Wildcard);
    for (source, _, _) in &fixture.sources {
        let slot = exporter.sources.len();
        exporter.sources.insert(*source, (slot, slot));
    }
    assert_eq!(
        exporter.pattern(&pattern),
        Err("unsupported pattern".into())
    );
    assert_eq!(
        exporter.ty(&Type::Variable(TypeVariableId::generated(999))),
        Err("unsupported type".into())
    );
}

#[test]
fn reference_requires_sealed_handle_identity_and_owned_resource_argument() {
    let fixture = effect_program("restored-clause-suffix");
    let mut pending = vec![fixture.program.root()];
    let resource = loop {
        let id = pending.pop().expect("fixture contains cell");
        let node = fixture.program.node(id).expect("node");
        if let EffectExprKind::Operation(EffectOperation::Resource(resource)) = &node.kind {
            break resource;
        }
        pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
    };
    let mut exporter = Exporter::default();
    assert_eq!(
        exporter.ty(resource.handle.ty()),
        Err("unsealed or unsupported resource handle".into())
    );
    exporter.resource_id(resource.acquisition.identity);
    assert!(exporter.ty(resource.handle.ty()).is_ok());
    let fake = Type::Application(
        Box::new(Type::Nominal(crate::types::NominalTypeId::new(
            resource.acquisition.builtin,
            1,
        ))),
        Box::new(Type::Variable(resource.acquisition.identity)),
    );
    assert_eq!(
        exporter.ty(&fake),
        Err("unsealed or unsupported resource handle".into())
    );
}

#[test]
fn rejects_registration_and_generated_root_handlers() {
    let fixture = effect_program("restored-clause-suffix");
    let program = &fixture.program;
    let mut pending = vec![program.root()];
    let handler = loop {
        let id = pending.pop().expect("fixture contains handler");
        let node = program.node(id).expect("node");
        if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &node.kind {
            break handler;
        }
        pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
    };
    let span = program
        .node(program.root())
        .expect("root")
        .origin
        .primary_span();
    let mut exporter = Exporter::default();
    let registration = EffectExprKind::Operation(EffectOperation::Registration(
        super::effect::RegistrationScopeNode {
            handler: handler.id(),
            callback: BinderId::generated(900),
            body: handler.body(),
            span,
        },
    ));
    assert_eq!(
        exporter.kind(program, &registration),
        Err("hook registration".into())
    );
    let root = crate::resolved::HookRootContract {
        target: handler.effect().clone(),
        span,
        target_span: span,
        operation: handler.clauses()[0].operation(),
        input: BinderId::generated(900),
        resume: handler.clauses()[0].resume(),
    };
    let generated = EffectExprKind::Operation(EffectOperation::Handler(
        handler.clone().with_hook_root(Some(root)),
    ));
    assert_eq!(
        exporter.kind(program, &generated),
        Err("generated hook handler".into())
    );
}

#[test]
fn renders_actual_node_count_for_a_second_supported_fixture() {
    let fixture = effect_program("surviving-handler");
    let generated = export(&fixture.program, &fixture.sources).expect("small fixture exports");
    let count = generated.matches("originalId :=").count();
    assert_ne!(count, 55, "second fixture must exercise a different size");
    assert!(generated.contains(&format!("example : graph.nodes.length = {count} := rfl")));
}
