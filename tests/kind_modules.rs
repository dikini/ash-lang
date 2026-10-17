use std::{
    collections::HashMap,
    fs,
    path::Path,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    interface::{ImplId, InterfaceId},
    module::{LoadedModule, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{BinderId, ExportSummary, ImportedTypeAccess, ResolvedDefinitionKind},
    types::{ConstructorId, Kind, NominalTypeId, Type, TypeVariableId},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-kind-modules-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("kind-module fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).expect("kind-module fixture should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn module_named<'a>(graph: &'a ash::module::ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("the named route module should be loaded")
}

#[test]
fn body_free_summary_supplies_direct_kinds() {
    let tree = ModuleTree::create();
    tree.write(
        "dependency.ash",
        concat!(
            "pub type Option<A> =\nNone\n| Some(A)\n\n",
            "pub type Wrap<F : Type -> Type> = Wrap\n\n",
            "pub interface Consumer<C : (Type -> Type) -> Type> {\n",
            "consume : C<Option> -> Unit\n",
            "}\n\n",
            "pub lift<F : Type -> Type> : F<Int> -> F<Int>\n",
            "lift value = value\n",
            "\n",
            "pub type Holder<F : Type -> Type> = Holder\n\n",
            "pub interface Observe<A> {\n",
            "observe : A -> Bool\n",
            "}\n\n",
            "pub impl<F : Type -> Type> Observe<Holder<F>> {\n",
            "observe value = true\n",
            "}\n",
        ),
    );
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import dependency (Wrap, Consumer, lift, impl Observe)\n",
            "probe : Unit -> Unit where Consumer<Wrap>\n",
            "probe value = value\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the direct kind fixture should load");
    let dependency = graph
        .modules()
        .iter()
        .find(|module| module.id() != graph.entry())
        .expect("the dependency should load before the entry");
    let dependency = check_module(
        resolve_module(dependency, &[]).expect("the defining module should resolve and kind-check"),
    )
    .expect("the defining module should type-check");
    let entry = graph
        .module(graph.entry())
        .expect("the entry module should remain loaded");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency.exports()).unwrap())
        .collect::<Vec<_>>();

    let resolved = resolve_module(entry, &dependencies)
        .expect("direct body-free nominal, interface, and scheme kinds should authenticate");
    assert_eq!(resolved.definitions().len(), 1);
    assert!(resolved.interfaces().is_empty());
    assert!(resolved.registry().nominals().is_empty());
}

#[test]
fn body_free_summary_preserves_defining_kinds() {
    let tree = ModuleTree::create();
    tree.write(
        "dependency.ash",
        concat!(
            "pub type Option<A> =\nNone\n| Some(A)\n\n",
            "pub type Wrap<F : Type -> Type> = Wrap(F<Int>)\n\n",
            "pub interface Consumer<C : (Type -> Type) -> Type> {\n",
            "consume : C<Option> -> Unit\n",
            "}\n\n",
            "pub lift<F : Type -> Type> : F<Int> -> F<Int>\n",
            "lift value = value\n",
            "\n",
            "type Hidden<F : Type -> Type> = Hidden(F<Int>)\n\n",
            "pub interface Observe<A> {\n",
            "observe : A -> Bool\n",
            "}\n\n",
            "pub impl<F : Type -> Type> Observe<Hidden<F>> {\n",
            "observe value = true\n",
            "}\n",
        ),
    );
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import dependency (Wrap, Consumer, lift, impl Observe)\n",
            "probe : Unit -> Unit where Consumer<Wrap>\n",
            "probe value = value\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the detached body-free fixture should load");
    let dependency = graph
        .modules()
        .iter()
        .find(|module| module.id() != graph.entry())
        .expect("the dependency should load before the entry");
    let dependency = check_module(
        resolve_module(dependency, &[]).expect("the defining module should resolve and kind-check"),
    )
    .expect("the defining module should type-check");

    let summary = dependency.into_exports();
    let entry = graph
        .module(graph.entry())
        .expect("the entry module should remain loaded");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, &summary).unwrap())
        .collect::<Vec<_>>();

    let resolved = resolve_module(entry, &dependencies)
        .expect("all defining kinds should authenticate after dependency bodies are discarded");
    assert_eq!(resolved.definitions().len(), 1);
    assert!(resolved.interfaces().is_empty());
    assert!(resolved.registry().nominals().is_empty());
}

#[test]
fn detached_summaries_preserve_defining_kinds_across_every_import_route() {
    #[derive(Clone, Copy)]
    struct DefiningIdentities {
        option: NominalTypeId,
        wrap: NominalTypeId,
        wrap_parameters: [TypeVariableId; 2],
        hidden: NominalTypeId,
        capsule: NominalTypeId,
        first: ConstructorId,
        observe: InterfaceId,
        consumer: InterfaceId,
        lift: BinderId,
        wrap_implementation: ImplId,
        hidden_implementation: ImplId,
        capsule_implementation: ImplId,
    }

    let tree = ModuleTree::create();
    tree.write(
        "base.ash",
        concat!(
            "pub type Option<A> =\nNone\n| Some(A)\n\n",
            "pub type Wrap<F : Type -> Type, A> =\nFirst(F<A>)\n| Second(F<A>)\n\n",
            "type Hidden<F : Type -> Type> = Hidden(F<Int>)\n\n",
            "pub conceal<F : Type -> Type> : F<Int> -> Hidden<F>\n",
            "conceal value = Hidden(value)\n\n",
            "pub expose<F : Type -> Type> : Hidden<F> -> Hidden<F>\n",
            "expose value = value\n\n",
            "pub reveal<F : Type -> Type> : Hidden<F> -> F<Int>\n",
            "reveal (Hidden(value)) = value\n\n",
            "pub opaque type Capsule<F : Type -> Type> = Seal(F<Int>)\n\n",
            "pub seal<F : Type -> Type> : F<Int> -> Capsule<F>\n",
            "seal value = Seal(value)\n\n",
            "pub unseal<F : Type -> Type> : Capsule<F> -> F<Int>\n",
            "unseal (Seal(value)) = value\n\n",
            "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
            "pub interface Consumer<C : (Type -> Type) -> Type -> Type> {\n",
            "consume : C<Option, Int> -> Unit\n}\n\n",
            "pub impl<F : Type -> Type, A> Observe<Wrap<F, A>> {\n",
            "observe value = value\n}\n\n",
            "pub impl<F : Type -> Type> Observe<Hidden<F>> {\n",
            "observe value = value\n}\n\n",
            "pub impl<F : Type -> Type> Observe<Capsule<F>> {\n",
            "observe value = value\n}\n\n",
            "pub lift<F : Type -> Type> : F<Int> -> F<Int>\n",
            "lift value = value\n",
        ),
    );
    let facade = concat!(
        "pub import base (Option, Wrap, First, lift, conceal, expose, reveal, ",
        "Capsule, seal, unseal, Observe, observe, Consumer, consume, impl Observe)\n",
    );
    tree.write("inner.ash", facade);
    tree.write(
        "outer.ash",
        concat!(
            "pub import inner (Option, Wrap, First, lift, conceal, expose, reveal, ",
            "Capsule, seal, unseal, Observe, observe, Consumer, consume, impl Observe)\n",
        ),
    );
    tree.write("left.ash", facade);
    tree.write("right.ash", facade);
    tree.write(
        "qualified.ash",
        concat!(
            "import base as Base\n",
            "qualified<F : Type -> Type> : Base.Wrap<F, Int> -> Base.Wrap<F, Int>\n",
            "qualified value = value\n\n",
            "lifted<F : Type -> Type> : F<Int> -> F<Int>\n",
            "lifted value = Base.lift(value)\n\n",
            "qualifiedRequirement : Unit -> Unit where Base.Consumer<Base.Wrap>\n",
            "qualifiedRequirement value = value\n",
        ),
    );
    tree.write(
        "targeted.ash",
        concat!(
            "import base (Option, Wrap, First, lift, Consumer)\n",
            "targeted<F : Type -> Type> : Wrap<F, Int> -> Wrap<F, Int>\n",
            "targeted value = value\n\n",
            "lifted : Option<Int> -> Option<Int>\n",
            "lifted value = lift(value)\n\n",
            "targetedRequirement : Unit -> Unit where Consumer<Wrap>\n",
            "targetedRequirement value = value\n",
        ),
    );
    tree.write(
        "implementation_only.ash",
        concat!(
            "import base as Base\n",
            "import base (impl Observe)\n\n",
            "interface Observe<A> {\nlocalObserve : A -> A\n}\n\n",
            "observe : Unit -> Unit\nobserve value = value\n\n",
            "selected<F : Type -> Type, A> : Base.Wrap<F, A> -> Base.Wrap<F, A>\n",
            "selected value = Base.observe(value)\n",
        ),
    );
    tree.write(
        "transitive.ash",
        concat!(
            "import outer (Option, Wrap, lift, Consumer, observe, impl Observe)\n",
            "transitive<A> : Wrap<Option, A> -> Wrap<Option, A>\n",
            "transitive value = observe(value)\n\n",
            "transitiveLift : Option<Int> -> Option<Int>\n",
            "transitiveLift value = lift(value)\n\n",
            "transitiveRequirement : Unit -> Unit where Consumer<Wrap>\n",
            "transitiveRequirement value = value\n",
        ),
    );
    tree.write(
        "diamond.ash",
        concat!(
            "import left (Option as LeftOption, Wrap as LeftWrap, lift as leftLift, ",
            "Consumer as LeftConsumer, observe as leftObserve, ",
            "impl Observe)\n",
            "import right (Option as RightOption, Wrap as RightWrap, lift as rightLift, ",
            "Consumer as RightConsumer, observe as rightObserve, ",
            "impl Observe)\n",
            "diamond<A> : RightWrap<LeftOption, A> -> LeftWrap<RightOption, A>\n",
            "diamond value = rightObserve(leftObserve(value))\n\n",
            "diamondLift : LeftOption<Int> -> RightOption<Int>\n",
            "diamondLift value = rightLift(leftLift(value))\n\n",
            "diamondRequirement : Unit -> Unit where LeftConsumer<LeftWrap>\n",
            "diamondRequirement value = value\n",
        ),
    );
    tree.write(
        "opaque_route.ash",
        concat!(
            "import base (Capsule, seal, unseal, observe, impl Observe)\n",
            "roundTrip<F : Type -> Type> : F<Int> -> F<Int>\n",
            "roundTrip value = unseal(observe(seal(value)))\n",
        ),
    );
    tree.write(
        "hidden.ash",
        concat!(
            "import base (conceal, expose, reveal, observe, impl Observe)\n",
            "hidden<F : Type -> Type> : F<Int> -> F<Int>\n",
            "hidden value = reveal(observe(expose(conceal(value))))\n",
        ),
    );
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import qualified as Qualified\n",
            "import targeted as Targeted\n",
            "import implementation_only as ImplementationOnly\n",
            "import transitive as Transitive\n",
            "import diamond as Diamond\n",
            "import opaque_route as OpaqueRoute\n",
            "import hidden as Hidden\n",
            "main : Unit -> Unit\nmain value = value\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the detached route matrix should load");
    let base_id = module_named(&graph, "base.ash").id();
    let mut summaries = HashMap::<_, ExportSummary>::new();
    let mut defining = None;

    for module in graph.modules() {
        let resolved = {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let summary = summaries
                        .get(&edge.target())
                        .expect("every dependency body must already be discarded");
                    DependencyExports::new(edge, summary)
                        .expect("each detached summary must match its direct edge")
                })
                .collect::<Vec<_>>();
            resolve_module(module, &dependencies)
                .expect("every detached route consumer should resolve and authenticate Kinds")
        };

        let file_name = Path::new(module.source().display_path())
            .file_name()
            .and_then(|name| name.to_str())
            .expect("each route fixture should have a UTF-8 file name");
        if module.id() == base_id {
            let nominal = |spelling| {
                resolved
                    .registry()
                    .nominals()
                    .iter()
                    .find(|nominal| nominal.spelling == spelling)
                    .expect("the defining nominal should exist")
                    .id
            };
            let wrap = nominal("Wrap");
            let wrap_parameters = resolved.registry().nominal_parameters(wrap).unwrap();
            let identities = DefiningIdentities {
                option: nominal("Option"),
                wrap,
                wrap_parameters: [wrap_parameters[0].id, wrap_parameters[1].id],
                hidden: nominal("Hidden"),
                capsule: nominal("Capsule"),
                first: resolved
                    .registry()
                    .constructors()
                    .iter()
                    .find(|constructor| constructor.spelling == "First")
                    .expect("First should retain its defining identity")
                    .id,
                observe: resolved
                    .interfaces()
                    .iter()
                    .find(|interface| interface.spelling == "Observe")
                    .expect("Observe should retain its defining identity")
                    .id,
                consumer: resolved
                    .interfaces()
                    .iter()
                    .find(|interface| interface.spelling == "Consumer")
                    .expect("Consumer should retain its defining identity")
                    .id,
                lift: resolved
                    .definitions()
                    .iter()
                    .find_map(|definition| match &definition.kind {
                        ResolvedDefinitionKind::Equational(global)
                        | ResolvedDefinitionKind::ForeignConstant(global)
                            if global.interface.name.spelling == "lift" =>
                        {
                            Some(global.interface.name.id)
                        }
                        ResolvedDefinitionKind::Equational(_)
                        | ResolvedDefinitionKind::ForeignConstant(_)
                        | ResolvedDefinitionKind::InlineOperational(_) => None,
                    })
                    .expect("lift should retain its defining binder identity"),
                wrap_implementation: resolved.implementations()[0].id,
                hidden_implementation: resolved.implementations()[1].id,
                capsule_implementation: resolved.implementations()[2].id,
            };
            assert_eq!(
                resolved.registry().nominal_parameters(wrap).unwrap()[0].kind,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            );
            defining = Some(identities);
        } else if matches!(
            file_name,
            "qualified.ash"
                | "targeted.ash"
                | "implementation_only.ash"
                | "transitive.ash"
                | "diamond.ash"
                | "opaque_route.ash"
                | "hidden.ash"
        ) {
            let identities = defining.expect("the defining IDs must precede every consumer");
            let imported = resolved.imported_facts();
            let expects_wrap = matches!(
                file_name,
                "qualified.ash"
                    | "targeted.ash"
                    | "implementation_only.ash"
                    | "transitive.ash"
                    | "diamond.ash"
            );
            if expects_wrap {
                let wrap = imported
                    .nominal(identities.wrap)
                    .expect("the route must retain the defining Wrap identity");
                assert_eq!(
                    wrap.parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
                let consumer = imported
                    .interface(identities.consumer)
                    .expect("the route must retain Consumer's defining identity");
                let [consumer_parameter] = consumer.parameters.as_ref() else {
                    panic!("the unary Consumer interface should retain one parameter");
                };
                assert_eq!(
                    consumer_parameter.kind,
                    Kind::Arrow(
                        Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                        Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)))
                    )
                );
                let lift = imported
                    .global(identities.lift)
                    .expect("the route must retain lift's defining identity");
                assert_eq!(
                    lift.scheme.type_parameters[0].1,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
            }
            if matches!(file_name, "targeted.ash") {
                assert!(imported.nominal(identities.option).is_some());
                let first = imported
                    .constructor(identities.first)
                    .expect("the targeted route must retain First's physical scheme");
                assert_eq!(
                    first.scheme.type_parameters.as_ref(),
                    [
                        (
                            identities.wrap_parameters[0],
                            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                        ),
                        (identities.wrap_parameters[1], Kind::Type),
                    ]
                );
                assert!(first.scheme.requirements.is_empty());
                assert_eq!(
                    first.scheme.value_type(),
                    &Type::Function(
                        Box::new(Type::Application(
                            Box::new(Type::Variable(identities.wrap_parameters[0])),
                            Box::new(Type::Variable(identities.wrap_parameters[1])),
                        )),
                        Box::new(Type::Application(
                            Box::new(Type::Application(
                                Box::new(Type::Nominal(identities.wrap)),
                                Box::new(Type::Variable(identities.wrap_parameters[0])),
                            )),
                            Box::new(Type::Variable(identities.wrap_parameters[1])),
                        )),
                    )
                );
            }
            if matches!(
                file_name,
                "implementation_only.ash" | "transitive.ash" | "diamond.ash"
            ) {
                assert!(imported.interface(identities.observe).is_some());
                let implementation = imported
                    .implementation(identities.wrap_implementation)
                    .expect("the route must retain the defining Wrap implementation");
                assert_eq!(
                    implementation.head_parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
            }
            if file_name == "opaque_route.ash" {
                let opaque = imported
                    .nominal(identities.capsule)
                    .expect("the opaque route must retain Capsule's defining identity");
                assert_eq!(opaque.access, ImportedTypeAccess::Opaque);
                assert_eq!(
                    opaque.parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
                assert!(opaque.constructors.is_empty());
                let implementation = imported
                    .implementation(identities.capsule_implementation)
                    .expect("the opaque route must retain its implementation evidence");
                assert_eq!(
                    implementation.head_parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
            }
            if file_name == "hidden.ash" {
                let hidden = imported
                    .nominal(identities.hidden)
                    .expect("public schemes must retain the private Hidden identity");
                assert_eq!(hidden.access, ImportedTypeAccess::Hidden);
                assert_eq!(
                    hidden.parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
                assert!(hidden.constructors.is_empty());
                let implementation = imported
                    .implementation(identities.hidden_implementation)
                    .expect("the hidden route must retain its implementation evidence");
                assert_eq!(
                    implementation.head_parameters[0].kind,
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
                );
            }
        }

        let summary = check_module(resolved)
            .expect("every route consumer should type-check from detached facts")
            .into_exports();
        assert!(summaries.insert(module.id(), summary).is_none());
    }
}
