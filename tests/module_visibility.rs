use std::{
    collections::HashMap,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, run_path},
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::ExportSummary,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempModule(PathBuf);

impl TempModule {
    fn create(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-module-visibility-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self
            .0
            .parent()
            .expect("the module fixture should have a parent")
            .join(relative);
        fs::write(path, text).expect("dependency fixture should be writable");
    }
}

impl Drop for TempModule {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn resolve_local(text: &str) {
    let fixture = TempModule::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the local module fixture should load");
    let mut summaries = HashMap::<_, ExportSummary>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(edge, summaries.get(&edge.target()).unwrap())
                    .expect("each dependency summary should authenticate its actual edge")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("the local module should resolve");
        if module.id() == graph.entry() {
            return;
        }
        summaries.insert(
            module.id(),
            check_module(resolved)
                .expect("the canonical dependency should check")
                .into_exports(),
        );
    }
    panic!("the local entry should remain admitted");
}

#[test]
fn private_types_and_constructors_remain_available_inside_their_module() {
    resolve_local(concat!(
        "type Hidden = Hidden(Int)\n",
        "main : Unit -> Hidden\n",
        "main () = Hidden(1)\n",
    ));
}

#[test]
fn opaque_constructors_remain_available_inside_their_defining_module() {
    resolve_local(concat!(
        "pub opaque type Token = Seal(Int)\n",
        "main : Token -> Token\n",
        "main Seal(value) = Seal(value)\n",
    ));
}

#[test]
fn public_generic_impl_composes_over_an_unnameable_hidden_carrier() {
    let fixture = TempModule::create(concat!(
        "import carrier as Carrier\n",
        "import carrier (impl Read)\n\n",
        "main : Unit -> Int\n",
        "main () = Carrier.read(Carrier.make(42))\n",
    ));
    fixture.write(
        "carrier.ash",
        concat!(
            "type Hidden = Hidden(Int)\n\n",
            "type Wrap<A> = Wrap(A)\n\n",
            "pub interface Read<A> {\nread : A -> Int\n}\n\n",
            "pub impl Read<Hidden> {\n",
            "read (Hidden value) = value\n",
            "}\n\n",
            "pub impl Read<Wrap<A>> where Read<A> {\n",
            "read (Wrap(value)) = read value\n",
            "}\n\n",
            "pub make : Int -> Wrap<Hidden>\n",
            "make value = Wrap(Hidden(value))\n",
        ),
    );

    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("hidden generic implementation facts should remain usable without exported names");
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn public_generic_impl_uses_an_opaque_constructor_only_in_its_defining_module() {
    let fixture = TempModule::create(concat!(
        "import token as Token\n",
        "import token (impl Read)\n\n",
        "main : Unit -> Int\n",
        "main () = Token.read(Token.make(42))\n",
    ));
    fixture.write(
        "token.ash",
        concat!(
            "pub opaque type Token<A> = Token(A)\n\n",
            "pub interface Read<A> {\nread : A -> Int\n}\n\n",
            "pub impl Read<Int> {\nread value = value\n}\n\n",
            "pub impl Read<Token<A>> where Read<A> {\n",
            "read (Token(value)) = read value\n",
            "}\n\n",
            "pub make : Int -> Token<Int>\n",
            "make value = Token(value)\n",
        ),
    );

    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect(
        "opaque generic implementation bodies should retain defining-module constructor access",
    );
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}
