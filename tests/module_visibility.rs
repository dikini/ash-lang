use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
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
    let module = graph
        .module(graph.entry())
        .expect("the entry module should remain admitted");
    let dependencies: &[DependencyExports<'_>] = &[];
    resolve_module(module, dependencies).expect("the local module should resolve");
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
