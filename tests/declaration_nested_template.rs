use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-nested-template-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => {
                    for (name, text) in [
                        (
                            "outer_forms.ash",
                            include_str!("../docs/design/macros/fixtures/nested/outer_forms.ash"),
                        ),
                        (
                            "inner_forms.ash",
                            include_str!("../docs/design/macros/fixtures/nested/inner_forms.ash"),
                        ),
                        (
                            "entry.ash",
                            "import outer_forms (syntax outer)\n\nmain : Unit -> Int\nmain () = 42\n",
                        ),
                    ] {
                        fs::write(path.join(name), text).unwrap();
                    }
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("nested template fixture: {error}"),
            }
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn unused_fixed_i20_nested_template_is_admitted_without_expansion() {
    let fixture = Fixture::new();
    let program = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("the exact unused I20 nested template is admitted");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}
