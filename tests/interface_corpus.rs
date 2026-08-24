//! End-to-end observations for the accepted interface-evidence increment.

use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-interface-corpus-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("corpus fixture directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("corpus fixture parent should be creatable");
        }
        fs::write(&path, text).expect("corpus fixture should be writable");
        path
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn observe(entry: &Path, value: &str, ty: Type) {
    let observation = run_path(RunConfiguration {
        entry: entry.to_path_buf(),
        roots: ModuleRoots::empty(),
    })
    .expect("the interface corpus program should run");

    assert_eq!(observation.value_display(), value);
    assert_eq!(observation.type_display(), ty.to_string());
    assert_eq!(observation.ty, ty);
}

#[test]
fn local_equal_int_observes_true() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = equal(1, 1)\n",
        ),
    );

    observe(&entry, "true", Type::Bool);
}

#[test]
fn cross_module_constrained_equal_observes_true() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import equality as Equality\n\n",
            "main : Unit -> Bool\n",
            "main () = Equality.same((1, 1))\n",
        ),
    );
    tree.write(
        "equality.ash",
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "pub same : (A, A) -> Bool where Equal<A>\n",
            "same pair = equal pair\n",
        ),
    );

    observe(&entry, "true", Type::Bool);
}

#[test]
fn complete_and_targeted_imports_observe_the_same_evidence() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import equality as Complete\n",
            "import equality (equal)\n\n",
            "main : Unit -> (Bool, Bool)\n",
            "main () = (Complete.equal(1, 1), equal(1, 1))\n",
        ),
    );
    tree.write(
        "equality.ash",
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n",
        ),
    );

    observe(
        &entry,
        "(true, true)",
        Type::Tuple(vec![Type::Bool, Type::Bool].into_boxed_slice()),
    );
}

#[test]
fn one_method_occurrence_does_not_retain_unused_same_typed_evidence() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Select<A> {\n",
            "first : A -> A\n",
            "second : A -> A\n",
            "}\n\n",
            "impl Select<Int> {\n",
            "first value = value\n\n",
            "second value = 0\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = first 42\n",
        ),
    );

    observe(&entry, "42", Type::Int);
}

#[test]
fn hidden_carrier_composes_to_forty_two() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import carrier as Carrier\n\n",
            "main : Unit -> Int\n",
            "main () = Carrier.read(Carrier.transform(Carrier.make(42)))\n",
        ),
    );
    tree.write(
        "carrier.ash",
        concat!(
            "type Hidden = Hidden(Int)\n\n",
            "pub interface Transform<A> {\n",
            "transform : A -> A\n",
            "}\n\n",
            "pub impl Transform<Hidden> {\n",
            "transform value = value\n",
            "}\n\n",
            "pub make : Int -> Hidden\n",
            "make value = Hidden(value)\n\n",
            "pub read : Hidden -> Int\n",
            "read (Hidden value) = value\n",
        ),
    );

    observe(&entry, "42", Type::Int);
}

#[test]
fn opaque_carrier_uses_public_operations() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import token as Token\n\n",
            "main : Unit -> Bool\n",
            "main () = Token.equal(Token.make(42), Token.make(42))\n",
        ),
    );
    tree.write(
        "token.ash",
        concat!(
            "pub opaque type Token = Token(Int)\n\n",
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "pub impl Equal<Token> {\n",
            "equal (Token(left), Token(right)) = left == right\n",
            "}\n\n",
            "pub make : Int -> Token\n",
            "make value = Token(value)\n",
        ),
    );

    observe(&entry, "true", Type::Bool);
}

#[test]
fn higher_order_abstract_evidence_observes_true() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "same : A -> A -> Bool where Equal<A>\n",
            "same left = fn(right) {\n",
            "equal(left, right)\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = same 1 1\n",
        ),
    );

    observe(&entry, "true", Type::Bool);
}

#[test]
fn equational_and_operational_constraints_agree() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n\n",
            "impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "same_equational : (A, A) -> Bool where Equal<A>\n",
            "same_equational pair = equal pair\n\n",
            "fn same_operational(pair : (A, A)) -> Bool where Equal<A> {\n",
            "equal pair\n",
            "}\n\n",
            "main : Unit -> (Bool, Bool)\n",
            "main () = (same_equational (1, 1), same_operational((1, 1)))\n",
        ),
    );

    observe(
        &entry,
        "(true, true)",
        Type::Tuple(vec![Type::Bool, Type::Bool].into_boxed_slice()),
    );
}
