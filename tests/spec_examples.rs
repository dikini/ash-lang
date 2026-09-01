use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, validate_modules},
    driver::{FileFailure, PipelineFailure, RunConfiguration, SyntaxFailure, run_path},
    elaborate::{Elaborator, TypeError, TypeReason, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    interface::InterfaceReason,
    kind::{KindExpectation, KindFailure, KindReason},
    lexer::LexReason,
    module::{LoadGraphError, ModuleRoots, load_module_graph},
    resolve::{ResolveReason, resolve_module},
    resolved::ResolvedDefinitionKind,
    types::{Kind, Type},
};

const V001: &str = include_str!("fixtures/first-stratum/valid/v001-precedence.ash");
const V002_EQUATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-equational.ash");
const V002_OPERATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-operational.ash");
const V003: &str = include_str!("fixtures/first-stratum/valid/v003-local-shadowing.ash");
const V004: &str = include_str!("fixtures/first-stratum/valid/v004-capture.ash");
const V008: &str = include_str!("fixtures/first-stratum/valid/v008-mixed.ash");
const RECURSIVE_GLOBAL: &str = include_str!("fixtures/recursion/valid/global-mutual.ash");
const RECURSIVE_LOCAL: &str = include_str!("fixtures/recursion/valid/local-mutual.ash");
const UNSAFE_RECURSIVE_INITIALIZER: &str =
    include_str!("fixtures/recursion/type/unsafe-initializer.ash");

const CURRIED_EQUATIONAL_MODULE: &str = "add : Int -> Int -> Int\nadd left = fn(right) {\n    left + right\n}\n\nmain : Unit -> Int\nmain () = add 20 22\n";
const CONTEXTUAL_BLOCK_MODULE: &str = "main : Unit -> Int\nmain () = {\n    let constant : Unit -> Int = {\n        fn(ignored) {\n            1\n        }\n    }\n    constant ()\n}\n";
const HIGHER_ORDER_OPERATIONAL_MODULE: &str = "fn add(left : Int) -> Int -> Int {\n    fn(right) {\n        left + right\n    }\n}\n\nmain : Unit -> Int\nmain () = add 20 22\n";
const FUNCTION_RESULT_MODULE: &str = "identity : Int -> Int\nidentity value = value\n\nmain : Unit -> (Int -> Int)\nmain () = identity\n";
const COMMENT_REJECTION_MODULE: &str =
    "// comments are not in Ash\nmain : Unit -> Int\nmain () = 1\n";
const UNKNOWN_NAME_REJECTION_MODULE: &str = "main : Unit -> Int\nmain () = missing 1\n";
const TYPE_REJECTION_MODULE: &str = "main : Unit -> Int\nmain () = true + 1\n";
const IRREFUTABLE_TUPLE_MODULE: &str =
    "main : Unit -> Int\nmain () = {\n    let (left, right) = (20, 22)\n    left + right\n}\n";
const OPERATIONAL_TUPLE_PATTERN_MODULE: &str = "fn add((left, right) : (Int, Int)) -> Int {\n    left + right\n}\n\nmain : Unit -> Int\nmain () = add(20, 22)\n";
const CONTEXTUAL_MATCH_MODULE: &str = "fn choose(flag : Bool) -> Int -> Int {\n    match flag {\n        true => fn(value) {\n            value + 1\n        }\n        false => fn(value) {\n            value * 2\n        }\n    }\n}\n\nmain : Unit -> Int\nmain () = choose true 41\n";
const TREE_PRESENTATIONS_MODULE: &str = "type Tree =\n    Tip(Int)\n    | Fork(Tree, Tree)\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nfn size_match(tree : Tree) -> Int {\n    match tree {\n        Tip(value) => 1\n        Fork(left, right) => size_match left + size_match right\n    }\n}\n\nmain : Unit -> Int\nmain () = size (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))\n";
const HIGHER_ORDER_CONSTRUCTOR_MODULE: &str = "type Wrapped =\n    Wrap(Int)\n\nfn build(make : Int -> Wrapped) -> Wrapped {\n    make 42\n}\n\nmain : Unit -> Int\nmain () = match build Wrap {\n    Wrap(value) => value\n}\n";
const CYCLIC_STREAM_MODULE: &str = "type Stream =\n    Next(Int, Stream)\n\nmain : Unit -> Stream\nmain () = {\n    let rec ones : Stream = Next(1, ones)\n    ones\n}\n";
const RANK_ONE_POLYMORPHISM_MODULE: &str = "type Option<A> =\n    None\n    | Some(A)\n\nid : A -> A\nid value = value\n\nmain : Unit -> (Option<Int>, Bool)\nmain () = {\n    let local = fn(value) {\n        value\n    }\n    (id(Some(42)), local(false))\n}\n";
const MODULE_NEWTYPE_MODULE: &str = concat!(
    "newtype UserId = UserId(Int)\n\n",
    "increment : UserId -> UserId\n",
    "increment (UserId value) = UserId(value + 1)\n\n",
    "main : Unit -> UserId\n",
    "main () = increment(UserId(41))\n",
);

const MAIN_MODULE: &str = "main : Unit -> Int\nmain () = 42\n";
const SIBLING_ENTRY_MODULE: &str =
    "import arithmetic as Arithmetic\n\nmain : Unit -> Int\nmain () = Arithmetic.answer(())\n";
const SIBLING_ARITHMETIC_MODULE: &str = "pub answer : Unit -> Int\nanswer () = 42\n";
const NAMED_ROOT_ENTRY_MODULE: &str =
    "import @std.answer as Answer\n\nmain : Unit -> Int\nmain () = Answer.value(())\n";
const NAMED_ROOT_ANSWER_MODULE: &str = "pub value : Unit -> Int\nvalue () = 42\n";
const TARGETED_ENTRY_MODULE: &str = "import arithmetic (answer as imported_answer)\n\nmain : Unit -> Int\nmain () = imported_answer(())\n";
const OPAQUE_ENTRY_MODULE: &str = "import token as Token\n\nmain : Unit -> Int\nmain () = {\n    let token : Token.Token = Token.make(41)\n    Token.read(Token.step(token))\n}\n";
const OPAQUE_TOKEN_MODULE: &str = "pub opaque type Token = Token(Int)\n\npub make : Int -> Token\nmake value = Token(value)\n\npub step : Token -> Token\nstep (Token value) = Token(value + 1)\n\npub read : Token -> Int\nread (Token value) = value\n";
const HIDDEN_ENTRY_MODULE: &str = "import carrier as Carrier\n\nmain : Unit -> Int\nmain () = {\n    let hidden = Carrier.make(41)\n    Carrier.read(Carrier.step(hidden))\n}\n";
const HIDDEN_CARRIER_MODULE: &str = "type Hidden = Hidden(Int)\n\npub make : Int -> Hidden\nmake value = Hidden(value)\n\npub step : Hidden -> Hidden\nstep (Hidden value) = Hidden(value + 1)\n\npub read : Hidden -> Int\nread (Hidden value) = value\n";
const TRANSPARENT_ENTRY_MODULE: &str = "import choice as Choice\n\nmain : Unit -> Int\nmain () = match Choice.sample(()) {\n    Choice.First(value) => value\n    Choice.Second(value) => value + 1\n}\n";
const TRANSPARENT_CHOICE_MODULE: &str = "pub type Choice =\n    First(Int)\n    | Second(Int)\n\npub sample : Unit -> Choice\nsample () = First(42)\n";
const LOCAL_INTERFACE_EVIDENCE_MODULE: &str = concat!(
    "interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "impl Equal<Int> {\n",
    "    equal (left, right) = left == right\n",
    "}\n\n",
    "main : Unit -> Bool\n",
    "main () = equal(1, 1)\n",
);
const CONSTRAINED_IMPORT_ENTRY_MODULE: &str = concat!(
    "import equality as Equality\n",
    "import equality (impl Equal)\n\n",
    "main : Unit -> Bool\n",
    "main () = Equality.same((1, 1))\n",
);
const CONSTRAINED_IMPORT_LIBRARY_MODULE: &str = concat!(
    "pub interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "pub impl Equal<Int> {\n",
    "    equal (left, right) = left == right\n",
    "}\n\n",
    "pub same : (A, A) -> Bool where Equal<A>\n",
    "same pair = equal pair\n",
);
const NAME_ONLY_IMPORT_ENTRY_MODULE: &str = concat!(
    "import equality (Equal, equal)\n\n",
    "main : Unit -> Bool\n",
    "main () = equal(1, 1)\n",
);
const EQUALITY_IMPLEMENTATION_MODULE: &str = concat!(
    "pub interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "pub impl Equal<Int> {\n",
    "    equal (left, right) = left == right\n",
    "}\n",
);
const PUBLIC_NAME_REEXPORT_ENTRY_MODULE: &str = concat!(
    "import facade (facade_answer)\n\n",
    "main : Unit -> Int\n",
    "main () = facade_answer(())\n",
);
const PUBLIC_NAME_REEXPORT_FACADE_MODULE: &str =
    "pub import arithmetic (answer as facade_answer)\n";
const IMPLEMENTATION_FACADE_ENTRY_MODULE: &str = concat!(
    "import facade (Equal, equal, impl Equal)\n\n",
    "main : Unit -> Bool\n",
    "main () = equal(1, 1)\n",
);
const IMPLEMENTATION_FACADE_MODULE: &str = "pub import equality (Equal, equal, impl Equal)\n";
const GENERIC_PREREQUISITE_EVIDENCE_MODULE: &str = concat!(
    "type Option<A> =\n",
    "    None\n",
    "    | Some(A)\n\n",
    "interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "impl Equal<Int> {\n",
    "    equal (left, right) = left == right\n",
    "}\n\n",
    "impl Equal<Option<A>> where Equal<A> {\n",
    "    equal (None, None) = true\n",
    "    equal (Some(left), Some(right)) = equal(left, right)\n",
    "    equal _ = false\n",
    "}\n\n",
    "main : Unit -> Bool\n",
    "main () = equal(Some(1), Some(1))\n",
);
const DETERMINED_GENERIC_PREREQUISITE_MODULE: &str = concat!(
    "type Option<A> =\n",
    "    None\n",
    "    | Some(A)\n\n",
    "interface Measure<Key, Result> where Key -> Result {\n",
    "    measure : Key -> Int\n",
    "}\n\n",
    "impl Measure<Int, Int> {\n",
    "    measure value = value\n",
    "}\n\n",
    "impl<A> Measure<Option<A>, Option<A>> where Measure<A, A> {\n",
    "    measure value = 42\n",
    "}\n\n",
    "main : Unit -> Int\n",
    "main () = measure(Some(1))\n",
);
const INTERFACE_HIDDEN_ENTRY_MODULE: &str = concat!(
    "import carrier as Carrier\n",
    "import carrier (impl Transform)\n\n",
    "main : Unit -> Int\n",
    "main () = Carrier.read(Carrier.transform(Carrier.make(42)))\n",
);
const INTERFACE_HIDDEN_CARRIER_MODULE: &str = concat!(
    "type Hidden = Hidden(Int)\n\n",
    "pub interface Transform<A> {\n",
    "    transform : A -> A\n",
    "}\n\n",
    "pub impl Transform<Hidden> {\n",
    "    transform value = value\n",
    "}\n\n",
    "pub make : Int -> Hidden\n",
    "make value = Hidden(value)\n\n",
    "pub read : Hidden -> Int\n",
    "read (Hidden value) = value\n",
);
const INTERFACE_OPAQUE_ENTRY_MODULE: &str = concat!(
    "import token as Token\n",
    "import token (impl Equal)\n\n",
    "main : Unit -> Bool\n",
    "main () = Token.equal(Token.make(42), Token.make(42))\n",
);
const INTERFACE_OPAQUE_TOKEN_MODULE: &str = concat!(
    "pub opaque type Token = Token(Int)\n\n",
    "pub interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "pub impl Equal<Token> {\n",
    "    equal (Token(left), Token(right)) = left == right\n",
    "}\n\n",
    "pub make : Int -> Token\n",
    "make value = Token(value)\n",
);
const CONSTRAINED_PRESENTATIONS_MODULE: &str = concat!(
    "interface Equal<A> {\n",
    "    equal : (A, A) -> Bool\n",
    "}\n\n",
    "impl Equal<Int> {\n",
    "    equal (left, right) = left == right\n",
    "}\n\n",
    "same_equational : (A, A) -> Bool where Equal<A>\n",
    "same_equational pair = equal pair\n\n",
    "fn same_operational(pair : (A, A)) -> Bool where Equal<A> {\n",
    "    equal pair\n",
    "}\n\n",
    "main : Unit -> (Bool, Bool)\n",
    "main () = (same_equational (1, 1), same_operational (1, 1))\n",
);
const CONTEXTUAL_TYPE_NOMINAL_MODULE: &str =
    include_str!("fixtures/explicit-kinds/ordinary-type-nominal.ash");
const LINKED_HIGHER_KINDED_ENTRY_MODULE: &str =
    include_str!("fixtures/explicit-kinds/linked-product/entry.ash");
const LINKED_HIGHER_KINDED_DEPENDENCY_MODULE: &str =
    include_str!("fixtures/explicit-kinds/linked-product/dependency.ash");
const METHOD_PARAMETER_INTERFACE_MODULE: &str =
    include_str!("fixtures/method-parameters/linked-product/interface.ash");
const METHOD_PARAMETER_IMPLEMENTATION_MODULE: &str =
    include_str!("fixtures/method-parameters/linked-product/implementation.ash");
const METHOD_PARAMETER_ENTRY_MODULE: &str =
    include_str!("fixtures/method-parameters/linked-product/entry.ash");
const METHOD_PARAMETER_MIGRATION_REJECTED_MODULE: &str = concat!(
    "interface Project<I> {\n",
    "project : (I, A) -> A\n",
    "}\n\n",
    "impl Project<Int> {\n",
    "project (owner, value) = value\n",
    "}\n\n",
    "main : Unit -> Int\n",
    "main () = project((0, 42))\n",
);
const METHOD_PARAMETER_MIGRATION_ACCEPTED_MODULE: &str = concat!(
    "interface Project<I> {\n",
    "project<A> : (I, A) -> A\n",
    "}\n\n",
    "impl Project<Int> {\n",
    "project (owner, value) = value\n",
    "}\n\n",
    "main : Unit -> Int\n",
    "main () = project((0, 42))\n",
);
const RELATIONAL_INTERFACE_MODULE: &str = concat!(
    "interface Measure<Key, Result> where Key -> Result {\n",
    "    measure : Key -> Int\n",
    "}\n\n",
    "impl Measure<Bool, Unit> {\n",
    "    measure value = 42\n",
    "}\n\n",
    "main : Unit -> Int\n",
    "main () = measure(true)\n",
);
const BINDER_POLICY_MODULE: &str = concat!(
    "type Phantom<Unused, A> = Phantom(A)\n",
    "type Pair<Left, Right> = Pair(Left, Right)\n\n",
    "interface Witness<Value> {\n",
    "    witness : Value -> Bool\n",
    "}\n\n",
    "ordered<B, A> : A -> B -> A\n",
    "ordered left right = left\n\n",
    "fn operational<D, C>(left : C, right : D) -> C {\n",
    "    left\n",
    "}\n\n",
    "legacy : Y -> X -> Y\n",
    "legacy left right = left\n\n",
    "impl<F, E> Witness<Pair<E, F>> {\n",
    "    witness value = true\n",
    "}\n\n",
    "impl Witness<(S, R)> {\n",
    "    witness value = true\n",
    "}\n\n",
    "main : Unit -> Int\n",
    "main () = 42\n",
);
const INTERLEAVED_BINDER_REGISTRY_MODULE: &str = concat!(
    "type Pair<Left, Right> = Pair(Left, Right)\n\n",
    "interface Witness<Value> {\n",
    "    witness : Value -> Bool\n",
    "}\n\n",
    "impl<F, E> Witness<Pair<E, F>> {\n",
    "    witness value = true\n",
    "}\n\n",
    "legacy : Y -> X -> Y\n",
    "legacy left right = left\n\n",
    "main : Unit -> Int\n",
    "main () = 42\n",
);
const HIGHER_KINDED_INTERFACE_MODULE: &str = concat!(
    "type Option<A> =\n",
    "    None\n",
    "    | Some(A)\n\n",
    "interface Transform<F : Type -> Type> {\n",
    "    transform : (Int -> Int, F<Int>) -> F<Int>\n",
    "}\n\n",
    "impl Transform<Option> {\n",
    "    transform (function, None) = None\n",
    "    transform (function, Some(value)) = Some(function(value))\n",
    "}\n\n",
    "increment : Int -> Int\n",
    "increment value = value + 1\n\n",
    "apply_transform<F : Type -> Type> : (Int -> Int, F<Int>) -> F<Int> where Transform<F>\n",
    "apply_transform pair = transform pair\n\n",
    "fn relay<F : Type -> Type, A>(value : F<A>) -> F<A> {\n",
    "    value\n",
    "}\n\n",
    "main : Unit -> (Option<Int>, Bool, Unit)\n",
    "main () = (relay(apply_transform((increment, Some(41)))), true, ())\n",
);
const EXPECTED_TYPE_KIND_REJECTION_MODULE: &str = concat!(
    "type Option<A> =\n",
    "    None\n",
    "    | Some(A)\n\n",
    "bad : Unit -> Option\n",
    "bad () = None\n\n",
    "main : Unit -> Unit\n",
    "main () = ()\n",
);
const NO_KIND_INFERENCE_REJECTION_MODULE: &str = concat!(
    "legacy : F<Int> -> Unit\n",
    "legacy value = ()\n\n",
    "main : Unit -> Unit\n",
    "main () = ()\n",
);
const INTERFACE_KIND_ARGUMENT_REJECTION_MODULE: &str = concat!(
    "interface Higher<F : Type -> Type> {\n",
    "    higher : F<Int> -> Unit\n",
    "}\n\n",
    "bad : Unit -> Unit where Higher<Int>\n",
    "bad value = value\n\n",
    "main : Unit -> Unit\n",
    "main () = ()\n",
);
const CORE_KIND_MODULE: &str = concat!(
    "type Option<A> =\n",
    "    None\n",
    "    | Some(A)\n\n",
    "keep<F : Type -> Type, A> : F<A> -> F<A>\n",
    "keep value = value\n\n",
    "main : Unit -> Option<Int>\n",
    "main () = keep(Some(42))\n",
);

const PHASE_DEPENDENT_NO_KIND_INFERENCE: &str = "Every omitted declaration kind annotation, and every binder introduced by an omitted global or implementation binder list, is fixed to `Type`. Ash does not infer a kind for those binders. This is the current phase-dependent language constraint, not a commitment against a later bounded declaration-local inference rule.";

const EXPLICIT_KIND_RULE_FRAGMENTS: &[(&str, &str)] = &[
    (
        "spec/lexical-structure.md",
        "Angle brackets delimit parameter lists on nominal, global, and\nimplementation declarations, method parameter lists",
    ),
    (
        "spec/syntax.md",
        "type_parameter ::= upper_identifier [ \":\" kind ] ;",
    ),
    ("spec/syntax.md", "kind ::= kind_atom [ \"->\" kind ] ;"),
    (
        "spec/syntax.md",
        "interface_parameters ::= \"<\" type_parameter { \",\" type_parameter } \">\" ;",
    ),
    (
        "spec/syntax.md",
        "global_signature ::= identifier [ type_parameters ]",
    ),
    ("spec/syntax.md", "\"impl\" [ type_parameters ]"),
    ("spec/static-semantics.md", "family kind-synthesis:"),
    ("spec/static-semantics.md", "K-Primitive :="),
    ("spec/static-semantics.md", "K-Variable :="),
    ("spec/static-semantics.md", "K-Inference :="),
    ("spec/static-semantics.md", "K-Nominal :="),
    ("spec/static-semantics.md", "K-Application :="),
    ("spec/static-semantics.md", "K-Tuple :="),
    ("spec/static-semantics.md", "K-Function :="),
    ("spec/static-semantics.md", "K-Value-Type :="),
    ("spec/static-semantics.md", "K-Interface-Argument :="),
];

const METHOD_PARAMETER_RULE_FRAGMENTS: &[(&str, &str)] = &[
    (
        "spec/syntax.md",
        "interface_method ::= identifier [ type_parameters ] \":\" type ;",
    ),
    (
        "spec/name-resolution.md",
        "An absent method parameter list binds no method-local parameter.",
    ),
    (
        "spec/name-resolution.md",
        "A present method parameter list is an ordered bijection with the method type's\nfree variables other than the interface parameters.",
    ),
    (
        "spec/static-semantics.md",
        "MethodScheme = forall method_parameters. method_value_type",
    ),
    (
        "spec/static-semantics.md",
        "freshen(method_parameters) = method_arguments",
    ),
    (
        "spec/static-semantics.md",
        "method_parameters are rigid while checking the method",
    ),
    (
        "spec/elaboration.md",
        "forall definition_parameters.\n    (forall method_parameters. substituted_method_value_type) ->",
    ),
    (
        "spec/elaboration.md",
        "Core admits a nested scheme only in an authenticated compiler-generated method-evidence position.",
    ),
    (
        "spec/elaboration.md",
        "Independent Core validation consumes every method-evidence authentication fact exactly once.",
    ),
    (
        "spec/dynamic-semantics.md",
        "The evaluator does not inspect method authentication records or method schemes.",
    ),
    (
        "spec/README.md",
        "Ordinary source value positions remain rank-1.",
    ),
];

const RELATIONAL_INTERFACE_RULE_FRAGMENTS: &[(&str, &str)] = &[
    (
        "spec/lexical-structure.md",
        "Angle brackets delimit nonempty\nordered parameter and argument lists on interfaces",
    ),
    (
        "spec/syntax.md",
        "interface_determination ::=\n  \"where\" determination_side \"->\" determination_side ;",
    ),
    (
        "spec/name-resolution.md",
        "The\noptional determination edge resolves only parameter names from that same interface declaration.",
    ),
    (
        "spec/static-semantics.md",
        "A determination edge is total: its nonempty, disjoint sides preserve declaration order and together name every interface parameter exactly once.",
    ),
    (
        "spec/static-semantics.md",
        "Snapshot eligibility\ngates only pending determined occurrence roots at their owning closure.",
    ),
    (
        "spec/static-semantics.md",
        "determined requirements for the same InterfaceId have no equal-key,\n    unequal-dependent pair",
    ),
    (
        "spec/static-semantics.md",
        "determined prerequisites for the same InterfaceId have no equal-key,\n    unequal-dependent pair",
    ),
    (
        "spec/elaboration.md",
        "Interface substitution is simultaneous and follows declaration order.",
    ),
    (
        "spec/dynamic-semantics.md",
        "Determination metadata erases before Core synthesis.",
    ),
    (
        "spec/README.md",
        "An interface declares one or more ordered, fixed-kinded type parameters",
    ),
];

const NEWTYPE_RULE_FRAGMENTS: &[(&str, &str)] = &[
    (
        "spec/README.md",
        "A module `newtype` introduces a nominal type over one representation",
    ),
    (
        "spec/lexical-structure.md",
        "The reserved words `fn`, `let`, `rec`, `and`, `type`, `newtype`",
    ),
    (
        "spec/syntax.md",
        "newtype_declaration ::=\n  [ \"pub\" [ \"opaque\" ] ]",
    ),
    (
        "spec/name-resolution.md",
        "A `newtype` receives the same module-owned nominal and constructor identity forms",
    ),
    (
        "spec/static-semantics.md",
        "The directed graph containing only `newtype` representation edges must be acyclic.",
    ),
    (
        "spec/elaboration.md",
        "A newtype constructor occurrence lowers to an ordinary unary function whose body is a wrap conversion.",
    ),
    ("spec/dynamic-semantics.md", "E-Newtype-Conversion :="),
];

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempDirectory(PathBuf);

impl TempDirectory {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-spec-examples-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("the example parent should be creatable");
        }
        fs::write(&path, text).expect("the module example should be writable");
        path
    }

    fn directory(&self, relative: &str) -> PathBuf {
        let path = self.0.join(relative);
        fs::create_dir_all(&path).expect("the module-root example should be creatable");
        path
    }
}

impl Drop for TempDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct TempFile {
    _directory: TempDirectory,
    path: PathBuf,
}

impl TempFile {
    fn write(text: &str) -> Self {
        Self::write_named("source.ash", text)
    }

    fn write_named(name: &str, text: &str) -> Self {
        let directory = TempDirectory::create();
        let path = directory.0.join(name);
        let owned = Self {
            _directory: directory,
            path,
        };
        fs::write(&owned.path, text).expect("the tool example should be writable");
        owned
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn run(name: &str, text: &str) -> Result<ash::driver::Observation, PipelineFailure> {
    let source = TempFile::write_named(name, text);
    match run_path(RunConfiguration {
        entry: source.path.clone(),
        roots: ModuleRoots::empty(),
    }) {
        Ok(observation) => Ok(observation),
        Err(FileFailure::Pipeline(failure)) => Err(failure),
        Err(FileFailure::Graph(LoadGraphError::Syntax(failure))) => {
            Err(PipelineFailure::Syntax(Box::new(SyntaxFailure {
                lexical: failure.lexical,
                parser: failure.parser,
                resource: failure.resource,
            })))
        }
        Err(FileFailure::Graph(LoadGraphError::Projection { error, .. })) => {
            Err(PipelineFailure::Projection(error))
        }
        Err(FileFailure::Graph(LoadGraphError::SourceModel { error, .. }))
        | Err(FileFailure::Source(error)) => Err(PipelineFailure::SourceModel(error)),
        Err(failure) => panic!("the specification module reached an input failure: {failure}"),
    }
}

fn assert_observation(name: &str, text: &str, value: &str, ty: &str) {
    let observation = run(name, text).expect("the documented example should be accepted");
    assert_eq!(observation.value_display(), value);
    assert_eq!(observation.type_display(), ty);
}

fn assert_documented(path: &str, source: &str) {
    let document = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("missing documentation harness data {path}: {error}"));
    assert!(
        document.contains(source.trim_end()),
        "{path} must contain its executable source example"
    );
}

fn assert_normative_fragment(path: &str, fragment: &str) {
    let document = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("missing normative manifest data {path}: {error}"));
    assert!(
        document.contains(fragment),
        "{path} must contain normative fragment {fragment:?}"
    );
}

fn source_kind_error(name: &str, text: &str) -> Box<ash::kind::KindError> {
    let failure = run(name, text).expect_err("the documented kind rejection should fail");
    let PipelineFailure::Kind(KindFailure::Source(error)) = failure else {
        panic!("the documented kind rejection should fail at kind checking: {failure:?}")
    };
    error
}

fn type_to_type_kind() -> Kind {
    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
}

fn assert_module_tree(
    entry_text: &str,
    dependencies: &[(&str, &str)],
    roots: ModuleRoots,
) -> ash::driver::Observation {
    let tree = TempDirectory::create();
    let entry = tree.write("app/main.ash", entry_text);
    for (path, text) in dependencies {
        tree.write(path, text);
    }
    run_path(RunConfiguration { entry, roots })
        .expect("the documented module tree should be accepted")
}

fn exact_range(source: &str, needle: &str) -> (u32, u32) {
    let start = source
        .find(needle)
        .unwrap_or_else(|| panic!("the fixture should contain {needle:?}"));
    let end = start + needle.len();
    (
        u32::try_from(start).expect("the fixture offset should fit in a source span"),
        u32::try_from(end).expect("the fixture offset should fit in a source span"),
    )
}

fn exact_last_range(source: &str, needle: &str) -> (u32, u32) {
    let start = source
        .rfind(needle)
        .unwrap_or_else(|| panic!("the fixture should contain {needle:?}"));
    let end = start + needle.len();
    (
        u32::try_from(start).expect("the fixture offset should fit in a source span"),
        u32::try_from(end).expect("the fixture offset should fit in a source span"),
    )
}

#[test]
fn overview_main_application_example_is_executable() {
    assert_observation("main.ash", MAIN_MODULE, "42", "Int");
    assert_documented("README.md", MAIN_MODULE);
}

#[test]
fn overview_sibling_import_example_is_executable() {
    let observation = assert_module_tree(
        SIBLING_ENTRY_MODULE,
        &[("app/arithmetic.ash", SIBLING_ARITHMETIC_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    assert_documented("spec/README.md", SIBLING_ENTRY_MODULE);
    assert_documented("spec/README.md", SIBLING_ARITHMETIC_MODULE);
}

#[test]
fn overview_module_newtype_example_is_executable() {
    assert_observation("module-newtype.ash", MODULE_NEWTYPE_MODULE, "42", "UserId");
    assert_documented("spec/README.md", MODULE_NEWTYPE_MODULE);
}

#[test]
fn tool_named_root_example_has_exact_cli_observation() {
    let tree = TempDirectory::create();
    tree.write("app/main.ash", NAMED_ROOT_ENTRY_MODULE);
    tree.directory("standard");
    tree.write("standard/answer.ash", NAMED_ROOT_ANSWER_MODULE);

    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .current_dir(&tree.0)
        .arg("--root")
        .arg("std=standard")
        .arg("app/main.ash")
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", NAMED_ROOT_ENTRY_MODULE);
    assert_documented("docs/tools/ash.md", NAMED_ROOT_ANSWER_MODULE);
}

#[test]
fn overview_targeted_import_example_is_executable() {
    let observation = assert_module_tree(
        TARGETED_ENTRY_MODULE,
        &[("app/arithmetic.ash", SIBLING_ARITHMETIC_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_documented("spec/README.md", TARGETED_ENTRY_MODULE);
}

#[test]
fn resolution_targeted_public_name_reexport_is_executable() {
    let observation = assert_module_tree(
        PUBLIC_NAME_REEXPORT_ENTRY_MODULE,
        &[
            ("app/arithmetic.ash", SIBLING_ARITHMETIC_MODULE),
            ("app/facade.ash", PUBLIC_NAME_REEXPORT_FACADE_MODULE),
        ],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    assert_documented("spec/name-resolution.md", PUBLIC_NAME_REEXPORT_ENTRY_MODULE);
    assert_documented(
        "spec/name-resolution.md",
        PUBLIC_NAME_REEXPORT_FACADE_MODULE,
    );
    assert_documented("spec/name-resolution.md", SIBLING_ARITHMETIC_MODULE);
}

#[test]
fn overview_opaque_smart_constructor_example_is_executable() {
    let observation = assert_module_tree(
        OPAQUE_ENTRY_MODULE,
        &[("app/token.ash", OPAQUE_TOKEN_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_documented("spec/README.md", OPAQUE_ENTRY_MODULE);
    assert_documented("spec/README.md", OPAQUE_TOKEN_MODULE);
}

#[test]
fn overview_hidden_carrier_example_is_executable() {
    let observation = assert_module_tree(
        HIDDEN_ENTRY_MODULE,
        &[("app/carrier.ash", HIDDEN_CARRIER_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_documented("spec/README.md", HIDDEN_ENTRY_MODULE);
    assert_documented("spec/README.md", HIDDEN_CARRIER_MODULE);
}

#[test]
fn overview_transparent_matching_example_is_executable() {
    let observation = assert_module_tree(
        TRANSPARENT_ENTRY_MODULE,
        &[("app/choice.ash", TRANSPARENT_CHOICE_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_documented("spec/README.md", TRANSPARENT_ENTRY_MODULE);
    assert_documented("spec/README.md", TRANSPARENT_CHOICE_MODULE);
}

#[test]
fn overview_local_interface_evidence_example_is_executable() {
    assert_observation(
        "local-interface-evidence.ash",
        LOCAL_INTERFACE_EVIDENCE_MODULE,
        "true",
        "Bool",
    );
    assert_documented("spec/README.md", LOCAL_INTERFACE_EVIDENCE_MODULE);
}

#[test]
fn overview_implementation_only_selector_beside_qualified_import_is_executable() {
    let observation = assert_module_tree(
        CONSTRAINED_IMPORT_ENTRY_MODULE,
        &[("app/equality.ash", CONSTRAINED_IMPORT_LIBRARY_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.type_display(), "Bool");
    assert_documented("spec/README.md", CONSTRAINED_IMPORT_ENTRY_MODULE);
    assert_documented("spec/README.md", CONSTRAINED_IMPORT_LIBRARY_MODULE);
}

#[test]
fn overview_name_only_import_has_structured_unsatisfied_constraint() {
    let tree = TempDirectory::create();
    let entry = tree.write("app/main.ash", NAME_ONLY_IMPORT_ENTRY_MODULE);
    tree.write("app/equality.ash", EQUALITY_IMPLEMENTATION_MODULE);

    let failure = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("a name-only import should not make implementation evidence available");
    let FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Interface(diagnostic))) = failure
    else {
        panic!("the name-only method use should retain an interface diagnostic")
    };

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.reason.to_string(), "constraint.unsatisfied");
    assert_eq!(
        diagnostic.primary.message(),
        "no available implementation satisfies this interface obligation"
    );
    let primary = diagnostic.primary.span();
    assert_eq!(
        (primary.range().start(), primary.range().end()),
        exact_last_range(NAME_ONLY_IMPORT_ENTRY_MODULE, "equal")
    );
    let [declaration, import, interface] = diagnostic.related.as_slice() else {
        panic!("the name-only failure should retain exactly three ordered causes")
    };
    assert_eq!(
        declaration.message(),
        "this declaration introduced the interface obligation"
    );
    assert_eq!(
        (
            declaration.span().range().start(),
            declaration.span().range().end()
        ),
        exact_range(EQUALITY_IMPLEMENTATION_MODULE, "equal : (A, A) -> Bool")
    );
    assert_eq!(
        import.message(),
        "this import made the declaration available"
    );
    let selector_start = NAME_ONLY_IMPORT_ENTRY_MODULE
        .find("Equal, equal")
        .expect("the name-only fixture should contain its method selector")
        + "Equal, ".len();
    let selector_end = selector_start + "equal".len();
    assert_eq!(
        (import.span().range().start(), import.span().range().end()),
        (
            u32::try_from(selector_start).expect("the selector offset should fit in a source span"),
            u32::try_from(selector_end).expect("the selector offset should fit in a source span")
        )
    );
    assert_eq!(
        interface.message(),
        "this interface declaration participates in the failing selection"
    );
    assert_eq!(
        (
            interface.span().range().start(),
            interface.span().range().end()
        ),
        exact_range(
            EQUALITY_IMPLEMENTATION_MODULE,
            "pub interface Equal<A> {\n    equal : (A, A) -> Bool\n}"
        )
    );
    assert_eq!(primary.source(), import.span().source());
    assert_eq!(declaration.span().source(), interface.span().source());
    assert_ne!(primary.source(), declaration.span().source());
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
    assert!(diagnostic.help.is_none());
    assert_documented("spec/name-resolution.md", NAME_ONLY_IMPORT_ENTRY_MODULE);
    assert_documented("spec/name-resolution.md", EQUALITY_IMPLEMENTATION_MODULE);
}

#[test]
fn overview_three_module_implementation_facade_is_executable() {
    let observation = assert_module_tree(
        IMPLEMENTATION_FACADE_ENTRY_MODULE,
        &[
            ("app/equality.ash", EQUALITY_IMPLEMENTATION_MODULE),
            ("app/facade.ash", IMPLEMENTATION_FACADE_MODULE),
        ],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.type_display(), "Bool");
    assert_documented("spec/README.md", IMPLEMENTATION_FACADE_ENTRY_MODULE);
    assert_documented("spec/README.md", IMPLEMENTATION_FACADE_MODULE);
    assert_documented("spec/README.md", EQUALITY_IMPLEMENTATION_MODULE);
}

#[test]
fn overview_linked_higher_kinded_example_is_executable() {
    let observation = assert_module_tree(
        LINKED_HIGHER_KINDED_ENTRY_MODULE,
        &[("app/dependency.ash", LINKED_HIGHER_KINDED_DEPENDENCY_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    assert_documented("spec/README.md", LINKED_HIGHER_KINDED_ENTRY_MODULE);
    assert_documented("spec/README.md", LINKED_HIGHER_KINDED_DEPENDENCY_MODULE);
}

#[test]
fn overview_linked_polymorphic_method_evidence_is_executable() {
    let observation = assert_module_tree(
        METHOD_PARAMETER_ENTRY_MODULE,
        &[
            ("app/api.ash", METHOD_PARAMETER_INTERFACE_MODULE),
            ("app/carrier.ash", METHOD_PARAMETER_IMPLEMENTATION_MODULE),
        ],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "(Box(true), Box(42))");
    assert_eq!(observation.type_display(), "(Box<Bool>, Box<Int>)");
    for source in [
        METHOD_PARAMETER_INTERFACE_MODULE,
        METHOD_PARAMETER_IMPLEMENTATION_MODULE,
        METHOD_PARAMETER_ENTRY_MODULE,
    ] {
        assert_documented("spec/README.md", source);
    }
}

#[test]
fn static_semantics_generic_prerequisite_evidence_example_is_executable() {
    assert_observation(
        "generic-prerequisite-evidence.ash",
        GENERIC_PREREQUISITE_EVIDENCE_MODULE,
        "true",
        "Bool",
    );
    assert_documented(
        "spec/static-semantics.md",
        GENERIC_PREREQUISITE_EVIDENCE_MODULE,
    );
}

#[test]
fn static_semantics_determined_generic_prerequisite_uses_recursive_complete_selection() {
    assert_observation(
        "determined-generic-prerequisite.ash",
        DETERMINED_GENERIC_PREREQUISITE_MODULE,
        "42",
        "Int",
    );
    assert_documented(
        "spec/static-semantics.md",
        DETERMINED_GENERIC_PREREQUISITE_MODULE,
    );
}

#[test]
fn resolution_hidden_carrier_interface_example_uses_public_operations() {
    let observation = assert_module_tree(
        INTERFACE_HIDDEN_ENTRY_MODULE,
        &[("app/carrier.ash", INTERFACE_HIDDEN_CARRIER_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    assert_documented("spec/name-resolution.md", INTERFACE_HIDDEN_ENTRY_MODULE);
    assert_documented("spec/name-resolution.md", INTERFACE_HIDDEN_CARRIER_MODULE);
}

#[test]
fn resolution_opaque_carrier_interface_example_uses_public_operations() {
    let observation = assert_module_tree(
        INTERFACE_OPAQUE_ENTRY_MODULE,
        &[("app/token.ash", INTERFACE_OPAQUE_TOKEN_MODULE)],
        ModuleRoots::empty(),
    );
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.type_display(), "Bool");
    assert_documented("spec/name-resolution.md", INTERFACE_OPAQUE_ENTRY_MODULE);
    assert_documented("spec/name-resolution.md", INTERFACE_OPAQUE_TOKEN_MODULE);
}

#[test]
fn syntax_constrained_global_presentations_are_executable() {
    assert_observation(
        "constrained-presentations.ash",
        CONSTRAINED_PRESENTATIONS_MODULE,
        "(true, true)",
        "(Bool, Bool)",
    );
    assert_documented("spec/syntax.md", CONSTRAINED_PRESENTATIONS_MODULE);
}

#[test]
fn syntax_contextual_type_nominal_is_executable() {
    assert_observation(
        "contextual-type-nominal.ash",
        CONTEXTUAL_TYPE_NOMINAL_MODULE,
        "Type",
        "Type",
    );
    assert_documented("spec/syntax.md", CONTEXTUAL_TYPE_NOMINAL_MODULE);
}

#[test]
fn resolution_binder_policies_are_executable_and_ordered() {
    let source = TempFile::write_named("binder-policy.ash", BINDER_POLICY_MODULE);
    let graph = load_module_graph(source.path(), &ModuleRoots::empty())
        .expect("the documented binder-policy module should load");
    let resolved = resolve_module(&graph.modules()[0], &[])
        .expect("the documented binder-policy module should resolve");

    let phantom = resolved
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "Phantom")
        .expect("the phantom nominal should resolve");
    assert_eq!(
        resolved
            .registry()
            .nominal_parameters(phantom.id)
            .expect("the phantom nominal should retain its parameters")
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("Unused", &Kind::Type), ("A", &Kind::Type)],
    );

    let [interface] = resolved.interfaces() else {
        panic!("the binder-policy module should have one interface")
    };
    assert_eq!(
        (
            interface.parameters[0].spelling.as_str(),
            &interface.parameters[0].kind
        ),
        ("Value", &Kind::Type),
    );

    let mut equational_parameters = Vec::new();
    let mut operational_parameters = None;
    for definition in resolved.definitions() {
        match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => {
                equational_parameters.push((
                    global.interface.name.spelling.as_str(),
                    global
                        .interface
                        .type_parameters
                        .iter()
                        .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
                        .collect::<Vec<_>>(),
                ));
            }
            ResolvedDefinitionKind::InlineOperational(global) => {
                operational_parameters = Some(
                    global
                        .header
                        .type_parameters
                        .iter()
                        .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
                        .collect::<Vec<_>>(),
                );
            }
        }
    }
    assert_eq!(
        equational_parameters
            .iter()
            .find(|(name, _)| *name == "ordered")
            .expect("ordered should resolve")
            .1,
        [("B", &Kind::Type), ("A", &Kind::Type)],
    );
    assert_eq!(
        operational_parameters.expect("operational should resolve"),
        [("D", &Kind::Type), ("C", &Kind::Type)],
    );
    assert_eq!(
        equational_parameters
            .iter()
            .find(|(name, _)| *name == "legacy")
            .expect("legacy should resolve")
            .1,
        [("Y", &Kind::Type), ("X", &Kind::Type)],
    );

    let [explicit, implicit] = resolved.implementations() else {
        panic!("the binder-policy module should have two implementations")
    };
    assert_eq!(
        explicit
            .head_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("F", &Kind::Type), ("E", &Kind::Type)],
    );
    assert_eq!(
        implicit
            .head_parameters
            .iter()
            .map(|parameter| (parameter.spelling.as_str(), &parameter.kind))
            .collect::<Vec<_>>(),
        [("S", &Kind::Type), ("R", &Kind::Type)],
    );

    assert_observation("binder-policy.ash", BINDER_POLICY_MODULE, "42", "Int");
    assert_documented("spec/name-resolution.md", BINDER_POLICY_MODULE);
}

#[test]
fn resolution_interleaved_explicit_implementation_and_implicit_global_reach_core() {
    assert_observation(
        "interleaved-binder-registry.ash",
        INTERLEAVED_BINDER_REGISTRY_MODULE,
        "42",
        "Int",
    );
}

#[test]
fn static_semantics_kind_synthesis_and_interface_argument_are_executable() {
    assert_observation(
        "higher-kinded-interface.ash",
        HIGHER_KINDED_INTERFACE_MODULE,
        "(Some(42), true, ())",
        "(Option<Int>, Bool, Unit)",
    );
    assert_documented("spec/static-semantics.md", HIGHER_KINDED_INTERFACE_MODULE);
}

#[test]
fn static_semantics_kind_failures_are_structured_and_phase_scoped() {
    let expected_type = source_kind_error(
        "kind-expected-type.ash",
        EXPECTED_TYPE_KIND_REJECTION_MODULE,
    );
    assert_eq!(expected_type.reason, KindReason::ExpectedType);
    assert_eq!(
        expected_type.expectation(),
        &KindExpectation::Exact(Kind::Type),
    );
    assert_eq!(expected_type.found_kind(), Some(&type_to_type_kind()));
    assert_eq!(
        (
            expected_type.primary.span().range().start(),
            expected_type.primary.span().range().end(),
        ),
        exact_last_range(EXPECTED_TYPE_KIND_REJECTION_MODULE, "Option"),
    );
    let [expected_type_declaration] = expected_type.related.as_slice() else {
        panic!("kind.expected-type should retain its nominal declaration")
    };
    assert_eq!(
        expected_type_declaration.message(),
        "the found kind is fixed by this declaration",
    );
    assert_eq!(
        (
            expected_type_declaration.span().range().start(),
            expected_type_declaration.span().range().end(),
        ),
        exact_range(
            EXPECTED_TYPE_KIND_REJECTION_MODULE,
            "type Option<A> =\n    None\n    | Some(A)",
        ),
    );

    let no_inference =
        source_kind_error("no-kind-inference.ash", NO_KIND_INFERENCE_REJECTION_MODULE);
    assert_eq!(no_inference.reason, KindReason::NotApplicable);
    assert_eq!(
        no_inference.expectation(),
        &KindExpectation::Function { domain: Kind::Type },
    );
    assert_eq!(no_inference.found_kind(), Some(&Kind::Type));
    assert_eq!(
        (
            no_inference.primary.span().range().start(),
            no_inference.primary.span().range().end(),
        ),
        exact_range(NO_KIND_INFERENCE_REJECTION_MODULE, "F<Int>"),
    );
    let [implicit_binder] = no_inference.related.as_slice() else {
        panic!("the implicit kind should retain its defining binder site")
    };
    assert_eq!(
        implicit_binder.message(),
        "the applied type's kind is fixed by this declaration",
    );
    assert_eq!(
        (
            implicit_binder.span().range().start(),
            implicit_binder.span().range().end(),
        ),
        exact_range(NO_KIND_INFERENCE_REJECTION_MODULE, "F"),
    );

    let interface_argument = source_kind_error(
        "interface-kind-argument.ash",
        INTERFACE_KIND_ARGUMENT_REJECTION_MODULE,
    );
    assert_eq!(interface_argument.reason, KindReason::Argument);
    assert_eq!(
        interface_argument.expectation(),
        &KindExpectation::Exact(type_to_type_kind()),
    );
    assert_eq!(interface_argument.found_kind(), Some(&Kind::Type));
    assert_eq!(
        (
            interface_argument.primary.span().range().start(),
            interface_argument.primary.span().range().end(),
        ),
        exact_last_range(INTERFACE_KIND_ARGUMENT_REJECTION_MODULE, "Int"),
    );
    let [interface_parameter] = interface_argument.related.as_slice() else {
        panic!("kind.argument should retain its interface parameter")
    };
    assert_eq!(
        interface_parameter.message(),
        "the interface parameter kind is declared here",
    );
    assert_eq!(
        (
            interface_parameter.span().range().start(),
            interface_parameter.span().range().end(),
        ),
        exact_range(INTERFACE_KIND_ARGUMENT_REJECTION_MODULE, "F"),
    );

    for source in [
        EXPECTED_TYPE_KIND_REJECTION_MODULE,
        NO_KIND_INFERENCE_REJECTION_MODULE,
        INTERFACE_KIND_ARGUMENT_REJECTION_MODULE,
    ] {
        assert_documented("spec/static-semantics.md", source);
    }
    assert_normative_fragment(
        "spec/static-semantics.md",
        PHASE_DEPENDENT_NO_KIND_INFERENCE,
    );
}

#[test]
fn syntax_equational_global_example_v002_is_executable() {
    assert_observation("spec-v002-equational.ash", V002_EQUATIONAL, "42", "Int");
    assert_documented("spec/syntax.md", V002_EQUATIONAL);
}

#[test]
fn syntax_inline_operational_global_example_v002_is_executable() {
    assert_observation("spec-v002-operational.ash", V002_OPERATIONAL, "42", "Int");
    assert_documented("spec/syntax.md", V002_OPERATIONAL);
}

#[test]
fn syntax_local_recursive_group_example_is_executable() {
    assert_observation("spec-local-recursion.ash", RECURSIVE_LOCAL, "42", "Int");
    assert_documented("spec/syntax.md", RECURSIVE_LOCAL);
}

#[test]
fn resolution_global_recursive_scope_example_is_executable() {
    assert_observation("spec-global-recursion.ash", RECURSIVE_GLOBAL, "42", "Int");
    assert_documented("spec/name-resolution.md", RECURSIVE_GLOBAL);
}

#[test]
fn static_semantics_rejects_unsafe_recursive_initialization() {
    let failure = run("spec-unsafe-recursion.ash", UNSAFE_RECURSIVE_INITIALIZER)
        .expect_err("recursive values require direct function initialization");
    let PipelineFailure::Typing(TypeError::Source(actual)) = failure else {
        panic!("unsafe recursive initialization should fail during typing")
    };
    assert_eq!(actual.reason, TypeReason::UnsafeRecursiveRoot);
    assert_documented("spec/static-semantics.md", UNSAFE_RECURSIVE_INITIALIZER);
}

#[test]
fn dynamic_recursive_group_example_is_executable() {
    assert_observation("spec-dynamic-recursion.ash", RECURSIVE_LOCAL, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", RECURSIVE_LOCAL);
}

#[test]
fn tool_recursive_example_has_exact_cli_observation() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg("tests/fixtures/recursion/valid/global-mutual.ash")
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", RECURSIVE_GLOBAL);
}

#[test]
fn syntax_curried_equational_example_is_executable() {
    assert_observation(
        "spec-curried-equational.ash",
        CURRIED_EQUATIONAL_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/elaboration.md", CURRIED_EQUATIONAL_MODULE);
}

#[test]
fn lexical_comment_rejection_example_has_its_documented_reason() {
    let failure = run("spec-comment-rejection.ash", COMMENT_REJECTION_MODULE)
        .expect_err("comments are outside this lexical structure");
    let PipelineFailure::Syntax(actual) = failure else {
        panic!("the comment example should fail during syntax processing");
    };
    assert_eq!(
        actual
            .lexical
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::Comment]
    );
    assert_documented("spec/lexical-structure.md", COMMENT_REJECTION_MODULE);
}

#[test]
fn resolution_unknown_name_example_has_its_documented_reason() {
    let failure = run("spec-unknown-name.ash", UNKNOWN_NAME_REJECTION_MODULE)
        .expect_err("an unresolved occurrence should be rejected");
    let PipelineFailure::Resolution(actual) = failure else {
        panic!("the unknown-name example should fail during resolution");
    };
    assert_eq!(actual.reason, ResolveReason::UnknownName);
    assert_documented("spec/name-resolution.md", UNKNOWN_NAME_REJECTION_MODULE);
}

#[test]
fn static_semantics_operand_example_has_its_documented_reason() {
    let failure = run("spec-operator-operand.ash", TYPE_REJECTION_MODULE)
        .expect_err("a Boolean addition operand should be rejected");
    let PipelineFailure::Typing(TypeError::Source(actual)) = failure else {
        panic!("the operand example should fail during typing");
    };
    assert_eq!(actual.reason, TypeReason::OperatorOperand);
    assert_documented("spec/static-semantics.md", TYPE_REJECTION_MODULE);
}

#[test]
fn static_semantics_contextual_block_example_is_executable() {
    assert_observation(
        "spec-contextual-block.ash",
        CONTEXTUAL_BLOCK_MODULE,
        "1",
        "Int",
    );
    assert_documented("spec/static-semantics.md", CONTEXTUAL_BLOCK_MODULE);
}

#[test]
fn static_semantics_higher_order_operational_example_is_executable() {
    assert_observation(
        "spec-higher-order-operational.ash",
        HIGHER_ORDER_OPERATIONAL_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/static-semantics.md", HIGHER_ORDER_OPERATIONAL_MODULE);
}

#[test]
fn static_semantics_irrefutable_tuple_binding_is_executable() {
    assert_observation(
        "spec-irrefutable-tuple.ash",
        IRREFUTABLE_TUPLE_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/static-semantics.md", IRREFUTABLE_TUPLE_MODULE);
}

#[test]
fn static_semantics_operational_tuple_pattern_is_executable() {
    assert_observation(
        "spec-operational-tuple-pattern.ash",
        OPERATIONAL_TUPLE_PATTERN_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/static-semantics.md", OPERATIONAL_TUPLE_PATTERN_MODULE);
}

#[test]
fn static_semantics_contextual_match_checks_function_arms() {
    assert_observation(
        "spec-contextual-match.ash",
        CONTEXTUAL_MATCH_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/static-semantics.md", CONTEXTUAL_MATCH_MODULE);
}

#[test]
fn static_semantics_rank_one_polymorphism_is_executable() {
    assert_observation(
        "spec-rank-one-polymorphism.ash",
        RANK_ONE_POLYMORPHISM_MODULE,
        "(Some(42), false)",
        "(Option<Int>, Bool)",
    );
    assert_documented("spec/static-semantics.md", RANK_ONE_POLYMORPHISM_MODULE);
}

#[test]
fn elaboration_tree_presentations_are_equivalent() {
    assert_observation(
        "spec-tree-presentations.ash",
        TREE_PRESENTATIONS_MODULE,
        "4",
        "Int",
    );
    assert_documented("spec/elaboration.md", TREE_PRESENTATIONS_MODULE);
}

#[test]
fn elaboration_payload_constructor_is_higher_order() {
    assert_observation(
        "spec-higher-order-constructor.ash",
        HIGHER_ORDER_CONSTRUCTOR_MODULE,
        "42",
        "Int",
    );
    assert_documented("spec/elaboration.md", HIGHER_ORDER_CONSTRUCTOR_MODULE);
}

#[test]
fn elaboration_distinguishes_structural_application_from_simultaneous_instantiation() {
    let source = TempFile::write_named("core-kinds.ash", CORE_KIND_MODULE);
    let graph = load_module_graph(source.path(), &ModuleRoots::empty())
        .expect("the documented Core kind module should load");
    let resolved = resolve_module(&graph.modules()[0], &[])
        .expect("the documented Core kind module should resolve");
    let option = resolved
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "Option")
        .expect("Option should resolve")
        .id;
    let keep = resolved
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global)
                if global.interface.name.spelling == "keep" =>
            {
                Some(&global.interface)
            }
            ResolvedDefinitionKind::Equational(_)
            | ResolvedDefinitionKind::InlineOperational(_) => None,
        })
        .expect("keep should resolve");
    let keep_binder = keep.name.id;
    let [f_parameter, a_parameter] = keep.type_parameters.as_ref() else {
        panic!("keep should retain two ordered kinded parameters")
    };
    assert_eq!(f_parameter.kind, type_to_type_kind());
    assert_eq!(a_parameter.kind, Kind::Type);
    let f = f_parameter.id;
    let a = a_parameter.id;

    let checked = check_module(resolved).expect("the documented Core kind module should check");
    let linked = link_modules(vec![checked], graph.entry())
        .expect("the documented Core kind module should link");
    let linked = validate_interface_evidence(linked)
        .expect("the documented Core kind module should authenticate evidence");
    let mut elaborator = Elaborator::for_module_program(&linked)
        .expect("the documented Core kind module should establish its binder namespace");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("the documented Core kind module should synthesize Core");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the documented Core kind module should finish Core construction");
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
    let validated = validate_modules(unchecked, &sources, &module_sources)
        .expect("the documented Core kind module should independently validate");

    let mut work = vec![validated.root()];
    let mut abstraction_id = None;
    let mut simultaneous_arguments = None;
    while let Some(id) = work.pop() {
        let node = validated
            .node(id)
            .expect("every documented Core child should exist");
        match &node.kind {
            PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                for member in group.members() {
                    if member.binder().id() == keep_binder {
                        assert!(
                            abstraction_id.replace(member.initializer()).is_none(),
                            "keep should have one Core initializer",
                        );
                    }
                }
            }
            PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                let function = validated
                    .node(application.function())
                    .expect("the Core type-application function should exist");
                if matches!(
                    function.kind,
                    PureExprKind::Variable(variable) if variable.binder() == keep_binder
                ) {
                    assert!(
                        simultaneous_arguments
                            .replace(application.arguments().to_vec())
                            .is_none(),
                        "keep should have one simultaneous Core instantiation",
                    );
                }
            }
            PureExprKind::Value(_)
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Bind(_)
                | PureComputation::Apply(_)
                | PureComputation::Primitive(_)
                | PureComputation::Tuple(_)
                | PureComputation::Match(_)
                | PureComputation::NewtypeConversion(_)
                | PureComputation::TypeAbstraction(_),
            ) => {}
        }
        work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }

    let abstraction = validated
        .node(abstraction_id.expect("keep should retain its Core abstraction"))
        .expect("keep's Core abstraction should exist");
    let PureExprKind::Computation(PureComputation::TypeAbstraction(type_abstraction)) =
        &abstraction.kind
    else {
        panic!("keep's initializer should be one Core type abstraction")
    };
    assert_eq!(
        type_abstraction.parameters(),
        [(f, type_to_type_kind()), (a, Kind::Type)],
    );
    let Type::Forall(scheme_parameters, scheme_body) = &abstraction.ty else {
        panic!("keep's abstraction should expose its outer scheme")
    };
    assert_eq!(scheme_parameters.as_ref(), type_abstraction.parameters());
    let applied = Type::Application(Box::new(Type::Variable(f)), Box::new(Type::Variable(a)));
    assert_eq!(
        scheme_body.as_ref(),
        &Type::Function(Box::new(applied.clone()), Box::new(applied)),
    );
    assert_eq!(
        simultaneous_arguments.expect("keep should be instantiated"),
        [Type::Nominal(option), Type::Int],
    );

    assert_observation(
        "core-kinds.ash",
        CORE_KIND_MODULE,
        "Some(42)",
        "Option<Int>",
    );
    assert_documented("spec/elaboration.md", CORE_KIND_MODULE);
}

#[test]
fn dynamic_cyclic_data_observation_is_finite() {
    assert_observation(
        "spec-cyclic-stream.ash",
        CYCLIC_STREAM_MODULE,
        "Next(1, <cycle>)",
        "Stream",
    );
    assert_documented("spec/dynamic-semantics.md", CYCLIC_STREAM_MODULE);
}

#[test]
fn dynamic_binding_derivation_example_v003_is_executable() {
    assert_observation("spec-v003.ash", V003, "2", "Int");
    assert_documented("spec/dynamic-semantics.md", V003);
}

#[test]
fn dynamic_primitive_derivation_example_v001_is_executable() {
    assert_observation("spec-v001.ash", V001, "7", "Int");
    assert_documented("spec/dynamic-semantics.md", V001);
}

#[test]
fn dynamic_application_derivation_example_v002_is_executable() {
    assert_observation("spec-v002.ash", V002_EQUATIONAL, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V002_EQUATIONAL);
}

#[test]
fn dynamic_capture_derivation_example_v004_is_executable() {
    assert_observation("spec-v004.ash", V004, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V004);
}

#[test]
fn dynamic_nested_application_derivation_example_v008_is_executable() {
    assert_observation("spec-v008.ash", V008, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V008);
}

#[test]
fn tool_success_example_has_exact_cli_observation() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg("tests/fixtures/first-stratum/valid/v008-mixed.ash")
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", V008);
}

#[test]
fn tool_module_newtype_observation_has_exact_cli_output() {
    let source = TempFile::write(MODULE_NEWTYPE_MODULE);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented module-newtype executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : UserId\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", MODULE_NEWTYPE_MODULE);
}

#[test]
fn tool_example_temp_source_requires_exclusive_directory_ownership() {
    let harness = include_str!("spec_examples.rs");
    let exclusive_creation = ["match fs::", "create_dir(&path)"].concat();
    let process_only_path = ["\"ash-spec-function-result-", "{}.ash\""].concat();
    let file_guard = ["let owned = Self ", "{"].concat();
    let guarded_write = ["fs::", "write(&owned.path"].concat();
    assert!(
        harness.contains(&exclusive_creation),
        "the documentation harness must acquire a unique temporary directory"
    );
    assert!(
        !harness.contains(&process_only_path),
        "a process-only filename can overwrite an unowned shared-temp path"
    );
    let guard_position = harness
        .find(&file_guard)
        .expect("the temporary file needs an RAII cleanup guard");
    let write_position = harness
        .find(&guarded_write)
        .expect("the guarded temporary source should be written");
    assert!(
        guard_position < write_position,
        "the cleanup guard must exist before a partial write can fail"
    );
}

#[test]
fn tool_function_result_uses_opaque_rendering() {
    let source = TempFile::write(FUNCTION_RESULT_MODULE);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"<function> : Int -> Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", FUNCTION_RESULT_MODULE);
}

#[test]
fn tool_cyclic_data_uses_structural_rendering() {
    let source = TempFile::write(CYCLIC_STREAM_MODULE);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"Next(1, <cycle>) : Stream\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", CYCLIC_STREAM_MODULE);
}

#[test]
fn tool_rank_one_example_has_exact_cli_observation() {
    let source = TempFile::write(RANK_ONE_POLYMORPHISM_MODULE);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"(Some(42), false) : (Option<Int>, Bool)\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", RANK_ONE_POLYMORPHISM_MODULE);
}

#[test]
fn tool_higher_kinded_example_has_exact_cli_observation() {
    let source = TempFile::write(HIGHER_KINDED_INTERFACE_MODULE);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented higher-kinded executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        output.stdout,
        b"(Some(42), true, ()) : (Option<Int>, Bool, Unit)\n"
    );
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", HIGHER_KINDED_INTERFACE_MODULE);
}

#[test]
fn tool_method_parameter_example_has_exact_cli_observation() {
    let tree = TempDirectory::create();
    tree.write("app/api.ash", METHOD_PARAMETER_INTERFACE_MODULE);
    tree.write("app/carrier.ash", METHOD_PARAMETER_IMPLEMENTATION_MODULE);
    tree.write("app/entry.ash", METHOD_PARAMETER_ENTRY_MODULE);

    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .current_dir(&tree.0)
        .arg("app/entry.ash")
        .output()
        .expect("the documented method-parameter executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        output.stdout,
        b"(Box(true), Box(42)) : (Box<Bool>, Box<Int>)\n"
    );
    assert!(output.stderr.is_empty());
    for source in [
        METHOD_PARAMETER_INTERFACE_MODULE,
        METHOD_PARAMETER_IMPLEMENTATION_MODULE,
        METHOD_PARAMETER_ENTRY_MODULE,
    ] {
        assert_documented("docs/tools/ash.md", source);
    }
}

#[test]
fn tool_method_parameter_migration_is_executable_and_documented() {
    let failure = run(
        "method-parameter-migration-rejected.ash",
        METHOD_PARAMETER_MIGRATION_REJECTED_MODULE,
    )
    .expect_err("an absent list should keep the predecessor rejection");
    let PipelineFailure::Typing(TypeError::Interface(diagnostic)) = failure else {
        panic!("the absent-list migration example should fail at interface checking")
    };
    assert_eq!(diagnostic.reason, InterfaceReason::MethodParameter);

    assert_observation(
        "method-parameter-migration-accepted.ash",
        METHOD_PARAMETER_MIGRATION_ACCEPTED_MODULE,
        "42",
        "Int",
    );
    for source in [
        METHOD_PARAMETER_MIGRATION_REJECTED_MODULE,
        METHOD_PARAMETER_MIGRATION_ACCEPTED_MODULE,
    ] {
        assert_documented("docs/tools/ash.md", source);
    }
}

#[test]
fn tool_source_rejection_uses_status_one_and_stderr() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(Path::new(
            "tests/fixtures/first-stratum/type/t002-operator-operand.ash",
        ))
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("type.operator-operand\n"));
    assert_documented("docs/tools/ash.md", TYPE_REJECTION_MODULE);
}

#[test]
fn normative_document_manifest_is_complete() {
    for path in [
        "spec/README.md",
        "spec/lexical-structure.md",
        "spec/syntax.md",
        "spec/name-resolution.md",
        "spec/static-semantics.md",
        "spec/elaboration.md",
        "spec/dynamic-semantics.md",
        "docs/tools/README.md",
        "docs/tools/ash.md",
    ] {
        assert!(
            Path::new(path).is_file(),
            "missing documentation harness datum {path}"
        );
    }
}

#[test]
fn explicit_kind_normative_rule_manifest_is_complete() {
    for &(path, fragment) in EXPLICIT_KIND_RULE_FRAGMENTS {
        assert_normative_fragment(path, fragment);
    }
}

#[test]
fn method_parameter_normative_rule_manifest_is_complete() {
    for &(path, fragment) in METHOD_PARAMETER_RULE_FRAGMENTS {
        assert_normative_fragment(path, fragment);
    }
}

#[test]
fn relational_interface_overview_example_is_executable() {
    assert_observation("main.ash", RELATIONAL_INTERFACE_MODULE, "42", "Int");
    assert_documented("spec/README.md", RELATIONAL_INTERFACE_MODULE);
}

#[test]
fn relational_interface_normative_rule_manifest_is_complete() {
    for &(path, fragment) in RELATIONAL_INTERFACE_RULE_FRAGMENTS {
        assert_normative_fragment(path, fragment);
    }
}

#[test]
fn module_newtype_normative_rule_manifest_is_complete() {
    for &(path, fragment) in NEWTYPE_RULE_FRAGMENTS {
        assert_normative_fragment(path, fragment);
    }
}
