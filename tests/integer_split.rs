use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn run(source: &str) -> String {
    let path = std::env::temp_dir().join(format!(
        "ash-split-{}-{}.ash",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    let _ = fs::remove_file(path);
    result
        .unwrap_or_else(|error| panic!("{error:?}"))
        .value_display()
        .to_owned()
}

#[test]
fn split_preserves_unbounded_integer_values() {
    let source = r#"import @builtin.integer as I
main : Unit -> (Int, Int)
main () = match I.split_base256 $N {
    I.Parts((q, r)) => (q, r)
    I.Negative => (999, 999)
}
"#;
    for (n, expected) in [
        ("0", "(0, 0)"),
        ("1", "(0, 1)"),
        ("255", "(0, 255)"),
        ("256", "(1, 0)"),
        ("257", "(1, 1)"),
        (
            "340282366920938463463374607431768211456",
            "(1329227995784915872903807060280344576, 0)",
        ),
        (
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
            "(452312848583266388373324160190187140051835877600158453279131187530910662656, 0)",
        ),
    ] {
        assert_eq!(run(&source.replace("$N", n)), expected, "input {n}");
    }
}

#[test]
fn split_evaluates_the_effectful_operand() {
    assert_eq!(
        run(r#"import @builtin.integer as I
import @builtin.cell as Cell
effect Read {
    value : Unit -> Int
}
main : Unit -> (Int, Int, Int)
main () = resource cell<R> count = 0 {
let result = handle (I.split_base256 (perform Read.value ())) with Read {
    value ignored => {
        let _ = Cell.write (count, (Cell.read count) + 1)
        resume 257
    }
}
match result {
    I.Parts((q, r)) => (q, r, Cell.read count)
    I.Negative => (999, 999, Cell.read count)
}
}
"#),
        "(1, 1, 1)"
    );
}

#[test]
fn selected_outer_region_keeps_the_split_result_live() {
    assert_eq!(
        run(r#"import @builtin.integer as I
main : Unit -> Bool
main () = region<R> outer {
    let result = region<S> inner {
        using outer {
            I.split_base256 257
        }
    }
    match result {
        I.Parts((q, r)) => match q == 1 {
            true => r == 1
            false => false
        }
        I.Negative => false
    }
}
"#),
        "true"
    );
}

#[test]
fn aliases_preserve_identity_and_ordinary_replacements_keep_their_body() {
    assert_eq!(
        run(r#"import @builtin.integer as I
main : Unit -> (Bool, Bool)
main () = {
    let alias = I.split_base256
    let replacement : Int -> I.SplitResult = fn(value) {
        I.Negative
    }
    let exact = match alias 257 {
        I.Parts((q, r)) => match q == 1 {
            true => r == 1
            false => false
        }
        I.Negative => false
    }
    let ordinary = match replacement 257 {
        I.Parts((q, r)) => false
        I.Negative => true
    }
    (exact, ordinary)
}
"#),
        "(true, true)"
    );
}

#[test]
fn public_reexports_preserve_the_canonical_operation_and_result() {
    let directory = std::env::temp_dir().join(format!(
        "ash-split-facade-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    fs::write(
        directory.join("facade.ash"),
        "pub import @builtin.integer (SplitResult, Parts, Negative, split_base256 as cut)\n",
    )
    .unwrap();
    fs::write(
        directory.join("entry.ash"),
        r#"import facade as F
main : Unit -> (Int, Int)
main () = match F.cut 257 {
    F.Parts((q, r)) => (q, r)
    F.Negative => (999, 999)
}
"#,
    )
    .unwrap();
    let result = run_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    });
    fs::remove_dir_all(directory).unwrap();
    assert_eq!(
        result
            .unwrap_or_else(|error| panic!("{error:?}"))
            .value_display(),
        "(1, 1)"
    );
}
