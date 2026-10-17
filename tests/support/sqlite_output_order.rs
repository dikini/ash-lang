//! Reorder only the two Prepare outputs and their canonical report fields.
//! The resulting declaration is admission-only until bound to a real C wrapper
//! with the corresponding reversed signature.

pub fn offset_first(source: &str) -> String {
    let mut source = source.to_owned();
    for (before, after) in [
        (
            "out(pointer(Address)), out(pointer(InputAddress))",
            "out(pointer(InputAddress)), out(pointer(Address))",
        ),
        (
            "Int, Foreign.Output<Foreign.Nullable<StatementState<C, S>>>, Foreign.Output<Foreign.Nullable<Int>>",
            "Int, Foreign.Output<Foreign.Nullable<Int>>, Foreign.Output<Foreign.Nullable<StatementState<C, S>>>",
        ),
        ("output 3 as owner", "output 4 as owner"),
        ("output 4 as offset_into", "output 3 as offset_into"),
        ("readable 3, readable 4", "readable 4, readable 3"),
        ("readable 3, unreadable 4", "readable 4, unreadable 3"),
        (
            "code, Foreign.Readable(Foreign.NonNull(state)), Foreign.Readable(Foreign.NonNull(tail))",
            "code, Foreign.Readable(Foreign.NonNull(tail)), Foreign.Readable(Foreign.NonNull(state))",
        ),
        (
            "code, Foreign.Readable(Foreign.Null), _",
            "code, __OWNER_NULL__",
        ),
        (
            "code, _, Foreign.Readable(Foreign.Null)",
            "code, Foreign.Readable(Foreign.Null), _",
        ),
        (
            "code, __OWNER_NULL__",
            "code, _, Foreign.Readable(Foreign.Null)",
        ),
    ] {
        // Some callers prepare only the declaration, without resource patterns.
        if source.contains(before) {
            source = source.replace(before, after);
        }
    }
    source
}
