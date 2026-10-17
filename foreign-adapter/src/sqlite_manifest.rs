//! Historical DN-0036 SQLite registration, outside the product compiler API.
//! The same declarations serve only the retained experiment and compiler tests.

use super::contract::{
    foreign::{
        ForeignConstructorDeclaration, ForeignEffectDeclaration, ForeignManifest,
        ForeignManifestSchema, ForeignOperationDeclaration, ForeignRegistrationError,
        ForeignResultRelation, ForeignTypeCategory, ForeignTypeDeclaration,
    },
    module::{ForeignOperationRole, ForeignRegistrationId},
};

fn data(
    name: &str,
    parameters: &[&str],
    constructors: &[(&str, Option<&str>)],
) -> ForeignTypeDeclaration {
    ForeignTypeDeclaration {
        name: name.into(),
        parameters: parameters
            .iter()
            .map(|parameter| (*parameter).into())
            .collect(),
        category: ForeignTypeCategory::Data,
        constructors: constructors
            .iter()
            .map(|(name, payload)| ForeignConstructorDeclaration {
                name: (*name).into(),
                payload: payload.map(str::to_owned),
            })
            .collect(),
    }
}
fn state(name: &str, parameters: &[&str]) -> ForeignTypeDeclaration {
    ForeignTypeDeclaration {
        name: name.into(),
        parameters: parameters
            .iter()
            .map(|parameter| (*parameter).into())
            .collect(),
        category: ForeignTypeCategory::State,
        constructors: Vec::new(),
    }
}
fn operation(
    name: &str,
    signature: &str,
    role: ForeignOperationRole,
    state_operands: Vec<Vec<usize>>,
    result: ForeignResultRelation,
) -> ForeignOperationDeclaration {
    ForeignOperationDeclaration {
        name: name.into(),
        signature: signature.into(),
        role,
        owned_identity_position: 0,
        state_operands,
        retained_arguments: Vec::new(),
        result,
    }
}
/// Builds the historical copying SQLite experiment manifest without native calls.
/// Product libraries use passive Ash declarations and generated bridges instead.
/// # Errors
/// Returns a manifest error if its authored declaration schema is invalid.
pub fn sqlite_manifest(
    id: ForeignRegistrationId,
) -> Result<ForeignManifest, ForeignRegistrationError> {
    use ForeignOperationRole::{Acquire, Borrow, Finish};
    let types = vec![
        state("ConnectionState", &["R"]),
        state("StatementState", &["S", "C"]),
        data(
            "OpenConfig",
            &[],
            &[("InMemory", None), ("File", Some("String"))],
        ),
        data(
            "InputFault",
            &[],
            &[
                ("BadIndex", None),
                ("BadInteger", None),
                ("BadBytes", None),
                ("BadColumn", None),
                ("ColumnTypeMismatch", None),
                ("BadSql", None),
                ("MultipleStatements", None),
                ("BadPath", None),
                ("BadText", None),
            ],
        ),
        data(
            "ProtocolFault",
            &[],
            &[
                ("NotPrepared", None),
                ("NotRow", None),
                ("AfterDone", None),
                ("ClosedOwner", None),
            ],
        ),
        data(
            "Error",
            &[],
            &[
                ("NativeFailure", Some("Int, String")),
                ("InputFailure", Some("InputFault")),
                ("ProtocolFailure", Some("ProtocolFault")),
                ("ConversionFailure", None),
                ("AllocationFailure", None),
            ],
        ),
        data("OpenError", &[], &[("OpenFailure", Some("Error"))]),
        data("CloseError", &[], &[("CloseFailure", Some("Error"))]),
        data(
            "PrepareError",
            &[],
            &[("PrepareFailure", Some("Error")), ("EmptySql", None)],
        ),
        data("FinalizeError", &[], &[("FinalizeFailure", Some("Error"))]),
        data(
            "Result",
            &["T"],
            &[("Ok", Some("T")), ("Err", Some("Error"))],
        ),
        data(
            "StepResult",
            &[],
            &[("Row", None), ("Done", None), ("StepError", Some("Error"))],
        ),
        data(
            "BytesOrNull",
            &[],
            &[("NullBytes", None), ("BlobBytes", Some("Bytes"))],
        ),
        data(
            "Acquire",
            &["State", "E"],
            &[("Acquired", Some("State")), ("Refused", Some("E"))],
        ),
        data(
            "Finish",
            &["State", "E"],
            &[
                ("Consumed", None),
                ("ConsumedFailure", Some("E")),
                ("Retained", Some("State, E")),
            ],
        ),
        data(
            "TextOrNull",
            &[],
            &[("NullText", None), ("TextValue", Some("String"))],
        ),
    ];
    let acquire = |state: &str, error: &str, retained_parameters| ForeignResultRelation::Acquire {
        state: state.into(),
        error: error.into(),
        report: "Acquire".into(),
        retained_parameters,
    };
    let finish = |state: &str, error: &str| ForeignResultRelation::Finish {
        state: state.into(),
        error: error.into(),
        report: "Finish".into(),
    };
    let connection = ForeignEffectDeclaration {
        name: "Connection".into(),
        parameters: vec!["R".into()],
        operations: vec![
            operation(
                "open",
                "OpenConfig -> Acquire<ConnectionState<R>, OpenError>",
                Acquire,
                vec![],
                acquire("ConnectionState", "OpenError", vec![]),
            ),
            operation(
                "diagnostic",
                "ConnectionState<R> -> Error",
                Borrow,
                vec![vec![]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "close",
                "ConnectionState<R> -> Finish<ConnectionState<R>, CloseError>",
                Finish,
                vec![vec![]],
                finish("ConnectionState", "CloseError"),
            ),
        ],
    };
    let mut statement = ForeignEffectDeclaration {
        name: "Statement".into(),
        parameters: vec!["S".into(), "C".into()],
        operations: vec![
            operation(
                "prepare",
                "(ConnectionState<C>, String) -> Acquire<StatementState<S, C>, PrepareError>",
                Acquire,
                vec![vec![0]],
                acquire("StatementState", "PrepareError", vec![1]),
            ),
            operation(
                "bind_int",
                "(StatementState<S, C>, Int, Int) -> Result<Unit>",
                Borrow,
                vec![vec![0]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "step",
                "StatementState<S, C> -> StepResult",
                Borrow,
                vec![vec![]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "column_int",
                "(StatementState<S, C>, Int) -> Result<Int>",
                Borrow,
                vec![vec![0]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "finalize",
                "StatementState<S, C> -> Finish<StatementState<S, C>, FinalizeError>",
                Finish,
                vec![vec![]],
                finish("StatementState", "FinalizeError"),
            ),
            operation(
                "bind_bytes",
                "(StatementState<S, C>, Int, BytesOrNull) -> Result<Unit>",
                Borrow,
                vec![vec![0]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "column_bytes",
                "(StatementState<S, C>, Int) -> Result<BytesOrNull>",
                Borrow,
                vec![vec![0]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "reset",
                "StatementState<S, C> -> Result<Unit>",
                Borrow,
                vec![vec![]],
                ForeignResultRelation::Independent,
            ),
            operation(
                "clear_bindings",
                "StatementState<S, C> -> Result<Unit>",
                Borrow,
                vec![vec![]],
                ForeignResultRelation::Independent,
            ),
        ],
    };
    statement.operations.extend([
        operation(
            "bind_text",
            "(StatementState<S, C>, Int, TextOrNull) -> Result<Unit>",
            Borrow,
            vec![vec![0]],
            ForeignResultRelation::Independent,
        ),
        operation(
            "column_text",
            "(StatementState<S, C>, Int) -> Result<TextOrNull>",
            Borrow,
            vec![vec![0]],
            ForeignResultRelation::Independent,
        ),
    ]);
    ForeignManifest::new(
        "@foreign.sqlite",
        id,
        ForeignManifestSchema {
            types,
            effects: vec![connection, statement],
            state_access: None,
            foundation: None,
        },
    )
}
