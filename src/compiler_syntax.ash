pub opaque type Token = HiddenToken
pub opaque type Identifier = HiddenIdentifier
pub opaque type ExpressionFragment = HiddenExpressionFragment
pub opaque type Input = HiddenInput
pub opaque type Origin = HiddenOrigin
pub opaque type ParseFailure = HiddenParseFailure

pub type Syntax = Syntax(Nodes)
pub type Nodes = NoNodes
    | MoreNodes(Node, Nodes)
pub type Node = TokenNode(Token, Origin)
    | IdentifierNode(Identifier, Origin)
    | GroupNode(Delimiter, Syntax, Origin)
    | ExpressionNode(ExpressionFragment, Origin)
    | TypeNode(TypeFragment, Origin)
    | PatternNode(PatternFragment, Origin)
    | DeclarationNode(DeclarationFragment, Origin)
pub type Delimiter = Parentheses
    | Braces
pub type Origins = NoOrigins
    | MoreOrigins(Origin, Origins)
pub type Capture = ExpressionCapture(ExpressionFragment)
    | IdentifierCapture(Identifier, Origin)
    | TypeCapture(TypeFragment)
    | PatternCapture(PatternFragment)
    | DeclarationCapture(DeclarationFragment)
    | RepeatedCapture(Captures)
pub type CaptureResult = Captured(Capture)
    | MissingCapture
pub type OriginsResult = Combined(Origin)
    | MissingOrigins
pub type IdentifierResult = MadeIdentifier(Identifier)
    | InvalidIdentifier
pub type TokenKind = Wildcard
    | IntegerLiteral
    | StringLiteral
    | True
    | False
    | Fn
    | Let
    | Rec
    | And
    | Type
    | Newtype
    | Effect
    | Match
    | Perform
    | Handle
    | With
    | Resume
    | Resource
    | Region
    | Using
    | Hook
    | Register
    | Cleanup
    | Discard
    | Retain
    | Import
    | As
    | Pub
    | Opaque
    | Interface
    | Impl
    | Where
    | IntType
    | BytesType
    | StringType
    | BoolType
    | UnitType
    | At
    | Dot
    | Colon
    | Equal
    | EqualEqual
    | Plus
    | Star
    | Arrow
    | FatArrow
    | Pipe
    | Bang
    | Comma
    | Less
    | Greater
    | LineEnd
    | SyntaxKeyword
    | Dollar
pub type TokenResult = MadeToken(Token)
    | InvalidToken
pub type ParseResult = Parsed(ExpressionFragment)
    | ParseRejected(ParseFailure)
    | ParsedType(TypeFragment)
    | ParsedPattern(PatternFragment)
    | ParsedDeclaration(DeclarationFragment)
pub type MacroDiagnostic = MacroDiagnostic(String, Origin, Origins)
    | SyntaxDiagnostic(ParseFailure)
pub type MacroResult = Expanded(Syntax)
    | Rejected(MacroDiagnostic)

pub opaque type TypeFragment = HiddenTypeFragment
pub opaque type PatternFragment = HiddenPatternFragment
pub opaque type DeclarationFragment = HiddenDeclarationFragment
pub type Captures = NoCaptures
    | MoreCaptures(Capture, Captures)

pub effect Ops {
    capture : (Input, Int) -> CaptureResult
    invocation_origin : Input -> Origin
    definition_origin : Input -> Origin
    token_kind : Token -> TokenKind
    token_spelling : Token -> String
    identifier_spelling : Identifier -> String
    expression_syntax : ExpressionFragment -> Syntax
    make_token : (TokenKind, String) -> TokenResult
    parse_expression : (Input, Syntax) -> ParseResult
    fresh_identifier : (Input, String, Origin) -> IdentifierResult
    definition_identifier : (Input, String, Origin) -> IdentifierResult
    caller_identifier : (Input, String, Origin) -> IdentifierResult
    combine_origins : (Input, Origins) -> OriginsResult
    declaration_syntax : DeclarationFragment -> Syntax
    type_syntax : TypeFragment -> Syntax
    parse_type : (Input, Syntax) -> ParseResult
    pattern_syntax : PatternFragment -> Syntax
    parse_pattern : (Input, Syntax) -> ParseResult
}

pub capture : (Input, Int) -> CaptureResult ! {Ops}
capture value = perform Ops.capture value
pub invocation_origin : Input -> Origin ! {Ops}
invocation_origin value = perform Ops.invocation_origin value
pub definition_origin : Input -> Origin ! {Ops}
definition_origin value = perform Ops.definition_origin value
pub token_kind : Token -> TokenKind ! {Ops}
token_kind value = perform Ops.token_kind value
pub token_spelling : Token -> String ! {Ops}
token_spelling value = perform Ops.token_spelling value
pub identifier_spelling : Identifier -> String ! {Ops}
identifier_spelling value = perform Ops.identifier_spelling value
pub expression_syntax : ExpressionFragment -> Syntax ! {Ops}
expression_syntax value = perform Ops.expression_syntax value
pub make_token : (TokenKind, String) -> TokenResult ! {Ops}
make_token value = perform Ops.make_token value
pub parse_expression : (Input, Syntax) -> ParseResult ! {Ops}
parse_expression value = perform Ops.parse_expression value
pub fresh_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
fresh_identifier value = perform Ops.fresh_identifier value
pub definition_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
definition_identifier value = perform Ops.definition_identifier value
pub caller_identifier : (Input, String, Origin) -> IdentifierResult ! {Ops}
caller_identifier value = perform Ops.caller_identifier value
pub combine_origins : (Input, Origins) -> OriginsResult ! {Ops}
combine_origins value = perform Ops.combine_origins value
pub declaration_syntax : DeclarationFragment -> Syntax ! {Ops}
declaration_syntax value = perform Ops.declaration_syntax value
pub type_syntax : TypeFragment -> Syntax ! {Ops}
type_syntax value = perform Ops.type_syntax value
pub parse_type : (Input, Syntax) -> ParseResult ! {Ops}
parse_type value = perform Ops.parse_type value
pub pattern_syntax : PatternFragment -> Syntax ! {Ops}
pattern_syntax value = perform Ops.pattern_syntax value
pub parse_pattern : (Input, Syntax) -> ParseResult ! {Ops}
parse_pattern value = perform Ops.parse_pattern value
