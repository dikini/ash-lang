//! Monomorphic data, tuple, and pattern pipeline used by CP-0003 sources.
//!
//! The retained first-stratum pipeline remains unchanged for sources that do
//! not use the increment. This module keeps the increment's parse, resolution,
//! static, validation, and evaluation boundaries explicit while the shared
//! public representations converge.

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use crate::{
    driver::Observation,
    integer::Integer,
    lexer::{Token, TokenKind, lex},
    source::{SourceFile, SourceId, Span},
    types::{ConstructorId, NominalTypeId, Type, same_type},
};

/// Reports whether a source needs the CP-0003 grammar.
#[must_use]
pub fn uses_extended_syntax(text: &str) -> bool {
    text.lines().any(|line| {
        let code = line.split_once("//").map_or(line, |(code, _)| code);
        code.contains(',')
            || code.contains('|')
            || code.contains("=>")
            || code
                .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
                .any(|word| {
                    word == "type"
                        || word == "match"
                        || word == "_"
                        || (word.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
                            && !matches!(word, "Int" | "Bool" | "Unit"))
                })
    })
}

/// Stage that owns an extended-pipeline source rejection or internal failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExtendedStage {
    /// Lexical or grammatical source rejection.
    Syntax,
    /// Type or constructor name-resolution rejection.
    Resolution,
    /// Static typing, patterns, coverage, or recursive-safety rejection.
    Typing,
    /// Independently detected compiler representation failure.
    Validation,
    /// Runtime invariant failure.
    Runtime,
}

/// A stable structured failure from the data-and-pattern pipeline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtendedFailure {
    /// Owning pipeline stage.
    pub stage: ExtendedStage,
    /// Stable diagnostic reason.
    pub reason: &'static str,
    /// Plain-language primary explanation.
    pub message: String,
    /// Exact primary source span when the owning stage has one.
    pub primary: Option<Span>,
}

impl ExtendedFailure {
    fn source(stage: ExtendedStage, reason: &'static str, message: impl Into<String>) -> Self {
        Self {
            stage,
            reason,
            message: message.into(),
            primary: None,
        }
    }

    fn at(mut self, span: Span) -> Self {
        self.primary = Some(span);
        self
    }

    /// Reports whether this failure rejects source rather than compiler state.
    #[must_use]
    pub const fn is_source_rejection(&self) -> bool {
        matches!(
            self.stage,
            ExtendedStage::Syntax | ExtendedStage::Resolution | ExtendedStage::Typing
        )
    }
}

impl fmt::Display for ExtendedFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}\n{}", self.reason, self.message)
    }
}

impl Error for ExtendedFailure {}

#[derive(Clone, Debug)]
struct Program {
    types: Vec<TypeDeclaration>,
    globals: Vec<Global>,
    result: Expr,
}

#[derive(Clone, Debug)]
struct TypeDeclaration {
    name: String,
    constructors: Vec<ConstructorDeclaration>,
}

#[derive(Clone, Debug)]
struct ConstructorDeclaration {
    name: String,
    fields: Vec<SurfaceType>,
}

#[derive(Clone, Debug)]
enum Global {
    Equational {
        name: String,
        annotation: SurfaceType,
        clauses: Vec<Clause>,
    },
    Operational {
        name: String,
        parameters: Vec<(Pattern, SurfaceType)>,
        result: SurfaceType,
        body: Expr,
    },
}

#[derive(Clone, Debug)]
struct Clause {
    patterns: Vec<Pattern>,
    body: Expr,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum SurfaceType {
    Int,
    Bool,
    Unit,
    Named(String),
    Tuple(Vec<Self>),
    Function(Box<Self>, Box<Self>),
}

#[derive(Clone, Debug)]
enum Expr {
    Integer(Integer),
    Boolean(bool),
    Unit,
    Name(String),
    Tuple(Vec<Self>),
    Apply(Box<Self>, Box<Self>),
    Add(Box<Self>, Box<Self>),
    Multiply(Box<Self>, Box<Self>),
    Equal(Box<Self>, Box<Self>),
    Function(Pattern, Box<Self>),
    Block(Vec<LocalDeclaration>, Box<Self>),
    Match(Box<Self>, Vec<Arm>),
}

#[derive(Clone, Debug)]
enum LocalDeclaration {
    Binding {
        pattern: Pattern,
        annotation: Option<SurfaceType>,
        initializer: Expr,
    },
    Recursive(Vec<RecursiveMember>),
}

#[derive(Clone, Debug)]
struct RecursiveMember {
    name: String,
    annotation: SurfaceType,
    initializer: Expr,
}

#[derive(Clone, Debug)]
struct Arm {
    pattern: Pattern,
    body: Expr,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Pattern {
    Binder(String),
    Wildcard,
    Boolean(bool),
    Unit,
    Tuple(Vec<Self>),
    Constructor(String, Option<Box<Self>>),
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    fn parse_program(&mut self) -> Result<Program, ExtendedFailure> {
        self.skip_lines();
        let mut types = Vec::new();
        while self.at(&TokenKind::Type) {
            types.push(self.parse_type_declaration()?);
            self.skip_lines();
        }
        let mut globals = Vec::new();
        while self.starts_global() {
            globals.push(self.parse_global()?);
            self.skip_lines();
        }
        if self.at(&TokenKind::EndOfFile) {
            return Err(self.syntax(
                "parse.expected-result",
                "the file requires a result expression",
            ));
        }
        let result = self.parse_expression()?;
        self.skip_lines();
        self.expect(&TokenKind::EndOfFile, "end of input")?;
        Ok(Program {
            types,
            globals,
            result,
        })
    }

    fn parse_type_declaration(&mut self) -> Result<TypeDeclaration, ExtendedFailure> {
        self.bump();
        let name = self.take_upper("a nominal type name")?;
        self.expect(&TokenKind::Equal, "=")?;
        self.skip_lines();
        let mut constructors = Vec::new();
        constructors.push(self.parse_constructor_declaration()?);
        while self.at(&TokenKind::LineEnd) && self.nth_is(1, &TokenKind::Pipe) {
            self.bump();
            self.bump();
            constructors.push(self.parse_constructor_declaration()?);
        }
        if constructors.is_empty() {
            return Err(self.syntax(
                "parse.empty-type-declaration",
                "a type declaration needs a constructor",
            ));
        }
        Ok(TypeDeclaration { name, constructors })
    }

    fn parse_constructor_declaration(&mut self) -> Result<ConstructorDeclaration, ExtendedFailure> {
        let name = self.take_upper("a constructor name")?;
        let mut fields = Vec::new();
        if self.at(&TokenKind::LeftParen) {
            self.bump();
            if self.at(&TokenKind::RightParen) {
                return Err(self.syntax(
                    "parse.constructor-payload",
                    "a constructor payload cannot use empty parentheses",
                ));
            }
            fields.push(self.parse_type()?);
            while self.at(&TokenKind::Comma) {
                self.bump();
                fields.push(self.parse_type()?);
            }
            self.expect(&TokenKind::RightParen, ")")?;
        }
        Ok(ConstructorDeclaration { name, fields })
    }

    fn starts_global(&self) -> bool {
        matches!(
            (self.current(), self.nth(1)),
            (Some(TokenKind::Identifier(_)), Some(TokenKind::Colon))
                | (Some(TokenKind::Fn), Some(TokenKind::Identifier(_)))
        )
    }

    fn parse_global(&mut self) -> Result<Global, ExtendedFailure> {
        if self.at(&TokenKind::Fn) {
            self.parse_operational_global()
        } else {
            self.parse_equational_global()
        }
    }

    fn parse_equational_global(&mut self) -> Result<Global, ExtendedFailure> {
        let name = self.take_identifier("a global name")?;
        self.expect(&TokenKind::Colon, ":")?;
        let annotation = self.parse_type()?;
        self.require_line()?;
        let mut clauses = Vec::new();
        loop {
            let clause_name = self.take_identifier("an equation name")?;
            if clause_name != name {
                return Err(ExtendedFailure::source(
                    ExtendedStage::Resolution,
                    "resolve.equation-name-mismatch",
                    format!("equation `{clause_name}` does not match interface `{name}`"),
                ));
            }
            let mut patterns = Vec::new();
            while !self.at(&TokenKind::Equal) {
                if self.at(&TokenKind::LineEnd) || self.at(&TokenKind::EndOfFile) {
                    return Err(self.syntax("parse.expected-form", "an equation requires ="));
                }
                patterns.push(self.parse_pattern()?);
            }
            self.bump();
            let body = self.parse_expression()?;
            clauses.push(Clause { patterns, body });
            if !self.at(&TokenKind::LineEnd) {
                break;
            }
            self.bump();
            if !self.looks_like_equation(&name) {
                break;
            }
        }
        Ok(Global::Equational {
            name,
            annotation,
            clauses,
        })
    }

    fn looks_like_equation(&self, expected_name: &str) -> bool {
        if !matches!(self.current(), Some(TokenKind::Identifier(name)) if name == expected_name) {
            return false;
        }
        let mut offset = 1;
        let mut depth = 0_usize;
        loop {
            match self.nth(offset) {
                Some(TokenKind::LeftParen) => depth += 1,
                Some(TokenKind::RightParen) => depth = depth.saturating_sub(1),
                Some(TokenKind::Equal) if depth == 0 => return true,
                Some(TokenKind::LineEnd | TokenKind::EndOfFile) if depth == 0 => return false,
                Some(_) => {}
                None => return false,
            }
            offset += 1;
        }
    }

    fn parse_operational_global(&mut self) -> Result<Global, ExtendedFailure> {
        self.bump();
        let name = self.take_identifier("a global function name")?;
        self.expect(&TokenKind::LeftParen, "(")?;
        let mut parameters = Vec::new();
        if !self.at(&TokenKind::RightParen) {
            loop {
                let pattern = self.parse_pattern()?;
                self.expect(&TokenKind::Colon, ":")?;
                let ty = self.parse_type()?;
                parameters.push((pattern, ty));
                if !self.at(&TokenKind::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&TokenKind::RightParen, ")")?;
        self.expect(&TokenKind::Arrow, "->")?;
        let result = self.parse_type()?;
        let body = self.parse_block()?;
        Ok(Global::Operational {
            name,
            parameters,
            result,
            body,
        })
    }

    fn parse_type(&mut self) -> Result<SurfaceType, ExtendedFailure> {
        let domain = self.parse_atomic_type()?;
        if self.at(&TokenKind::Arrow) {
            self.bump();
            let codomain = self.parse_type()?;
            Ok(SurfaceType::Function(Box::new(domain), Box::new(codomain)))
        } else {
            Ok(domain)
        }
    }

    fn parse_atomic_type(&mut self) -> Result<SurfaceType, ExtendedFailure> {
        match self.current() {
            Some(TokenKind::IntType) => {
                self.bump();
                Ok(SurfaceType::Int)
            }
            Some(TokenKind::BoolType) => {
                self.bump();
                Ok(SurfaceType::Bool)
            }
            Some(TokenKind::UnitType) => {
                self.bump();
                Ok(SurfaceType::Unit)
            }
            Some(TokenKind::UpperIdentifier(name)) => {
                let name = name.clone();
                self.bump();
                Ok(SurfaceType::Named(name))
            }
            Some(TokenKind::LeftParen) => {
                self.bump();
                let first = self.parse_type()?;
                if self.at(&TokenKind::Comma) {
                    let mut elements = vec![first];
                    while self.at(&TokenKind::Comma) {
                        self.bump();
                        elements.push(self.parse_type()?);
                    }
                    self.expect(&TokenKind::RightParen, ")")?;
                    Ok(SurfaceType::Tuple(elements))
                } else {
                    self.expect(&TokenKind::RightParen, ")")?;
                    Ok(first)
                }
            }
            _ => Err(self.syntax("parse.expected-type", "a type is required")),
        }
    }

    fn parse_expression(&mut self) -> Result<Expr, ExtendedFailure> {
        match self.current() {
            Some(TokenKind::LeftBrace) => self.parse_block(),
            Some(TokenKind::Fn) => self.parse_function(),
            Some(TokenKind::Match) => self.parse_match(),
            _ => self.parse_precedence(0),
        }
    }

    fn parse_precedence(&mut self, minimum: u8) -> Result<Expr, ExtendedFailure> {
        let mut left = self.parse_primary()?;
        loop {
            if self.starts_primary() && 40 >= minimum {
                let right = self.parse_precedence(41)?;
                left = Expr::Apply(Box::new(left), Box::new(right));
                continue;
            }
            let (precedence, operation) = match self.current() {
                Some(TokenKind::EqualEqual) => (10, 0),
                Some(TokenKind::Plus) => (20, 1),
                Some(TokenKind::Star) => (30, 2),
                _ => break,
            };
            if precedence < minimum {
                break;
            }
            self.bump();
            let right = self.parse_precedence(precedence + 1)?;
            left = match operation {
                0 => Expr::Equal(Box::new(left), Box::new(right)),
                1 => Expr::Add(Box::new(left), Box::new(right)),
                _ => Expr::Multiply(Box::new(left), Box::new(right)),
            };
        }
        Ok(left)
    }

    fn parse_primary(&mut self) -> Result<Expr, ExtendedFailure> {
        match self.current() {
            Some(TokenKind::Integer(value)) => {
                let value = value.clone();
                self.bump();
                Ok(Expr::Integer(value))
            }
            Some(TokenKind::True) => {
                self.bump();
                Ok(Expr::Boolean(true))
            }
            Some(TokenKind::False) => {
                self.bump();
                Ok(Expr::Boolean(false))
            }
            Some(TokenKind::Identifier(name) | TokenKind::UpperIdentifier(name)) => {
                let name = name.clone();
                self.bump();
                Ok(Expr::Name(name))
            }
            Some(TokenKind::LeftParen) => self.parse_parenthesized_expression(),
            _ => Err(self.syntax(
                "parse.expected-operand",
                "an expression operand is required",
            )),
        }
    }

    fn parse_parenthesized_expression(&mut self) -> Result<Expr, ExtendedFailure> {
        self.bump();
        if self.at(&TokenKind::RightParen) {
            self.bump();
            return Ok(Expr::Unit);
        }
        let first = self.parse_expression()?;
        if self.at(&TokenKind::Comma) {
            let mut elements = vec![first];
            while self.at(&TokenKind::Comma) {
                self.bump();
                elements.push(self.parse_expression()?);
            }
            self.expect(&TokenKind::RightParen, ")")?;
            Ok(Expr::Tuple(elements))
        } else {
            self.expect(&TokenKind::RightParen, ")")?;
            Ok(first)
        }
    }

    fn parse_function(&mut self) -> Result<Expr, ExtendedFailure> {
        self.bump();
        self.expect(&TokenKind::LeftParen, "(")?;
        let first = self.parse_pattern()?;
        let pattern = if self.at(&TokenKind::Comma) {
            let mut patterns = vec![first];
            while self.at(&TokenKind::Comma) {
                self.bump();
                patterns.push(self.parse_pattern()?);
            }
            Pattern::Tuple(patterns)
        } else {
            first
        };
        self.expect(&TokenKind::RightParen, ")")?;
        let body = self.parse_block()?;
        Ok(Expr::Function(pattern, Box::new(body)))
    }

    fn parse_match(&mut self) -> Result<Expr, ExtendedFailure> {
        self.bump();
        let scrutinee = self.parse_expression()?;
        self.expect(&TokenKind::LeftBrace, "{")?;
        self.skip_lines();
        let mut arms = Vec::new();
        while !self.at(&TokenKind::RightBrace) && !self.at(&TokenKind::EndOfFile) {
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::FatArrow, "=>")?;
            let body = self.parse_expression()?;
            arms.push(Arm { pattern, body });
            if self.at(&TokenKind::LineEnd) {
                self.skip_lines();
            } else if !self.at(&TokenKind::RightBrace) {
                return Err(self.syntax("parse.expected-line-end", "match arms are line-delimited"));
            }
        }
        self.expect(&TokenKind::RightBrace, "}")?;
        if arms.is_empty() {
            return Err(self.syntax("parse.empty-match", "a match needs at least one arm"));
        }
        Ok(Expr::Match(Box::new(scrutinee), arms))
    }

    fn parse_block(&mut self) -> Result<Expr, ExtendedFailure> {
        self.expect(&TokenKind::LeftBrace, "{")?;
        self.skip_lines();
        let mut declarations = Vec::new();
        while self.at(&TokenKind::Let) {
            self.bump();
            if self.at(&TokenKind::Rec) {
                self.bump();
                let mut members = vec![self.parse_recursive_member()?];
                while self.at(&TokenKind::LineEnd) && self.nth_is(1, &TokenKind::And) {
                    self.bump();
                    self.bump();
                    members.push(self.parse_recursive_member()?);
                }
                declarations.push(LocalDeclaration::Recursive(members));
            } else {
                let pattern = self.parse_pattern()?;
                let annotation = if self.at(&TokenKind::Colon) {
                    self.bump();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Equal, "=")?;
                let initializer = self.parse_expression()?;
                declarations.push(LocalDeclaration::Binding {
                    pattern,
                    annotation,
                    initializer,
                });
            }
            self.require_line()?;
        }
        let result = self.parse_expression()?;
        self.skip_lines();
        self.expect(&TokenKind::RightBrace, "}")?;
        Ok(Expr::Block(declarations, Box::new(result)))
    }

    fn parse_recursive_member(&mut self) -> Result<RecursiveMember, ExtendedFailure> {
        let name = self.take_identifier("a recursive member name")?;
        self.expect(&TokenKind::Colon, ":")?;
        let annotation = self.parse_type()?;
        self.expect(&TokenKind::Equal, "=")?;
        let initializer = self.parse_expression()?;
        Ok(RecursiveMember {
            name,
            annotation,
            initializer,
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ExtendedFailure> {
        self.parse_pattern_inner(false)
    }

    fn parse_pattern_inner(
        &mut self,
        allow_juxtaposed_constructor_payload: bool,
    ) -> Result<Pattern, ExtendedFailure> {
        match self.current() {
            Some(TokenKind::Identifier(name)) => {
                let name = name.clone();
                self.bump();
                Ok(Pattern::Binder(name))
            }
            Some(TokenKind::Wildcard) => {
                self.bump();
                Ok(Pattern::Wildcard)
            }
            Some(TokenKind::True) => {
                self.bump();
                Ok(Pattern::Boolean(true))
            }
            Some(TokenKind::False) => {
                self.bump();
                Ok(Pattern::Boolean(false))
            }
            Some(TokenKind::UpperIdentifier(name)) => {
                let name = name.clone();
                self.bump();
                let payload = if self.at(&TokenKind::LeftParen) {
                    self.bump();
                    let first = self.parse_pattern()?;
                    let pattern = if self.at(&TokenKind::Comma) {
                        let mut patterns = vec![first];
                        while self.at(&TokenKind::Comma) {
                            self.bump();
                            patterns.push(self.parse_pattern()?);
                        }
                        Pattern::Tuple(patterns)
                    } else {
                        first
                    };
                    self.expect(&TokenKind::RightParen, ")")?;
                    Some(Box::new(pattern))
                } else if allow_juxtaposed_constructor_payload && self.starts_pattern() {
                    Some(Box::new(self.parse_pattern_inner(true)?))
                } else {
                    None
                };
                Ok(Pattern::Constructor(name, payload))
            }
            Some(TokenKind::LeftParen) => {
                self.bump();
                if self.at(&TokenKind::RightParen) {
                    self.bump();
                    return Ok(Pattern::Unit);
                }
                let first = self.parse_pattern_inner(true)?;
                if self.at(&TokenKind::Comma) {
                    let mut patterns = vec![first];
                    while self.at(&TokenKind::Comma) {
                        self.bump();
                        patterns.push(self.parse_pattern()?);
                    }
                    self.expect(&TokenKind::RightParen, ")")?;
                    Ok(Pattern::Tuple(patterns))
                } else {
                    self.expect(&TokenKind::RightParen, ")")?;
                    Ok(first)
                }
            }
            Some(TokenKind::Integer(_)) => Err(self.syntax(
                "parse.integer-pattern",
                "integer patterns are not available",
            )),
            _ => Err(self.syntax("parse.expected-pattern", "a pattern is required")),
        }
    }

    fn starts_pattern(&self) -> bool {
        matches!(
            self.current(),
            Some(
                TokenKind::Identifier(_)
                    | TokenKind::Wildcard
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::UpperIdentifier(_)
                    | TokenKind::LeftParen
            )
        )
    }

    fn starts_primary(&self) -> bool {
        matches!(
            self.current(),
            Some(
                TokenKind::Integer(_)
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::Identifier(_)
                    | TokenKind::UpperIdentifier(_)
                    | TokenKind::LeftParen
            )
        )
    }

    fn current(&self) -> Option<&TokenKind> {
        self.tokens.get(self.position).map(|token| &token.kind)
    }

    fn nth(&self, distance: usize) -> Option<&TokenKind> {
        self.tokens
            .get(self.position.saturating_add(distance))
            .map(|token| &token.kind)
    }

    fn nth_is(&self, distance: usize, expected: &TokenKind) -> bool {
        self.nth(distance).is_some_and(|actual| {
            std::mem::discriminant(actual) == std::mem::discriminant(expected)
        })
    }

    fn at(&self, expected: &TokenKind) -> bool {
        self.nth_is(0, expected)
    }

    fn bump(&mut self) {
        self.position = self.position.saturating_add(1);
    }

    fn expect(&mut self, expected: &TokenKind, description: &str) -> Result<(), ExtendedFailure> {
        if self.at(expected) {
            self.bump();
            Ok(())
        } else {
            Err(self.syntax(
                "parse.expected-form",
                format!("expected {description}, found {:?}", self.current()),
            ))
        }
    }

    fn take_identifier(&mut self, description: &str) -> Result<String, ExtendedFailure> {
        let Some(TokenKind::Identifier(name)) = self.current() else {
            return Err(self.syntax(
                "parse.expected-identifier",
                format!("expected {description}"),
            ));
        };
        let name = name.clone();
        self.bump();
        Ok(name)
    }

    fn take_upper(&mut self, description: &str) -> Result<String, ExtendedFailure> {
        let Some(TokenKind::UpperIdentifier(name)) = self.current() else {
            return Err(self.syntax(
                "parse.expected-uppercase-identifier",
                format!("expected {description}"),
            ));
        };
        let name = name.clone();
        self.bump();
        Ok(name)
    }

    fn skip_lines(&mut self) {
        while self.at(&TokenKind::LineEnd) {
            self.bump();
        }
    }

    fn require_line(&mut self) -> Result<(), ExtendedFailure> {
        if self.at(&TokenKind::LineEnd) {
            self.bump();
            Ok(())
        } else {
            Err(self.syntax("parse.expected-line-end", "a logical line end is required"))
        }
    }

    fn syntax(&self, reason: &'static str, message: impl Into<String>) -> ExtendedFailure {
        let failure = ExtendedFailure::source(ExtendedStage::Syntax, reason, message);
        self.tokens
            .get(self.position)
            .map_or(failure.clone(), |token| failure.at(token.span))
    }
}

/// Immutable nominal and constructor metadata carried across the extended
/// resolved, checked, and runtime boundaries.
#[derive(Clone, Debug)]
pub struct Registry {
    source: SourceId,
    types: Arc<[TypeInfo]>,
    constructors: Arc<[ConstructorInfo]>,
    type_names: Arc<HashMap<String, NominalTypeId>>,
    constructor_names: Arc<HashMap<String, ConstructorId>>,
}

/// Metadata for one nonempty nominal sum.
#[derive(Clone, Debug)]
pub struct TypeInfo {
    /// Stable nominal identity.
    pub id: NominalTypeId,
    /// Source spelling.
    pub name: String,
    /// Constructors in declaration order.
    pub constructors: Box<[ConstructorId]>,
}

/// Metadata for one globally visible constructor value.
#[derive(Clone, Debug)]
pub struct ConstructorInfo {
    /// Stable constructor identity.
    pub id: ConstructorId,
    /// Nominal owner.
    pub owner: NominalTypeId,
    /// Source spelling.
    pub name: String,
    /// Zero or one semantic payload type.
    pub payload: Option<Type>,
}

impl Registry {
    fn resolve(program: &Program, source: SourceId) -> Result<Self, ExtendedFailure> {
        let mut type_names = HashMap::new();
        for (index, declaration) in program.types.iter().enumerate() {
            let declaration_index = u32::try_from(index).map_err(|_| {
                ExtendedFailure::source(
                    ExtendedStage::Resolution,
                    "resolve.type-id-exhausted",
                    "the source contains too many type declarations",
                )
            })?;
            let id = NominalTypeId::new(source, declaration_index);
            if type_names.insert(declaration.name.clone(), id).is_some() {
                return Err(ExtendedFailure::source(
                    ExtendedStage::Resolution,
                    "resolve.duplicate-type",
                    format!("type `{}` is declared more than once", declaration.name),
                ));
            }
        }

        let mut constructor_names = HashMap::new();
        let mut constructors = Vec::new();
        let mut types = Vec::with_capacity(program.types.len());
        for declaration in &program.types {
            let owner = type_names[&declaration.name];
            if declaration.constructors.is_empty() {
                return Err(ExtendedFailure::source(
                    ExtendedStage::Resolution,
                    "resolve.empty-type",
                    format!("type `{}` needs at least one constructor", declaration.name),
                ));
            }
            let mut owned = Vec::with_capacity(declaration.constructors.len());
            for (index, constructor) in declaration.constructors.iter().enumerate() {
                let constructor_index = u32::try_from(index).map_err(|_| {
                    ExtendedFailure::source(
                        ExtendedStage::Resolution,
                        "resolve.constructor-id-exhausted",
                        "a type contains too many constructors",
                    )
                })?;
                let id = ConstructorId::new(owner, constructor_index);
                if constructor_names
                    .insert(constructor.name.clone(), id)
                    .is_some()
                {
                    return Err(ExtendedFailure::source(
                        ExtendedStage::Resolution,
                        "resolve.duplicate-constructor",
                        format!(
                            "constructor `{}` is declared more than once",
                            constructor.name
                        ),
                    ));
                }
                owned.push(id);
                constructors.push((id, constructor));
            }
            types.push(TypeInfo {
                id: owner,
                name: declaration.name.clone(),
                constructors: owned.into_boxed_slice(),
            });
        }

        let mut registry = Self {
            source,
            types: types.into(),
            constructors: Arc::from([]),
            type_names: Arc::new(type_names),
            constructor_names: Arc::new(constructor_names),
        };
        let mut resolved_constructors = Vec::with_capacity(constructors.len());
        for (id, constructor) in constructors {
            let fields = constructor
                .fields
                .iter()
                .map(|field| registry.resolve_type(field))
                .collect::<Result<Vec<_>, _>>()?;
            let payload = match fields.len() {
                0 => None,
                1 => fields.into_iter().next(),
                _ => Some(Type::Tuple(fields.into_boxed_slice())),
            };
            resolved_constructors.push(ConstructorInfo {
                id,
                owner: id.owner(),
                name: constructor.name.clone(),
                payload,
            });
        }
        registry.constructors = resolved_constructors.into();
        Ok(registry)
    }

    fn resolve_type(&self, surface: &SurfaceType) -> Result<Type, ExtendedFailure> {
        match surface {
            SurfaceType::Int => Ok(Type::Int),
            SurfaceType::Bool => Ok(Type::Bool),
            SurfaceType::Unit => Ok(Type::Unit),
            SurfaceType::Named(name) => self
                .type_names
                .get(name)
                .copied()
                .map(Type::Nominal)
                .ok_or_else(|| {
                    ExtendedFailure::source(
                        ExtendedStage::Resolution,
                        "resolve.unknown-type",
                        format!("type `{name}` is not declared in this file"),
                    )
                }),
            SurfaceType::Tuple(elements) => {
                if elements.len() < 2 {
                    return Err(ExtendedFailure::source(
                        ExtendedStage::Resolution,
                        "resolve.tuple-arity",
                        "a tuple type needs at least two elements",
                    ));
                }
                Ok(Type::Tuple(
                    elements
                        .iter()
                        .map(|element| self.resolve_type(element))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_boxed_slice(),
                ))
            }
            SurfaceType::Function(domain, codomain) => Ok(Type::Function(
                Box::new(self.resolve_type(domain)?),
                Box::new(self.resolve_type(codomain)?),
            )),
        }
    }

    /// Returns the source identity that owns every nominal identity here.
    #[must_use]
    pub const fn source(&self) -> SourceId {
        self.source
    }

    /// Returns nominal declarations in source order.
    #[must_use]
    pub fn types(&self) -> &[TypeInfo] {
        &self.types
    }

    /// Returns constructor declarations in owner and declaration order.
    #[must_use]
    pub fn constructors(&self) -> &[ConstructorInfo] {
        &self.constructors
    }

    /// Looks up a nominal declaration by stable identity.
    #[must_use]
    pub fn type_info(&self, id: NominalTypeId) -> Option<&TypeInfo> {
        if id.source() != self.source {
            return None;
        }
        self.types.get(usize::try_from(id.declaration()).ok()?)
    }

    /// Looks up a constructor declaration by stable identity.
    #[must_use]
    pub fn constructor(&self, id: ConstructorId) -> Option<&ConstructorInfo> {
        self.constructors
            .iter()
            .find(|constructor| constructor.id == id)
    }

    /// Looks up a globally visible constructor by source spelling.
    #[must_use]
    pub fn constructor_named(&self, name: &str) -> Option<&ConstructorInfo> {
        self.constructor(*self.constructor_names.get(name)?)
    }

    fn validate(&self) -> Result<(), ExtendedFailure> {
        let invalid =
            |reason, message| ExtendedFailure::source(ExtendedStage::Validation, reason, message);
        let mut declared_constructors = HashSet::new();
        for (declaration, info) in self.types.iter().enumerate() {
            let Ok(declaration) = u32::try_from(declaration) else {
                return Err(invalid(
                    "validation.type-identity",
                    "a nominal declaration index does not fit its identity",
                ));
            };
            if info.id != NominalTypeId::new(self.source, declaration)
                || self.type_names.get(&info.name) != Some(&info.id)
            {
                return Err(invalid(
                    "validation.type-identity",
                    "nominal registry identity or name mapping is inconsistent",
                ));
            }
            if info.constructors.is_empty() {
                return Err(invalid(
                    "validation.empty-type",
                    "a nominal declaration has no constructor",
                ));
            }
            for (index, id) in info.constructors.iter().copied().enumerate() {
                let Ok(index) = u32::try_from(index) else {
                    return Err(invalid(
                        "validation.constructor-identity",
                        "a constructor index does not fit its identity",
                    ));
                };
                if id != ConstructorId::new(info.id, index) || !declared_constructors.insert(id) {
                    return Err(invalid(
                        "validation.constructor-identity",
                        "constructor ownership or identity is inconsistent",
                    ));
                }
            }
        }
        if declared_constructors.len() != self.constructors.len() {
            return Err(invalid(
                "validation.registry-closure",
                "the nominal and constructor registries do not contain the same identities",
            ));
        }
        for constructor in self.constructors.iter() {
            if constructor.owner != constructor.id.owner()
                || !declared_constructors.contains(&constructor.id)
                || self.constructor_names.get(&constructor.name) != Some(&constructor.id)
            {
                return Err(invalid(
                    "validation.constructor-identity",
                    "constructor metadata is inconsistent with its owner or name mapping",
                ));
            }
            let mut pending = constructor.payload.iter().collect::<Vec<_>>();
            while let Some(ty) = pending.pop() {
                match ty {
                    Type::Nominal(id) if self.type_info(*id).is_none() => {
                        return Err(invalid(
                            "validation.foreign-type",
                            "a constructor payload refers outside its registry",
                        ));
                    }
                    Type::Tuple(elements) if elements.len() < 2 => {
                        return Err(invalid(
                            "validation.tuple-arity",
                            "a constructor payload contains an invalid tuple type",
                        ));
                    }
                    Type::Tuple(elements) => pending.extend(elements),
                    Type::Function(domain, codomain) => {
                        pending.push(codomain);
                        pending.push(domain);
                    }
                    Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
                }
            }
        }
        Ok(())
    }

    fn type_display(&self, ty: &Type) -> String {
        fn render(registry: &Registry, ty: &Type, output: &mut String, domain: bool) {
            match ty {
                Type::Int => output.push_str("Int"),
                Type::Bool => output.push_str("Bool"),
                Type::Unit => output.push_str("Unit"),
                Type::Nominal(id) => output.push_str(
                    registry
                        .type_info(*id)
                        .map_or("<foreign-type>", |info| info.name.as_str()),
                ),
                Type::Tuple(elements) => {
                    output.push('(');
                    for (index, element) in elements.iter().enumerate() {
                        if index > 0 {
                            output.push_str(", ");
                        }
                        render(registry, element, output, false);
                    }
                    output.push(')');
                }
                Type::Function(parameter, result) => {
                    if domain {
                        output.push('(');
                    }
                    render(registry, parameter, output, true);
                    output.push_str(" -> ");
                    render(registry, result, output, false);
                    if domain {
                        output.push(')');
                    }
                }
            }
        }
        let mut output = String::new();
        render(self, ty, &mut output, false);
        output
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum CheckedPattern {
    Binder(String),
    Wildcard,
    Boolean(bool),
    Unit,
    Tuple(Box<[Self]>),
    Constructor(ConstructorId, Option<Box<Self>>),
}

impl CheckedPattern {
    fn is_wildcard(&self) -> bool {
        matches!(self, Self::Binder(_) | Self::Wildcard)
    }
}

/// Structured typed Core for the monomorphic data-and-pattern dialect.
///
/// The registry is immutable and shared by validation, transforms, and
/// evaluation. The contained syntax is private so consumers cannot bypass the
/// validated construction boundary.
#[derive(Clone)]
pub struct ExtendedCoreProgram {
    syntax: Program,
    registry: Arc<Registry>,
    result_type: Type,
}

impl ExtendedCoreProgram {
    /// Returns the immutable nominal and constructor registry.
    #[must_use]
    pub fn registry(&self) -> &Arc<Registry> {
        &self.registry
    }

    /// Returns the checked program-result type.
    #[must_use]
    pub const fn result_type(&self) -> &Type {
        &self.result_type
    }
}

struct Checker {
    registry: Arc<Registry>,
    globals: HashMap<String, Type>,
}

impl Checker {
    fn check(
        syntax: Program,
        registry: Arc<Registry>,
    ) -> Result<ExtendedCoreProgram, ExtendedFailure> {
        let mut globals = HashMap::new();
        for constructor in registry.constructors.iter() {
            let result = Type::Nominal(constructor.owner);
            let ty = constructor
                .payload
                .as_ref()
                .map_or(result.clone(), |payload| {
                    Type::Function(Box::new(payload.clone()), Box::new(result))
                });
            globals.insert(constructor.name.clone(), ty);
        }
        for global in &syntax.globals {
            let (name, ty) = match global {
                Global::Equational {
                    name, annotation, ..
                } => (name, registry.resolve_type(annotation)?),
                Global::Operational {
                    name,
                    parameters,
                    result,
                    ..
                } => {
                    if parameters.is_empty() {
                        return Err(ExtendedFailure::source(
                            ExtendedStage::Typing,
                            "equation.arity",
                            "a function needs at least one parameter",
                        ));
                    }
                    let domains = parameters
                        .iter()
                        .map(|(_, ty)| registry.resolve_type(ty))
                        .collect::<Result<Vec<_>, _>>()?;
                    let domain = if domains.len() == 1 {
                        domains.into_iter().next().expect("one checked domain")
                    } else {
                        Type::Tuple(domains.into_boxed_slice())
                    };
                    let result = registry.resolve_type(result)?;
                    (name, Type::Function(Box::new(domain), Box::new(result)))
                }
            };
            if globals.insert(name.clone(), ty).is_some() {
                return Err(ExtendedFailure::source(
                    ExtendedStage::Typing,
                    "resolve.duplicate-global",
                    format!("global `{name}` is defined more than once"),
                ));
            }
        }

        let checker = Self {
            registry: Arc::clone(&registry),
            globals: globals.clone(),
        };
        for global in &syntax.globals {
            checker.check_global(global)?;
        }
        let result_type = checker.infer_expr(&syntax.result, &globals)?;
        Ok(ExtendedCoreProgram {
            syntax,
            registry,
            result_type,
        })
    }

    fn check_global(&self, global: &Global) -> Result<(), ExtendedFailure> {
        match global {
            Global::Equational { name, clauses, .. } => {
                let function_type = self.globals.get(name).ok_or_else(|| self.internal())?;
                let Some(first) = clauses.first() else {
                    return Err(self.typing("equation.arity", "an equation group needs a clause"));
                };
                let arity = first.patterns.len();
                if arity == 0 || clauses.iter().any(|clause| clause.patterns.len() != arity) {
                    return Err(self.typing(
                        "equation.arity",
                        "contiguous equation clauses must have the same positive pattern count",
                    ));
                }
                let (domains, codomain) =
                    expose_domains(function_type, arity).ok_or_else(|| {
                        self.typing(
                            "equation.arity",
                            "the equation pattern count exceeds its declared arrow layers",
                        )
                    })?;
                let mut checked_rows = Vec::new();
                for clause in clauses {
                    let mut environment = self.globals.clone();
                    let mut row = Vec::new();
                    for (pattern, domain) in clause.patterns.iter().zip(domains.iter()) {
                        let (checked, bindings) = self.check_pattern(pattern, domain)?;
                        environment.extend(bindings);
                        row.push(checked);
                    }
                    if usefulness(&checked_rows, &row, &domains, &self.registry).is_none() {
                        return Err(self.typing(
                            "coverage.redundant-case",
                            "this equation clause cannot match a new input",
                        ));
                    }
                    self.check_expr(&clause.body, &codomain, &environment)?;
                    checked_rows.push(row);
                }
                if let Some(witness) = usefulness(
                    &checked_rows,
                    &vec![CheckedPattern::Wildcard; arity],
                    &domains,
                    &self.registry,
                ) {
                    return Err(self.typing(
                        "coverage.non-exhaustive",
                        format!(
                            "equations do not cover {}",
                            display_witness(&witness, &self.registry)
                        ),
                    ));
                }
                Ok(())
            }
            Global::Operational {
                name,
                parameters,
                body,
                ..
            } => {
                let function_type = self.globals.get(name).ok_or_else(|| self.internal())?;
                let Type::Function(domain, codomain) = function_type else {
                    return Err(self.internal());
                };
                let pattern = if parameters.len() == 1 {
                    parameters[0].0.clone()
                } else {
                    Pattern::Tuple(
                        parameters
                            .iter()
                            .map(|(pattern, _)| pattern.clone())
                            .collect(),
                    )
                };
                let (_, bindings) = self.check_pattern(&pattern, domain)?;
                let mut environment = self.globals.clone();
                environment.extend(bindings);
                self.check_expr(body, codomain, &environment)
            }
        }
    }

    fn infer_expr(
        &self,
        expression: &Expr,
        environment: &HashMap<String, Type>,
    ) -> Result<Type, ExtendedFailure> {
        match expression {
            Expr::Integer(_) => Ok(Type::Int),
            Expr::Boolean(_) => Ok(Type::Bool),
            Expr::Unit => Ok(Type::Unit),
            Expr::Name(name) => environment.get(name).cloned().ok_or_else(|| {
                let reason = if name.as_bytes().first().is_some_and(u8::is_ascii_uppercase) {
                    "resolve.unknown-constructor"
                } else {
                    "resolve.unknown-name"
                };
                ExtendedFailure::source(
                    ExtendedStage::Resolution,
                    reason,
                    format!("`{name}` is not visible here"),
                )
            }),
            Expr::Tuple(elements) => {
                if elements.len() < 2 {
                    return Err(
                        self.typing("type.tuple-arity", "a tuple needs at least two elements")
                    );
                }
                Ok(Type::Tuple(
                    elements
                        .iter()
                        .map(|element| self.infer_expr(element, environment))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_boxed_slice(),
                ))
            }
            Expr::Apply(function, argument) => {
                let function_type = self.infer_expr(function, environment)?;
                let Type::Function(domain, codomain) = function_type else {
                    return Err(self.typing(
                        "type.not-applicable",
                        "the function position is not callable",
                    ));
                };
                self.check_expr(argument, &domain, environment)?;
                Ok(*codomain)
            }
            Expr::Add(left, right) | Expr::Multiply(left, right) => {
                self.check_expr(left, &Type::Int, environment)?;
                self.check_expr(right, &Type::Int, environment)?;
                Ok(Type::Int)
            }
            Expr::Equal(left, right) => {
                self.check_expr(left, &Type::Int, environment)?;
                self.check_expr(right, &Type::Int, environment)?;
                Ok(Type::Bool)
            }
            Expr::Function(_, _) => Err(self.typing(
                "type.function-needs-context",
                "an anonymous function needs an expected function type",
            )),
            Expr::Block(declarations, result) => {
                let mut local = environment.clone();
                for declaration in declarations {
                    match declaration {
                        LocalDeclaration::Binding {
                            pattern,
                            annotation,
                            initializer,
                        } => {
                            let ty = if let Some(annotation) = annotation {
                                let ty = self.registry.resolve_type(annotation)?;
                                self.check_expr(initializer, &ty, &local)?;
                                ty
                            } else {
                                self.infer_expr(initializer, &local)?
                            };
                            let (checked, bindings) = self.check_pattern(pattern, &ty)?;
                            if usefulness(
                                &[],
                                std::slice::from_ref(&checked),
                                std::slice::from_ref(&ty),
                                &self.registry,
                            )
                            .is_none()
                            {
                                return Err(self.internal());
                            }
                            if usefulness(
                                &[vec![checked]],
                                &[CheckedPattern::Wildcard],
                                std::slice::from_ref(&ty),
                                &self.registry,
                            )
                            .is_some()
                            {
                                return Err(self.typing(
                                    "pattern.refutable-binding",
                                    "an unconditional local pattern must be irrefutable",
                                ));
                            }
                            local.extend(bindings);
                        }
                        LocalDeclaration::Recursive(members) => {
                            self.check_recursive_group(members, &mut local)?;
                        }
                    }
                }
                self.infer_expr(result, &local)
            }
            Expr::Match(scrutinee, arms) => {
                let scrutinee_type = self.infer_expr(scrutinee, environment)?;
                let mut rows = Vec::new();
                let mut result_type = None;
                for arm in arms {
                    let (pattern, bindings) = self.check_pattern(&arm.pattern, &scrutinee_type)?;
                    if usefulness(
                        &rows,
                        std::slice::from_ref(&pattern),
                        std::slice::from_ref(&scrutinee_type),
                        &self.registry,
                    )
                    .is_none()
                    {
                        return Err(self.typing(
                            "coverage.redundant-case",
                            "this match arm cannot select a new value",
                        ));
                    }
                    let mut arm_environment = environment.clone();
                    arm_environment.extend(bindings);
                    let arm_type = if let Some(expected) = &result_type {
                        self.check_expr(&arm.body, expected, &arm_environment)?;
                        expected.clone()
                    } else {
                        self.infer_expr(&arm.body, &arm_environment)?
                    };
                    result_type = Some(arm_type);
                    rows.push(vec![pattern]);
                }
                if let Some(witness) = usefulness(
                    &rows,
                    &[CheckedPattern::Wildcard],
                    std::slice::from_ref(&scrutinee_type),
                    &self.registry,
                ) {
                    return Err(self.typing(
                        "coverage.non-exhaustive",
                        format!(
                            "match does not cover {}",
                            display_witness(&witness, &self.registry)
                        ),
                    ));
                }
                result_type
                    .ok_or_else(|| self.typing("coverage.non-exhaustive", "a match needs an arm"))
            }
        }
    }

    fn check_expr(
        &self,
        expression: &Expr,
        expected: &Type,
        environment: &HashMap<String, Type>,
    ) -> Result<(), ExtendedFailure> {
        if let (Expr::Function(pattern, body), Type::Function(domain, codomain)) =
            (expression, expected)
        {
            let (_, bindings) = self.check_pattern(pattern, domain)?;
            let mut local = environment.clone();
            local.extend(bindings);
            return self.check_expr(body, codomain, &local);
        }
        let found = self.infer_expr(expression, environment)?;
        if same_type(&found, expected) {
            Ok(())
        } else {
            Err(self.typing(
                "type.mismatch",
                format!(
                    "expected {}, found {}",
                    self.registry.type_display(expected),
                    self.registry.type_display(&found)
                ),
            ))
        }
    }

    fn check_recursive_group(
        &self,
        members: &[RecursiveMember],
        environment: &mut HashMap<String, Type>,
    ) -> Result<(), ExtendedFailure> {
        let mut names = HashSet::new();
        let mut resolved = Vec::with_capacity(members.len());
        for member in members {
            if !names.insert(member.name.clone()) {
                return Err(self.typing(
                    "resolve.duplicate-recursive-member",
                    format!("recursive member `{}` is repeated", member.name),
                ));
            }
            let ty = self.registry.resolve_type(&member.annotation)?;
            environment.insert(member.name.clone(), ty.clone());
            resolved.push(ty);
        }
        for (member, ty) in members.iter().zip(resolved.iter()) {
            match (&member.initializer, ty) {
                (Expr::Function(_, _), Type::Function(_, _)) => {}
                (_, Type::Nominal(owner)) => {
                    check_guarded_root(&member.initializer, *owner, &names, &self.registry)?;
                }
                _ => {
                    return Err(self.typing(
                        "recursion.unsafe-root",
                        "a recursive member must be a direct function or constructor-rooted data value",
                    ));
                }
            }
            self.check_expr(&member.initializer, ty, environment)?;
        }
        Ok(())
    }

    fn check_pattern(
        &self,
        pattern: &Pattern,
        expected: &Type,
    ) -> Result<(CheckedPattern, HashMap<String, Type>), ExtendedFailure> {
        let mut binders = HashMap::new();
        let checked = self.check_pattern_into(pattern, expected, &mut binders)?;
        Ok((checked, binders))
    }

    fn check_pattern_into(
        &self,
        pattern: &Pattern,
        expected: &Type,
        binders: &mut HashMap<String, Type>,
    ) -> Result<CheckedPattern, ExtendedFailure> {
        match pattern {
            Pattern::Binder(name) => {
                if binders.insert(name.clone(), expected.clone()).is_some() {
                    return Err(self.typing(
                        "pattern.duplicate-binder",
                        format!("pattern binder `{name}` occurs more than once"),
                    ));
                }
                Ok(CheckedPattern::Binder(name.clone()))
            }
            Pattern::Wildcard => Ok(CheckedPattern::Wildcard),
            Pattern::Boolean(value) if *expected == Type::Bool => {
                Ok(CheckedPattern::Boolean(*value))
            }
            Pattern::Unit if *expected == Type::Unit => Ok(CheckedPattern::Unit),
            Pattern::Tuple(patterns) => {
                let Type::Tuple(elements) = expected else {
                    return Err(
                        self.typing("pattern.tuple-type", "a tuple pattern needs a tuple input")
                    );
                };
                if patterns.len() != elements.len() {
                    return Err(self.typing(
                        "pattern.tuple-arity",
                        "tuple pattern arity does not match its input",
                    ));
                }
                Ok(CheckedPattern::Tuple(
                    patterns
                        .iter()
                        .zip(elements.iter())
                        .map(|(pattern, ty)| self.check_pattern_into(pattern, ty, binders))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_boxed_slice(),
                ))
            }
            Pattern::Constructor(name, payload) => {
                let constructor = self.registry.constructor_named(name).ok_or_else(|| {
                    ExtendedFailure::source(
                        ExtendedStage::Resolution,
                        "resolve.unknown-constructor",
                        format!("constructor `{name}` is not declared"),
                    )
                })?;
                if !matches!(expected, Type::Nominal(owner) if *owner == constructor.owner) {
                    return Err(self.typing(
                        "pattern.constructor-owner",
                        format!("constructor `{name}` does not belong to the matched nominal type"),
                    ));
                }
                let checked_payload = match (&constructor.payload, payload) {
                    (None, None) => None,
                    (Some(payload_type), Some(pattern)) => Some(Box::new(
                        self.check_pattern_into(pattern, payload_type, binders)?,
                    )),
                    _ => {
                        return Err(self.typing(
                            "pattern.constructor-payload",
                            format!(
                                "constructor `{name}` payload shape does not match its declaration"
                            ),
                        ));
                    }
                };
                Ok(CheckedPattern::Constructor(constructor.id, checked_payload))
            }
            _ => Err(self.typing(
                "pattern.type-mismatch",
                "pattern does not match its expected type",
            )),
        }
    }

    fn typing(&self, reason: &'static str, message: impl Into<String>) -> ExtendedFailure {
        ExtendedFailure::source(ExtendedStage::Typing, reason, message)
    }

    fn internal(&self) -> ExtendedFailure {
        ExtendedFailure::source(
            ExtendedStage::Validation,
            "internal.extended-validation",
            "the checked extended representation is inconsistent",
        )
    }
}

fn validate_checked(program: &ExtendedCoreProgram) -> Result<(), ExtendedFailure> {
    program.registry.validate()?;
    let rechecked = Checker::check(program.syntax.clone(), Arc::clone(&program.registry)).map_err(
        |failure| {
            ExtendedFailure::source(
                ExtendedStage::Validation,
                "validation.recheck",
                format!("independent validation rejected typed Core: {failure}"),
            )
        },
    )?;
    if !same_type(&program.result_type, &rechecked.result_type) {
        return Err(ExtendedFailure::source(
            ExtendedStage::Validation,
            "validation.result-type",
            "the checked result type disagrees with independent validation",
        ));
    }
    Ok(())
}

fn transform_checked(program: &ExtendedCoreProgram, fold_literals: bool) -> ExtendedCoreProgram {
    fn expression(node: &Expr, fold_literals: bool) -> Expr {
        let rebuilt = match node {
            Expr::Integer(value) => Expr::Integer(value.clone()),
            Expr::Boolean(value) => Expr::Boolean(*value),
            Expr::Unit => Expr::Unit,
            Expr::Name(name) => Expr::Name(name.clone()),
            Expr::Tuple(elements) => Expr::Tuple(
                elements
                    .iter()
                    .map(|element| expression(element, fold_literals))
                    .collect(),
            ),
            Expr::Apply(function, argument) => Expr::Apply(
                Box::new(expression(function, fold_literals)),
                Box::new(expression(argument, fold_literals)),
            ),
            Expr::Add(left, right) => Expr::Add(
                Box::new(expression(left, fold_literals)),
                Box::new(expression(right, fold_literals)),
            ),
            Expr::Multiply(left, right) => Expr::Multiply(
                Box::new(expression(left, fold_literals)),
                Box::new(expression(right, fold_literals)),
            ),
            Expr::Equal(left, right) => Expr::Equal(
                Box::new(expression(left, fold_literals)),
                Box::new(expression(right, fold_literals)),
            ),
            Expr::Function(pattern, body) => {
                Expr::Function(pattern.clone(), Box::new(expression(body, fold_literals)))
            }
            Expr::Block(declarations, result) => Expr::Block(
                declarations
                    .iter()
                    .map(|declaration| match declaration {
                        LocalDeclaration::Binding {
                            pattern,
                            annotation,
                            initializer,
                        } => LocalDeclaration::Binding {
                            pattern: pattern.clone(),
                            annotation: annotation.clone(),
                            initializer: expression(initializer, fold_literals),
                        },
                        LocalDeclaration::Recursive(members) => LocalDeclaration::Recursive(
                            members
                                .iter()
                                .map(|member| RecursiveMember {
                                    name: member.name.clone(),
                                    annotation: member.annotation.clone(),
                                    initializer: expression(&member.initializer, fold_literals),
                                })
                                .collect(),
                        ),
                    })
                    .collect(),
                Box::new(expression(result, fold_literals)),
            ),
            Expr::Match(scrutinee, arms) => Expr::Match(
                Box::new(expression(scrutinee, fold_literals)),
                arms.iter()
                    .map(|arm| Arm {
                        pattern: arm.pattern.clone(),
                        body: expression(&arm.body, fold_literals),
                    })
                    .collect(),
            ),
        };
        if !fold_literals {
            return rebuilt;
        }
        match rebuilt {
            Expr::Add(left, right) => match (*left, *right) {
                (Expr::Integer(left), Expr::Integer(right)) => Expr::Integer(&left + &right),
                (left, right) => Expr::Add(Box::new(left), Box::new(right)),
            },
            Expr::Multiply(left, right) => match (*left, *right) {
                (Expr::Integer(left), Expr::Integer(right)) => Expr::Integer(&left * &right),
                (left, right) => Expr::Multiply(Box::new(left), Box::new(right)),
            },
            other => other,
        }
    }

    let syntax = Program {
        types: program.syntax.types.clone(),
        globals: program
            .syntax
            .globals
            .iter()
            .map(|global| match global {
                Global::Equational {
                    name,
                    annotation,
                    clauses,
                } => Global::Equational {
                    name: name.clone(),
                    annotation: annotation.clone(),
                    clauses: clauses
                        .iter()
                        .map(|clause| Clause {
                            patterns: clause.patterns.clone(),
                            body: expression(&clause.body, fold_literals),
                        })
                        .collect(),
                },
                Global::Operational {
                    name,
                    parameters,
                    result,
                    body,
                } => Global::Operational {
                    name: name.clone(),
                    parameters: parameters.clone(),
                    result: result.clone(),
                    body: expression(body, fold_literals),
                },
            })
            .collect(),
        result: expression(&program.syntax.result, fold_literals),
    };
    ExtendedCoreProgram {
        syntax,
        registry: Arc::clone(&program.registry),
        result_type: program.result_type.clone(),
    }
}

fn expose_domains(function: &Type, count: usize) -> Option<(Vec<Type>, Type)> {
    let mut current = function;
    let mut domains = Vec::with_capacity(count);
    for _ in 0..count {
        let Type::Function(domain, codomain) = current else {
            return None;
        };
        domains.push(domain.as_ref().clone());
        current = codomain;
    }
    Some((domains, current.clone()))
}

fn check_guarded_root(
    expression: &Expr,
    owner: NominalTypeId,
    recursive_names: &HashSet<String>,
    registry: &Registry,
) -> Result<(), ExtendedFailure> {
    let Expr::Apply(function, payload) = expression else {
        return Err(ExtendedFailure::source(
            ExtendedStage::Typing,
            "recursion.unsafe-root",
            "recursive data must be rooted at a fully applied payload constructor",
        ));
    };
    let Expr::Name(name) = function.as_ref() else {
        return Err(ExtendedFailure::source(
            ExtendedStage::Typing,
            "recursion.unsafe-root",
            "recursive data root is not a constructor",
        ));
    };
    let Some(constructor) = registry.constructor_named(name) else {
        return Err(ExtendedFailure::source(
            ExtendedStage::Typing,
            "recursion.unsafe-root",
            "recursive data root is not a known constructor",
        ));
    };
    if constructor.owner != owner || constructor.payload.is_none() {
        return Err(ExtendedFailure::source(
            ExtendedStage::Typing,
            "recursion.unsafe-root",
            "recursive data root does not fully apply a constructor of its declared type",
        ));
    }
    check_guarded_payload(payload, recursive_names, registry)
}

fn check_guarded_payload(
    expression: &Expr,
    recursive_names: &HashSet<String>,
    registry: &Registry,
) -> Result<(), ExtendedFailure> {
    if !contains_recursive_name(expression, recursive_names) {
        return Ok(());
    }
    match expression {
        Expr::Name(name) if recursive_names.contains(name) => Ok(()),
        Expr::Tuple(elements) => {
            for element in elements {
                check_guarded_payload(element, recursive_names, registry)?;
            }
            Ok(())
        }
        Expr::Function(_, _) => Ok(()),
        Expr::Apply(function, payload) => {
            if let Expr::Name(name) = function.as_ref()
                && registry
                    .constructor_named(name)
                    .is_some_and(|constructor| constructor.payload.is_some())
            {
                return check_guarded_payload(payload, recursive_names, registry);
            }
            Err(ExtendedFailure::source(
                ExtendedStage::Typing,
                "recursion.unguarded-use",
                "a recursive occurrence passes through an ordinary call",
            ))
        }
        _ => Err(ExtendedFailure::source(
            ExtendedStage::Typing,
            "recursion.unguarded-use",
            "a recursive occurrence passes through a forcing expression",
        )),
    }
}

fn contains_recursive_name(expression: &Expr, names: &HashSet<String>) -> bool {
    match expression {
        Expr::Name(name) => names.contains(name),
        Expr::Tuple(elements) => elements
            .iter()
            .any(|element| contains_recursive_name(element, names)),
        Expr::Apply(left, right)
        | Expr::Add(left, right)
        | Expr::Multiply(left, right)
        | Expr::Equal(left, right) => {
            contains_recursive_name(left, names) || contains_recursive_name(right, names)
        }
        Expr::Function(_, body) => contains_recursive_name(body, names),
        Expr::Block(declarations, result) => {
            declarations.iter().any(|declaration| match declaration {
                LocalDeclaration::Binding { initializer, .. } => {
                    contains_recursive_name(initializer, names)
                }
                LocalDeclaration::Recursive(members) => members
                    .iter()
                    .any(|member| contains_recursive_name(&member.initializer, names)),
            }) || contains_recursive_name(result, names)
        }
        Expr::Match(scrutinee, arms) => {
            contains_recursive_name(scrutinee, names)
                || arms
                    .iter()
                    .any(|arm| contains_recursive_name(&arm.body, names))
        }
        Expr::Integer(_) | Expr::Boolean(_) | Expr::Unit => false,
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Head {
    Boolean(bool),
    Unit,
    Tuple(usize),
    Constructor(ConstructorId),
}

type UsefulnessState = (Vec<Vec<CheckedPattern>>, Vec<CheckedPattern>, Vec<Type>);

fn usefulness(
    matrix: &[Vec<CheckedPattern>],
    candidate: &[CheckedPattern],
    types: &[Type],
    registry: &Registry,
) -> Option<Vec<CheckedPattern>> {
    let mut active = HashSet::new();
    usefulness_inner(matrix, candidate, types, registry, 256, &mut active)
}

fn usefulness_inner(
    matrix: &[Vec<CheckedPattern>],
    candidate: &[CheckedPattern],
    types: &[Type],
    registry: &Registry,
    fuel: usize,
    active: &mut HashSet<UsefulnessState>,
) -> Option<Vec<CheckedPattern>> {
    if candidate.is_empty() {
        return matrix.is_empty().then(Vec::new);
    }
    if matrix.is_empty() {
        return Some(candidate.to_vec());
    }
    if matrix
        .iter()
        .any(|row| row.iter().all(CheckedPattern::is_wildcard))
    {
        return None;
    }
    if fuel == 0
        || types.len() != candidate.len()
        || matrix.iter().any(|row| row.len() != candidate.len())
    {
        return None;
    }
    let state = (matrix.to_vec(), candidate.to_vec(), types.to_vec());
    if !active.insert(state.clone()) {
        return None;
    }

    let first_type = &types[0];
    let result = if candidate[0].is_wildcard() {
        if let Some(heads) = heads_for_type(first_type, registry) {
            let mut found = None;
            for head in heads {
                let argument_types = head_types(head, first_type, registry);
                let specialized_matrix = specialize_matrix(matrix, head, argument_types.len());
                let mut specialized_candidate =
                    vec![CheckedPattern::Wildcard; argument_types.len()];
                specialized_candidate.extend_from_slice(&candidate[1..]);
                let mut specialized_types = argument_types.clone();
                specialized_types.extend_from_slice(&types[1..]);
                if let Some(mut witness) = usefulness_inner(
                    &specialized_matrix,
                    &specialized_candidate,
                    &specialized_types,
                    registry,
                    fuel - 1,
                    active,
                ) {
                    let arguments = witness.drain(..argument_types.len()).collect::<Vec<_>>();
                    let mut rebuilt = vec![pattern_from_head(head, arguments)];
                    rebuilt.extend(witness);
                    found = Some(rebuilt);
                    break;
                }
            }
            found
        } else {
            let default = matrix
                .iter()
                .filter(|row| row[0].is_wildcard())
                .map(|row| row[1..].to_vec())
                .collect::<Vec<_>>();
            usefulness_inner(
                &default,
                &candidate[1..],
                &types[1..],
                registry,
                fuel - 1,
                active,
            )
            .map(|mut witness| {
                let mut rebuilt = vec![CheckedPattern::Wildcard];
                rebuilt.append(&mut witness);
                rebuilt
            })
        }
    } else {
        let head = pattern_head(&candidate[0])?;
        let argument_types = head_types(head, first_type, registry);
        let specialized_matrix = specialize_matrix(matrix, head, argument_types.len());
        let mut specialized_candidate = pattern_arguments(&candidate[0]);
        specialized_candidate.extend_from_slice(&candidate[1..]);
        let mut specialized_types = argument_types.clone();
        specialized_types.extend_from_slice(&types[1..]);
        usefulness_inner(
            &specialized_matrix,
            &specialized_candidate,
            &specialized_types,
            registry,
            fuel - 1,
            active,
        )
        .map(|mut witness| {
            let arguments = witness.drain(..argument_types.len()).collect::<Vec<_>>();
            let mut rebuilt = vec![pattern_from_head(head, arguments)];
            rebuilt.extend(witness);
            rebuilt
        })
    };
    active.remove(&state);
    result
}

fn heads_for_type(ty: &Type, registry: &Registry) -> Option<Vec<Head>> {
    match ty {
        Type::Bool => Some(vec![Head::Boolean(true), Head::Boolean(false)]),
        Type::Unit => Some(vec![Head::Unit]),
        Type::Tuple(elements) => Some(vec![Head::Tuple(elements.len())]),
        Type::Nominal(id) => Some(
            registry
                .type_info(*id)?
                .constructors
                .iter()
                .copied()
                .map(Head::Constructor)
                .collect(),
        ),
        Type::Int | Type::Function(_, _) => None,
    }
}

fn head_types(head: Head, ty: &Type, registry: &Registry) -> Vec<Type> {
    match head {
        Head::Boolean(_) | Head::Unit => Vec::new(),
        Head::Tuple(count) => match ty {
            Type::Tuple(elements) if elements.len() == count => elements.to_vec(),
            _ => Vec::new(),
        },
        Head::Constructor(id) => registry
            .constructor(id)
            .and_then(|constructor| constructor.payload.clone())
            .into_iter()
            .collect(),
    }
}

fn pattern_head(pattern: &CheckedPattern) -> Option<Head> {
    match pattern {
        CheckedPattern::Boolean(value) => Some(Head::Boolean(*value)),
        CheckedPattern::Unit => Some(Head::Unit),
        CheckedPattern::Tuple(elements) => Some(Head::Tuple(elements.len())),
        CheckedPattern::Constructor(id, _) => Some(Head::Constructor(*id)),
        CheckedPattern::Binder(_) | CheckedPattern::Wildcard => None,
    }
}

fn pattern_arguments(pattern: &CheckedPattern) -> Vec<CheckedPattern> {
    match pattern {
        CheckedPattern::Tuple(elements) => elements.to_vec(),
        CheckedPattern::Constructor(_, Some(payload)) => vec![payload.as_ref().clone()],
        CheckedPattern::Boolean(_)
        | CheckedPattern::Unit
        | CheckedPattern::Constructor(_, None)
        | CheckedPattern::Binder(_)
        | CheckedPattern::Wildcard => Vec::new(),
    }
}

fn specialize_matrix(
    matrix: &[Vec<CheckedPattern>],
    head: Head,
    argument_count: usize,
) -> Vec<Vec<CheckedPattern>> {
    let mut specialized = Vec::new();
    for row in matrix {
        if row[0].is_wildcard() {
            let mut result = vec![CheckedPattern::Wildcard; argument_count];
            result.extend_from_slice(&row[1..]);
            specialized.push(result);
        } else if pattern_head(&row[0]) == Some(head) {
            let mut result = pattern_arguments(&row[0]);
            result.extend_from_slice(&row[1..]);
            specialized.push(result);
        }
    }
    specialized
}

fn pattern_from_head(head: Head, mut arguments: Vec<CheckedPattern>) -> CheckedPattern {
    match head {
        Head::Boolean(value) => CheckedPattern::Boolean(value),
        Head::Unit => CheckedPattern::Unit,
        Head::Tuple(_) => CheckedPattern::Tuple(arguments.into_boxed_slice()),
        Head::Constructor(id) => CheckedPattern::Constructor(
            id,
            (!arguments.is_empty()).then(|| Box::new(arguments.remove(0))),
        ),
    }
}

fn display_witness(witness: &[CheckedPattern], registry: &Registry) -> String {
    witness
        .iter()
        .map(|pattern| display_pattern(pattern, registry))
        .collect::<Vec<_>>()
        .join(" ")
}

fn display_pattern(pattern: &CheckedPattern, registry: &Registry) -> String {
    match pattern {
        CheckedPattern::Binder(_) | CheckedPattern::Wildcard => "_".into(),
        CheckedPattern::Boolean(value) => value.to_string(),
        CheckedPattern::Unit => "()".into(),
        CheckedPattern::Tuple(elements) => format!(
            "({})",
            elements
                .iter()
                .map(|element| display_pattern(element, registry))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        CheckedPattern::Constructor(id, payload) => {
            let name = registry
                .constructor(*id)
                .map_or("<foreign-constructor>", |constructor| {
                    constructor.name.as_str()
                });
            payload.as_ref().map_or_else(
                || name.to_owned(),
                |payload| format!("{name}({})", display_pattern(payload, registry)),
            )
        }
    }
}

type Location = usize;
type RuntimeEnvironment = HashMap<String, Location>;

#[derive(Clone)]
enum HeapCell {
    Uninitialized,
    Alias(Location),
    Integer(Integer),
    Boolean(bool),
    Unit,
    Tuple(Box<[Location]>),
    Constructor(ConstructorId, Option<Location>),
    Function(RuntimeFunction),
}

#[derive(Clone)]
enum RuntimeFunction {
    Closure {
        pattern: Pattern,
        body: Expr,
        environment: RuntimeEnvironment,
    },
    Equations {
        clauses: Vec<Clause>,
        arity: usize,
        arguments: Vec<Location>,
        environment: RuntimeEnvironment,
    },
    Constructor(ConstructorId),
}

struct Runtime {
    registry: Arc<Registry>,
    cells: Vec<HeapCell>,
}

impl Runtime {
    fn new(registry: Arc<Registry>) -> Self {
        Self {
            registry,
            cells: Vec::new(),
        }
    }

    fn allocate(&mut self, cell: HeapCell) -> Result<Location, ExtendedFailure> {
        if self.cells.len() == usize::MAX {
            return Err(
                self.runtime_failure("runtime.heap-capacity", "the evaluation heap is full")
            );
        }
        let location = self.cells.len();
        self.cells.push(cell);
        Ok(location)
    }

    fn resolve_alias(&self, location: Location) -> Result<Location, ExtendedFailure> {
        let mut current = location;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(current) {
                return Err(
                    self.runtime_failure("runtime.alias-loop", "the heap contains an alias loop")
                );
            }
            match self.cells.get(current) {
                Some(HeapCell::Alias(next)) => current = *next,
                Some(HeapCell::Uninitialized) => {
                    return Err(self.runtime_failure(
                        "runtime.uninitialized-location",
                        "evaluation reached an uninitialized recursive slot",
                    ));
                }
                Some(_) => return Ok(current),
                None => {
                    return Err(self.runtime_failure(
                        "runtime.invalid-location",
                        "evaluation referenced a location outside the heap",
                    ));
                }
            }
        }
    }

    fn evaluate_program(
        &mut self,
        program: &ExtendedCoreProgram,
    ) -> Result<Location, ExtendedFailure> {
        let mut environment = RuntimeEnvironment::new();
        let mut global_slots = Vec::with_capacity(program.syntax.globals.len());
        for global in &program.syntax.globals {
            let name = match global {
                Global::Equational { name, .. } | Global::Operational { name, .. } => name,
            };
            let slot = self.allocate(HeapCell::Uninitialized)?;
            environment.insert(name.clone(), slot);
            global_slots.push(slot);
        }
        for (global, slot) in program.syntax.globals.iter().zip(global_slots) {
            let function = match global {
                Global::Equational { clauses, .. } => RuntimeFunction::Equations {
                    clauses: clauses.clone(),
                    arity: clauses.first().map_or(0, |clause| clause.patterns.len()),
                    arguments: Vec::new(),
                    environment: environment.clone(),
                },
                Global::Operational {
                    parameters, body, ..
                } => {
                    let pattern = if parameters.len() == 1 {
                        parameters[0].0.clone()
                    } else {
                        Pattern::Tuple(
                            parameters
                                .iter()
                                .map(|(pattern, _)| pattern.clone())
                                .collect(),
                        )
                    };
                    RuntimeFunction::Closure {
                        pattern,
                        body: body.clone(),
                        environment: environment.clone(),
                    }
                }
            };
            let function_location = self.allocate(HeapCell::Function(function))?;
            self.cells[slot] = HeapCell::Alias(function_location);
        }
        self.evaluate(&program.syntax.result, &environment)
    }

    fn evaluate(
        &mut self,
        expression: &Expr,
        environment: &RuntimeEnvironment,
    ) -> Result<Location, ExtendedFailure> {
        match expression {
            Expr::Integer(value) => self.allocate(HeapCell::Integer(value.clone())),
            Expr::Boolean(value) => self.allocate(HeapCell::Boolean(*value)),
            Expr::Unit => self.allocate(HeapCell::Unit),
            Expr::Name(name) => {
                if let Some(location) = environment.get(name) {
                    return Ok(*location);
                }
                let constructor = self.registry.constructor_named(name).ok_or_else(|| {
                    self.runtime_failure(
                        "runtime.missing-binding",
                        format!("`{name}` has no runtime binding"),
                    )
                })?;
                if constructor.payload.is_some() {
                    self.allocate(HeapCell::Function(RuntimeFunction::Constructor(
                        constructor.id,
                    )))
                } else {
                    self.allocate(HeapCell::Constructor(constructor.id, None))
                }
            }
            Expr::Tuple(elements) => {
                let mut values = Vec::with_capacity(elements.len());
                for element in elements {
                    values.push(self.evaluate(element, environment)?);
                }
                self.allocate(HeapCell::Tuple(values.into_boxed_slice()))
            }
            Expr::Apply(function, argument) => {
                let function = self.evaluate(function, environment)?;
                let argument = self.evaluate(argument, environment)?;
                self.apply(function, argument)
            }
            Expr::Add(left, right) => {
                let left = self.evaluate_integer(left, environment)?;
                let right = self.evaluate_integer(right, environment)?;
                self.allocate(HeapCell::Integer(&left + &right))
            }
            Expr::Multiply(left, right) => {
                let left = self.evaluate_integer(left, environment)?;
                let right = self.evaluate_integer(right, environment)?;
                self.allocate(HeapCell::Integer(&left * &right))
            }
            Expr::Equal(left, right) => {
                let left = self.evaluate_integer(left, environment)?;
                let right = self.evaluate_integer(right, environment)?;
                self.allocate(HeapCell::Boolean(left == right))
            }
            Expr::Function(pattern, body) => {
                self.allocate(HeapCell::Function(RuntimeFunction::Closure {
                    pattern: pattern.clone(),
                    body: body.as_ref().clone(),
                    environment: environment.clone(),
                }))
            }
            Expr::Block(declarations, result) => {
                let mut local = environment.clone();
                for declaration in declarations {
                    match declaration {
                        LocalDeclaration::Binding {
                            pattern,
                            initializer,
                            ..
                        } => {
                            let value = self.evaluate(initializer, &local)?;
                            let mut bindings = Vec::new();
                            if !self.matches(pattern, value, &mut bindings)? {
                                return Err(self.runtime_failure(
                                    "runtime.impossible-match-failure",
                                    "a validated irrefutable binding did not match",
                                ));
                            }
                            local.extend(bindings);
                        }
                        LocalDeclaration::Recursive(members) => {
                            let mut slots = Vec::with_capacity(members.len());
                            for member in members {
                                let slot = self.allocate(HeapCell::Uninitialized)?;
                                local.insert(member.name.clone(), slot);
                                slots.push(slot);
                            }
                            for (member, slot) in members.iter().zip(slots) {
                                let value = self.evaluate(&member.initializer, &local)?;
                                self.cells[slot] = HeapCell::Alias(value);
                            }
                        }
                    }
                }
                self.evaluate(result, &local)
            }
            Expr::Match(scrutinee, arms) => {
                let value = self.evaluate(scrutinee, environment)?;
                for arm in arms {
                    let mut bindings = Vec::new();
                    if self.matches(&arm.pattern, value, &mut bindings)? {
                        let mut local = environment.clone();
                        local.extend(bindings);
                        return self.evaluate(&arm.body, &local);
                    }
                }
                Err(self.runtime_failure(
                    "runtime.impossible-match-failure",
                    "a validated exhaustive match selected no arm",
                ))
            }
        }
    }

    fn evaluate_integer(
        &mut self,
        expression: &Expr,
        environment: &RuntimeEnvironment,
    ) -> Result<Integer, ExtendedFailure> {
        let location = self.evaluate(expression, environment)?;
        let resolved = self.resolve_alias(location)?;
        match self.cells.get(resolved) {
            Some(HeapCell::Integer(value)) => Ok(value.clone()),
            _ => Err(self.runtime_failure(
                "runtime.primitive-value",
                "an integer primitive received a non-integer value",
            )),
        }
    }

    fn apply(
        &mut self,
        function: Location,
        argument: Location,
    ) -> Result<Location, ExtendedFailure> {
        let location = self.resolve_alias(function)?;
        let Some(HeapCell::Function(function)) = self.cells.get(location).cloned() else {
            return Err(self.runtime_failure(
                "runtime.unexpected-function-value",
                "application received a non-function value",
            ));
        };
        match function {
            RuntimeFunction::Constructor(id) => {
                self.allocate(HeapCell::Constructor(id, Some(argument)))
            }
            RuntimeFunction::Closure {
                pattern,
                body,
                mut environment,
            } => {
                let mut bindings = Vec::new();
                if !self.matches(&pattern, argument, &mut bindings)? {
                    return Err(self.runtime_failure(
                        "runtime.impossible-match-failure",
                        "a validated function-domain pattern did not match",
                    ));
                }
                environment.extend(bindings);
                self.evaluate(&body, &environment)
            }
            RuntimeFunction::Equations {
                clauses,
                arity,
                mut arguments,
                environment,
            } => {
                arguments.push(argument);
                if arguments.len() < arity {
                    return self.allocate(HeapCell::Function(RuntimeFunction::Equations {
                        clauses,
                        arity,
                        arguments,
                        environment,
                    }));
                }
                for clause in &clauses {
                    let mut bindings = Vec::new();
                    let mut selected = true;
                    for (pattern, argument) in clause.patterns.iter().zip(arguments.iter()) {
                        if !self.matches(pattern, *argument, &mut bindings)? {
                            selected = false;
                            break;
                        }
                    }
                    if selected {
                        let mut local = environment.clone();
                        local.extend(bindings);
                        return self.evaluate(&clause.body, &local);
                    }
                }
                Err(self.runtime_failure(
                    "runtime.impossible-match-failure",
                    "validated exhaustive equations selected no clause",
                ))
            }
        }
    }

    fn matches(
        &self,
        pattern: &Pattern,
        value: Location,
        bindings: &mut Vec<(String, Location)>,
    ) -> Result<bool, ExtendedFailure> {
        let mut work = vec![(pattern, value)];
        while let Some((pattern, value)) = work.pop() {
            match pattern {
                Pattern::Binder(name) => bindings.push((name.clone(), value)),
                Pattern::Wildcard => {}
                Pattern::Boolean(expected) => {
                    let location = self.resolve_alias(value)?;
                    if !matches!(self.cells.get(location), Some(HeapCell::Boolean(found)) if found == expected)
                    {
                        return Ok(false);
                    }
                }
                Pattern::Unit => {
                    let location = self.resolve_alias(value)?;
                    if !matches!(self.cells.get(location), Some(HeapCell::Unit)) {
                        return Ok(false);
                    }
                }
                Pattern::Tuple(patterns) => {
                    let location = self.resolve_alias(value)?;
                    let Some(HeapCell::Tuple(elements)) = self.cells.get(location) else {
                        return Ok(false);
                    };
                    if patterns.len() != elements.len() {
                        return Ok(false);
                    }
                    work.extend(
                        patterns
                            .iter()
                            .zip(elements.iter())
                            .rev()
                            .map(|(pattern, value)| (pattern, *value)),
                    );
                }
                Pattern::Constructor(name, payload_pattern) => {
                    let expected = self.registry.constructor_named(name).ok_or_else(|| {
                        self.runtime_failure(
                            "runtime.unknown-constructor",
                            "validated pattern constructor is absent",
                        )
                    })?;
                    let location = self.resolve_alias(value)?;
                    let Some(HeapCell::Constructor(found, payload)) = self.cells.get(location)
                    else {
                        return Ok(false);
                    };
                    if *found != expected.id {
                        return Ok(false);
                    }
                    match (payload_pattern, payload) {
                        (None, None) => {}
                        (Some(pattern), Some(payload)) => work.push((pattern, *payload)),
                        _ => return Ok(false),
                    }
                }
            }
        }
        Ok(true)
    }

    fn runtime_failure(&self, reason: &'static str, message: impl Into<String>) -> ExtendedFailure {
        ExtendedFailure::source(ExtendedStage::Runtime, reason, message)
    }
}

/// Heap-backed observed result of an extended evaluation.
#[derive(Clone)]
pub struct ObservedValue {
    heap: Arc<ObservedHeap>,
    root: Location,
}

struct ObservedHeap {
    registry: Arc<Registry>,
    cells: Box<[HeapCell]>,
}

impl fmt::Debug for ObservedValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ObservedValue")
            .field("root", &self.root)
            .field("heap_cells", &self.heap.cells.len())
            .finish()
    }
}

impl fmt::Display for ObservedValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.render())
    }
}

impl ObservedValue {
    fn render(&self) -> String {
        enum Task {
            Enter(Location),
            Exit(Location),
            Text(&'static str),
        }

        let resolve_alias = |start: Location| {
            let mut location = start;
            let mut aliases = HashSet::new();
            loop {
                if !aliases.insert(location) {
                    return Err("<alias-cycle>");
                }
                match self.heap.cells.get(location) {
                    Some(HeapCell::Alias(next)) => location = *next,
                    Some(_) => return Ok(location),
                    None => return Err("<invalid-location>"),
                }
            }
        };
        let mut output = String::new();
        let mut active = HashSet::new();
        let mut tasks = vec![Task::Enter(self.root)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Exit(location) => {
                    active.remove(&location);
                }
                Task::Enter(requested) => {
                    let location = match resolve_alias(requested) {
                        Ok(location) => location,
                        Err(marker) => {
                            output.push_str(marker);
                            continue;
                        }
                    };
                    if !active.insert(location) {
                        output.push_str("<cycle>");
                        continue;
                    }
                    tasks.push(Task::Exit(location));
                    match self.heap.cells.get(location) {
                        Some(HeapCell::Integer(value)) => output.push_str(&value.to_string()),
                        Some(HeapCell::Boolean(value)) => output.push_str(&value.to_string()),
                        Some(HeapCell::Unit) => output.push_str("()"),
                        Some(HeapCell::Tuple(elements)) => {
                            output.push('(');
                            tasks.push(Task::Text(")"));
                            for (index, element) in elements.iter().enumerate().rev() {
                                tasks.push(Task::Enter(*element));
                                if index > 0 {
                                    tasks.push(Task::Text(", "));
                                }
                            }
                        }
                        Some(HeapCell::Constructor(id, payload)) => {
                            let name = self
                                .heap
                                .registry
                                .constructor(*id)
                                .map_or("<foreign-constructor>", |constructor| {
                                    constructor.name.as_str()
                                });
                            output.push_str(name);
                            if let Some(payload) = payload {
                                output.push('(');
                                tasks.push(Task::Text(")"));
                                match resolve_alias(*payload) {
                                    Ok(payload_location) => {
                                        if let Some(HeapCell::Tuple(elements)) =
                                            self.heap.cells.get(payload_location)
                                        {
                                            for (index, element) in
                                                elements.iter().enumerate().rev()
                                            {
                                                tasks.push(Task::Enter(*element));
                                                if index > 0 {
                                                    tasks.push(Task::Text(", "));
                                                }
                                            }
                                        } else {
                                            tasks.push(Task::Enter(*payload));
                                        }
                                    }
                                    Err(marker) => output.push_str(marker),
                                }
                            }
                        }
                        Some(HeapCell::Function(_)) => output.push_str("<function>"),
                        Some(HeapCell::Uninitialized) => output.push_str("<uninitialized>"),
                        Some(HeapCell::Alias(_)) => output.push_str("<invalid-alias>"),
                        None => output.push_str("<invalid-location>"),
                    }
                }
            }
        }
        output
    }
}

/// Compiles one source through syntax, resolution, typing, and validation.
///
/// # Errors
///
/// Returns the structured rejection or internal validation failure owned by
/// the first stage that cannot produce its complete result.
pub fn compile(source: &SourceFile) -> Result<ExtendedCoreProgram, ExtendedFailure> {
    let lexed = lex(source).map_err(|error| {
        ExtendedFailure::source(
            ExtendedStage::Runtime,
            "internal.source-model",
            error.to_string(),
        )
    })?;
    if let Some(diagnostic) = lexed.diagnostics.first() {
        return Err(ExtendedFailure::source(
            ExtendedStage::Syntax,
            "lex.extended-source",
            diagnostic.render_plain(),
        )
        .at(diagnostic.primary.span()));
    }
    let mut parser = Parser::new(lexed.tokens);
    let syntax = parser.parse_program()?;
    let registry = Arc::new(Registry::resolve(&syntax, source.id())?);
    registry.validate()?;
    let checked = Checker::check(syntax, Arc::clone(&registry))?;
    validate_checked(&checked)?;
    Ok(checked)
}

/// Independently validates data-and-pattern Core.
///
/// # Errors
///
/// Returns an internal validation failure if the registry, patterns, coverage,
/// scope, or result type is inconsistent.
pub fn validate_core(program: &ExtendedCoreProgram) -> Result<(), ExtendedFailure> {
    validate_checked(program)
}

/// Rebuilds data-and-pattern Core without changing its typed structure.
#[must_use]
pub fn identity_traversal(program: &ExtendedCoreProgram) -> ExtendedCoreProgram {
    transform_checked(program, false)
}

/// Folds literal integer addition and multiplication in data-and-pattern Core.
#[must_use]
pub fn fold_literal_primitives(program: &ExtendedCoreProgram) -> ExtendedCoreProgram {
    transform_checked(program, true)
}

/// Evaluates independently validated data-and-pattern Core.
///
/// # Errors
///
/// Returns a validation or structured internal runtime failure.
pub fn evaluate_core(program: &ExtendedCoreProgram) -> Result<Observation, ExtendedFailure> {
    validate_checked(program)?;
    let registry = Arc::clone(&program.registry);
    let mut runtime = Runtime::new(Arc::clone(&registry));
    let root = runtime.evaluate_program(program)?;
    let observed = ObservedValue {
        heap: Arc::new(ObservedHeap {
            registry: Arc::clone(&registry),
            cells: runtime.cells.into_boxed_slice(),
        }),
        root,
    };
    let type_display = registry.type_display(&program.result_type);
    Ok(Observation::extended(
        crate::eval::Value::Extended(observed),
        program.result_type.clone(),
        type_display,
    ))
}

/// Runs the complete CP-0003 pipeline for one admitted source.
pub fn run(source: &SourceFile) -> Result<Observation, ExtendedFailure> {
    let checked = compile(source)?;
    let transformed = identity_traversal(&checked);
    validate_core(&transformed)?;
    evaluate_core(&transformed)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked(text: &str) -> ExtendedCoreProgram {
        let source = SourceFile::new("extended-validation.ash", text).expect("fixture should fit");
        let lexed = lex(&source).expect("fixture should lex");
        assert!(lexed.diagnostics.is_empty());
        let syntax = Parser::new(lexed.tokens)
            .parse_program()
            .expect("fixture should parse");
        let registry =
            Arc::new(Registry::resolve(&syntax, source.id()).expect("fixture should resolve"));
        Checker::check(syntax, registry).expect("fixture should check")
    }

    fn evaluate_display(program: &ExtendedCoreProgram) -> String {
        let mut runtime = Runtime::new(Arc::clone(&program.registry));
        let root = runtime
            .evaluate_program(program)
            .expect("validated fixture should evaluate");
        ObservedValue {
            heap: Arc::new(ObservedHeap {
                registry: Arc::clone(&program.registry),
                cells: runtime.cells.into_boxed_slice(),
            }),
            root,
        }
        .render()
    }

    #[test]
    fn registry_validation_rejects_empty_nominal_metadata() {
        let source = SourceFile::new("malformed-registry.ash", "0")
            .expect("fixture should fit")
            .id();
        let id = NominalTypeId::new(source, 0);
        let registry = Registry {
            source,
            types: Arc::from([TypeInfo {
                id,
                name: "Empty".into(),
                constructors: Box::new([]),
            }]),
            constructors: Arc::from([]),
            type_names: Arc::new(HashMap::from([("Empty".into(), id)])),
            constructor_names: Arc::new(HashMap::new()),
        };

        let failure = registry.validate().expect_err("empty sums must be invalid");
        assert_eq!(failure.stage, ExtendedStage::Validation);
        assert_eq!(failure.reason, "validation.empty-type");
    }

    #[test]
    fn independent_validation_rejects_a_corrupted_result_type() {
        let mut program = checked("type Wrapped =\nWrap(Int)\n\nWrap(1)\n");
        program.result_type = Type::Bool;

        let failure = validate_checked(&program).expect_err("the forged type must be invalid");
        assert_eq!(failure.stage, ExtendedStage::Validation);
        assert_eq!(failure.reason, "validation.result-type");
    }

    #[test]
    fn transforms_preserve_registries_validate_and_evaluate_equivalently() {
        let original = checked(
            "type Pair =\nPair(Int, Int)\n\nmatch Pair(20 + 1, 7 * 3) {\nPair(left, right) => left + right\n}\n",
        );
        let identity = transform_checked(&original, false);
        let folded = transform_checked(&original, true);

        assert!(Arc::ptr_eq(&original.registry, &identity.registry));
        assert!(Arc::ptr_eq(&original.registry, &folded.registry));
        validate_checked(&identity).expect("identity output should validate");
        validate_checked(&folded).expect("folded output should validate");
        assert_eq!(evaluate_display(&original), "42");
        assert_eq!(evaluate_display(&identity), "42");
        assert_eq!(evaluate_display(&folded), "42");
    }

    #[test]
    fn identity_transform_preserves_cyclic_data_observation() {
        let original = checked(
            "type Stream =\nNext(Int, Stream)\n\n{\nlet rec ones : Stream = Next(1, ones)\nones\n}\n",
        );
        let transformed = transform_checked(&original, false);
        validate_checked(&transformed).expect("identity output should validate");
        assert_eq!(evaluate_display(&original), "Next(1, <cycle>)");
        assert_eq!(evaluate_display(&transformed), "Next(1, <cycle>)");
    }
}
