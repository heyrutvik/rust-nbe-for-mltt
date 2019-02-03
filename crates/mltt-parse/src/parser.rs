//! The parser
//!
//! # Naive grammar
//!
//! The language follows the following [BNF]-style grammar:
//!
//! ```text
//! module  ::= item* EOF
//!
//! item    ::= DOC_COMMENT* IDENTIFIER ":" term ";"
//!           | DOC_COMMENT* IDENTIFIER IDENTIFIER* "=" term ";"
//!
//! term    ::= IDENTIFIER
//!           | STRING_LITERAL
//!           | CHAR_LITERAL
//!           | INT_LITERAL
//!           | FLOAT_LITERAL
//!           | "let" IDENTIFIER "=" term "in" term
//!           | term ":" term
//!           | "(" term ")"
//!           | "Fun" ("(" IDENTIFIER+ ":" term ")")+ "->" term
//!           | term "->" term
//!           | "fun" IDENTIFIER+ "=>" term
//!           | term term
//!           | "Pair" "{" (IDENTIFIER ":")? term "," term "}"
//!           | "pair" "{" term "," term "}"
//!           | term "." ("fst" | "snd")
//!           | "Type" ("^" INT_LITERAL)?
//! ```
//!
//! Note that there are a number of ambiguities here that we will have to
//! address through the use of top-down operator precedence parsing and some
//! ordered choice.
//!
//! [BNF]: https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
//!

use language_reporting::{Diagnostic, Label};
use mltt_concrete::syntax::concrete::{Item, Term};
use mltt_span::FileSpan;

use crate::token::{DelimKind, Token, TokenKind};

pub fn parse_program<'file>(
    tokens: impl Iterator<Item = Token<&'file str>>,
) -> Result<Vec<Item>, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program()?;
    parser.expect_eof()?;
    Ok(program)
}

pub fn parse_item<'file>(
    tokens: impl Iterator<Item = Token<&'file str>>,
) -> Result<Item, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let item = parser.parse_item()?;
    parser.expect_eof()?;
    Ok(item)
}

pub fn parse_term<'file>(
    tokens: impl Iterator<Item = Token<&'file str>>,
) -> Result<Term, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let term = parser.parse_term(Prec(0))?;
    parser.expect_eof()?;
    Ok(term)
}

trait Matcher<Given> {
    fn is_match(&self, given: &Given) -> bool;
}

impl<Slice> Matcher<Token<Slice>> for TokenKind {
    fn is_match(&self, given: &Token<Slice>) -> bool {
        given.kind == *self
    }
}

struct Keyword<Value>(pub Value);

impl<Slice, Value> Matcher<Token<Slice>> for Keyword<Value>
where
    Slice: PartialEq<Value>,
{
    fn is_match(&self, given: &Token<Slice>) -> bool {
        given.kind == TokenKind::Keyword && given.slice == self.0
    }
}

struct ArgTermStart;

impl<Slice> Matcher<Token<Slice>> for ArgTermStart {
    fn is_match(&self, given: &Token<Slice>) -> bool {
        match given.kind {
            TokenKind::Identifier
            | TokenKind::StringLiteral
            | TokenKind::CharLiteral
            | TokenKind::IntLiteral
            | TokenKind::FloatLiteral
            | TokenKind::Open(DelimKind::Paren) => true,
            _ => false,
        }
    }
}

/// The precedence or 'binding strength' of an infix operator
///
/// This controls how different operators should [be prioritised][order-of-operations]
/// in the absence of explicit grouping. For example, if `*` has a greater
/// precedence than `+`, then `a * b + c` will be parsed as `(a * b) + c`.
///
/// [order-of-operations]: https://en.wikipedia.org/wiki/Order_of_operations
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Prec(pub u32);

impl std::ops::Add<u32> for Prec {
    type Output = Prec;

    fn add(self, other: u32) -> Prec {
        Prec(self.0 + other)
    }
}

impl std::ops::Sub<u32> for Prec {
    type Output = Prec;

    fn sub(self, other: u32) -> Prec {
        Prec(self.0.saturating_sub(other))
    }
}

impl PartialEq<u32> for Prec {
    fn eq(&self, other: &u32) -> bool {
        self.eq(&Prec(*other))
    }
}

impl PartialOrd<u32> for Prec {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&Prec(*other))
    }
}

/// Skip whitespace or line comment tokens
fn next_non_whitespace<'file>(
    tokens: &mut impl Iterator<Item = Token<&'file str>>,
) -> Option<Token<&'file str>> {
    tokens.skip_while(Token::is_whitespace).next()
}

/// A language parser
struct Parser<Tokens: Iterator> {
    /// The underlying iterator of tokens.
    tokens: Tokens,
    /// For remembering the peeked token.
    peeked: Option<Tokens::Item>,
}

impl<'file, Tokens> Parser<Tokens>
where
    Tokens: Iterator<Item = Token<&'file str>>,
{
    /// Create a new parser from an iterator of tokens
    fn new(mut tokens: Tokens) -> Parser<Tokens> {
        let peeked = next_non_whitespace(&mut tokens);
        Parser { tokens, peeked }
    }

    /// Peek at the current lookahead token.
    fn peek(&self) -> Option<&Token<&'file str>> {
        self.peeked.as_ref()
    }

    /// Consume the current token and load the next one. Return the old token.
    fn advance(&mut self) -> Option<Token<&'file str>> {
        let next_token = std::mem::replace(&mut self.peeked, next_non_whitespace(&mut self.tokens));

        log::trace!(
            "shift: consumed = {:?}, lookahead = {:?}",
            next_token,
            self.peek(),
        );

        next_token
    }

    fn check_match(&self, matcher: impl Matcher<Token<&'file str>>) -> bool {
        self.peek().map_or(false, |token| matcher.is_match(token))
    }

    fn try_match(&mut self, matcher: impl Matcher<Token<&'file str>>) -> Option<Token<&'file str>> {
        if self.check_match(matcher) {
            self.advance()
        } else {
            None
        }
    }

    fn expect_match(
        &mut self,
        matcher: impl Matcher<Token<&'file str>>,
    ) -> Result<Token<&'file str>, Diagnostic<FileSpan>> {
        self.try_match(matcher).ok_or_else(|| {
            log::debug!("unexpected: lookahead = {:?}", self.peek());
            match self.peek() {
                None => Diagnostic::new_error("unexpected EOF"), // FIXME: Span
                Some(token) => Diagnostic::new_error("unexpected token")
                    .with_label(Label::new_primary(token.span).with_message("token forund here")),
            }
        })
    }

    fn try_identifier(&mut self) -> Option<String> {
        Some(self.try_match(TokenKind::Identifier)?.slice.to_owned())
    }

    fn expect_identifier(&mut self) -> Result<String, Diagnostic<FileSpan>> {
        Ok(self.expect_match(TokenKind::Identifier)?.slice.to_owned())
    }

    fn expect_eof(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.peek() {
            None => Ok(()),
            Some(token) => {
                log::debug!("non-eof token {:?}", token);
                Err(Diagnostic::new_error("expected EOF")
                    .with_label(Label::new_primary(token.span).with_message("unexpected token")))
            },
        }
    }

    fn expect_doc_comments(&mut self) -> Vec<String> {
        let mut docs = Vec::new();
        while let Some(doc_token) = self.try_match(TokenKind::LineDoc) {
            docs.push(doc_token.slice.to_owned());
        }
        docs
    }

    /// Expect a program
    ///
    /// ```text
    /// program ::= item*
    /// ```
    fn parse_program(&mut self) -> Result<Vec<Item>, Diagnostic<FileSpan>> {
        let mut items = Vec::new();
        while self.peek().is_some() {
            items.push(self.parse_item()?);
        }
        Ok(items)
    }

    /// Expect an item
    ///
    /// ```text
    /// item ::= DOC_COMMENT* IDENTIFIER ":" term(0) ";"
    ///        | DOC_COMMENT* IDENTIFIER IDENTIFIER* "=" term(0) ";"
    /// ```
    fn parse_item(&mut self) -> Result<Item, Diagnostic<FileSpan>> {
        log::trace!("expecting item");

        let docs = self.expect_doc_comments();
        let name = self.expect_identifier()?;

        log::trace!("item name: {:?}", name);

        if self.try_match(TokenKind::Colon).is_some() {
            log::trace!("expecting item declaration");

            let ann = self.parse_term(Prec(0))?;
            self.expect_match(TokenKind::Semicolon)?;

            Ok(Item::Declaration { docs, name, ann })
        } else {
            log::trace!("expecting item definition");

            let mut params = Vec::new();
            while let Some(name) = self.try_identifier() {
                params.push(name);
            }
            if self.try_match(TokenKind::Equals).is_some() {
                let body = self.parse_term(Prec(0))?;
                self.expect_match(TokenKind::Semicolon)?;

                Ok(Item::Definition {
                    docs,
                    name,
                    params,
                    body,
                })
            } else if params.is_empty() {
                // TODO: Span
                Err(Diagnostic::new_error("expected declaration or definition"))
            } else {
                // TODO: Span
                Err(Diagnostic::new_error(
                    "expected equals after definition parameters",
                ))
            }
        }
    }

    /// Expect a term
    ///
    /// ```text
    /// term(prec) ::= operators(prec) {
    ///     prefix  "let"               ::= let
    ///     prefix  "("                 ::= parens fun-app
    ///     prefix  "Fun"               ::= fun-type
    ///     prefix  "fun"               ::= fun-intro
    ///     prefix  "Pair"              ::= pair-type
    ///     prefix  "pair"              ::= pair-intro
    ///     prefix  "Type"              ::= universe
    ///     prefix  IDENTIFIER          ::= fun-app
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= pair-proj fun-app
    ///     infixr  ":"             20  ::= ann
    ///     infixr  "->"            50  ::= fun-arrow-type
    /// }
    /// ```
    fn parse_term(&mut self, right_prec: Prec) -> Result<Term, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.slice) {
            (TokenKind::Identifier, _) => {
                let term = self.parse_var(token)?;
                self.parse_fun_app(term)
            },
            (TokenKind::StringLiteral, _) => unimplemented!("string literal"),
            (TokenKind::CharLiteral, _) => unimplemented!("char literal"),
            (TokenKind::IntLiteral, _) => unimplemented!("int literal"),
            (TokenKind::FloatLiteral, _) => unimplemented!("float literal"),
            (TokenKind::Open(DelimKind::Paren), _) => {
                let term = self.parse_parens(token)?;
                self.parse_fun_app(term)
            },
            (TokenKind::Keyword, "Fun") => self.parse_fun_ty(token),
            (TokenKind::Keyword, "fun") => self.parse_fun_intro(token),
            (TokenKind::Keyword, "Pair") => self.parse_pair_ty(token),
            (TokenKind::Keyword, "pair") => self.parse_pair_intro(token),
            (TokenKind::Keyword, "let") => self.parse_let(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_pair_proj(term, token)?;
                    term = self.parse_fun_app(term)?;
                },
                TokenKind::Colon if right_prec < 20 => {
                    let token = self.advance().unwrap();
                    term = self.parse_ann(term, token)?;
                },
                TokenKind::RArrow if right_prec < 50 => {
                    let token = self.advance().unwrap();
                    term = self.parse_fun_arrow_type(term, token)?;
                },
                _ => break,
            }
        }

        Ok(term)
    }

    /// Expect an argument term
    ///
    /// ```text
    /// arg-term(prec) ::= operators(prec) {
    ///     prefix  "("                 ::= parens
    ///     prefix  "Type"              ::= universe
    ///     nilfix  IDENTIFIER
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= pair-proj
    /// }
    /// ```
    fn parse_arg_term(&mut self, right_prec: Prec) -> Result<Term, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.slice) {
            (TokenKind::Identifier, _) => self.parse_var(token),
            (TokenKind::StringLiteral, _) => unimplemented!("string literal"),
            (TokenKind::CharLiteral, _) => unimplemented!("char literal"),
            (TokenKind::IntLiteral, _) => unimplemented!("int literal"),
            (TokenKind::FloatLiteral, _) => unimplemented!("float literal"),
            (TokenKind::Open(DelimKind::Paren), _) => self.parse_parens(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_pair_proj(term, token)?;
                },
                _ => break,
            }
        }

        Ok(term)
    }

    /// Expect the trailing part of a variable
    fn parse_var(&mut self, token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Var(token.slice.to_owned()))
    }

    /// Expect the trailing part of a function introduction
    ///
    /// ```text
    /// fun-ty ::= ("("IDENTIFIER+ ":" term(0) ")")+ "->" term(50 - 1)
    /// ```
    fn parse_fun_ty(&mut self, token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        let mut params = Vec::new();

        while let Some(paren_token) = self.try_match(TokenKind::Open(DelimKind::Paren)) {
            let mut param_names = Vec::new();
            while let Some(param_name) = self.try_identifier() {
                param_names.push(param_name);
            }
            if param_names.is_empty() {
                return Err(Diagnostic::new_error("expected at least one parameter")
                    .with_label(Label::new_primary(paren_token.span).with_message(
                        "at least one parameter was expected after this parenthesis",
                    )));
            }

            self.expect_match(TokenKind::Colon)?;
            let param_ty = self.parse_term(Prec(0))?;
            params.push((param_names, param_ty));

            self.expect_match(TokenKind::Close(DelimKind::Paren))?;
        }

        if params.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameter").with_label(
                    Label::new_primary(token.span)
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }

        self.expect_match(TokenKind::RArrow)?;
        let body_ty = self.parse_term(Prec(50 - 1))?;

        Ok(Term::FunType(params, Box::new(body_ty)))
    }

    /// Expect the trailing part of a function introduction
    ///
    /// ```text
    /// fun-intro ::= IDENTIFIER+ "=>" term(0)
    /// ```
    fn parse_fun_intro(&mut self, token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        let mut params = Vec::new();
        while let Some(name) = self.try_identifier() {
            params.push(name);
        }
        if params.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameters").with_label(
                    Label::new_primary(token.span)
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }
        self.expect_match(TokenKind::RFatArrow)?;
        let body = self.parse_term(Prec(0))?;

        Ok(Term::FunIntro(params, Box::new(body)))
    }

    /// Expect the trailing part of a parenthesis grouping
    ///
    /// ```text
    /// parens ::= term(0) ")"
    /// ```
    fn parse_parens(&mut self, _token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        let term = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Close(DelimKind::Paren))?;

        Ok(Term::Parens(Box::new(term)))
    }

    /// Expect the trailing part of a pair type
    ///
    /// ```text
    /// pair-intro ::= "{" (IDENTIFIER ":")? term(0) "," term(0) "}"
    /// ```
    fn parse_pair_ty(&mut self, _token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        self.expect_match(TokenKind::Open(DelimKind::Brace))?;
        let fst_name = self.try_identifier();
        if fst_name.is_some() {
            self.expect_match(TokenKind::Colon)?;
        }
        let fst = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Comma)?;
        let snd = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Close(DelimKind::Brace))?;

        Ok(Term::PairType(fst_name, Box::new(fst), Box::new(snd)))
    }

    /// Expect the trailing part of a pair introduction
    ///
    /// ```text
    /// pair-intro ::= "{" term(0) "," term(0) "}"
    /// ```
    fn parse_pair_intro(
        &mut self,
        _token: Token<&'file str>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        self.expect_match(TokenKind::Open(DelimKind::Brace))?;
        let fst = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Comma)?;
        let snd = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Close(DelimKind::Brace))?;

        Ok(Term::PairIntro(Box::new(fst), Box::new(snd)))
    }

    /// Expect the trailing part of a let expression
    ///
    /// ```text
    /// let ::= IDENTIFIER "=" term(0) "in" term(0)
    /// ```
    fn parse_let(&mut self, _token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        let name = self.expect_identifier()?;
        self.expect_match(TokenKind::Equals)?;
        let def_term = self.parse_term(Prec(0))?;
        self.expect_match(Keyword("in"))?;
        let body_term = self.parse_term(Prec(0))?;

        Ok(Term::Let(name, Box::new(def_term), Box::new(body_term)))
    }

    /// Expect the trailing part of a universe
    ///
    /// ```text
    /// universe ::= ("^" INT_LITERAL)?
    /// ```
    fn parse_universe(&mut self, _token: Token<&'file str>) -> Result<Term, Diagnostic<FileSpan>> {
        if self.try_match(TokenKind::Caret).is_some() {
            let integer_token = self.expect_match(TokenKind::IntLiteral)?;
            // FIXME: if prefixed integer
            // FIXME: if separators
            Ok(Term::Universe(Some(integer_token.slice.parse().unwrap())))
        } else {
            Ok(Term::Universe(None))
        }
    }

    /// Expect the trailing part of a projection
    ///
    /// ```text
    /// pair-proj ::= ("fst" | "snd")
    /// ```
    fn parse_pair_proj(
        &mut self,
        lhs: Term,
        token: Token<&'file str>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        if self.try_match(Keyword("fst")).is_some() {
            Ok(Term::PairFst(Box::new(lhs)))
        } else if self.try_match(Keyword("snd")).is_some() {
            Ok(Term::PairSnd(Box::new(lhs)))
        } else {
            Err(Diagnostic::new_error("expected projection").with_label(
                Label::new_primary(token.span).with_message("`fst` or `snd` was expected the `.`"),
            ))
        }
    }

    /// Expect the trailing part of a type annotation
    ///
    /// ```text
    /// ann ::= term(20 - 1)
    /// ```
    fn parse_ann(
        &mut self,
        lhs: Term,
        _token: Token<&'file str>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(20 - 1))?;

        Ok(Term::Ann(Box::new(lhs), Box::new(rhs)))
    }

    /// Expect the trailing part of a function arrow
    ///
    /// ```text
    /// fun-arrow-type ::= term(50 - 1)
    /// ```
    fn parse_fun_arrow_type(
        &mut self,
        lhs: Term,
        _token: Token<&'file str>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(50 - 1))?;

        Ok(Term::FunArrowType(Box::new(lhs), Box::new(rhs)))
    }

    /// Expect the trailing part of a function application
    ///
    /// ```text
    /// fun-app ::= arg-term(0)*
    /// ```
    fn parse_fun_app(&mut self, lhs: Term) -> Result<Term, Diagnostic<FileSpan>> {
        let mut args = Vec::new();

        while self.check_match(ArgTermStart) {
            args.push(self.parse_arg_term(Prec(0))?);
        }

        if args.is_empty() {
            Ok(lhs)
        } else {
            Ok(Term::FunApp(Box::new(lhs), args))
        }
    }
}

#[cfg(test)]
mod tests {
    use language_reporting::termcolor::{ColorChoice, StandardStream};
    use mltt_span::Files;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::lexer::Lexer;

    macro_rules! test_term {
        ($src:expr, $expected_term:expr,) => {{
            test_term!($src, $expected_term);
        }};
        ($src:expr, $expected_term:expr) => {{
            let _ = pretty_env_logger::try_init();

            let mut files = Files::new();
            let file_id = files.add("test", $src);
            let term = match parse_term(Lexer::new(&files[file_id])) {
                Ok(term) => term,
                Err(diagnostic) => {
                    let writer = StandardStream::stdout(ColorChoice::Always);
                    language_reporting::emit(
                        &mut writer.lock(),
                        &files,
                        &diagnostic,
                        &language_reporting::DefaultConfig,
                    )
                    .unwrap();
                    panic!("error encountered");
                },
            };

            assert_eq!(term, $expected_term);
        }};
    }

    #[test]
    fn var() {
        test_term!("var", Term::Var("var".to_owned()));
    }

    #[test]
    fn let_expr() {
        test_term!(
            "let var = Type in var",
            Term::Let(
                "var".to_owned(),
                Box::new(Term::Universe(None)),
                Box::new(Term::Var("var".to_owned())),
            ),
        );
    }

    #[test]
    fn parens() {
        test_term!("(foo)", Term::Parens(Box::new(Term::Var("foo".to_owned()))));
    }

    #[test]
    fn fun_ty() {
        test_term!(
            r"Fun (x y : Type) (z : Type) -> x",
            Term::FunType(
                vec![
                    (vec!["x".to_owned(), "y".to_owned()], Term::Universe(None)),
                    (vec!["z".to_owned()], Term::Universe(None)),
                ],
                Box::new(Term::Var("x".to_owned())),
            ),
        );
    }

    #[test]
    fn fun_arrow_type() {
        test_term!(
            "Foo -> Bar",
            Term::FunArrowType(
                Box::new(Term::Var("Foo".to_owned())),
                Box::new(Term::Var("Bar".to_owned()))
            ),
        );
    }

    #[test]
    fn fun_arrow_type_nested() {
        test_term!(
            "Foo -> Bar -> Baz",
            Term::FunArrowType(
                Box::new(Term::Var("Foo".to_owned())),
                Box::new(Term::FunArrowType(
                    Box::new(Term::Var("Bar".to_owned())),
                    Box::new(Term::Var("Baz".to_owned())),
                )),
            ),
        );
    }

    #[test]
    fn fun_arrow_type_fun_app() {
        test_term!(
            "Option A -> Option B -> Option C",
            Term::FunArrowType(
                Box::new(Term::FunApp(
                    Box::new(Term::Var("Option".to_owned())),
                    vec![Term::Var("A".to_owned())]
                )),
                Box::new(Term::FunArrowType(
                    Box::new(Term::FunApp(
                        Box::new(Term::Var("Option".to_owned())),
                        vec![Term::Var("B".to_owned())]
                    )),
                    Box::new(Term::FunApp(
                        Box::new(Term::Var("Option".to_owned())),
                        vec![Term::Var("C".to_owned())]
                    )),
                ),)
            ),
        );
    }

    #[test]
    fn fun_intro() {
        test_term!(
            r"fun x => x",
            Term::FunIntro(vec!["x".to_owned()], Box::new(Term::Var("x".to_owned()))),
        );
    }

    #[test]
    fn fun_intro_multi_params() {
        test_term!(
            r"fun x y z => x",
            Term::FunIntro(
                vec!["x".to_owned(), "y".to_owned(), "z".to_owned()],
                Box::new(Term::Var("x".to_owned())),
            ),
        );
    }

    #[test]
    fn fun_app_1() {
        test_term!(
            r"foo arg",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![Term::Var("arg".to_owned())],
            ),
        );
    }

    #[test]
    fn fun_app_2a() {
        test_term!(
            r"foo arg1 arg2",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![Term::Var("arg1".to_owned()), Term::Var("arg2".to_owned())],
            ),
        );
    }

    #[test]
    fn fun_app_2b() {
        test_term!(
            r"foo (arg1) arg2.fst.snd arg3",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![
                    Term::Parens(Box::new(Term::Var("arg1".to_owned()))),
                    Term::PairSnd(Box::new(Term::PairFst(Box::new(Term::Var(
                        "arg2".to_owned()
                    ))))),
                    Term::Var("arg3".to_owned()),
                ],
            ),
        );
    }

    #[test]
    fn pair_type() {
        test_term!(
            "Pair { Type, Type }",
            Term::PairType(
                None,
                Box::new(Term::Universe(None)),
                Box::new(Term::Universe(None)),
            ),
        );
    }

    #[test]
    fn dependent_pair_type() {
        test_term!(
            "Pair { x : Type, Type }",
            Term::PairType(
                Some("x".to_owned()),
                Box::new(Term::Universe(None)),
                Box::new(Term::Universe(None)),
            ),
        );
    }

    #[test]
    fn pair_intro() {
        test_term!(
            "pair { x, y }",
            Term::PairIntro(
                Box::new(Term::Var("x".to_owned())),
                Box::new(Term::Var("y".to_owned())),
            ),
        );
    }

    #[test]
    fn pair_fst() {
        test_term!(
            "foo.fst",
            Term::PairFst(Box::new(Term::Var("foo".to_owned()))),
        );
    }

    #[test]
    fn pair_fst_fst() {
        test_term!(
            "foo.fst.fst",
            Term::PairFst(Box::new(Term::PairFst(Box::new(Term::Var(
                "foo".to_owned(),
            ))))),
        );
    }

    #[test]
    fn pair_snd() {
        test_term!(
            "foo.snd",
            Term::PairSnd(Box::new(Term::Var("foo".to_owned()))),
        );
    }

    #[test]
    fn pair_snd_snd() {
        test_term!(
            "foo.snd.snd",
            Term::PairSnd(Box::new(Term::PairSnd(Box::new(Term::Var(
                "foo".to_owned(),
            ))))),
        );
    }

    #[test]
    fn pair_fst_snd() {
        test_term!(
            "foo.fst.snd",
            Term::PairSnd(Box::new(Term::PairFst(Box::new(Term::Var(
                "foo".to_owned(),
            ))))),
        );
    }

    #[test]
    fn pair_fst_fun_app() {
        test_term!(
            "foo.fst bar baz.snd",
            Term::FunApp(
                Box::new(Term::PairFst(Box::new(Term::Var("foo".to_owned())))),
                vec![
                    Term::Var("bar".to_owned()),
                    Term::PairSnd(Box::new(Term::Var("baz".to_owned()))),
                ],
            ),
        );
    }

    #[test]
    fn ann() {
        test_term!(
            "foo : Bar : Baz",
            Term::Ann(
                Box::new(Term::Var("foo".to_owned())),
                Box::new(Term::Ann(
                    Box::new(Term::Var("Bar".to_owned())),
                    Box::new(Term::Var("Baz".to_owned()))
                )),
            ),
        );
    }

    #[test]
    fn universe() {
        test_term!("Type", Term::Universe(None));
    }

    #[test]
    fn universe_level_0() {
        test_term!("Type^0", Term::Universe(Some(0)));
    }

    #[test]
    fn universe_level_23() {
        test_term!("Type^23", Term::Universe(Some(23)));
    }
}
