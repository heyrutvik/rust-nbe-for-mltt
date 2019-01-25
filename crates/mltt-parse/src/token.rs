use mltt_span::FileSpan;

/// A kind of delimiter
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DelimKind {
    /// A round parenthesis: `(` or `)`
    Paren,
    /// A curly brace: `{` or `}`
    Brace,
    /// A square bracket: `[` or `]`
    Bracket,
}

/// A tag that makes it easier to remember what type of token this is
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Error,

    Whitespace,
    LineComment,
    LineDoc,

    Keyword,
    Symbol,
    Identifier,
    StringLiteral,
    CharLiteral,
    IntLiteral,
    FloatLiteral,

    BSlash,
    Caret,
    Colon,
    Dot,
    Equals,
    RArrow,
    RFatArrow,

    Comma,
    Semicolon,

    Open(DelimKind),
    Close(DelimKind),
}

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'file> {
    /// The token kind
    pub kind: TokenKind,
    /// The slice of source code that produced the token
    pub slice: &'file str,
    /// The span in the source code
    pub span: FileSpan,
}

impl Token<'_> {
    pub fn is_whitespace(&self) -> bool {
        self.kind == TokenKind::Whitespace || self.kind == TokenKind::LineComment
    }

    pub fn is_keyword(&self, slice: &str) -> bool {
        self.kind == TokenKind::Keyword && self.slice == slice
    }
}