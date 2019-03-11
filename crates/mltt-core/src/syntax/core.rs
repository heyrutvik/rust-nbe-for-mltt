//! The checked core syntax

use pretty::{BoxDoc, Doc};
use std::fmt;
use std::rc::Rc;

use crate::syntax::{AppMode, Label, LiteralIntro, LiteralType, UniverseLevel, VarIndex};

pub type Env = im::Vector<RcTerm>;

/// Top-level items
#[derive(Debug, Clone, PartialEq)]
pub struct Item {
    pub doc: String,
    pub label: String,
    pub term_ty: RcTerm,
    pub term: RcTerm,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RcTerm {
    pub inner: Rc<Term>,
}

impl From<Term> for RcTerm {
    fn from(src: Term) -> RcTerm {
        RcTerm {
            inner: Rc::new(src),
        }
    }
}

impl AsRef<Term> for RcTerm {
    fn as_ref(&self) -> &Term {
        self.inner.as_ref()
    }
}

impl fmt::Display for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Core terms
// TODO: explicitly annotate with types
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(VarIndex),
    /// Let bindings
    Let(RcTerm, RcTerm),

    /// Literal types
    LiteralType(LiteralType),
    /// Literal introductions
    LiteralIntro(LiteralIntro),

    /// Dependent function types
    FunType(AppMode, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(AppMode, RcTerm),
    /// Eliminate a function (application)
    FunElim(RcTerm, AppMode, RcTerm),

    /// Dependent record types
    RecordType(Vec<(String, Label, RcTerm)>),
    /// Introduce a record
    RecordIntro(Vec<(Label, RcTerm)>),
    /// Eliminate a record (projection)
    RecordElim(RcTerm, Label),

    /// Universe of types
    Universe(UniverseLevel),
}

impl RcTerm {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        self.inner.to_doc()
    }
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Let(def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def.as_ref()))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body.as_ref())),
                Term::FunType(app_mode, param_ty, body_ty) => {
                    let param = match app_mode {
                        AppMode::Explicit => Doc::nil()
                            .append("(")
                            .append("_")
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(param_ty.as_ref()))
                            .append(")"),
                        AppMode::Implicit(label) => Doc::nil()
                            .append("{")
                            .append(&label.0)
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(param_ty.as_ref()))
                            .append("}"),
                    };

                    Doc::nil()
                        .append(Doc::group(
                            Doc::text("Fun").append(Doc::space()).append(param),
                        ))
                        .append(Doc::space())
                        .append("->")
                        .append(Doc::space())
                        .append(to_doc_app(body_ty.as_ref()))
                },
                Term::FunIntro(app_mode, body) => {
                    let param = match app_mode {
                        AppMode::Explicit => Doc::text("_"),
                        AppMode::Implicit(label) => Doc::nil()
                            .append("{")
                            .append(&label.0)
                            .append(Doc::space())
                            .append("=")
                            .append(Doc::space())
                            .append("_")
                            .append("}"),
                    };

                    Doc::nil()
                        .append("fun")
                        .append(Doc::space())
                        .append(param)
                        .append(Doc::space())
                        .append("=>")
                        .append(Doc::space())
                        .append(to_doc_app(body.as_ref()))
                },
                Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
                Term::RecordType(ty_fields) => Doc::nil()
                    .append("Record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(
                        Doc::intersperse(
                            ty_fields.iter().map(|(_, label, ty)| {
                                Doc::nil()
                                    .append(&label.0)
                                    .append(Doc::space())
                                    .append(":")
                                    .append(Doc::space())
                                    .append(to_doc_app(ty.as_ref()))
                                    .append(";")
                            }),
                            Doc::newline(),
                        )
                        .nest(4),
                    )
                    .append(Doc::newline())
                    .append("}"),
                Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                    Doc::text("record {}")
                },
                Term::RecordIntro(intro_fields) => Doc::nil()
                    .append("record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(
                        Doc::intersperse(
                            intro_fields.iter().map(|(label, term)| {
                                Doc::nil()
                                    .append(&label.0)
                                    .append(Doc::space())
                                    .append("=")
                                    .append(Doc::space())
                                    .append(to_doc_app(term.as_ref()))
                                    .append(";")
                            }),
                            Doc::newline(),
                        )
                        .nest(4),
                    )
                    .append(Doc::newline())
                    .append("}"),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::FunElim(fun, app_mode, arg) => {
                    let arg = match app_mode {
                        AppMode::Explicit => to_doc_atomic(arg.as_ref()),
                        AppMode::Implicit(label) => Doc::nil()
                            .append("{")
                            .append(&label.0)
                            .append(Doc::space())
                            .append("=")
                            .append(Doc::space())
                            .append(to_doc_term(arg.as_ref()))
                            .append("}"),
                    };

                    Doc::nil()
                        .append(to_doc_term(fun.as_ref()))
                        .append(Doc::space())
                        .append(arg)
                },
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Var(VarIndex(index)) => Doc::as_string(format!("@{}", index)),
                Term::LiteralType(literal_ty) => literal_ty.to_doc(),
                Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
                Term::RecordElim(record, label) => {
                    to_doc_atomic(record.as_ref()).append(".").append(&label.0)
                },
                Term::Universe(UniverseLevel(level)) => {
                    Doc::text("Type^").append(Doc::as_string(level))
                },
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
