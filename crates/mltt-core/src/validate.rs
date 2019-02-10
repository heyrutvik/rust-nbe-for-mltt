//! Bidirectional type checking of the core syntax
//!
//! This is used to verify that the core syntax is correctly formed, for
//! debugging purposes.

use im;
use std::error::Error;
use std::fmt;

use crate::nbe::{self, NbeError};
use crate::syntax::core::{self, Item, RcTerm, Term};
use crate::syntax::domain::{self, RcType, RcValue, Value};
use crate::syntax::{DbIndex, DbLevel, UniverseLevel};

/// Local type checking context
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    /// Number of local entries
    level: DbLevel,
    /// Values to be used during evaluation
    values: domain::Env,
    /// Type annotations of the binders we have passed over
    binders: im::Vector<RcType>,
}

impl Context {
    /// Create a new, empty context
    pub fn new() -> Context {
        Context {
            level: DbLevel(0),
            values: domain::Env::new(),
            binders: im::Vector::new(),
        }
    }

    /// Number of local entries in the context
    pub fn level(&self) -> DbLevel {
        self.level
    }

    /// Values to be used during evaluation
    pub fn values(&self) -> &domain::Env {
        &self.values
    }

    /// Add a new local entry to the context
    pub fn insert_local(&mut self, value: RcValue, ty: RcType) {
        self.level += 1;
        self.values.push_front(value);
        self.binders.push_front(ty);
    }

    /// Add a new binder to the context, returning a value that points to the parameter
    pub fn insert_binder(&mut self, ty: RcType) -> RcValue {
        let param = RcValue::var(self.level());
        self.insert_local(param.clone(), ty);
        param
    }

    /// Lookup the type annotation of a binder in the context
    pub fn lookup_binder(&self, index: DbIndex) -> Option<&RcType> {
        self.binders.get(index.0 as usize)
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(&self, term: &core::RcTerm) -> Result<domain::RcValue, NbeError> {
        nbe::eval(term, self.values())
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context
    pub fn expect_subtype(&self, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
        if nbe::check_subtype(self.level(), ty1, ty2)? {
            Ok(())
        } else {
            Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
        }
    }
}

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    ExpectedFunType {
        found: RcType,
    },
    ExpectedPairType {
        found: RcType,
    },
    ExpectedUniverse {
        over: Option<UniverseLevel>,
        found: RcType,
    },
    ExpectedSubtype(RcType, RcType),
    AmbiguousTerm(RcTerm),
    UnboundVariable,
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TypeError::Nbe(error) => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { over, .. } => match over {
                None => write!(f, "expected universe"),
                Some(level) => write!(f, "expected universe over level `{}`", level.0),
            },
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable => write!(f, "unbound variable"),
            TypeError::Nbe(err) => err.fmt(f),
        }
    }
}

/// Check that this is a valid module
pub fn check_module(items: &[Item]) -> Result<(), TypeError> {
    let mut context = Context::new();

    for item in items {
        log::trace!("checking item:\t{}", item.name);

        check_term_ty(&context, &item.term_ty)?;
        let term_ty = context.eval(&item.term_ty)?;
        check_term(&context, &item.term, &term_ty)?;
        let value = context.eval(&item.term)?;
        context.insert_local(value, term_ty);

        log::trace!("validated item:\t{}", item.name);
    }

    Ok(())
}

/// Check that a term conforms to a given type
pub fn check_term(context: &Context, term: &RcTerm, expected_ty: &RcType) -> Result<(), TypeError> {
    log::trace!("checking term:\t\t{}", term);

    match term.as_ref() {
        Term::Literal(literal) => unimplemented!("literals {:?}", literal),
        Term::Let(def, body) => {
            let mut body_context = context.clone();
            body_context.insert_local(context.eval(def)?, synth_term(context, def)?);

            check_term(&body_context, body, expected_ty)
        },

        Term::FunType(ann_ty, body_ty) | Term::PairType(ann_ty, body_ty) => {
            check_term(context, ann_ty, expected_ty)?;
            let ann_ty_value = context.eval(ann_ty)?;

            let mut body_ty_context = context.clone();
            body_ty_context.insert_binder(ann_ty_value);

            check_term(&body_ty_context, body_ty, expected_ty)
        },
        Term::FunIntro(body) => match expected_ty.as_ref() {
            Value::FunType(param_ty, body_ty) => {
                let mut body_context = context.clone();
                let param = body_context.insert_binder(param_ty.clone());
                let body_ty = nbe::do_closure_app(body_ty, param)?;

                check_term(&body_context, body, &body_ty)
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        Term::PairIntro(fst, snd) => match expected_ty.as_ref() {
            Value::PairType(fst_ty, snd_ty) => {
                check_term(context, fst, fst_ty)?;
                let fst_value = context.eval(fst)?;
                check_term(context, snd, &nbe::do_closure_app(snd_ty, fst_value)?)
            },
            _ => Err(TypeError::ExpectedPairType {
                found: expected_ty.clone(),
            }),
        },

        Term::Universe(term_level) => match expected_ty.as_ref() {
            Value::Universe(ann_level) if term_level < ann_level => Ok(()),
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(*term_level),
                found: expected_ty.clone(),
            }),
        },

        _ => context.expect_subtype(&synth_term(context, term)?, expected_ty),
    }
}

/// Synthesize the type of the term
pub fn synth_term(context: &Context, term: &RcTerm) -> Result<RcType, TypeError> {
    log::trace!("synthesizing term:\t\t{}", term);

    match term.as_ref() {
        Term::Var(index) => match context.lookup_binder(*index) {
            None => Err(TypeError::UnboundVariable),
            Some(ann) => Ok(ann.clone()),
        },
        Term::Literal(literal) => unimplemented!("literals {:?}", literal),
        Term::Let(def, body) => {
            let mut body_context = context.clone();
            let def_ty = synth_term(context, def)?;
            body_context.insert_local(context.eval(def)?, def_ty);

            synth_term(&body_context, body)
        },

        Term::FunApp(fun, arg) => {
            let fun_ty = synth_term(context, fun)?;
            match fun_ty.as_ref() {
                Value::FunType(arg_ty, body_ty) => {
                    check_term(context, arg, arg_ty)?;
                    let arg_value = context.eval(arg)?;
                    Ok(nbe::do_closure_app(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairFst(pair) => {
            let pair_ty = synth_term(context, pair)?;
            match pair_ty.as_ref() {
                Value::PairType(fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(pair) => {
            let pair_ty = synth_term(context, pair)?;
            match pair_ty.as_ref() {
                Value::PairType(_, snd_ty) => {
                    let fst = context.eval(&RcTerm::from(Term::PairFst(pair.clone())))?;
                    Ok(nbe::do_closure_app(snd_ty, fst)?)
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(term.clone())),
    }
}

/// Check that the given term is a type
pub fn check_term_ty(context: &Context, term: &RcTerm) -> Result<(), TypeError> {
    log::trace!("checking term is type:\t{}", term);

    match term.as_ref() {
        Term::Let(def, body) => {
            let mut body_context = context.clone();
            body_context.insert_local(context.eval(def)?, synth_term(context, def)?);

            check_term_ty(&body_context, body)
        },

        Term::FunType(ann, body) | Term::PairType(ann, body) => {
            check_term_ty(context, ann)?;
            let ann_value = context.eval(ann)?;

            let mut body_context = context.clone();
            body_context.insert_binder(ann_value);

            check_term_ty(&body_context, body)
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth_term(context, term)?;
            match synth_ty.as_ref() {
                Value::Universe(_) => Ok(()),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: synth_ty,
                }),
            }
        },
    }
}
