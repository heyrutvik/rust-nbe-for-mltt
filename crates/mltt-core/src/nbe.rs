//! Normalization by evaluation
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use std::error::Error;
use std::fmt;

use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{self, Closure, RcType, RcValue, Value};
use crate::syntax::normal::{self, Normal, RcNormal};
use crate::syntax::{DbIndex, DbLevel};

/// An error produced during normalization
///
/// If a term has been successfully type checked prior to evaluation or
/// normalization, then this error should never be produced.
#[derive(Debug, Clone, PartialEq)]
pub struct NbeError {
    pub message: String,
}

impl NbeError {
    pub fn new(message: impl Into<String>) -> NbeError {
        NbeError {
            message: message.into(),
        }
    }
}

impl Error for NbeError {}

impl fmt::Display for NbeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "failed to normalize: {}", self.message)
    }
}

/// Return the first element of a pair
fn do_pair_fst(pair: &RcValue) -> Result<RcValue, NbeError> {
    match pair.as_ref() {
        Value::PairIntro(fst, _) => Ok(fst.clone()),
        Value::Neutral(pair) => {
            let fst = domain::RcNeutral::from(domain::Neutral::PairFst(pair.clone()));
            Ok(RcValue::from(Value::Neutral(fst)))
        },
        _ => Err(NbeError::new("do_pair_fst: not a pair")),
    }
}

/// Return the second element of a pair
fn do_pair_snd(pair: &RcValue) -> Result<RcValue, NbeError> {
    match pair.as_ref() {
        Value::PairIntro(_, snd) => Ok(snd.clone()),
        Value::Neutral(pair_ne) => {
            let snd = domain::RcNeutral::from(domain::Neutral::PairSnd(pair_ne.clone()));
            Ok(RcValue::from(Value::Neutral(snd)))
        },
        _ => Err(NbeError::new("do_pair_snd: not a pair")),
    }
}

/// Apply a closure to an argument
pub fn do_closure_app(closure: &Closure, arg: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.push_front(arg);
    eval(&closure.term, &env)
}

/// Apply a function to an argument
pub fn do_fun_app(fun: &RcValue, arg: RcValue) -> Result<RcValue, NbeError> {
    match fun.as_ref() {
        Value::FunIntro(_, body) => do_closure_app(body, arg),
        Value::Neutral(fun) => {
            let body = domain::RcNeutral::from(domain::Neutral::FunApp(fun.clone(), arg.clone()));
            Ok(RcValue::from(Value::Neutral(body)))
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Evaluate a syntactic term into a semantic value
pub fn eval(term: &RcTerm, env: &domain::Env) -> Result<RcValue, NbeError> {
    match term.as_ref() {
        Term::Var(DbIndex(index)) => match env.get(*index as usize) {
            Some(value) => Ok(value.clone()),
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::Literal(literal) => Ok(RcValue::from(Value::Literal(literal.clone()))),
        Term::Let(def, /* _, */ body) => {
            let def = eval(def, env)?;
            let mut env = env.clone();
            env.push_front(def);
            eval(body, &env)
        },

        // Functions
        Term::FunType(param_ty, body_ty) => {
            let param_ty = eval(param_ty, env)?;
            let body_ty = Closure::new(body_ty.clone(), env.clone());

            Ok(RcValue::from(Value::FunType(param_ty, body_ty)))
        },
        Term::FunIntro(param_ty, body) => {
            let param_ty = eval(param_ty, env)?;
            let body = Closure::new(body.clone(), env.clone());

            Ok(RcValue::from(Value::FunIntro(param_ty, body)))
        },
        Term::FunApp(fun, arg) => do_fun_app(&eval(fun, env)?, eval(arg, env)?),

        // Pairs
        Term::PairType(fst_ty, snd_ty) => {
            let fst_ty = eval(fst_ty, env)?;
            let snd_ty = Closure::new(snd_ty.clone(), env.clone());

            Ok(RcValue::from(Value::PairType(fst_ty, snd_ty)))
        },
        Term::PairIntro(fst, snd /* _, _, _ */) => {
            let fst = eval(fst, env)?;
            let snd = eval(snd, env)?;

            Ok(RcValue::from(Value::PairIntro(fst, snd)))
        },
        Term::PairFst(pair) => do_pair_fst(&eval(pair, env)?),
        Term::PairSnd(pair) => do_pair_snd(&eval(pair, env)?),

        // Universes
        Term::Universe(level) => Ok(RcValue::from(Value::Universe(*level))),
    }
}

/// Quote back a term into normal form
pub fn read_back_term(level: DbLevel, term: &RcValue) -> Result<RcNormal, NbeError> {
    match term.as_ref() {
        Value::Neutral(term) => {
            let neutral = read_back_neutral(level, term)?;

            Ok(RcNormal::from(Normal::Neutral(neutral)))
        },

        // Literals
        Value::Literal(literal) => Ok(RcNormal::from(Normal::Literal(literal.clone()))),

        // Functions
        Value::FunType(param_ty, body_ty) => {
            let param = RcValue::var(level);
            let param_ty = param_ty.clone();
            let body_ty = do_closure_app(body_ty, param)?;

            Ok(RcNormal::from(Normal::FunType(
                read_back_term(level, &param_ty)?,
                read_back_term(level + 1, &body_ty)?,
            )))
        },
        Value::FunIntro(param_ty, body) => {
            let param = RcValue::var(level);
            let param_ty = read_back_term(level, &param_ty)?;
            let body = read_back_term(level + 1, &do_closure_app(body, param.clone())?)?;

            Ok(RcNormal::from(Normal::FunIntro(param_ty, body)))
        },

        // Pairs
        Value::PairType(fst_ty, snd_ty) => {
            let fst = RcValue::var(level);
            let fst_ty = fst_ty.clone();
            let snd_ty = do_closure_app(snd_ty, fst)?;

            Ok(RcNormal::from(Normal::PairType(
                read_back_term(level, &fst_ty)?,
                read_back_term(level + 1, &snd_ty)?,
            )))
        },
        Value::PairIntro(fst, snd) => {
            let fst = read_back_term(level, &fst)?;
            let snd = read_back_term(level, &snd)?;

            Ok(RcNormal::from(Normal::PairIntro(fst, snd)))
        },

        // Universes
        Value::Universe(level) => Ok(RcNormal::from(Normal::Universe(*level))),
    }
}

/// Quote back a neutral term into normal form
pub fn read_back_neutral(
    level: DbLevel,
    neutral: &domain::RcNeutral,
) -> Result<normal::RcNeutral, NbeError> {
    match &neutral.as_ref() {
        domain::Neutral::Var(var_level) => {
            let index = DbIndex(level.0 - (var_level.0 + 1));

            Ok(normal::RcNeutral::from(normal::Neutral::Var(index)))
        },
        domain::Neutral::FunApp(fun, arg) => {
            let fun = read_back_neutral(level, fun)?;
            let arg = read_back_term(level, arg)?;

            Ok(normal::RcNeutral::from(normal::Neutral::FunApp(fun, arg)))
        },
        domain::Neutral::PairFst(pair) => {
            let pair = read_back_neutral(level, pair)?;

            Ok(normal::RcNeutral::from(normal::Neutral::PairFst(pair)))
        },
        domain::Neutral::PairSnd(pair) => {
            let pair = read_back_neutral(level, pair)?;

            Ok(normal::RcNeutral::from(normal::Neutral::PairSnd(pair)))
        },
    }
}

/// Check whether a semantic type is a subtype of another
pub fn check_subtype(level: DbLevel, ty1: &RcType, ty2: &RcType) -> Result<bool, NbeError> {
    match (&ty1.as_ref(), &ty2.as_ref()) {
        (&Value::Neutral(term1), &Value::Neutral(term2)) => {
            let term1 = read_back_neutral(level, term1)?;
            let term2 = read_back_neutral(level, term2)?;

            Ok(term1 == term2)
        },
        (&Value::FunType(param_ty1, body_ty1), &Value::FunType(param_ty2, body_ty2)) => {
            let param = RcValue::var(level);

            Ok(check_subtype(level, param_ty2, param_ty1)? && {
                let body_ty1 = do_closure_app(body_ty1, param.clone())?;
                let body_ty2 = do_closure_app(body_ty2, param)?;
                check_subtype(level + 1, &body_ty1, &body_ty2)?
            })
        },
        (&Value::PairType(fst_ty1, snd_ty1), &Value::PairType(fst_ty2, snd_ty2)) => {
            let fst = RcValue::var(level);

            Ok(check_subtype(level, fst_ty1, fst_ty2)? && {
                let snd_ty1 = do_closure_app(snd_ty1, fst.clone())?;
                let snd_ty2 = do_closure_app(snd_ty2, fst)?;
                check_subtype(level + 1, &snd_ty1, &snd_ty2)?
            })
        },
        (&Value::Universe(level1), &Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}
