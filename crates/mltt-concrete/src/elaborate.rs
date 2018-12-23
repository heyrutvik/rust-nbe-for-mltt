//! Elaboration of the implicit syntax into the explicit syntax
//!
//! Performs the following:
//!
//! - name resolution
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

use im;
use mltt_core::nbe::{self, NbeError};
use mltt_core::syntax::core;
use mltt_core::syntax::domain::{self, RcType, RcValue, Value};
use mltt_core::syntax::{DbIndex, DbLevel, UniverseLevel};

use crate::syntax::raw;

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context<'term> {
    /// Number of local entries
    size: u32,
    /// Values to be used during evaluation
    values: domain::Env,
    /// Types of the binders we have passed over
    tys: im::Vector<(Option<&'term String>, RcType)>,
}

impl<'term> Context<'term> {
    pub fn new() -> Context<'term> {
        Context {
            size: 0,
            values: domain::Env::new(),
            tys: im::Vector::new(),
        }
    }

    pub fn insert(&mut self, ident: impl Into<Option<&'term String>>, value: RcValue, ty: RcType) {
        self.size += 1;
        self.values.push_front(value);
        self.tys.push_front((ident.into(), ty));
    }

    pub fn lookup_ty(&self, ident: &str) -> Option<(DbIndex, &RcType)> {
        for (i, &(ref n, ref ty)) in self.tys.iter().enumerate() {
            if Some(ident) == n.map(String::as_str) {
                return Some((DbIndex(i as u32), ty));
            }
        }
        None
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
    AmbiguousTerm(raw::RcTerm),
    AmbiguousPatternVariable(String),
    UnboundVariable(String),
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

fn check_subtype(context: &Context, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
    if nbe::check_subtype(context.size, ty1, ty2)? {
        Ok(())
    } else {
        Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
    }
}

/// Check that a term conforms to a given type
pub fn check_term<'term>(
    context: &Context<'term>,
    raw_term: &'term raw::RcTerm,
    expected_ty: &RcType,
) -> Result<core::RcTerm, TypeError> {
    match *raw_term.inner {
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let body = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                check_term(&context, raw_body, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },
        raw::Term::Case(ref scrutinees, ref equations) => {
            unimplemented!("elaborate::check: case expressions");
        },

        raw::Term::FunType(ref ident, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_term_ty(context, raw_param_ty)?;
            let param_ty_value = nbe::eval(&param_ty, &context.values)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(context.size)), param_ty_value);
                check_term_ty(&context, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },
        raw::Term::FunIntro(ref ident, ref body) => match *expected_ty.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let param = RcValue::var(DbLevel(context.size));
                let body_ty = nbe::do_closure_app(body_ty, param.clone())?;
                let body = {
                    let mut context = context.clone();
                    context.insert(ident, param, param_ty.clone());
                    check_term(&context, body, &body_ty)?
                };

                Ok(core::RcTerm::from(core::Term::FunIntro(body)))
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        raw::Term::PairType(ref ident, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_term_ty(context, raw_fst_ty)?;
            let fst_ty_value = nbe::eval(&fst_ty, &context.values)?;
            let snd_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(context.size)), fst_ty_value);
                check_term_ty(&context, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },
        raw::Term::PairIntro(ref raw_fst, ref raw_snd) => match *expected_ty.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                let fst = check_term(context, raw_fst, fst_ty)?;
                let fst_value = nbe::eval(&fst, &context.values)?;
                let snd_ty_value = nbe::do_closure_app(snd_ty, fst_value)?;
                let snd = check_term(context, raw_snd, &snd_ty_value)?;

                Ok(core::RcTerm::from(core::Term::PairIntro(fst, snd)))
            },
            _ => Err(TypeError::ExpectedPairType {
                found: expected_ty.clone(),
            }),
        },

        raw::Term::Universe(term_level) => match *expected_ty.inner {
            Value::Universe(ann_level) if term_level < ann_level => {
                Ok(core::RcTerm::from(core::Term::Universe(term_level)))
            },
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(term_level),
                found: expected_ty.clone(),
            }),
        },

        _ => {
            let (term, synth_ty) = synth_term(context, raw_term)?;
            check_subtype(context, &synth_ty, expected_ty)?;
            Ok(term)
        },
    }
}

/// Synthesize the type of the term
pub fn synth_term<'term>(
    context: &Context<'term>,
    raw_term: &'term raw::RcTerm,
) -> Result<(core::RcTerm, RcType), TypeError> {
    match *raw_term.inner {
        raw::Term::Var(ref ident) => match context.lookup_ty(ident.as_str()) {
            None => Err(TypeError::UnboundVariable(ident.clone())),
            Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
        },
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let (body, body_ty) = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                synth_term(&context, raw_body)?
            };

            Ok((core::RcTerm::from(core::Term::Let(def, body)), body_ty))
        },
        raw::Term::Ann(ref raw_term, ref raw_ann) => {
            let ann = check_term_ty(context, raw_ann)?;
            let ann_value = nbe::eval(&ann, &context.values)?;
            let term = check_term(context, raw_term, &ann_value)?;

            Ok((term, ann_value))
        },

        raw::Term::FunApp(ref raw_fun, ref raw_arg) => {
            let (fun, fun_ty) = synth_term(context, raw_fun)?;
            match *fun_ty.inner {
                Value::FunType(ref param_ty, ref body_ty) => {
                    let arg = check_term(context, raw_arg, param_ty)?;
                    let arg_value = nbe::eval(&arg, &context.values)?;
                    let term = core::RcTerm::from(core::Term::FunApp(fun, arg));

                    Ok((term, nbe::do_closure_app(body_ty, arg_value)?))
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        raw::Term::PairFst(ref raw_pair) => {
            let (pair, pair_ty) = synth_term(context, raw_pair)?;
            match *pair_ty.inner {
                Value::PairType(ref fst_ty, _) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    Ok((fst, fst_ty.clone()))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        raw::Term::PairSnd(ref raw_pair) => {
            let (pair, pair_ty) = synth_term(context, raw_pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    let fst_value = nbe::eval(&fst, &context.values)?;
                    let snd = core::RcTerm::from(core::Term::PairSnd(pair));

                    Ok((snd, nbe::do_closure_app(snd_ty, fst_value)?))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(raw_term.clone())),
    }
}

/// Check that the given term is a type
pub fn check_term_ty<'term>(
    context: &Context<'term>,
    raw_term: &'term raw::RcTerm,
) -> Result<core::RcTerm, TypeError> {
    match *raw_term.inner {
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let body = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                check_term_ty(&context, raw_body)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },

        raw::Term::FunType(ref ident, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_term_ty(context, raw_param_ty)?;
            let param_ty_value = nbe::eval(&param_ty, &context.values)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(context.size)), param_ty_value);
                check_term_ty(&context, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },

        raw::Term::PairType(ref ident, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_term_ty(context, raw_fst_ty)?;
            let fst_ty_value = nbe::eval(&fst_ty, &context.values)?;
            let snd_ty = {
                let mut snd_ty_context = context.clone();
                snd_ty_context.insert(ident, RcValue::var(DbLevel(context.size)), fst_ty_value);
                check_term_ty(&snd_ty_context, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },

        raw::Term::Universe(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),

        _ => {
            let (term, term_ty) = synth_term(context, raw_term)?;
            match *term_ty.inner {
                Value::Universe(_) => Ok(term),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: term_ty,
                }),
            }
        },
    }
}

/// Check that a pattern conforms to a given type
pub fn check_pattern<'term>(
    context: &Context<'term>,
    raw_pattern: &'term raw::RcPattern,
    expected_ty: &RcType,
) -> Result<Vec<String>, TypeError> {
    match *raw_pattern.inner {
        raw::Pattern::Var(ref ident) => Ok(vec![ident.clone()]),

        _ => {
            let (pattern_vars, pattern_ty) = synth_pattern(context, raw_pattern)?;
            check_subtype(context, &pattern_ty, expected_ty)?;
            Ok(pattern_vars)
        },
    }
}

/// Synthesize the type of the pattern
pub fn synth_pattern<'term>(
    context: &Context<'term>,
    raw_pattern: &'term raw::RcPattern,
) -> Result<(Vec<String>, RcType), TypeError> {
    match *raw_pattern.inner {
        raw::Pattern::Var(ref ident) => Err(TypeError::AmbiguousPatternVariable(ident.clone())),

        raw::Pattern::Ann(ref raw_pattern, ref raw_ann) => {
            let ann = check_term_ty(context, raw_ann)?;
            let ann_value = nbe::eval(&ann, &context.values)?;
            let pattern_vars = check_pattern(context, raw_pattern, &ann_value)?;

            Ok((pattern_vars, ann_value))
        },

        raw::Pattern::PairIntro(ref fst, ref snd) => unimplemented!("synth_pattern: PairIntro"),
    }
}

pub fn match_equations(
    scrutinees: Vec<raw::RcTerm>,
    equations: Vec<(Vec<raw::RcPattern>, core::RcTerm)>,
    default: &core::RcTerm,
) -> Result<core::RcTerm, TypeError> {
    // VARIABLE RULE:
    // - if each equation starts with a variable pattern:
    //   - pop the front of the list of scrutinees, calling it `s1`
    //   - for each equation:
    //     - pop the front of each pattern, calling it `p1`
    //     - substitute each usage of `p1` in the body of the equation with `s1`

    if equations.iter().all(|(patterns, _)| unimplemented!()) {
        // return match_equations(scrutinees, equations, default);
        unimplemented!()
    }

    // CONSTRUCTOR RULE:
    // - if each equation begins with a constructor
    //   - pop the front of the list of scrutinees, calling it `s1`
    //   - for each equation:
    //     - group together the equations that begin with the same constructor
    //     - for each group:
    //       - for each equation:
    //         - pop the front of each pattern
    //       - introduce new variables corresponding to each field of the constructor
    //       - match against these new variables with the subpatterns of the equations

    // EMPTY RULE:
    // - if list of scrutinees is empty
    //   - if each equation starts with a list of empty of patterns
    //     - replace entire expression with the body of the first equation

    if scrutinees.is_empty() {
        if equations.iter().all(|&(ref patts, _)| patts.is_empty()) {
            match equations.first() {
                Some(&(_, ref body)) => return Ok(body.clone()),
                None => return Ok(default.clone()),
            }
        } else {
            unimplemented!()
        }
    }

    // MIXTURE RULE:
    // - if not all equations start with a variable pattern or not all equations
    //   start with a constructor pattern
    //   - group the equations that start with a variable
    //   - group the equations that start with a constructor
    //   - TODO...

    unimplemented!()
}

// Algorithm inspired by _Elaborating Dependent (Co)Pattern Matching_ by Jesper
// Cockx and Andreas Abel.

/// A constraint to be applied to a pattern
type Constraint = (core::RcTerm, raw::RcPattern);

type Substitution = (core::RcTerm, raw::RcPattern);

/// A partially deconstructed clause
///
/// Note that on the left-hand side we have raw patterns. These will eventually
/// be converted into case trees in the core language on the right.
///
/// ```
/// [E]q̅ ↪︎ rhs
/// ```
struct Clause {
    /// ```
    /// E
    /// ```
    constraint: Constraint,
    /// ```
    /// q̅
    /// ```
    patterns: Vec<raw::RcPattern>,
    /// ```
    /// rhs
    /// ```
    body: core::RcTerm,
}

fn done(
    context: &Context,
    constraint: &Constraint,
) -> Result<Vec<Substitution>, TypeError> {
    unimplemented!()
}

/// Clauses:
///
/// ```
/// P = { [Eᵢ]q̅ᵢ ↪︎ rhsᵢ | i = 0..<m }
/// ```
#[allow(dead_code)]
fn check_clauses(
    context: &Context,
    clauses: &[Clause],
    scrutinees: &[raw::RcTerm],
    expected_ty: &RcType,
) -> Result<core::RcTerm, TypeError> {
    // Done
    //
    // Applies when the first user clause (in `P`) has no more copatterns and
    // all its constraints are solved according to `Γ ⊢ E ⇒ SOLVED(σ).
    if clauses[0].patterns.is_empty() {
        let substs = done(context, &clauses[0].constraint)?;

        // TODO
    }

    // Intro
    //
    // Applies when `C` is a function type and all the user clauses have at
    // least one application copattern.

    // TODO

    // SplitCon

    // TODO

    // SplitEq

    // TODO

    // SplitEmpty

    // TODO

    unimplemented!()
}

fn infer_clauses(
    context: &Context,
    clauses: &[Clause],
    scrutinees: &[raw::RcTerm],
    expected_ty: &RcType,
) -> Result<(core::RcTerm, RcType), TypeError> {
    unimplemented!()
}
