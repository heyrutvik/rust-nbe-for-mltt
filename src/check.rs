use im;

use nbe::{self, NbeError};
use syntax::core::{self, RcTerm, Term};
use syntax::domain::{self, RcValue, Value};
use syntax::{DbIndex, DbLevel, UniverseLevel};

#[derive(Debug, Clone)]
pub enum Entry {
    Term { term: RcValue, ann: RcValue },
    TopLevel { term: RcValue, ann: RcValue },
}

pub type Env = im::Vector<Entry>;

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    ExpectedFunType {
        found: RcValue,
    },
    ExpectedPairType {
        found: RcValue,
    },
    ExpectedUniverse {
        over: Option<UniverseLevel>,
        found: RcValue,
    },
    ExpectedSubtype(RcValue, RcValue),
    AmbiguousTerm(RcTerm),
    UnboundVariable,
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

fn env_to_domain_env(env: &Env) -> domain::Env {
    env.iter()
        .map(|entry| match *entry {
            Entry::Term { ref term, .. } => term.clone(),
            Entry::TopLevel { ref term, .. } => term.clone(),
        })
        .collect()
}

fn check_subtype(size: u32, ty1: &RcValue, ty2: &RcValue) -> Result<(), TypeError> {
    if nbe::check_subtype(size, ty1, ty2)? {
        Ok(())
    } else {
        Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
    }
}

pub fn check(env: &Env, size: u32, term: &RcTerm, ann: &RcValue) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            check(&body_env, size + 1, body, ann)
        },

        Term::NatType => match *ann.inner {
            Value::Universe(_) => Ok(()),
            _ => Err(TypeError::ExpectedUniverse {
                over: None,
                found: ann.clone(),
            }),
        },

        Term::FunType(ref ann, ref body) | Term::PairType(ref ann, ref body) => {
            check_ty(env, size, ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;

            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size), ann_value.clone()),
                ann: ann_value,
            });

            check_ty(&body_env, size + 1, body)
        },
        Term::FunIntro(ref body) => match *ann.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let var = RcValue::var(DbLevel(size), param_ty.clone());
                let body_ty = nbe::do_closure1(body_ty, var.clone())?;

                let mut body_env = env.clone();
                body_env.push_front(Entry::Term {
                    term: var,
                    ann: param_ty.clone(),
                });

                check(&body_env, size + 1, body, &body_ty)
            },
            _ => Err(TypeError::ExpectedFunType { found: ann.clone() }),
        },

        Term::PairIntro(ref fst, ref snd) => match *ann.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                check(env, size, fst, fst_ty)?;
                let fst_value = nbe::eval(fst, &env_to_domain_env(env))?;
                check(env, size, snd, &nbe::do_closure1(snd_ty, fst_value)?)
            },
            _ => Err(TypeError::ExpectedPairType { found: ann.clone() }),
        },

        Term::Universe(term_level) => match *ann.inner {
            Value::Universe(ann_level) if term_level < ann_level => Ok(()),
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(term_level),
                found: ann.clone(),
            }),
        },

        _ => check_subtype(size, &synth(env, size, term)?, ann),
    }
}

pub fn synth(env: &Env, size: u32, term: &RcTerm) -> Result<RcValue, TypeError> {
    match *term.inner {
        Term::Var(DbIndex(index)) => match env.get(index as usize) {
            None => Err(TypeError::UnboundVariable),
            Some(Entry::Term { ref ann, .. }) | Some(Entry::TopLevel { ref ann, .. }) => {
                Ok(ann.clone())
            },
        },
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            synth(&body_env, size + 1, body)
        },
        Term::Check(ref term, ref ann) => {
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;
            check(env, size, term, &ann_value)?;
            Ok(ann_value)
        },

        Term::NatZero => Ok(RcValue::from(Value::NatType)),
        Term::NatSucc(ref nat) => {
            let nat_ty = RcValue::from(Value::NatType);
            check(env, size, nat, &nat_ty)?;
            Ok(nat_ty)
        },
        Term::NatRec(ref motive, ref zero, ref succ, ref nat) => {
            //   | NRec (mot, zero, suc, n) ->
            //     check ~env ~size ~term:n ~tp:Nat;
            //     let var = D.mk_var Nat size in
            //     check_tp ~env:(add_term ~term:var ~tp:Nat env) ~size:(size + 1) ~term:mot;
            //     let sem_env = env_to_sem_env env in
            //     let zero_tp = Nbe.eval mot (Zero :: sem_env) in
            //     let ih_tp = Nbe.eval mot (var :: sem_env) in
            //     let ih_var = D.mk_var ih_tp (size + 1) in
            //     let suc_tp = Nbe.eval mot (Suc var :: sem_env) in
            //     check ~env ~size ~term:zero ~tp:zero_tp;
            //     check
            //       ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
            //       ~size:(size + 2)
            //       ~term:suc
            //       ~tp:suc_tp;
            //     Nbe.eval mot (Nbe.eval n sem_env :: sem_env)
            unimplemented!("synth: Term::NatRec")
        },

        Term::FunApp(ref fun, ref arg) => {
            let fun_ty = synth(env, size, fun)?;
            match *fun_ty.inner {
                Value::FunType(ref arg_ty, ref body_ty) => {
                    check(env, size, arg, arg_ty)?;
                    let arg_value = nbe::eval(arg, &env_to_domain_env(env))?;
                    Ok(nbe::do_closure1(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairFst(ref pair) => {
            let pair_ty = synth(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(ref fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(ref pair) => {
            let pair_ty = synth(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst = nbe::eval(
                        &RcTerm::from(Term::PairFst(pair.clone())),
                        &env_to_domain_env(env),
                    )?;
                    Ok(nbe::do_closure1(snd_ty, fst)?)
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(term.clone())),
    }
}

pub fn check_ty(env: &Env, size: u32, ty: &RcTerm) -> Result<(), TypeError> {
    match *ty.inner {
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            check_ty(&body_env, size + 1, body)
        },

        Term::NatType => Ok(()),

        Term::FunType(ref ann, ref body) | Term::PairType(ref ann, ref body) => {
            check_ty(env, size, ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;

            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size), ann_value.clone()),
                ann: ann_value,
            });

            check_ty(&body_env, size + 1, body)
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth(env, size, ty)?;
            match *synth_ty.inner {
                Value::Universe(_) => Ok(()),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: synth_ty,
                }),
            }
        },
    }
}

pub struct SynthVisitor {
    size: u32,
}

pub type SynthResult = Result<RcValue, TypeError>;

impl core::TermVisitor<SynthResult> for SynthVisitor {
    fn visit_var(&mut self, index: DbIndex) -> SynthResult {
        unimplemented!("visit_var")
    }
    fn visit_let(
        &mut self,
        def: impl Fn(&mut Self) -> SynthResult,
        body: impl Fn(&mut Self) -> SynthResult,
    ) -> SynthResult {
        unimplemented!("visit_let")
    }
    fn visit_check(&mut self, term: SynthResult, ann: SynthResult) -> SynthResult {
        unimplemented!("visit_check")
    }

    fn visit_nat_ty(&mut self) -> SynthResult {
        unimplemented!("visit_nat_ty")
    }
    fn visit_nat_zero(&mut self) -> SynthResult {
        unimplemented!("visit_nat_zero")
    }
    fn visit_nat_succ(&mut self, nat: SynthResult) -> SynthResult {
        unimplemented!("visit_nat_succ")
    }
    fn visit_nat_rec(
        &mut self,
        motive: SynthResult,
        zero: SynthResult,
        succ: SynthResult,
        nat: SynthResult,
    ) -> SynthResult {
        unimplemented!("visit_nat_rec")
    }

    fn visit_fun_ty(&mut self, src_ty: SynthResult, dst_ty: SynthResult) -> SynthResult {
        unimplemented!("visit_fun_ty")
    }
    fn visit_fun_intro(&mut self, body: SynthResult) -> SynthResult {
        unimplemented!("visit_fun_intro")
    }
    fn visit_fun_app(&mut self, fun: SynthResult, arg: SynthResult) -> SynthResult {
        unimplemented!("visit_fun_app")
    }

    fn visit_pair_ty(&mut self, fst_ty: SynthResult, snd_ty: SynthResult) -> SynthResult {
        unimplemented!("visit_pair_ty")
    }
    fn visit_pair_intro(&mut self, fst: SynthResult, snd: SynthResult) -> SynthResult {
        unimplemented!("visit_pair_intro")
    }
    fn visit_pair_fst(&mut self, pair: SynthResult) -> SynthResult {
        unimplemented!("visit_pair_fst")
    }
    fn visit_pair_snd(&mut self, pair: SynthResult) -> SynthResult {
        unimplemented!("visit_pair_snd")
    }

    fn visit_universe(&mut self, level: UniverseLevel) -> SynthResult {
        unimplemented!("visit_universe")
    }
}

pub struct CheckVisitor {
    size: u32,
}

pub type CheckResult = Result<(), TypeError>;

impl core::TermVisitor<CheckResult> for CheckVisitor {
    fn visit_var(&mut self, index: DbIndex) -> CheckResult {
        unimplemented!("visit_var")
    }
    fn visit_let(
        &mut self,
        def: impl Fn(&mut Self) -> CheckResult,
        body: impl Fn(&mut Self) -> CheckResult,
    ) -> CheckResult {
        unimplemented!("visit_let")
    }
    fn visit_check(&mut self, term: CheckResult, ann: CheckResult) -> CheckResult {
        unimplemented!("visit_check")
    }

    fn visit_nat_ty(&mut self) -> CheckResult {
        unimplemented!("visit_nat_ty")
    }
    fn visit_nat_zero(&mut self) -> CheckResult {
        unimplemented!("visit_nat_zero")
    }
    fn visit_nat_succ(&mut self, nat: CheckResult) -> CheckResult {
        unimplemented!("visit_nat_succ")
    }
    fn visit_nat_rec(
        &mut self,
        motive: CheckResult,
        zero: CheckResult,
        succ: CheckResult,
        nat: CheckResult,
    ) -> CheckResult {
        unimplemented!("visit_nat_rec")
    }

    fn visit_fun_ty(&mut self, src_ty: CheckResult, dst_ty: CheckResult) -> CheckResult {
        unimplemented!("visit_fun_ty")
    }
    fn visit_fun_intro(&mut self, body: CheckResult) -> CheckResult {
        unimplemented!("visit_fun_intro")
    }
    fn visit_fun_app(&mut self, fun: CheckResult, arg: CheckResult) -> CheckResult {
        unimplemented!("visit_fun_app")
    }

    fn visit_pair_ty(&mut self, fst_ty: CheckResult, snd_ty: CheckResult) -> CheckResult {
        unimplemented!("visit_pair_ty")
    }
    fn visit_pair_intro(&mut self, fst: CheckResult, snd: CheckResult) -> CheckResult {
        unimplemented!("visit_pair_intro")
    }
    fn visit_pair_fst(&mut self, pair: CheckResult) -> CheckResult {
        unimplemented!("visit_pair_fst")
    }
    fn visit_pair_snd(&mut self, pair: CheckResult) -> CheckResult {
        unimplemented!("visit_pair_snd")
    }

    fn visit_universe(&mut self, level: UniverseLevel) -> CheckResult {
        unimplemented!("visit_universe")
    }
}
