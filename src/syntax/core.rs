//! The surface syntax

use std::rc::Rc;

use syntax::{DbIndex, UniverseLevel};

pub type Env = im::Vector<RcTerm>;

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variables
    Var(DbIndex),
    /// Let bindings
    Let(RcTerm, /* BINDS */ RcTerm),
    /// A term that is explicitly annotated with a type
    Check(RcTerm, RcTerm),

    /// Type of natural numbers
    NatType,
    /// The natural number zero
    NatZero,
    /// The successor of a natural number
    NatSucc(RcTerm),
    /// Recursively eliminate a natural number
    NatRec(
        /* BINDS */ RcTerm,
        RcTerm,
        /* BINDS 2 */ RcTerm,
        RcTerm,
    ),

    /// Dependent function types
    FunType(RcTerm, /* BINDS */ RcTerm),
    /// Introduce a function
    FunIntro(/* BINDS */ RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent par types
    PairType(RcTerm, /* BINDS */ RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
}

pub trait TermVisitor<T> {
    fn visit_var(&mut self, index: DbIndex) -> T;
    fn visit_let(&mut self, def: impl Fn(&mut Self) -> T, body: impl Fn(&mut Self) -> T) -> T;
    fn visit_check(&mut self, term: T, ann: T) -> T;

    fn visit_nat_ty(&mut self) -> T;
    fn visit_nat_zero(&mut self) -> T;
    fn visit_nat_succ(&mut self, nat: T) -> T;
    fn visit_nat_rec(&mut self, motive: T, zero: T, succ: T, nat: T) -> T;

    fn visit_fun_ty(&mut self, src_ty: T, dst_ty: T) -> T;
    fn visit_fun_intro(&mut self, body: T) -> T;
    fn visit_fun_app(&mut self, fun: T, arg: T) -> T;

    fn visit_pair_ty(&mut self, fst_ty: T, snd_ty: T) -> T;
    fn visit_pair_intro(&mut self, fst: T, snd: T) -> T;
    fn visit_pair_fst(&mut self, pair: T) -> T;
    fn visit_pair_snd(&mut self, pair: T) -> T;

    fn visit_universe(&mut self, level: UniverseLevel) -> T;
}

impl RcTerm {
    pub fn dispatch<T>(&self, visitor: &mut impl TermVisitor<T>) -> T {
        match *self.inner {
            Term::Var(index) => visitor.visit_var(index),
            Term::Let(ref def, ref body) => visitor.visit_let(
                |visitor| def.dispatch(visitor),
                |visitor| body.dispatch(visitor),
            ),
            Term::Check(ref term, ref ann) => {
                let term = term.dispatch(visitor);
                let ann = ann.dispatch(visitor);
                visitor.visit_check(term, ann)
            },

            Term::NatType => visitor.visit_nat_ty(),
            Term::NatZero => visitor.visit_nat_zero(),
            Term::NatSucc(ref nat) => {
                let nat = nat.dispatch(visitor);
                visitor.visit_nat_succ(nat)
            },
            Term::NatRec(ref motive, ref zero, ref succ, ref nat) => {
                let motive = motive.dispatch(visitor);
                let zero = zero.dispatch(visitor);
                let succ = succ.dispatch(visitor);
                let nat = nat.dispatch(visitor);

                visitor.visit_nat_rec(motive, zero, succ, nat)
            },

            Term::FunType(ref src_ty, ref dst_ty) => {
                let src_ty = src_ty.dispatch(visitor);
                let dst_ty = dst_ty.dispatch(visitor);
                visitor.visit_fun_ty(src_ty, dst_ty)
            },
            Term::FunIntro(ref body) => {
                let body = body.dispatch(visitor);
                visitor.visit_fun_intro(body)
            },
            Term::FunApp(ref fun, ref arg) => {
                let fun = fun.dispatch(visitor);
                let arg = arg.dispatch(visitor);
                visitor.visit_fun_app(fun, arg)
            },

            Term::PairType(ref fst_ty, ref snd_ty) => {
                let fst_ty = fst_ty.dispatch(visitor);
                let snd_ty = snd_ty.dispatch(visitor);
                visitor.visit_pair_ty(fst_ty, snd_ty)
            },
            Term::PairIntro(ref fst, ref snd) => {
                let fst = fst.dispatch(visitor);
                let snd = snd.dispatch(visitor);
                visitor.visit_pair_intro(fst, snd)
            },
            Term::PairFst(ref pair) => {
                let pair = pair.dispatch(visitor);
                visitor.visit_pair_fst(pair)
            },
            Term::PairSnd(ref pair) => {
                let pair = pair.dispatch(visitor);
                visitor.visit_pair_snd(pair)
            },

            Term::Universe(level) => visitor.visit_universe(level),
        }
    }
}

/// Visitor that constructs a new term
pub struct NewTermVisitor {
    nat_ty: RcTerm,
    nat_zero: RcTerm,
    universe0: RcTerm,
    universe1: RcTerm,
    universe2: RcTerm,
}

impl NewTermVisitor {
    pub fn new() -> NewTermVisitor {
        NewTermVisitor {
            nat_ty: RcTerm::from(Term::NatType),
            nat_zero: RcTerm::from(Term::NatZero),
            universe0: RcTerm::from(Term::Universe(UniverseLevel(0))),
            universe1: RcTerm::from(Term::Universe(UniverseLevel(1))),
            universe2: RcTerm::from(Term::Universe(UniverseLevel(2))),
        }
    }
}

// TODO: property test
//     |term| term.dispatch(&mut NewTermVisitor) == term

impl TermVisitor<RcTerm> for NewTermVisitor {
    fn visit_var(&mut self, index: DbIndex) -> RcTerm {
        RcTerm::from(Term::Var(index))
    }

    fn visit_let(
        &mut self,
        def: impl Fn(&mut Self) -> RcTerm,
        body: impl Fn(&mut Self) -> RcTerm,
    ) -> RcTerm {
        RcTerm::from(Term::FunType(def(self), body(self)))
    }

    fn visit_check(&mut self, term: RcTerm, ann: RcTerm) -> RcTerm {
        RcTerm::from(Term::Check(term, ann))
    }

    // Natural numbers

    fn visit_nat_ty(&mut self) -> RcTerm {
        self.nat_ty.clone()
    }

    fn visit_nat_zero(&mut self) -> RcTerm {
        self.nat_zero.clone()
    }

    fn visit_nat_succ(&mut self, nat: RcTerm) -> RcTerm {
        RcTerm::from(Term::NatSucc(nat))
    }

    fn visit_nat_rec(&mut self, motive: RcTerm, zero: RcTerm, succ: RcTerm, nat: RcTerm) -> RcTerm {
        RcTerm::from(Term::NatRec(motive, zero, succ, nat))
    }

    // Functions

    fn visit_fun_ty(&mut self, src_ty: RcTerm, dst_ty: RcTerm) -> RcTerm {
        RcTerm::from(Term::FunType(src_ty, dst_ty))
    }

    fn visit_fun_intro(&mut self, body: RcTerm) -> RcTerm {
        RcTerm::from(Term::FunIntro(body))
    }

    fn visit_fun_app(&mut self, fun: RcTerm, arg: RcTerm) -> RcTerm {
        RcTerm::from(Term::FunApp(fun, arg))
    }

    // Pairs

    fn visit_pair_ty(&mut self, fst_ty: RcTerm, snd_ty: RcTerm) -> RcTerm {
        RcTerm::from(Term::PairType(fst_ty, snd_ty))
    }

    fn visit_pair_intro(&mut self, fst: RcTerm, snd: RcTerm) -> RcTerm {
        RcTerm::from(Term::PairIntro(fst, snd))
    }

    fn visit_pair_fst(&mut self, pair: RcTerm) -> RcTerm {
        RcTerm::from(Term::PairFst(pair))
    }

    fn visit_pair_snd(&mut self, pair: RcTerm) -> RcTerm {
        RcTerm::from(Term::PairSnd(pair))
    }

    // Universes

    fn visit_universe(&mut self, level: UniverseLevel) -> RcTerm {
        match level {
            UniverseLevel(0) => self.universe0.clone(),
            UniverseLevel(1) => self.universe1.clone(),
            UniverseLevel(2) => self.universe2.clone(),
            UniverseLevel(_) => RcTerm::from(Term::Universe(level)),
        }
    }
}
