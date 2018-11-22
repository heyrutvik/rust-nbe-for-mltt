//! The concrete syntax

use syntax::UniverseLevel;

pub type Ident = String;

pub type Signature = Vec<Decl>;

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Def { name: Ident, def: Term, ann: Term },
    NormalizeDef(Ident),
    NormalizeTerm { term: Term, ann: Term },
    Quit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(Ident),
    /// Let bindings
    Let(Ident, Box<Term>, Box<Term>),
    /// A term that is explicitly annotated with a type
    Check(Box<Term>, Box<Term>),

    /// Type of natural numbers
    NatType,
    /// Construct the successor of a natural number
    NatSucc(Box<Term>),
    /// Construct a natural number from a literal integer
    NatLit(u32),
    /// Recursively eliminate a natural number
    NatRec {
        motive: (Ident, Box<Term>),
        zero: Box<Term>,
        succ: (Ident, Ident, Box<Term>),
        nat: Box<Term>,
    },

    /// Dependent function type
    FunType(Ident, Box<Term>, Box<Term>),
    /// Introduce a function
    FunIntro(Ident, Box<Term>),
    /// Apply a function to an argument
    FunApp(Box<Term>, Vec<Term>),

    /// Dependent pair type
    PairType(Ident, Box<Term>, Box<Term>),
    /// Introduce a pair
    PairIntro(Box<Term>, Box<Term>),
    /// Project the first element of a pair
    PairFst(Box<Term>),
    /// Project the second element of a pair
    PairSnd(Box<Term>),

    /// Universe of types
    Universe(UniverseLevel),
}

pub trait TermVisitor<T> {
    fn visit_var(&mut self, ident: &Ident) -> T;
    fn visit_let(&mut self, ident: &Ident, def: T, body: T) -> T;
    fn visit_check(&mut self, term: T, ann: T) -> T;

    fn visit_nat_ty(&mut self) -> T;
    fn visit_nat_succ(&mut self, nat: T) -> T;
    fn visit_nat_lit(&mut self, nat: u32) -> T;
    fn visit_nat_rec(
        &mut self,
        motive: (&Ident, T),
        zero: T,
        succ: (&Ident, &Ident, T),
        nat: T,
    ) -> T;

    fn visit_fun_ty(&mut self, ident: &Ident, src_ty: T, dst_ty: T) -> T;
    fn visit_fun_intro(&mut self, ident: &Ident, body: T) -> T;
    fn visit_fun_app(&mut self, fun: T, args: Vec<T>) -> T;

    fn visit_pair_ty(&mut self, ident: &Ident, fst_ty: T, snd_ty: T) -> T;
    fn visit_pair_intro(&mut self, fst: T, snd: T) -> T;
    fn visit_pair_fst(&mut self, pair: T) -> T;
    fn visit_pair_snd(&mut self, pair: T) -> T;

    fn visit_universe(&mut self, level: UniverseLevel) -> T;
}

impl Term {
    pub fn dispatch<T>(&self, visitor: &mut impl TermVisitor<T>) -> T {
        match *self {
            Term::Var(ref ident) => visitor.visit_var(ident),
            Term::Let(ref ident, ref def, ref body) => {
                let def = def.dispatch(visitor);
                let body = body.dispatch(visitor);
                visitor.visit_let(ident, def, body)
            },
            Term::Check(ref term, ref ann) => {
                let term = term.dispatch(visitor);
                let ann = ann.dispatch(visitor);
                visitor.visit_check(term, ann)
            },

            Term::NatType => visitor.visit_nat_ty(),
            Term::NatSucc(ref nat) => {
                let nat = nat.dispatch(visitor);
                visitor.visit_nat_succ(nat)
            },
            Term::NatLit(nat) => visitor.visit_nat_lit(nat),
            Term::NatRec {
                motive: (ref motive_ident, ref motive_body),
                ref zero,
                succ: (ref succ_ident1, ref succ_ident2, ref succ_body),
                ref nat,
            } => {
                let motive_body = motive_body.dispatch(visitor);
                let zero = zero.dispatch(visitor);
                let succ_body = succ_body.dispatch(visitor);
                let nat = nat.dispatch(visitor);

                visitor.visit_nat_rec(
                    (motive_ident, motive_body),
                    zero,
                    (succ_ident1, succ_ident2, succ_body),
                    nat,
                )
            },

            Term::FunType(ref ident, ref src_ty, ref dst_ty) => {
                let src_ty = src_ty.dispatch(visitor);
                let dst_ty = dst_ty.dispatch(visitor);
                visitor.visit_fun_ty(ident, src_ty, dst_ty)
            },
            Term::FunIntro(ref ident, ref body) => {
                let body = body.dispatch(visitor);
                visitor.visit_fun_intro(ident, body)
            },
            Term::FunApp(ref fun, ref args) => {
                let fun = fun.dispatch(visitor);
                let args = args.iter().map(|arg| arg.dispatch(visitor)).collect();
                visitor.visit_fun_app(fun, args)
            },

            Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
                let fst_ty = fst_ty.dispatch(visitor);
                let snd_ty = snd_ty.dispatch(visitor);
                visitor.visit_pair_ty(ident, fst_ty, snd_ty)
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
pub struct NewTermVisitor;

// TODO: property test
//     |term| term.dispatch(&mut NewTermVisitor) == term

impl TermVisitor<Term> for NewTermVisitor {
    fn visit_var(&mut self, ident: &Ident) -> Term {
        Term::Var(ident.clone())
    }

    fn visit_let(&mut self, ident: &Ident, def: Term, body: Term) -> Term {
        Term::FunType(ident.clone(), Box::new(def), Box::new(body))
    }

    fn visit_check(&mut self, term: Term, ann: Term) -> Term {
        Term::Check(Box::new(term), Box::new(ann))
    }

    // Natural numbers

    fn visit_nat_ty(&mut self) -> Term {
        Term::NatType
    }

    fn visit_nat_succ(&mut self, nat: Term) -> Term {
        Term::NatSucc(Box::new(nat))
    }

    fn visit_nat_lit(&mut self, nat: u32) -> Term {
        Term::NatLit(nat)
    }

    fn visit_nat_rec(
        &mut self,
        (motive_ident, motive_body): (&Ident, Term),
        zero: Term,
        (succ_ident1, succ_ident2, succ_body): (&Ident, &Ident, Term),
        nat: Term,
    ) -> Term {
        Term::NatRec {
            motive: (motive_ident.clone(), Box::new(motive_body)),
            zero: Box::new(zero),
            succ: (
                succ_ident1.clone(),
                succ_ident2.clone(),
                Box::new(succ_body),
            ),
            nat: Box::new(nat),
        }
    }

    // Functions

    fn visit_fun_ty(&mut self, ident: &Ident, src_ty: Term, dst_ty: Term) -> Term {
        Term::FunType(ident.clone(), Box::new(src_ty), Box::new(dst_ty))
    }

    fn visit_fun_intro(&mut self, ident: &Ident, body: Term) -> Term {
        Term::FunIntro(ident.clone(), Box::new(body))
    }

    fn visit_fun_app(&mut self, fun: Term, args: Vec<Term>) -> Term {
        Term::FunApp(Box::new(fun), args)
    }

    // Pairs

    fn visit_pair_ty(&mut self, ident: &Ident, fst_ty: Term, snd_ty: Term) -> Term {
        Term::PairType(ident.clone(), Box::new(fst_ty), Box::new(snd_ty))
    }

    fn visit_pair_intro(&mut self, fst: Term, snd: Term) -> Term {
        Term::PairIntro(Box::new(fst), Box::new(snd))
    }

    fn visit_pair_fst(&mut self, pair: Term) -> Term {
        Term::PairFst(Box::new(pair))
    }

    fn visit_pair_snd(&mut self, pair: Term) -> Term {
        Term::PairSnd(Box::new(pair))
    }

    // Universes

    fn visit_universe(&mut self, level: UniverseLevel) -> Term {
        Term::Universe(level)
    }
}
