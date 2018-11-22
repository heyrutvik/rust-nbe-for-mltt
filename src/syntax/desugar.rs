use im;

use syntax::{concrete, core, DbIndex, UniverseLevel};

pub enum DesugarError {
    UnboundVar(concrete::Ident),
}

pub fn desugar(
    concrete_term: &concrete::Term,
    env: &im::Vector<concrete::Ident>,
) -> Result<core::RcTerm, DesugarError> {
    match *concrete_term {
        concrete::Term::Var(ref ident) => match env.iter().enumerate().find(|(_, i)| *i == ident) {
            None => Err(DesugarError::UnboundVar(ident.clone())),
            Some((index, _)) => Ok(core::RcTerm::from(core::Term::Var(DbIndex(index as u32)))),
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            Ok(core::RcTerm::from(core::Term::Let(desugar(def, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(body, &env)?
            })))
        },
        concrete::Term::Check(ref term, ref ann) => Ok(core::RcTerm::from(core::Term::Check(
            desugar(term, env)?,
            desugar(ann, env)?,
        ))),

        concrete::Term::NatType => Ok(core::RcTerm::from(core::Term::NatType)),
        concrete::Term::NatSucc(ref n) => {
            Ok(core::RcTerm::from(core::Term::NatSucc(desugar(n, env)?)))
        },
        concrete::Term::NatLit(nat) => {
            // let rec int_to_term = function
            //   | 0 -> S.Zero
            //   | n -> S.Suc (int_to_term (n - 1))

            unimplemented!("desugar: concrete::Term::NatLit")
        },
        concrete::Term::NatRec {
            motive: (ref motive_ident, ref motive_body),
            ref zero,
            succ: (ref succ_ident1, ref succ_ident2, ref succ_body),
            ref nat,
        } => Ok(core::RcTerm::from(core::Term::NatRec(
            {
                let mut env = env.clone();
                env.push_front(motive_ident.clone());
                desugar(motive_body, &env)?
            },
            desugar(zero, &env)?,
            {
                let mut env = env.clone();
                env.push_front(succ_ident1.clone());
                env.push_front(succ_ident2.clone());
                desugar(succ_body, &env)?
            },
            desugar(nat, &env)?,
        ))),

        concrete::Term::FunType(ref ident, ref src_ty, ref dst_ty) => Ok(core::RcTerm::from(
            core::Term::FunType(desugar(src_ty, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(dst_ty, &env)?
            }),
        )),
        concrete::Term::FunIntro(ref ident, ref dst_ty) => {
            Ok(core::RcTerm::from(core::Term::FunIntro({
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(dst_ty, &env)?
            })))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar(fun, env), |acc, arg| {
                Ok(core::RcTerm::from(core::Term::FunApp(
                    acc?,
                    desugar(arg, env)?,
                )))
            })
        },

        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => Ok(core::RcTerm::from(
            core::Term::PairType(desugar(fst_ty, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(snd_ty, &env)?
            }),
        )),
        concrete::Term::PairIntro(ref fst, ref snd) => Ok(core::RcTerm::from(
            core::Term::PairIntro(desugar(fst, env)?, desugar(snd, env)?),
        )),
        concrete::Term::PairFst(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairFst(desugar(pair, env)?)))
        },
        concrete::Term::PairSnd(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairSnd(desugar(pair, env)?)))
        },

        concrete::Term::Universe(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),
    }
}

/// A visitor that desugars terms in the concrete syntax into terms in the
/// core syntax
pub struct DesugarVisitor<V> {
    bindings: Vec<concrete::Ident>,
    downstream: V,
}

impl<V> DesugarVisitor<V> {
    pub fn new(downstream: V) -> DesugarVisitor<V> {
        DesugarVisitor {
            bindings: Vec::new(),
            downstream,
        }
    }

    pub fn lookup_binding(&self, ident: &concrete::Ident) -> Result<DbIndex, DesugarError> {
        self.bindings
            .iter()
            .rev()
            .enumerate()
            .find(|(_, i)| *i == ident)
            .map(|(index, _)| DbIndex(index as u32))
            .ok_or_else(|| DesugarError::UnboundVar(ident.clone()))
    }
}

impl<V, T> concrete::TermVisitor<Result<T, DesugarError>> for DesugarVisitor<V>
where
    V: core::TermVisitor<T>,
{
    fn visit_var(&mut self, ident: &concrete::Ident) -> Result<T, DesugarError> {
        let index = self.lookup_binding(ident)?;
        Ok(self.downstream.visit_var(index))
    }

    fn visit_let(
        &mut self,
        ident: &concrete::Ident,
        def: impl Fn(&mut Self) -> Result<T, DesugarError>,
        body: impl Fn(&mut Self) -> Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        let def = def(self)?;

        self.bindings.push(ident.clone());
        let body = body(self)?;
        self.bindings.pop();

        // FIXME: Is ignoring the downstream visitor here wise?

        // FIXME: Also this fails to satisfy the borrow checker:
        //
        //     |
        // 147 |         let def = def(self)?;
        //     |             --- captured outer variable
        // ...
        // 154 |         Ok(self.downstream.visit_let(|_| def, |_| body))
        //     |                                          ^^^ cannot move out of captured outer variable in an `Fn` closure

        Ok(self.downstream.visit_let(|_| def, |_| body))
    }

    fn visit_check(
        &mut self,
        term: Result<T, DesugarError>,
        ann: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_check(term?, ann?))
    }

    // Natural numbers

    fn visit_nat_ty(&mut self) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_nat_ty())
    }

    fn visit_nat_succ(&mut self, nat: Result<T, DesugarError>) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_nat_succ(nat?))
    }

    fn visit_nat_lit(&mut self, nat: u32) -> Result<T, DesugarError> {
        // let rec int_to_term = function
        //   | 0 -> S.Zero
        //   | n -> S.Suc (int_to_term (n - 1))

        unimplemented!("visit_nat_succ")
    }

    fn visit_nat_rec(
        &mut self,
        (motive_ident, motive_body): (&concrete::Ident, Result<T, DesugarError>),
        zero: Result<T, DesugarError>,
        (succ_ident1, succ_ident2, succ_body): (
            &concrete::Ident,
            &concrete::Ident,
            Result<T, DesugarError>,
        ),
        nat: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        self.bindings.push(motive_ident.clone());
        // TODO
        self.bindings.pop();

        self.bindings.push(succ_ident2.clone());
        self.bindings.push(succ_ident1.clone());
        // TODO
        self.bindings.pop();
        self.bindings.pop();

        unimplemented!("visit_nat_rec")
    }

    // Functions

    fn visit_fun_ty(
        &mut self,
        ident: &concrete::Ident,
        src_ty: Result<T, DesugarError>,
        dst_ty: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        self.bindings.push(ident.clone());
        // TODO
        self.bindings.pop();

        unimplemented!("visit_fun_ty")
    }

    fn visit_fun_intro(
        &mut self,
        ident: &concrete::Ident,
        body: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        self.bindings.push(ident.clone());
        // TODO
        self.bindings.pop();

        unimplemented!("visit_fun_intro")
    }

    fn visit_fun_app(
        &mut self,
        fun: Result<T, DesugarError>,
        args: Vec<Result<T, DesugarError>>,
    ) -> Result<T, DesugarError> {
        args.into_iter().fold(fun, |acc, arg| {
            Ok(self.downstream.visit_fun_app(acc?, arg?))
        })
    }

    // Pairs

    fn visit_pair_ty(
        &mut self,
        ident: &concrete::Ident,
        fst_ty: Result<T, DesugarError>,
        snd_ty: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        self.bindings.push(ident.clone());
        // TODO
        self.bindings.pop();

        unimplemented!("visit_pair_ty")
    }

    fn visit_pair_intro(
        &mut self,
        fst: Result<T, DesugarError>,
        snd: Result<T, DesugarError>,
    ) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_pair_intro(fst?, snd?))
    }

    fn visit_pair_fst(&mut self, pair: Result<T, DesugarError>) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_pair_fst(pair?))
    }

    fn visit_pair_snd(&mut self, pair: Result<T, DesugarError>) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_pair_snd(pair?))
    }

    // Universes

    fn visit_universe(&mut self, level: UniverseLevel) -> Result<T, DesugarError> {
        Ok(self.downstream.visit_universe(level))
    }
}
