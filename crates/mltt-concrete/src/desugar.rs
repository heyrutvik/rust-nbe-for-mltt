use mltt_core::syntax::UniverseLevel;

use crate::syntax::{concrete, raw};

pub fn desugar_term(term: &concrete::Term) -> raw::RcTerm {
    match *term {
        concrete::Term::Var(ref ident) => raw::RcTerm::from(raw::Term::Var(ident.clone())),
        concrete::Term::Let(ref ident, ref def, ref body) => {
            let def = desugar_term(def);
            let body = desugar_term(body);

            raw::RcTerm::from(raw::Term::Let(ident.clone(), def, body))
        },
        concrete::Term::Case(ref scrutinees, ref equations) => {
            let scrutinees = scrutinees
                .iter()
                .map(|scrutinee| desugar_term(scrutinee))
                .collect();

            let equations = equations
                .iter()
                .map(|(patterns, body)| desugar_equation(patterns, body))
                .collect();

            raw::RcTerm::from(raw::Term::Case(scrutinees, equations))
        },
        concrete::Term::Ann(ref term, ref ann) => {
            let term = desugar_term(term);
            let ann = desugar_term(ann);

            raw::RcTerm::from(raw::Term::Ann(term, ann))
        },
        concrete::Term::Parens(ref term) => desugar_term(term),

        // Functions
        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            let param_ty = desugar_term(param_ty);
            let body_ty = desugar_term(body_ty);

            raw::RcTerm::from(raw::Term::FunType(ident.clone(), param_ty, body_ty))
        },
        concrete::Term::FunIntro(ref ident, ref body) => {
            let body = desugar_term(body);

            raw::RcTerm::from(raw::Term::FunIntro(ident.clone(), body))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar_term(fun), |acc, arg| {
                let arg = desugar_term(arg);
                raw::RcTerm::from(raw::Term::FunApp(acc, arg))
            })
        },

        // Pairs
        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
            let fst_ty = desugar_term(fst_ty);
            let snd_ty = desugar_term(snd_ty);

            raw::RcTerm::from(raw::Term::PairType(ident.clone(), fst_ty, snd_ty))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => {
            let fst = desugar_term(fst);
            let snd = desugar_term(snd);

            raw::RcTerm::from(raw::Term::PairIntro(fst, snd))
        },
        concrete::Term::PairFst(ref pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairFst(pair))
        },
        concrete::Term::PairSnd(ref pair) => {
            let pair = desugar_term(pair);

            raw::RcTerm::from(raw::Term::PairSnd(pair))
        },

        // Universes
        concrete::Term::Universe(level) => match level {
            None => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(0))),
            Some(level) => raw::RcTerm::from(raw::Term::Universe(UniverseLevel(level))),
        },
    }
}

pub fn desugar_pattern(pattern: &concrete::Pattern) -> raw::RcPattern {
    match *pattern {
        concrete::Pattern::Var(ref ident) => raw::RcPattern::from(raw::Pattern::Var(ident.clone())),
        concrete::Pattern::Ann(ref pattern, ref pattern_ty) => {
            let pattern = desugar_pattern(pattern);
            let pattern_ty = desugar_term(pattern_ty);
            raw::RcPattern::from(raw::Pattern::Ann(pattern, pattern_ty))
        },
        concrete::Pattern::PairIntro(ref fst, ref snd) => {
            let fst = desugar_pattern(fst);
            let snd = desugar_pattern(snd);
            raw::RcPattern::from(raw::Pattern::PairIntro(fst, snd))
        },
    }
}

fn desugar_equation(
    patterns: &[concrete::Pattern],
    body: &concrete::Term,
) -> (Vec<raw::RcPattern>, raw::RcTerm) {
    let patterns = patterns
        .iter()
        .map(|pattern| desugar_pattern(&pattern))
        .collect();
    let body = desugar_term(body);

    (patterns, body)
}
