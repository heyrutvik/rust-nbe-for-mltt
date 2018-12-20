//! The semantic domain

use im;
use std::rc::Rc;

use crate::syntax::core::RcTerm;
use crate::syntax::{DbLevel, IdentHint, UniverseLevel, UniverseShift};

pub type Env = im::Vector<RcValue>;

/// A closure that binds a variable
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    // pub shift: UniverseShift,
    pub term: RcTerm,
    pub env: Env,
}

impl Closure {
    pub fn new(/*shift: UniverseShift,*/ term: RcTerm, env: Env) -> Closure {
        Closure {
            /*shift,*/ term,
            env,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RcValue {
    pub inner: Rc<Value>,
}

impl From<Value> for RcValue {
    fn from(src: Value) -> RcValue {
        RcValue {
            inner: Rc::new(src),
        }
    }
}

impl RcValue {
    /// Construct a variable
    pub fn var(level: DbLevel, shift: UniverseShift) -> RcValue {
        RcValue::from(Value::var(level, shift))
    }

    /// Shift universes
    pub fn shift_universe(&mut self, shift: UniverseShift) {
        Rc::make_mut(&mut self.inner).shift_universe(shift);
    }
}

/// Terms that are in _weak head normal form_
///
/// These can either be _neutral values_ (values that are stuck on a variable),
/// or _canonical values_.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Neutral values
    Neutral(RcNeutral),

    /// Dependent function types
    FunType(IdentHint, RcType, Closure),
    /// Introduce a function
    FunIntro(IdentHint, Closure),

    /// Dependent pair types
    PairType(IdentHint, RcType, Closure),
    /// Introduce a pair
    PairIntro(RcValue, RcValue),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable
    pub fn var(level: DbLevel, shift: UniverseShift) -> Value {
        Value::Neutral(RcNeutral::from(Neutral::Var(level, shift)))
    }

    /// Shift universes
    pub fn shift_universe(&mut self, shift: UniverseShift) {
        match *self {
            Value::Neutral(ref mut neutral) => neutral.shift_universe(shift),
            Value::FunType(_, ref mut param_ty, ref mut body_ty) => {
                param_ty.shift_universe(shift);
                unimplemented!()
            },
            Value::FunIntro(_, ref mut body) => unimplemented!(),
            Value::PairType(_, ref mut fst_ty, ref mut snd_ty) => {
                fst_ty.shift_universe(shift);
                unimplemented!()
            },
            Value::PairIntro(ref mut fst, ref mut snd) => {
                fst.shift_universe(shift);
                snd.shift_universe(shift);
            },
            Value::Universe(ref mut level) => *level += shift,
        }
    }
}

/// Alias for types - we are using describing a dependently typed language
/// types, so this is just an alias
pub type Type = Value;

/// Alias for reference counted types - we are using describing a dependently
/// typed language types, so this is just an alias
pub type RcType = RcValue;

#[derive(Debug, Clone, PartialEq)]
pub struct RcNeutral {
    pub inner: Rc<Neutral>,
}

impl RcNeutral {
    /// Shift universes
    pub fn shift_universe(&mut self, shift: UniverseShift) {
        Rc::make_mut(&mut self.inner).shift_universe(shift);
    }
}

impl From<Neutral> for RcNeutral {
    fn from(src: Neutral) -> RcNeutral {
        RcNeutral {
            inner: Rc::new(src),
        }
    }
}

/// Terms for which computation has stopped because of an attempt to evaluate a
/// variable
///
/// These are known as _neutral values_ or _accumulators_.
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variables
    Var(DbLevel, UniverseShift),

    /// Apply a function to an argument
    FunApp(RcNeutral, RcValue),

    /// Project the first element of a pair
    PairFst(RcNeutral),
    /// Project the second element of a pair
    PairSnd(RcNeutral),
}

impl Neutral {
    /// Shift universes
    pub fn shift_universe(&mut self, shift: UniverseShift) {
        match *self {
            Neutral::Var(..) => {},
            Neutral::FunApp(ref mut fun, ref mut arg) => {
                fun.shift_universe(shift);
                arg.shift_universe(shift);
            },
            Neutral::PairFst(ref mut pair) => pair.shift_universe(shift),
            Neutral::PairSnd(ref mut pair) => pair.shift_universe(shift),
        }
    }
}
