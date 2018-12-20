//! The various syntaxes of the language
//!
//! The core, domain, and normal syntaxes are mainly based off Mini-TT

use std::ops::{Add, AddAssign};

pub mod core;
pub mod domain;
pub mod normal;

/// A name hint that can be used for pretty printing later on
///
/// All hints are equal to each other, to allow for easily using the default
/// `PartialEq` derive for [alpha equivalence][alpha-equivalence].
///
/// [alpha-equivalence]: https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
#[derive(Debug, Clone, Eq)]
pub struct IdentHint(pub Option<String>);

impl From<Option<String>> for IdentHint {
    fn from(src: Option<String>) -> IdentHint {
        IdentHint(src)
    }
}

impl PartialEq for IdentHint {
    fn eq(&self, _: &IdentHint) -> bool {
        true
    }
}

/// DeBruijn level
///
/// This counts the total number of binders that we encounter when running up
/// the syntax tree to the root, _not including free binders_.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbLevel(pub u32);

/// DeBruijn index
///
/// This counts the number of binders we encounter when running up the tree to
/// get to the binder that bound this variable.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbIndex(pub u32);

/// The level of a universe
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);

/// A shift in the level of a universe
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseShift(pub u32);

impl Add<UniverseShift> for UniverseLevel {
    type Output = UniverseLevel;

    fn add(self, other: UniverseShift) -> UniverseLevel {
        UniverseLevel(self.0 + other.0)
    }
}

impl AddAssign<UniverseShift> for UniverseLevel {
    fn add_assign(&mut self, other: UniverseShift) {
        self.0 += other.0;
    }
}
