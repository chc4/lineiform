// We need a timestamp for nodes and ports such that we can push and pull the in time
// relative to other instructions in the same timeslice, but without invalidating e.g.
// the dependency ordering that we primarily use the times for - that is, an instruction
// at t=2 is always emitted after its t=1 dependencies.
//
// We use a fixednum timestamp for this. The 'major' time is the dependency time,
// while the 'minor' time allows us to order instructions within it; overflowing
// the minor time will just panic for now.


use rangemap::StepLite;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord)]
pub struct Timestamp {
    pub major: u16,
    pub minor: u16,
}

impl Timestamp {
    pub fn new() -> Self {
        Timestamp {
            major: 0,
            minor: 8,
        }
    }

    /// Increment the timestamp's major time
    #[must_use]
    pub fn increment(mut self) -> Self {
        self.major = self.major.checked_add(1).unwrap();
        self
    }

    /// Decrement the timestamp's major time
    #[must_use]
    pub fn decrement(mut self) -> Self {
        self.major = self.major.checked_sub(1).unwrap();
        self
    }

    /// Push the timestamp to a later minor time
    #[must_use]
    pub fn push(mut self) -> Self {
        self.minor = self.minor.checked_add(1).unwrap();
        self
    }

    /// Pull the timestamp to a sooner minor time
    #[must_use]
    pub fn pull(mut self) -> Self {
        self.minor = self.minor.checked_sub(1).unwrap();
        self
    }
}

impl PartialOrd for Timestamp {
    fn partial_cmp(&self, other: &Timestamp) -> Option<std::cmp::Ordering> {
        Some(self.major.cmp(&other.major).then(self.minor.cmp(&other.minor)))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn timestamp_cmp() {
        assert!(Timestamp::new() == Timestamp::new());
        assert!(Timestamp::new() <= Timestamp::new());
        assert!(Timestamp::new() >= Timestamp::new());
        assert!(Timestamp::new().increment() > Timestamp::new());
        assert!(Timestamp::new().push() > Timestamp::new());
        assert!(Timestamp::new().push() < Timestamp::new().increment());
        assert!(Timestamp::new().increment().push() > Timestamp::new().push());
        assert!(Timestamp::new().increment().push() > Timestamp::new().increment());
    }
}

impl StepLite for Timestamp {
    fn add_one(&self) -> Self {
        if self.minor == u16::MAX { let mut new = self.increment(); new.minor = u16::MIN; new }
        else { self.push() }
    }

    fn sub_one(&self) -> Self {
        if self.minor == u16::MIN { let mut new = self.decrement(); new.minor = u16::MAX; new }
        else { self.pull() }
    }
}

use core::fmt::{Display, Formatter};
impl Display for Timestamp {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}.{}", self.major, self.minor)
    }
}

/// Vector clock used for state effect ordering.
struct Clock {
    members: Vec<Timestamp>
}

impl Clock {
    pub fn new() -> Self {
        Clock { members: vec![] }
    }

    #[must_use]
    pub fn increment(mut self, member: usize) -> Self {
        self.members[member] = self.members[member].increment();
        self
    }

    #[must_use]
    pub fn decrement(mut self, member: usize) -> Self {
        self.members[member] = self.members[member].decrement();
        self
    }

}

















