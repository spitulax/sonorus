use std::cmp::Ordering;
use std::fmt::Display;

#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

impl Loc {
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }
}

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(if self.line > other.line {
            Ordering::Greater
        } else if self.line < other.line {
            Ordering::Less
        } else if self.col > other.col {
            Ordering::Greater
        } else if self.col < other.col {
            Ordering::Less
        } else {
            Ordering::Equal
        })
    }
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    #[test]
    fn ordering() {
        let a = Loc::new(0, 0);
        let b = Loc::new(0, 1);
        let c = Loc::new(1, 0);
        let d = Loc::new(1, 1);

        assert_eq!(a.cmp(&a), Ordering::Equal);
        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(a.cmp(&c), Ordering::Less);
        assert_eq!(a.cmp(&d), Ordering::Less);

        assert_eq!(b.cmp(&a), Ordering::Greater);
        assert_eq!(b.cmp(&b), Ordering::Equal);
        assert_eq!(b.cmp(&c), Ordering::Less);
        assert_eq!(b.cmp(&d), Ordering::Less);

        assert_eq!(c.cmp(&a), Ordering::Greater);
        assert_eq!(c.cmp(&b), Ordering::Greater);
        assert_eq!(c.cmp(&c), Ordering::Equal);
        assert_eq!(c.cmp(&d), Ordering::Less);

        assert_eq!(d.cmp(&a), Ordering::Greater);
        assert_eq!(d.cmp(&b), Ordering::Greater);
        assert_eq!(d.cmp(&c), Ordering::Greater);
        assert_eq!(d.cmp(&d), Ordering::Equal);
    }
}
