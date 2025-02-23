use std::fmt::Display;
use std::ops::{Add, Sub};
use std::str::from_utf8;

#[derive(Debug, Eq, PartialEq, Default)]
pub struct Span<T> {
    pub lo: T,
    pub hi: T,
}

impl<T: Ord> Span<T> {
    pub fn new(lo: T, hi: T) -> Self {
        Self { lo, hi }
    }
}

impl<T: Add<Output = T> + Ord + Clone> Span<T> {
    pub fn with_len(start: &T, len: &T) -> Self {
        Self::new(start.clone(), start.clone() + len.clone())
    }
}

impl<T: Sub<Output = T> + Clone> Span<T> {
    pub fn len(&self) -> T {
        self.hi.clone() - self.lo.clone()
    }
}

impl<T: Display> Display for Span<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.lo, self.hi)
    }
}

impl<T: Clone> Clone for Span<T> {
    fn clone(&self) -> Self {
        Self {
            lo: self.lo.clone(),
            hi: self.hi.clone(),
        }
    }
}

impl<T: Copy> Copy for Span<T> {}

#[derive(Debug, Default, Copy, Clone)]
pub struct SpanStr<'a> {
    s: &'a str,
    pub span: Span<usize>,
}

impl<'a> SpanStr<'a> {
    pub fn new(s: &'a str, lo: usize, hi: usize) -> Self {
        Self {
            s,
            span: Span { lo, hi },
        }
    }

    pub fn with_len(ctx: &'a str, start: usize, len: &usize) -> Self {
        Self::new(ctx, start, start + len)
    }

    pub fn len(&self) -> usize {
        self.span.hi - self.span.lo
    }

    pub fn to_bytes(&self) -> &'a [u8] {
        let lo = self.span.lo.max(0);
        let hi = self.span.hi.min(self.s.len());
        &self.s.as_bytes()[lo..hi]
    }

    /// Returns [`Some`] if the resulting slice is a valid UTF-8.
    pub fn to_string(&self) -> Option<&'a str> {
        let b = self.to_bytes();
        from_utf8(b).ok()
    }
}

impl PartialEq for SpanStr<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.to_bytes() == other.to_bytes()
    }
}

impl Display for SpanStr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Ignoring `s`
        write!(
            f,
            "({}..{} {:?})",
            self.span.lo,
            self.span.hi,
            self.to_string(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string() {
        let string = "Hello, World";
        let span1 = SpanStr::new(&string, 0, 5);
        let span2 = SpanStr::new(&string, 7, 100);
        assert_eq!(span1.to_bytes(), b"Hello");
        assert_eq!(span2.to_bytes(), b"World");
        assert_eq!(span1.to_string(), Some("Hello"));
        assert_eq!(span2.to_string(), Some("World"));
    }
}
