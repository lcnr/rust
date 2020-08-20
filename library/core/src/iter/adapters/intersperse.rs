use crate::fmt;

use super::super::{Iterator, Fuse};

/// An iterator that yields the elements of the inner iterator placing a seperator
/// between each of them.
///
/// This `struct` is created by the [`intersperse`] method on [`Iterator`]. See its
/// documentation for more.
///
/// [`intersperse`]: trait.Iterator.html#method.fintersperse
/// [`Iterator`]: trait.Iterator.html
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[unstable(feature = "iterator_intersperse", issue = "none")]
pub struct Intersperse<I: Iterator> {
    inner: Fuse<I>,
    next: Option<I::Item>,
    sep: I::Item,
}

impl<I: Iterator> Intersperse<I> {
    pub(in super::super) fn new(iter: I, sep: I::Item) -> Intersperse<I> {
        let mut iter = iter.fuse();
        let next = iter.next();
        Intersperse { inner: iter, next, sep }
    }
}

#[unstable(feature = "iterator_intersperse", issue = "none")]
impl<I: Clone + Iterator> Clone for Intersperse<I>
where
    I::Item: Clone,
{
    fn clone(&self) -> Self {
        Intersperse {
            inner: self.inner.clone(),
            next: self.next.clone(),
            sep: self.sep.clone(),
        }
    }
}

#[unstable(feature = "iterator_intersperse", issue = "none")]
impl<I: fmt::Debug + Iterator> fmt::Debug for Intersperse<I>
where
    I::Item: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Intersperse").field("inner", &self.inner).field("next", &self.next).field("sep", &self.sep).finish()
    }
}

#[unstable(feature = "iterator_intersperse", issue = "none")]
impl<I: Iterator> Iterator for Intersperse<I>
where
    I::Item: Clone,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        if let next @ Some(_) = self.next.take() {
            return next;
        }

        if let next @ Some(_) = self.inner.next() {
            self.next = next;
            Some(self.sep.clone())
        } else {
            None
        }
    }
}
