use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::fmt;

use primitives::{Positioned, StreamOnce, StreamingError};

/// A `BufferedStreamRef` wraps an instance `StreamOnce`, allowing it to be used as a `Stream`.
pub struct BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: 'a,
{
    offset: usize,
    buffer: &'a BufferedStream<I>,
}

impl<'a, I> fmt::Debug for BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let buffer_offset = unsafe { (*self.buffer.buffer.get()).offset };
        write!(
            f,
            "BufferedStreamRef {{ offset: {:?} buffer_offset: {:?} }}",
            self.offset,
            buffer_offset
        )
    }
}

impl<'a, I> Clone for BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Position: Clone,
    I::Item: 'a,
{
    fn clone(&self) -> BufferedStreamRef<'a, I> {
        BufferedStreamRef {
            offset: self.offset,
            buffer: self.buffer,
        }
    }
}

pub struct BufferedStream<I>
where
    I: StreamOnce + Positioned,
{
    buffer: UnsafeCell<BufferedStreamInner<I>>,
}

struct BufferedStreamInner<I>
where
    I: StreamOnce + Positioned,
{
    offset: usize,
    iter: I,
    buffer: VecDeque<(I::Item, I::Position)>,
}

impl<I> BufferedStreamInner<I>
where
    I: StreamOnce + Positioned,
    I::Position: Clone,
    I::Item: Clone,
{
    #[inline]
    fn uncons<E>(&mut self, offset: usize) -> Result<I::Item, E>
    where
        E: StreamingError<I::Item, I::Range>,
    {
        if offset >= self.offset {
            let position = self.iter.position();
            let item = try!(self.iter.uncons());
            self.offset += 1;
            // We want the VecDeque to only keep the last .capacity() elements so we need to remove
            // an element if it gets to large
            if self.buffer.len() == self.buffer.capacity() {
                self.buffer.pop_front();
            }
            self.buffer.push_back((item.clone(), position.clone()));
            Ok(item)
        } else if offset < self.offset - self.buffer.len() {
            // We have backtracked to far
            Err(StreamingError::message_static_message(
                "Backtracked to far".into(),
            ))
        } else {
            Ok(
                self.buffer[self.buffer.len() - (self.offset - offset)]
                    .0
                    .clone(),
            )
        }
    }

    #[inline]
    fn position(&self, offset: usize) -> I::Position {
        if offset >= self.offset {
            self.iter.position()
        } else if offset < self.offset - self.buffer.len() {
            self.buffer
                .front()
                .expect("Atleast 1 element in the buffer")
                .1
                .clone()
        } else {
            self.buffer[self.buffer.len() - (self.offset - offset)]
                .1
                .clone()
        }
    }
}

impl<I> BufferedStream<I>
where
    I: StreamOnce + Positioned,
    I::Position: Clone,
    I::Item: Clone,
{
    /// Constructs a new `BufferedStream` froma a `StreamOnce` instance with a `lookahead`
    /// number of elements that can be stored in the buffer.
    ///
    /// `BufferedStream` do not implement `Stream` itself. To retrieve a value which implement
    /// `Stream`, `as_stream` must be called.
    pub fn new(iter: I, lookahead: usize) -> BufferedStream<I> {
        BufferedStream {
            buffer: UnsafeCell::new(BufferedStreamInner {
                offset: 0,
                iter: iter,
                buffer: VecDeque::with_capacity(lookahead),
            }),
        }
    }

    /// Creates a `BufferedStreamRef` which implements `Stream`.
    ///
    /// `BufferedStreamRef` always implement `Stream` allowing one-shot streams to used as if it
    /// could be used multiple times.
    pub fn as_stream(&self) -> BufferedStreamRef<I> {
        BufferedStreamRef {
            offset: 0,
            buffer: self,
        }
    }
    #[inline]
    fn uncons<E>(&self, offset: usize) -> Result<I::Item, E>
    where
        E: StreamingError<I::Item, I::Range>,
    {
        unsafe { (*self.buffer.get()).uncons(offset) }
    }
    #[inline(always)]
    fn position(&self, offset: usize) -> I::Position {
        unsafe { (*self.buffer.get()).position(offset) }
    }
}

impl<'a, I> BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned,
{
}

impl<'a, I> Positioned for BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned + 'a,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.buffer.position(self.offset)
    }
}

impl<'a, I> StreamOnce for BufferedStreamRef<'a, I>
where
    I: StreamOnce + Positioned + 'a,
    I::Item: Clone + PartialEq + 'a,
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = I::Position;
    type Error = I::Error;

    #[inline]
    fn uncons<E>(&mut self) -> Result<I::Item, E>
    where
        E: StreamingError<Self::Item, Self::Range>,
    {
        let value = try!(self.buffer.uncons(self.offset));
        self.offset += 1;
        Ok(value)
    }
}
