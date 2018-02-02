use std::collections::VecDeque;

use error::StreamError;
use stream::{Positioned, Resetable, StreamErrorFor, StreamOnce};

#[derive(Debug, PartialEq)]
pub struct BufferedStream<I>
where
    I: StreamOnce + Positioned,
{
    offset: usize,
    iter: I,
    buffer_offset: usize,
    buffer: VecDeque<(I::Item, I::Position)>,
}

impl<I> Resetable for BufferedStream<I>
where
    I: Positioned,
{
    type Checkpoint = usize;
    fn checkpoint(&self) -> Self::Checkpoint {
        self.offset
    }
    fn reset(&mut self, checkpoint: Self::Checkpoint) {
        self.offset = checkpoint;
    }
}

impl<I> BufferedStream<I>
where
    I: StreamOnce + Positioned,
    I::Position: Clone,
    I::Item: Clone,
{
    /// Constructs a new `BufferedStream` from a `StreamOnce` instance with a `lookahead`
    /// number of elements that can be stored in the buffer.
    pub fn new(iter: I, lookahead: usize) -> BufferedStream<I> {
        BufferedStream {
            offset: 0,
            iter: iter,
            buffer_offset: 0,
            buffer: VecDeque::with_capacity(lookahead),
        }
    }
}

impl<I> Positioned for BufferedStream<I>
where
    I: StreamOnce + Positioned,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        if self.offset >= self.buffer_offset {
            self.iter.position()
        } else if self.offset < self.buffer_offset - self.buffer.len() {
            self.buffer
                .front()
                .expect("Atleast 1 element in the buffer")
                .1
                .clone()
        } else {
            self.buffer[self.buffer.len() - (self.buffer_offset - self.offset)]
                .1
                .clone()
        }
    }
}

impl<I> StreamOnce for BufferedStream<I>
where
    I: StreamOnce + Positioned,
    I::Item: Clone + PartialEq,
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = I::Position;
    type Error = I::Error;

    #[inline]
    fn uncons(&mut self) -> Result<I::Item, StreamErrorFor<Self>> {
        if self.offset >= self.buffer_offset {
            let position = self.iter.position();
            let item = try!(self.iter.uncons());
            self.buffer_offset += 1;
            // We want the VecDeque to only keep the last .capacity() elements so we need to remove
            // an element if it gets to large
            if self.buffer.len() == self.buffer.capacity() {
                self.buffer.pop_front();
            }
            self.buffer.push_back((item.clone(), position.clone()));
            self.offset += 1;
            Ok(item)
        } else if self.offset < self.buffer_offset - self.buffer.len() {
            // We have backtracked to far
            Err(StreamError::message_static_message(
                "Backtracked to far".into(),
            ))
        } else {
            let value = self.buffer[self.buffer.len() - (self.buffer_offset - self.offset)]
                .0
                .clone();
            self.offset += 1;
            Ok(value)
        }
    }
}
