use crate::{
    error::ParseResult,
    stream::{
        FullRangeStream, Positioned, RangeStreamOnce, ResetStream, StreamErrorFor, StreamOnce,
    },
};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct StateStream<S, U> {
    pub stream: S,
    pub state: U,
}

impl<S, U> Positioned for StateStream<S, U>
where
    S: Positioned,
{
    #[inline(always)]
    fn position(&self) -> Self::Position {
        self.stream.position()
    }
}

impl<S, U> ResetStream for StateStream<S, U>
where
    S: ResetStream,
{
    type Checkpoint = S::Checkpoint;

    #[inline(always)]
    fn checkpoint(&self) -> Self::Checkpoint {
        self.stream.checkpoint()
    }

    #[inline(always)]
    fn reset(&mut self, checkpoint: Self::Checkpoint) -> Result<(), Self::Error> {
        self.stream.reset(checkpoint)
    }
}

impl<S, U> StreamOnce for StateStream<S, U>
where
    S: StreamOnce,
{
    type Item = S::Item;
    type Range = S::Range;
    type Position = S::Position;
    type Error = S::Error;

    #[inline(always)]
    fn uncons(&mut self) -> Result<S::Item, StreamErrorFor<Self>> {
        self.stream.uncons()
    }

    fn is_partial(&self) -> bool {
        true
    }
}

impl<S, U> RangeStreamOnce for StateStream<S, U>
where
    S: RangeStreamOnce,
{
    #[inline(always)]
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>> {
        self.stream.uncons_range(size)
    }

    #[inline(always)]
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.stream.uncons_while(f)
    }

    fn uncons_while1<F>(&mut self, f: F) -> ParseResult<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Item) -> bool,
    {
        self.stream.uncons_while1(f)
    }

    #[inline(always)]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        self.stream.distance(end)
    }
}

impl<S, U> FullRangeStream for StateStream<S, U>
where
    S: FullRangeStream,
{
    #[inline(always)]
    fn range(&self) -> Self::Range {
        self.stream.range()
    }
}
