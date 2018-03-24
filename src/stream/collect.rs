use lib::marker::PhantomData;
use lib::iter::{repeat, FromIterator};

use error::ParseError;
use stream::{Positioned, RangeStreamOnce, Resetable, StreamErrorFor, StreamOnce};

pub trait StreamDistance: Resetable {
    fn distance(&self, checkpoint: &Self::Checkpoint) -> usize;
}

impl<T> StreamDistance for T
where
    T: RangeStreamOnce + Resetable,
{
    fn distance(&self, checkpoint: &Self::Checkpoint) -> usize {
        RangeStreamOnce::distance(self, checkpoint)
    }
}

/// Stream wrapper which collects its `Item`s into a container when producing a `Range`.
/// This lets streams which do not implement `RangeStreamOnce` work with range parsers at the cost
/// of needing to allocate a container for the items.
///
/// ```
/// # #![cfg(feature = "std")]
/// # extern crate combine;
/// # use combine::Parser;
/// # use combine::range::take_while;
/// # use combine::stream::{easy, collect, IteratorStream};
/// # use combine::stream::buffered::BufferedStream;
/// # use combine::stream::state::State;
/// # fn main() {
///     let stream = collect::Stream::<_, _, easy::Errors<_, _, _>>::new(
///         BufferedStream::new(State::new(IteratorStream::new("abc123".chars())), 1)
///     );
///     let result = take_while(|c: char| c.is_alphabetic())
///         .easy_parse(stream)
///         .map(|(o, _)| o);
///     assert_eq!(result, Ok("abc".to_string(), ));
/// # }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Stream<S, F, E> {
    stream: S,
    _marker: PhantomData<fn() -> (F, E)>,
}

impl<S, F, E> Stream<S, F, E> {
    pub fn new(stream: S) -> Self {
        Stream {
            stream,
            _marker: PhantomData,
        }
    }

    pub fn into_inner(self) -> S {
        self.stream
    }
}

impl<S, F, E> Resetable for Stream<S, F, E>
where
    S: Resetable,
{
    type Checkpoint = S::Checkpoint;

    fn checkpoint(&self) -> Self::Checkpoint {
        self.stream.checkpoint()
    }
    fn reset(&mut self, checkpoint: Self::Checkpoint) {
        self.stream.reset(checkpoint);
    }
}

impl<S, F, E> StreamOnce for Stream<S, F, E>
where
    S: StreamOnce + Resetable,
    E: ParseError<S::Item, F, S::Position>,
    F: PartialEq + Clone,
{
    type Item = S::Item;
    type Range = F;
    type Position = S::Position;
    type Error = E;

    #[inline]
    fn uncons(&mut self) -> Result<Self::Item, StreamErrorFor<Self>> {
        self.stream.uncons().map_err(|_| panic!())
    }

    fn is_partial(&self) -> bool {
        self.stream.is_partial()
    }
}

impl<S, F, E> RangeStreamOnce for Stream<S, F, E>
where
    S: StreamOnce + Resetable + StreamDistance,
    E: ParseError<S::Item, F, S::Position>,
    F: FromIterator<S::Item> + PartialEq + Clone,
{
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>> {
        repeat(())
            .take(size)
            .map(|_| self.stream.uncons())
            .collect::<Result<_, _>>()
            .map_err(|_| panic!())
    }

    #[inline]
    fn uncons_while<G>(&mut self, mut g: G) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        G: FnMut(Self::Item) -> bool,
    {
        repeat(())
            .scan((), |_, _| {
                let checkpoint = self.stream.checkpoint();
                match self.stream.uncons() {
                    Ok(i) => {
                        if g(i.clone()) {
                            Some(Ok(i))
                        } else {
                            self.stream.reset(checkpoint);
                            None
                        }
                    }
                    Err(err) => Some(Err(err)),
                }
            })
            .collect::<Result<_, _>>()
            .map_err(|_| panic!())
    }

    #[inline]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        self.stream.distance(end)
    }
}

impl<S, F, E> Positioned for Stream<S, F, E>
where
    S: StreamOnce + Resetable + Positioned,
    E: ParseError<S::Item, F, S::Position>,
    F: PartialEq + Clone,
{
    fn position(&self) -> S::Position {
        self.stream.position()
    }
}
