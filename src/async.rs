use {Parser, StreamOnce};
use primitives::ParseError;
use stream::{RangeStream, RangeStreamOnce, Resetable};

pub fn decode<P>(
    mut parser: P,
    src: P::Input,
    partial_state: &mut P::PartialState,
) -> Result<(Option<P::Output>, usize), <P::Input as StreamOnce>::Error>
where
    P: Parser,
    P::Input: RangeStream,
{
    let start = src.checkpoint();
    let mut input = src;
    match parser.parse_with_state(&mut input, partial_state) {
        Ok(message) => Ok((Some(message), input.distance(&start))),
        Err(err) => {
            return if input.is_partial() && err.is_unexpected_end_of_input() {
                Ok((None, input.distance(&start)))
            } else {
                Err(err)
            }
        }
    }
}
