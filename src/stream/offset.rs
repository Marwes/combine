use super::{
    slice_uncons_while_pos, CommitOk, ParseResult, PeekErr, RangeStreamOnce, ResetStream,
    StreamErrorFor, StreamOnce, Tracked, UnexpectedParse,
};

pub struct Stream<'a> {
    pub buffer: &'a bytes_05::Bytes,
    pub offset: usize,
}

impl StreamOnce for Stream<'_> {
    type Token = u8;

    type Range = bytes_05::Bytes;

    type Position = usize;

    type Error = UnexpectedParse;

    fn uncons(&mut self) -> Result<Self::Token, StreamErrorFor<Self>> {
        if let Some(&b) = self.buffer.get(self.offset) {
            self.offset += 1;
            Ok(b)
        } else {
            Err(UnexpectedParse::Eoi)
        }
    }
}

impl RangeStreamOnce for Stream<'_> {
    #[inline]
    fn uncons_range(&mut self, size: usize) -> Result<Self::Range, StreamErrorFor<Self>> {
        if self.offset + size < self.buffer.len() {
            let buf = self.buffer.slice(self.offset..self.offset + size);
            self.offset += size;
            Ok(buf)
        } else {
            Err(UnexpectedParse::Eoi)
        }
    }

    #[inline]
    fn uncons_while<F>(&mut self, f: F) -> Result<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Token) -> bool,
    {
        let size = slice_uncons_while_pos(self.buffer, 0, f);
        let buf = self.buffer.slice(self.offset..self.offset + size);
        self.offset += size;
        Ok(buf)
    }

    #[inline]
    fn uncons_while1<F>(&mut self, mut f: F) -> ParseResult<Self::Range, StreamErrorFor<Self>>
    where
        F: FnMut(Self::Token) -> bool,
    {
        if !self.buffer.first().cloned().map_or(false, &mut f) {
            return PeekErr(Tracked::from(UnexpectedParse::Unexpected));
        }
        let size = slice_uncons_while_pos(self.buffer, 1, f);
        let buf = self.buffer.slice(self.offset..self.offset + size);
        self.offset += size;
        CommitOk(buf)
    }

    #[inline]
    fn distance(&self, end: &Self::Checkpoint) -> usize {
        *end - self.offset
    }

    #[inline]
    fn range(&self) -> Self::Range {
        self.buffer.slice(self.offset..)
    }
}

impl ResetStream for Stream<'_> {
    type Checkpoint = usize;

    #[inline]
    fn checkpoint(&self) -> Self::Checkpoint {
        self.offset
    }

    #[inline]
    fn reset(&mut self, checkpoint: Self::Checkpoint) -> Result<(), Self::Error> {
        self.offset = checkpoint;
        Ok(())
    }
}
