use crate::stream::position::IndexPositioner;

use std::{
    io::{self, Read},
    mem::MaybeUninit,
};

#[cfg(any(feature = "futures-03", feature = "tokio-02"))]
use std::pin::Pin;

use bytes_05::{buf::BufMutExt, Buf, BufMut, BytesMut};

/// Used together with the `decode!` macro
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg_attr(feature = "pin-project", pin_project::pin_project)]
pub struct Decoder<R, S, P = IndexPositioner> {
    #[cfg_attr(feature = "pin-project", pin)]
    reader: R,
    pub positioner: P,
    state: S,
    buffer: BytesMut,
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<R, S, P> Decoder<R, S, P>
where
    P: Default,
    S: Default,
{
    pub fn new(reader: R) -> Self {
        Decoder {
            reader,
            positioner: P::default(),
            state: S::default(),
            buffer: Default::default(),
        }
    }
}

impl<R, S, P> Decoder<R, S, P> {
    #[doc(hidden)]
    pub fn advance(&mut self, removed: usize) {
        // Remove the data we have parsed and adjust `removed` to be the amount of data we
        // committed from `self.reader`
        self.buffer.advance(removed);
    }
}

impl<R, S, P> Decoder<R, S, P>
where
    R: Read,
{
    #[doc(hidden)]
    pub fn before_parse(&mut self) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        let mut end_of_input = false;

        let take = (8 * 1024).max(self.buffer.remaining_mut() as u64);
        let copied = io::copy(
            &mut (&mut self.reader).take(take),
            &mut (&mut self.buffer).writer(),
        )?;
        if copied == 0 {
            end_of_input = true;
        }
        Ok((
            &mut self.state,
            &mut self.positioner,
            &self.buffer,
            end_of_input,
        ))
    }
}

#[cfg(feature = "tokio-02")]
impl<R, S, P> Decoder<R, S, P>
where
    R: tokio_02_dep::io::AsyncRead,
{
    #[doc(hidden)]
    pub async fn before_parse_tokio(
        self: Pin<&mut Self>,
    ) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        use tokio_02_dep::io::AsyncReadExt;

        let mut self_ = self.project();
        let mut end_of_input = false;
        if !self_.buffer.has_remaining_mut() {
            self_.buffer.reserve(8 * 1024);
        }
        let copied = self_.reader.read_buf(self_.buffer).await?;
        if copied == 0 {
            end_of_input = true;
        }
        Ok((
            self_.state,
            self_.positioner,
            &self_.buffer[..],
            end_of_input,
        ))
    }
}

#[cfg(feature = "futures-03")]
impl<R, S, P> Decoder<R, S, P>
where
    R: futures_io_03::AsyncRead,
{
    #[doc(hidden)]
    pub async fn before_parse_async(
        self: Pin<&mut Self>,
    ) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        use futures_util_03::io::AsyncReadExt;

        let mut self_ = self.project();
        if !self_.buffer.has_remaining_mut() {
            self_.buffer.reserve(8 * 1024);
        }
        // Copy of tokio's read_buf method (but it has to force initialize the buffer)
        let copied = unsafe {
            let n = {
                let bs = self_.buffer.bytes_mut();

                for b in &mut *bs {
                    *b = MaybeUninit::new(0);
                }

                // Convert to `&mut [u8]`
                let bs = &mut *(bs as *mut [MaybeUninit<u8>] as *mut [u8]);

                let n = self_.reader.read(bs).await?;
                assert!(n <= bs.len(), "AsyncRead reported that it initialized more than the number of bytes in the buffer");
                n
            };

            self_.buffer.advance_mut(n);
            n
        };

        let end_of_input = copied == 0;
        Ok((
            self_.state,
            self_.positioner,
            &self_.buffer[..],
            end_of_input,
        ))
    }
}
