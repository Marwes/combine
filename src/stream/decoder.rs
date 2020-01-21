use crate::error::ParseError;

use std::{
    fmt,
    io::{self, Read},
};

#[cfg(any(feature = "futures-03", feature = "tokio-02"))]
use std::pin::Pin;

use bytes_05::{Buf, BufMut, BytesMut};

#[derive(Debug)]
pub enum Error<E, P> {
    Parse(E),
    Io { position: P, error: io::Error },
}

impl<'a, P> From<Error<crate::easy::Errors<u8, &'a [u8], P>, P>>
    for crate::easy::Errors<u8, &'a [u8], P>
where
    P: Ord,
{
    fn from(e: Error<crate::easy::Errors<u8, &'a [u8], P>, P>) -> Self {
        match e {
            Error::Parse(e) => e,
            Error::Io { position, error } => {
                crate::easy::Errors::from_error(position, crate::easy::Error::Other(error.into()))
            }
        }
    }
}

impl<E, P> std::error::Error for Error<E, P>
where
    E: std::error::Error,
    P: fmt::Display + fmt::Debug,
{
}

impl<E: fmt::Display, P: fmt::Display> fmt::Display for Error<E, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(e) => e.fmt(f),
            Error::Io { position: _, error } => error.fmt(f),
        }
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg(feature = "pin-project")]
pin_project_lite::pin_project! {
    /// Used together with the `decode!` macro
    pub struct Decoder<R, S, P> {
        #[pin]
        reader: R,
        position: P,
        state: S,
        buffer: BytesMut,
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg(not(feature = "pin-project"))]
/// Used together with the `decode!` macro
pub struct Decoder<R, S, P> {
    reader: R,
    position: P,
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
            position: P::default(),
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

    pub fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    pub fn position(&self) -> &P {
        &self.position
    }
}

impl<R, S, P> Decoder<R, S, P>
where
    R: Read,
{
    #[doc(hidden)]
    pub fn before_parse(&mut self) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        let mut end_of_input = false;

        let len = self.buffer.len();
        self.buffer.resize(len.saturating_add(8 * 1024), 0);

        let n = match self.reader.read(&mut self.buffer[len..]) {
            Ok(n) => {
                self.buffer.truncate(len + n);
                n
            }
            Err(err) => {
                self.buffer.truncate(len);
                return Err(err);
            }
        };
        if n == 0 {
            end_of_input = true;
        }
        Ok((
            &mut self.state,
            &mut self.position,
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
        let mut self_ = self.project();
        let mut end_of_input = false;
        if !self_.buffer.has_remaining_mut() {
            self_.buffer.reserve(8 * 1024);
        }
        let copied = <Pin<&mut R> as tokio_02_dep::io::AsyncReadExt>::read_buf(
            &mut self_.reader,
            self_.buffer,
        )
        .await?;
        if copied == 0 {
            end_of_input = true;
        }
        Ok((self_.state, self_.position, &self_.buffer[..], end_of_input))
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
        use std::mem::MaybeUninit;

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
        Ok((self_.state, self_.position, &self_.buffer[..], end_of_input))
    }
}
