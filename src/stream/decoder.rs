use crate::error::ParseError;

use std::{
    fmt,
    io::{self, Read},
};

use bytes_05::{Buf, BytesMut};

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
/// Used together with the `decode!` macro
pub struct Decoder<S, P> {
    position: P,
    state: S,
    buffer: BytesMut,
    end_of_input: bool,
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<S, P> Decoder<S, P>
where
    P: Default,
    S: Default,
{
    pub fn new() -> Self {
        Decoder {
            position: P::default(),
            state: S::default(),
            buffer: Default::default(),
            end_of_input: false,
        }
    }
}

impl<S, P> Decoder<S, P> {
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

    #[doc(hidden)]
    pub fn __inner(&mut self) -> (&mut S, &mut P, &mut bytes_05::BytesMut, bool) {
        (
            &mut self.state,
            &mut self.position,
            &mut self.buffer,
            self.end_of_input,
        )
    }
}

impl<S, P> Decoder<S, P> {
    #[doc(hidden)]
    pub fn __before_parse<R>(&mut self, mut reader: R) -> io::Result<()>
    where
        R: Read,
    {
        let len = self.buffer.len();
        self.buffer.resize(len.saturating_add(8 * 1024), 0);

        let n = match reader.read(&mut self.buffer[len..]) {
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
            self.end_of_input = true;
        }
        Ok(())
    }
}

#[cfg(feature = "tokio-02")]
impl<S, P> Decoder<S, P> {
    #[doc(hidden)]
    pub async fn __before_parse_tokio<R>(&mut self, reader: R) -> io::Result<()>
    where
        R: tokio_02_dep::io::AsyncRead,
    {
        use bytes_05::BufMut;
        use tokio_02_dep::io::AsyncReadExt;

        if !self.buffer.has_remaining_mut() {
            self.buffer.reserve(8 * 1024);
        }
        futures_util_03::pin_mut!(reader);
        let copied = reader.read_buf(&mut self.buffer).await?;
        if copied == 0 {
            self.end_of_input = true;
        }

        Ok(())
    }
}

#[cfg(feature = "futures-03")]
impl<S, P> Decoder<S, P> {
    #[doc(hidden)]
    pub async fn __before_parse_async<R>(&mut self, reader: R) -> io::Result<()>
    where
        R: futures_io_03::AsyncRead,
    {
        use std::mem::MaybeUninit;

        use bytes_05::BufMut;
        use futures_util_03::io::AsyncReadExt;

        if !self.buffer.has_remaining_mut() {
            self.buffer.reserve(8 * 1024);
        }
        futures_util_03::pin_mut!(reader);
        // Copy of tokio's read_buf method (but it has to force initialize the buffer)
        let copied = unsafe {
            let n = {
                let bs = self.buffer.bytes_mut();

                for b in &mut *bs {
                    *b = MaybeUninit::new(0);
                }

                // Convert to `&mut [u8]`
                let bs = &mut *(bs as *mut [MaybeUninit<u8>] as *mut [u8]);

                let n = reader.read(bs).await?;
                assert!(n <= bs.len(), "AsyncRead reported that it initialized more than the number of bytes in the buffer");
                n
            };

            self.buffer.advance_mut(n);
            n
        };

        self.end_of_input = copied == 0;
        Ok(())
    }
}
