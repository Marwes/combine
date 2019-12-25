use crate::stream::position::IndexPositioner;

use std::io::{self, BufRead};

#[cfg(any(feature = "futures-io-03", feature = "tokio-02"))]
use std::pin::Pin;

/// Used together with the `decode!` macro
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[cfg_attr(feature = "pin-project", pin_project::pin_project)]
pub struct Decoder<R, S, P = IndexPositioner> {
    #[cfg_attr(feature = "pin-project", pin)]
    reader: R,
    pub positioner: P,
    state: S,
    remaining: Vec<u8>,
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
            remaining: Vec::new(),
        }
    }
}

impl<R, S, P> Decoder<R, S, P> {
    #[doc(hidden)]
    pub fn remaining_len(&self) -> usize {
        self.remaining.len()
    }
}

impl<R, S, P> Decoder<R, S, P>
where
    R: BufRead,
{
    #[doc(hidden)]
    pub fn before_parse(&mut self) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        let mut end_of_input = false;
        let buffer = self.reader.fill_buf()?;
        if buffer.len() == 0 {
            end_of_input = true;
        }
        Ok((
            &mut self.state,
            &mut self.positioner,
            if !self.remaining.is_empty() {
                self.remaining.extend(buffer);
                &self.remaining[..]
            } else {
                buffer
            },
            end_of_input,
        ))
    }

    #[doc(hidden)]
    pub fn after_parse(
        &mut self,
        remaining_data: usize,
        mut removed: usize,
        done: bool,
    ) -> io::Result<()> {
        if !self.remaining.is_empty() {
            // Remove the data we have parsed and adjust `removed` to be the amount of data we
            // consumed from `self.reader`
            self.remaining.drain(..removed);
            if removed >= remaining_data {
                removed -= remaining_data;
            } else {
                removed = 0;
            }
        }

        let consume = if done {
            removed
        } else {
            // We have not enough data to produce a Value but we know that all the data of
            // the current buffer are necessary. Consume all the buffered data to ensure
            // that the next iteration actually reads more data.
            let buffer = self.reader.fill_buf()?;
            if remaining_data == 0 {
                self.remaining.extend(&buffer[removed..]);
            }
            buffer.len()
        };
        self.reader.consume(consume);
        Ok(())
    }
}

// https://github.com/tokio-rs/tokio/pull/1687
#[cfg(feature = "tokio-02")]
async fn fill_buf_tokio<R>(reader: Pin<&mut R>) -> io::Result<&[u8]>
where
    R: tokio_02_dep::io::AsyncBufRead,
{
    use std::{
        future::Future,
        task::{self, Poll},
    };

    struct FillBuf<'a, R>(Option<Pin<&'a mut R>>);
    impl<'a, R> Future for FillBuf<'a, R>
    where
        R: tokio_02_dep::io::AsyncBufRead,
    {
        type Output = io::Result<&'a [u8]>;

        fn poll(mut self: Pin<&mut Self>, cx: &mut task::Context) -> Poll<io::Result<&'a [u8]>> {
            match self.0.take() {
                Some(mut r) => match r.as_mut().poll_fill_buf(cx) {
                    // SAFETY We either drop `self.reader` and return a slice with the lifetime of the
                    // reader or we return Pending/Err (neither which contains `'a`).
                    // In either case `poll_fill_buf` can not be called while it's contents are exposed
                    Poll::Ready(Ok(x)) => unsafe { return Ok(&*(x as *const _)).into() },
                    Poll::Ready(Err(err)) => Err(err).into(),
                    Poll::Pending => {
                        self.0 = Some(r);
                        Poll::Pending
                    }
                },
                None => panic!("fill_buf polled after completion"),
            }
        }
    }
    FillBuf(Some(reader)).await
}

#[cfg(feature = "tokio-02")]
impl<R, S, P> Decoder<R, S, P>
where
    R: tokio_02_dep::io::AsyncBufRead,
{
    #[doc(hidden)]
    pub async fn before_parse_tokio(
        self: Pin<&mut Self>,
    ) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        let self_ = self.project();
        let mut end_of_input = false;
        let buffer = fill_buf_tokio(self_.reader).await?;
        if buffer.len() == 0 {
            end_of_input = true;
        }
        Ok((
            self_.state,
            self_.positioner,
            if !self_.remaining.is_empty() {
                self_.remaining.extend(buffer);
                &self_.remaining[..]
            } else {
                buffer
            },
            end_of_input,
        ))
    }

    #[doc(hidden)]
    pub async fn after_parse_tokio(
        self: Pin<&mut Self>,
        remaining_data: usize,
        mut removed: usize,
        done: bool,
    ) -> io::Result<()> {
        let mut self_ = self.project();
        if !self_.remaining.is_empty() {
            // Remove the data we have parsed and adjust `removed` to be the amount of data we
            // consumed from `self.reader`
            self_.remaining.drain(..removed);
            if removed >= remaining_data {
                removed -= remaining_data;
            } else {
                removed = 0;
            }
        }

        let consume = if done {
            removed
        } else {
            // We have not enough data to produce a Value but we know that all the data of
            // the current buffer are necessary. Consume all the buffered data to ensure
            // that the next iteration actually reads more data.
            let buffer = fill_buf_tokio(self_.reader.as_mut()).await?;
            if remaining_data == 0 {
                self_.remaining.extend(&buffer[removed..]);
            }
            buffer.len()
        };
        self_.reader.consume(consume);
        Ok(())
    }
}

// https://github.com/tokio-rs/tokio/pull/1687
#[cfg(feature = "futures-io-03")]
async fn fill_buf<R>(reader: std::pin::Pin<&mut R>) -> io::Result<&[u8]>
where
    R: futures_io_03::AsyncBufRead,
{
    use std::{
        future::Future,
        task::{self, Poll},
    };

    struct FillBuf<'a, R>(Option<Pin<&'a mut R>>);
    impl<'a, R> Future for FillBuf<'a, R>
    where
        R: futures_io_03::AsyncBufRead,
    {
        type Output = io::Result<&'a [u8]>;

        fn poll(mut self: Pin<&mut Self>, cx: &mut task::Context) -> Poll<io::Result<&'a [u8]>> {
            match self.0.take() {
                Some(mut r) => match r.as_mut().poll_fill_buf(cx) {
                    // SAFETY We either drop `self.reader` and return a slice with the lifetime of the
                    // reader or we return Pending/Err (neither which contains `'a`).
                    // In either case `poll_fill_buf` can not be called while it's contents are exposed
                    Poll::Ready(Ok(x)) => unsafe { return Ok(&*(x as *const _)).into() },
                    Poll::Ready(Err(err)) => Err(err).into(),
                    Poll::Pending => {
                        self.0 = Some(r);
                        Poll::Pending
                    }
                },
                None => panic!("fill_buf polled after completion"),
            }
        }
    }
    FillBuf(Some(reader)).await
}

#[cfg(feature = "futures-io-03")]
impl<R, S, P> Decoder<R, S, P>
where
    R: futures_io_03::AsyncBufRead,
{
    #[doc(hidden)]
    pub async fn before_parse_async(
        self: Pin<&mut Self>,
    ) -> io::Result<(&mut S, &mut P, &[u8], bool)> {
        let self_ = self.project();
        let mut end_of_input = false;
        let buffer = fill_buf(self_.reader).await?;
        if buffer.len() == 0 {
            end_of_input = true;
        }
        Ok((
            self_.state,
            self_.positioner,
            if !self_.remaining.is_empty() {
                self_.remaining.extend(buffer);
                &self_.remaining[..]
            } else {
                buffer
            },
            end_of_input,
        ))
    }

    #[doc(hidden)]
    pub async fn after_parse_async(
        self: Pin<&mut Self>,
        remaining_data: usize,
        mut removed: usize,
        done: bool,
    ) -> io::Result<()> {
        let mut self_ = self.project();
        if !self_.remaining.is_empty() {
            // Remove the data we have parsed and adjust `removed` to be the amount of data we
            // consumed from `self.reader`
            self_.remaining.drain(..removed);
            if removed >= remaining_data {
                removed -= remaining_data;
            } else {
                removed = 0;
            }
        }

        let consume = if done {
            removed
        } else {
            // We have not enough data to produce a Value but we know that all the data of
            // the current buffer are necessary. Consume all the buffered data to ensure
            // that the next iteration actually reads more data.
            let buffer = fill_buf(self_.reader.as_mut()).await?;
            if remaining_data == 0 {
                self_.remaining.extend(&buffer[removed..]);
            }
            buffer.len()
        };
        self_.reader.consume(consume);
        Ok(())
    }
}
