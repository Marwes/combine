use std::{
    io::{self, Read},
    mem::MaybeUninit,
    pin::Pin,
    task::{Context, Poll},
};

use {
    bytes_05::{Buf, BufMut, BytesMut},
    futures_util_03::ready,
    pin_project_lite::pin_project,
    tokio_02_dep::io::{AsyncBufRead, AsyncRead, AsyncWrite},
};

pin_project! {
    #[derive(Debug)]
    pub struct BufReader<R> {
        #[pin]
        inner: R,
        buf: BytesMut
    }
}

impl<R: AsyncRead> BufReader<R> {
    /// Creates a new `BufReader` with a default buffer capacity. The default is currently 8 KB,
    /// but may change in the future.
    pub fn new(inner: R) -> Self {
        Self::with_capacity(8096, inner)
    }

    /// Creates a new `BufReader` with the specified buffer capacity.
    pub fn with_capacity(capacity: usize, inner: R) -> Self {
        let buf = BytesMut::with_capacity(capacity);

        Self { inner, buf }
    }

    /// Gets a reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    /// Gets a pinned mutable reference to the underlying reader.
    ///
    /// It is inadvisable to directly read from the underlying reader.
    pub fn get_pin_mut(self: Pin<&mut Self>) -> Pin<&mut R> {
        self.project().inner
    }

    /// Consumes this `BufWriter`, returning the underlying reader.
    ///
    /// Note that any leftover data in the internal buffer is lost.
    pub fn into_inner(self) -> R {
        self.inner
    }

    /// Returns a reference to the internally buffered data.
    ///
    /// Unlike `fill_buf`, this will not attempt to fill the buffer if it is empty.
    pub fn buffer(&self) -> &[u8] {
        &self.buf
    }


    pub async fn extend_buf(self: Pin<&mut Self>) -> io::Result<usize> {
        let mut me = self.project();

        if !me.buf.has_remaining_mut() {
            me.buf.reserve(8 * 1024);
        }
        tokio_02_dep::io::AsyncReadExt::read_buf(&mut me.inner, me.buf).await
    }

    /// Invalidates all data in the internal buffer.
    #[inline]
    fn discard_buffer(self: Pin<&mut Self>) {
        let me = self.project();
        me.buf.clear();
    }
}

impl<R: AsyncRead> AsyncRead for BufReader<R> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut [u8],
    ) -> Poll<io::Result<usize>> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if !self.buf.has_remaining_mut() && buf.len() >= self.buf.len() {
            let res = ready!(self.as_mut().get_pin_mut().poll_read(cx, buf));
            self.discard_buffer();
            return Poll::Ready(res);
        }
        let mut rem = ready!(self.as_mut().poll_fill_buf(cx))?;
        let nread = rem.read(buf)?;
        self.consume(nread);
        Poll::Ready(Ok(nread))
    }

    // we can't skip unconditionally because of the large buffer case in read.
    unsafe fn prepare_uninitialized_buffer(&self, buf: &mut [MaybeUninit<u8>]) -> bool {
        self.inner.prepare_uninitialized_buffer(buf)
    }
}

impl<R: AsyncRead> AsyncBufRead for BufReader<R> {
    fn poll_fill_buf(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<&[u8]>> {
        let me = self.project();

        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.

        if me.buf.is_empty() {
            ready!(me.inner.poll_read_buf(cx, me.buf))?;
        }
        Poll::Ready(Ok(&me.buf[..]))
    }

    fn consume(self: Pin<&mut Self>, amt: usize) {
        let me = self.project();
        me.buf.advance(amt);
    }
}

impl<R: AsyncRead + AsyncWrite> AsyncWrite for BufReader<R> {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        self.get_pin_mut().poll_write(cx, buf)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        self.get_pin_mut().poll_flush(cx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        self.get_pin_mut().poll_shutdown(cx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use tokio_02_dep::{self as tokio, io::AsyncReadExt};

    #[tokio::test]
    async fn buf_reader() {
        let mut read = BufReader::with_capacity(3, &[1u8,2,3,4,5,6,7,8,9,0][..]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).await.unwrap();
        assert_eq!(buf, [4, 5, 6]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).await.unwrap();
        assert_eq!(buf, [7, 8, 9]);

        let mut buf = [1u8; 3];
        read.read(&mut buf).await.unwrap();
        assert_eq!(buf, [0, 1, 1]);
    }

    #[tokio::test]
    async fn buf_reader_buf() {
        let mut read = BufReader::with_capacity(3, &[1u8,2,3,4,5,6,7,8,9,0][..]);

        let mut buf = BytesMut::with_capacity(3);
        read.read_buf(&mut buf).await.unwrap();
        assert_eq!(&buf[..], [1, 2, 3]);

        read.read_buf(&mut buf).await.unwrap();
        assert_eq!(&buf[..], [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }

    #[tokio::test]
    async fn buf_reader_extend_buf() {
        let read = BufReader::with_capacity(3, &[1u8,2,3,4,5,6,7,8,9,0][..]);
        futures_util_03::pin_mut!(read);

        assert_eq!(read.as_mut().extend_buf().await.unwrap(), 3);
        assert_eq!(read.buffer(), [1, 2, 3]);

        assert_eq!(read.as_mut().extend_buf().await.unwrap(), 7);
        assert_eq!(read.buffer(), [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }
}
