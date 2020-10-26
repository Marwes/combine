use std::{
    io::{self, BufRead, Read},
    mem::MaybeUninit,
    pin::Pin,
};

#[cfg(feature = "futures-util-03")]
use std::{
    future::Future,
    task::{Context, Poll},
};

use {
    bytes_05::{Buf, BufMut, BytesMut},
    pin_project_lite::pin_project,
};

#[cfg(feature = "tokio-02")]
use tokio_02_dep::io::{AsyncBufRead, AsyncRead, AsyncWrite};

#[cfg(feature = "futures-util-03")]
use futures_util_03::ready;

pin_project! {
    /// `BufReader` used by `Decoder` when it is constructed with [`Decoder::new_bufferless`][]
    ///
    /// [`Decoder::new_bufferless`]: ../decoder/struct.Decoder.html#method.new_bufferless
    #[derive(Debug)]
    pub struct BufReader<R> {
        #[pin]
        inner: R,
        buf: BytesMut
    }
}

impl<R> BufReader<R> {
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

    /// Invalidates all data in the internal buffer.
    #[inline]
    #[cfg(feature = "tokio-02")]
    fn discard_buffer(self: Pin<&mut Self>) {
        let me = self.project();
        me.buf.clear();
    }
}

mod sealed {
    pub trait Sealed {}
}

#[doc(hidden)]
pub trait CombineBuffer<R>: sealed::Sealed {
    fn buffer<'a>(&'a self, read: &'a R) -> &'a [u8];

    fn advance(&mut self, read: &mut R, len: usize);

    fn advance_pin(&mut self, read: Pin<&mut R>, len: usize);
}

#[doc(hidden)]
pub trait CombineSyncRead<R>: CombineBuffer<R> {
    fn extend_buf_sync(&mut self, read: &mut R) -> io::Result<usize>;
}

#[cfg(feature = "tokio-02")]
#[doc(hidden)]
pub trait CombineRead<R>: CombineBuffer<R> {
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut R>,
    ) -> Poll<io::Result<usize>>;
}

#[cfg(feature = "futures-03")]
#[doc(hidden)]
pub trait CombineAsyncRead<R>: CombineBuffer<R> {
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut R>,
    ) -> Poll<io::Result<usize>>;

    fn extend_buf<'a>(&'a mut self, read: Pin<&'a mut R>) -> ExtendBuf<'a, Self, R>
    where
        Self: Sized;
}

#[cfg(feature = "futures-03")]
pin_project_lite::pin_project! {
    #[doc(hidden)]
    pub struct ExtendBuf<'a, C, R> {
        buffer: &'a mut C,
        read: Pin<&'a mut R>
    }
}

#[cfg(feature = "futures-03")]
impl<'a, C, R> Future for ExtendBuf<'a, C, R>
where
    C: CombineAsyncRead<R>,
{
    type Output = io::Result<usize>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let me = self.project();
        me.buffer.poll_extend_buf(cx, me.read.as_mut())
    }
}

/// Marker used by `Decoder` for an internal buffer
#[derive(Default)]
pub struct Buffer(pub(crate) BytesMut);

impl sealed::Sealed for Buffer {}

impl<R> CombineBuffer<R> for Buffer {
    fn buffer<'a>(&'a self, _read: &'a R) -> &'a [u8] {
        &self.0
    }

    fn advance(&mut self, _read: &mut R, len: usize) {
        self.0.advance(len);
    }

    fn advance_pin(&mut self, _read: Pin<&mut R>, len: usize) {
        self.0.advance(len);
    }
}

impl<R> CombineSyncRead<R> for Buffer
where
    R: Read,
{
    fn extend_buf_sync(&mut self, read: &mut R) -> io::Result<usize> {
        extend_buf_sync(&mut self.0, read)
    }
}

#[cfg(feature = "futures-03")]
impl<R> CombineAsyncRead<R> for Buffer
where
    R: futures_util_03::io::AsyncRead,
{
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut R>,
    ) -> Poll<io::Result<usize>> {
        poll_extend_buf(&mut self.0, cx, read)
    }

    fn extend_buf<'a>(&'a mut self, read: Pin<&'a mut R>) -> ExtendBuf<'a, Self, R> {
        if !self.0.has_remaining_mut() {
            self.0.reserve(8 * 1024);
        }
        // Copy of tokio's read_buf method (but it has to force initialize the buffer)
        let bs = self.0.bytes_mut();

        for b in &mut *bs {
            *b = MaybeUninit::new(0);
        }
        ExtendBuf { buffer: self, read }
    }
}

#[cfg(feature = "tokio-02")]
impl<R> CombineRead<R> for Buffer
where
    R: tokio_02_dep::io::AsyncRead,
{
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut R>,
    ) -> Poll<io::Result<usize>> {
        if !self.0.has_remaining_mut() {
            self.0.reserve(8 * 1024);
        }
        read.poll_read_buf(cx, &mut self.0)
    }
}

/// Marker used by `Decoder` for an external buffer
#[derive(Default)]
pub struct Bufferless;

impl sealed::Sealed for Bufferless {}

impl<R> CombineBuffer<BufReader<R>> for Bufferless {
    fn buffer<'a>(&'a self, read: &'a BufReader<R>) -> &'a [u8] {
        &read.buf
    }

    fn advance(&mut self, read: &mut BufReader<R>, len: usize) {
        read.buf.advance(len);
    }

    fn advance_pin(&mut self, read: Pin<&mut BufReader<R>>, len: usize) {
        read.project().buf.advance(len);
    }
}

impl<R> CombineSyncRead<BufReader<R>> for Bufferless
where
    R: Read,
{
    fn extend_buf_sync(&mut self, read: &mut BufReader<R>) -> io::Result<usize> {
        extend_buf_sync(&mut read.buf, &mut read.inner)
    }
}

fn extend_buf_sync<R>(buf: &mut BytesMut, read: &mut R) -> io::Result<usize>
where
    R: Read,
{
    if !buf.has_remaining_mut() {
        buf.reserve(8 * 1024);
    }

    // Copy of tokio's read_buf method (but it has to force initialize the buffer)
    let copied = unsafe {
        let n = {
            let bs = buf.bytes_mut();

            for b in &mut *bs {
                *b = MaybeUninit::new(0);
            }

            // Convert to `&mut [u8]`
            let bs = &mut *(bs as *mut [MaybeUninit<u8>] as *mut [u8]);

            let n = read.read(bs)?;
            assert!(n <= bs.len(), "AsyncRead reported that it initialized more than the number of bytes in the buffer");
            n
        };

        buf.advance_mut(n);
        n
    };
    Ok(copied)
}

#[cfg(feature = "tokio-02")]
impl<R> CombineRead<BufReader<R>> for Bufferless
where
    R: AsyncRead,
{
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut BufReader<R>>,
    ) -> Poll<io::Result<usize>> {
        let me = read.project();

        if !me.buf.has_remaining_mut() {
            me.buf.reserve(8 * 1024);
        }
        tokio_02_dep::io::AsyncRead::poll_read_buf(me.inner, cx, me.buf)
    }
}

#[cfg(feature = "futures-03")]
impl<R> CombineAsyncRead<BufReader<R>> for Bufferless
where
    R: futures_util_03::io::AsyncRead,
{
    fn poll_extend_buf(
        &mut self,
        cx: &mut Context<'_>,
        read: Pin<&mut BufReader<R>>,
    ) -> Poll<io::Result<usize>> {
        let me = read.project();

        poll_extend_buf(me.buf, cx, me.inner)
    }

    fn extend_buf<'a>(
        &'a mut self,
        mut read: Pin<&'a mut BufReader<R>>,
    ) -> ExtendBuf<'a, Self, BufReader<R>> {
        let me = read.as_mut().project();

        if !me.buf.has_remaining_mut() {
            me.buf.reserve(8 * 1024);
        }
        // Copy of tokio's read_buf method (but it has to force initialize the buffer)
        let bs = me.buf.bytes_mut();

        for b in &mut *bs {
            *b = MaybeUninit::new(0);
        }
        ExtendBuf { buffer: self, read }
    }
}

#[cfg(feature = "futures-03")]
fn poll_extend_buf<R>(
    buf: &mut BytesMut,
    cx: &mut Context<'_>,
    read: Pin<&mut R>,
) -> Poll<io::Result<usize>>
where
    R: futures_util_03::io::AsyncRead,
{
    // Copy of tokio's read_buf method (but it has to force initialize the buffer)
    let copied = unsafe {
        let n = {
            let bs = buf.bytes_mut();
            // Convert to `&mut [u8]`
            let bs = &mut *(bs as *mut [MaybeUninit<u8>] as *mut [u8]);

            let n = ready!(read.poll_read(cx, bs))?;
            assert!(n <= bs.len(), "AsyncRead reported that it initialized more than the number of bytes in the buffer");
            n
        };

        buf.advance_mut(n);
        n
    };
    Poll::Ready(Ok(copied))
}

#[cfg(feature = "tokio-02")]
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

#[cfg(feature = "tokio-02")]
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

#[cfg(feature = "tokio-02")]
impl<R: AsyncRead + AsyncWrite> AsyncWrite for BufReader<R> {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        self.get_pin_mut().poll_write(cx, buf)
    }

    fn poll_write_buf<B: Buf>(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut B,
    ) -> Poll<io::Result<usize>> {
        self.get_pin_mut().poll_write_buf(cx, buf)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        self.get_pin_mut().poll_flush(cx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        self.get_pin_mut().poll_shutdown(cx)
    }
}

impl<R: Read> Read for BufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we don't have any buffered data and we're doing a massive read
        // (larger than our internal buffer), bypass our internal buffer
        // entirely.
        if !self.buf.has_remaining_mut() && buf.len() >= self.buf.len() {
            let res = self.read(buf);
            self.buf.clear();
            return res;
        }
        let nread = {
            let mut rem = self.fill_buf()?;
            rem.read(buf)?
        };
        self.consume(nread);
        Ok(nread)
    }
}

impl<R: Read> BufRead for BufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we've reached the end of our internal buffer then we need to fetch
        // some more data from the underlying reader.
        // Branch using `>=` instead of the more correct `==`
        // to tell the compiler that the pos..cap slice is always valid.

        if self.buf.is_empty() {
            Bufferless.extend_buf_sync(self)?;
        }
        Ok(&self.buf[..])
    }

    fn consume(&mut self, amt: usize) {
        self.buf.advance(amt);
    }
}

#[cfg(test)]
#[cfg(feature = "futures-util-03")]
mod tests {
    use super::{BufReader, Bufferless, CombineRead};

    use std::{io, pin::Pin};

    use {
        bytes_05::BytesMut,
        tokio_02_dep::{
            self as tokio,
            io::{AsyncRead, AsyncReadExt},
        },
    };

    #[cfg(feature = "tokio-02")]
    impl<R: AsyncRead> BufReader<R> {
        async fn extend_buf_tokio(mut self: Pin<&mut Self>) -> io::Result<usize> {
            futures_util_03::future::poll_fn(|cx| Bufferless.poll_extend_buf(cx, self.as_mut()))
                .await
        }
    }

    #[tokio::test]
    async fn buf_reader() {
        let mut read = BufReader::with_capacity(3, &[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 0][..]);

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
        let mut read = BufReader::with_capacity(3, &[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 0][..]);

        let mut buf = BytesMut::with_capacity(3);
        read.read_buf(&mut buf).await.unwrap();
        assert_eq!(&buf[..], [1, 2, 3]);

        read.read_buf(&mut buf).await.unwrap();
        assert_eq!(&buf[..], [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }

    #[tokio::test]
    #[cfg(feature = "tokio-02")]
    async fn buf_reader_extend_buf() {
        let read = BufReader::with_capacity(3, &[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 0][..]);
        futures_util_03::pin_mut!(read);

        assert_eq!(read.as_mut().extend_buf_tokio().await.unwrap(), 3);
        assert_eq!(read.buffer(), [1, 2, 3]);

        assert_eq!(read.as_mut().extend_buf_tokio().await.unwrap(), 7);
        assert_eq!(read.buffer(), [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }
}

#[cfg(test)]
mod tests_sync {
    use super::{BufReader, Bufferless, CombineSyncRead};

    use std::io::Read;

    #[test]
    fn buf_reader() {
        let mut read = BufReader::with_capacity(3, &[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 0][..]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).unwrap();
        assert_eq!(buf, [4, 5, 6]);

        let mut buf = [0u8; 3];
        read.read(&mut buf).unwrap();
        assert_eq!(buf, [7, 8, 9]);

        let mut buf = [1u8; 3];
        read.read(&mut buf).unwrap();
        assert_eq!(buf, [0, 1, 1]);
    }

    #[test]
    fn buf_reader_extend_buf() {
        let mut read = BufReader::with_capacity(3, &[1u8, 2, 3, 4, 5, 6, 7, 8, 9, 0][..]);

        assert_eq!(Bufferless.extend_buf_sync(&mut read).unwrap(), 3);
        assert_eq!(read.buffer(), [1, 2, 3]);

        assert_eq!(Bufferless.extend_buf_sync(&mut read).unwrap(), 7);
        assert_eq!(read.buffer(), [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);
    }
}
