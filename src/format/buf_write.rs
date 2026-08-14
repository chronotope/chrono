use core::fmt::{self, Write};

const BUF_LEN: usize = size_of::<usize>() * 6;

#[inline(always)]
#[must_use = "use to advance pos"]
fn copy(dst: &mut [u8], src: &str) -> usize {
    dst[..src.len()].copy_from_slice(src.as_bytes());
    src.len()
}

pub(crate) struct BufWrite<'w, W: Write + ?Sized> {
    inner: &'w mut W,
    pos: usize,
    buf: [u8; BUF_LEN],
}

impl<'w, W: Write + ?Sized> BufWrite<'w, W> {
    pub(crate) fn new(inner: &'w mut W) -> Self {
        Self { inner, pos: 0, buf: [0; BUF_LEN] }
    }

    #[inline(always)]
    fn spare_mut(&mut self) -> &mut [u8] {
        // SAFETY: pos never exceeds BUF_LEN
        unsafe { self.buf.get_unchecked_mut(self.pos..) }
    }

    #[inline(always)]
    #[track_caller]
    fn advance(n: usize, _self: &mut Self) {
        debug_assert!(_self.pos + n <= BUF_LEN);
        _self.pos += n;
    }

    pub(crate) fn finish(mut self) -> fmt::Result {
        if self.pos > 0 { self.flush_inner() } else { Ok(()) }
    }

    fn flush_inner(&mut self) -> fmt::Result {
        let s = unsafe {
            // SAFETY: pos never exceeds BUF_LEN
            let filled = self.buf.get_unchecked(..self.pos);
            // SAFETY: BufWrite always writes valid utf8 to buf
            str::from_utf8_unchecked(filled)
        };
        self.inner.write_str(s)?;
        self.pos = 0;
        Ok(())
    }

    #[cold]
    fn flush(&mut self) -> Result<&mut [u8; BUF_LEN], core::fmt::Error> {
        self.flush_inner()?;
        Ok(&mut self.buf)
    }

    #[cold]
    fn copy_and_write_str(&mut self, s: &str) -> fmt::Result {
        let spare = self.spare_mut();
        let mid = s.floor_char_boundary(spare.len());
        let (head, tail) = s.split_at(mid);
        Self::advance(copy(spare, head), self);

        let spare = self.flush()?;
        if tail.len() <= spare.len() {
            Self::advance(copy(spare, tail), self);
            Ok(())
        } else {
            self.inner.write_str(tail)
        }
    }
}

impl<'w, W: Write + ?Sized> Write for BufWrite<'w, W> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let spare = self.spare_mut();
        if s.len() <= spare.len() {
            Self::advance(copy(spare, s), self);
            Ok(())
        } else {
            self.copy_and_write_str(s)
        }
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        let len = c.len_utf8();
        let spare = self.spare_mut();
        let dst = if len <= spare.len() { spare } else { self.flush()? };
        Self::advance(c.encode_utf8(dst).len(), self);
        Ok(())
    }
}
