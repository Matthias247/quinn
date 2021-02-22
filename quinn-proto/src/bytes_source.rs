//! Defines types which can be lazily converted into `Bytes` chunks

use bytes::Bytes;

/// A source of one or more buffers which can be converted into `Bytes` buffers on demand
///
/// The purpose of this data type is to defer conversion as long as possible,
/// so that no heap allocation is required in case no data is writable.
pub trait BytesSource {
    /// Returns the next chunk from the source of owned chunks.
    ///
    /// This method will consume parts of the source.
    // Calling it will yield `Bytes` elements up to the configured `limit`.
    fn pop_chunk(&mut self, limit: usize) -> Option<Bytes>;
}

/// Indicates how many bytes and chunks had been transferred in a write operation
#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub struct Written {
    /// The amount of bytes which had been written
    pub bytes: usize,
    /// The amount of full chunks which had been written
    ///
    /// If a chunk was only partially written, it will not be counted by this field.
    pub chunks: usize,
}

/// A [`BytesSource`] implementation for `&'a mut [Bytes]`
///
/// The type allows to dequeue [`Bytes`] chunks from an array of chunks, up to
/// a configured limit.
pub struct BytesArray<'a> {
    /// The wrapped slice of `Bytes`
    chunks: &'a mut [Bytes],
    /// The amount of bytes which are still available for consumption
    len: usize,
    /// The amount of bytes and chunks consumed from this source
    consumed: Written,
}

impl<'a> BytesArray<'a> {
    pub fn from_chunks(chunks: &'a mut [Bytes]) -> Self {
        let len = chunks.iter().map(|chunk| chunk.len()).sum();
        Self {
            chunks,
            len,
            consumed: Written::default(),
        }
    }
}

impl<'a> BytesSource for BytesArray<'a> {
    fn pop_chunk(&mut self, limit: usize) -> Option<Bytes> {
        // The loop exists to skip empty chunks while still marking them as
        // consumed
        while self.consumed.chunks < self.chunks.len() {
            let chunk = &mut self.chunks[self.consumed.chunks];

            if chunk.len() <= self.len {
                let chunk = std::mem::take(chunk);
                self.consumed.chunks += 1;
                if chunk.is_empty() {
                    continue;
                }
                self.len -= chunk.len();
                self.consumed.bytes += chunk.len();
                return Some(chunk);
            } else if self.len > 0 {
                let chunk = chunk.split_to(self.len);
                self.len = 0;
                self.consumed.bytes += chunk.len();
                return Some(chunk);
            } else {
                return None;
            }
        }

        None
    }
}

/// A [`BytesSource`] implementation for `&[u8]`
///
/// The type allows to dequeue a single [`Bytes`] chunk, which will be lazily
/// created from a reference. This allows to defer the allocation until it is
/// known how much data needs to be copied.
pub struct ByteSlice<'a> {
    /// The wrapped byte slice
    data: &'a [u8],
    /// The amount of bytes which are still available for consumption
    len: usize,
    /// The amount of bytes and chunks consumed from this source
    consumed: Written,
}

impl<'a> ByteSlice<'a> {
    pub fn from_slice(data: &'a [u8]) -> Self {
        let len = data.len();
        Self {
            data,
            len,
            consumed: Written::default(),
        }
    }
}

impl<'a> BytesSource for ByteSlice<'a> {
    fn pop_chunk(&mut self, limit: usize) -> Option<Bytes> {
        if self.len == 0 {
            return None;
        }

        let chunk = Bytes::from(self.data[..self.len].to_owned());
        self.consumed.bytes += chunk.len();
        if self.len == self.data.len() {
            self.consumed.chunks += 1;
        }
        self.len = 0;
        Some(chunk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bytes_array() {
        let full = b"Hello World 123456789 ABCDEFGHJIJKLMNOPQRSTUVWXYZ".to_owned();
        for limit in 0..full.len() {
            let mut chunks = [
                Bytes::from_static(b""),
                Bytes::from_static(b"Hello "),
                Bytes::from_static(b"Wo"),
                Bytes::from_static(b""),
                Bytes::from_static(b"r"),
                Bytes::from_static(b"ld"),
                Bytes::from_static(b""),
                Bytes::from_static(b" 12345678"),
                Bytes::from_static(b"9 ABCDE"),
                Bytes::from_static(b"F"),
                Bytes::from_static(b"GHJIJKLMNOPQRSTUVWXYZ"),
            ];
            let num_chunks = chunks.len();
            let last_chunk_len = chunks[chunks.len() - 1].len();

            let mut array = BytesArray::from_chunks(&mut chunks);
            assert_eq!(array.len, full.len());

            array.limit(limit);
            assert_eq!(array.len, limit);

            let mut buf = Vec::new();
            let mut chunks_popped = 0;
            while let Some(chunk) = array.pop_chunk() {
                buf.extend_from_slice(&chunk);
                chunks_popped += 1;
            }

            assert_eq!(&buf[..], &full[..limit]);
            assert_eq!(array.consumed().bytes, limit);

            if limit == full.len() {
                // Full consumption of the last chunk
                assert_eq!(array.consumed().chunks, num_chunks);
                // Since there are empty chunks, we consume more than there are popped
                assert_eq!(array.consumed().chunks, chunks_popped + 3);
            } else if limit > full.len() - last_chunk_len {
                // Partial consumption of the last chunk
                assert_eq!(array.consumed().chunks, num_chunks - 1);
                assert_eq!(array.consumed().chunks, chunks_popped + 2);
            }
        }
    }

    #[test]
    fn byte_slice() {
        let full = b"Hello World 123456789 ABCDEFGHJIJKLMNOPQRSTUVWXYZ".to_owned();
        for limit in 0..full.len() {
            let mut array = ByteSlice::from_slice(&full[..]);
            assert_eq!(array.len, full.len());

            array.limit(limit);
            assert_eq!(array.len, limit);

            let mut buf = Vec::new();
            while let Some(chunk) = array.pop_chunk() {
                buf.extend_from_slice(&chunk);
            }

            assert_eq!(&buf[..], &full[..limit]);
            assert_eq!(array.consumed().bytes, limit);

            if limit == full.len() {
                assert_eq!(array.consumed().chunks, 1);
            } else {
                assert_eq!(array.consumed().chunks, 0);
            }
        }
    }
}
