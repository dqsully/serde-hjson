use crate::error::{Error, ErrorCode, Result};
use crate::lib::ops::Deref;
use crate::lib::*;

#[cfg(feature = "std")]
use crate::io;
#[cfg(feature = "std")]
use crate::iter::LineColIterator;

#[cfg(feature = "raw_value")]
use crate::raw::BorrowedRawDeserializer;
#[cfg(all(feature = "raw_value", feature = "std"))]
use crate::raw::OwnedRawDeserializer;
#[cfg(feature = "raw_value")]
use serde::de::Visitor;

/// Trait used by the deserializer for iterating over input. This is manually
/// "specialized" for iterating over &[u8]. Once feature(specialization) is
/// stable we can use actual specialization.
///
/// This trait is sealed and cannot be implemented for types outside of
/// `serde_hjson`.
pub trait Read<'de>: private::Sealed {
    #[doc(hidden)]
    fn next(&mut self) -> Result<Option<u8>>;
    #[doc(hidden)]
    fn peek(&mut self) -> Result<Option<u8>>;
    #[doc(hidden)]
    fn peek_n(&mut self, bytes: usize) -> Result<&[u8]>;

    /// Only valid after a call to peek(). Discards the peeked byte.
    #[doc(hidden)]
    fn discard(&mut self);
    /// Only valid after a call to peek(). Discards the peeked byte.
    #[doc(hidden)]
    fn discard_n(&mut self, bytes: usize);

    /// Position of the most recent call to next().
    ///
    /// The most recent call was probably next() and not peek(), but this method
    /// should try to return a sensible result if the most recent call was
    /// actually peek() because we don't always know.
    ///
    /// Only called in case of an error, so performance is not important.
    #[doc(hidden)]
    fn position(&self) -> Position;

    /// Position of the most recent call to peek().
    ///
    /// The most recent call was probably peek() and not next(), but this method
    /// should try to return a sensible result if the most recent call was
    /// actually next() because we don't always know.
    ///
    /// Only called in case of an error, so performance is not important.
    #[doc(hidden)]
    fn peek_position(&self) -> Position;

    /// Offset from the beginning of the input to the next byte that would be
    /// returned by next() or peek().
    #[doc(hidden)]
    fn byte_offset(&self) -> usize;

    /// Assumes the previous byte was a quotation mark. Parses a JSON-escaped
    /// string until the next quotation mark using the given scratch space if
    /// necessary. The scratch space is initially empty.
    #[doc(hidden)]
    fn parse_double_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>>;

    /// Assumes the previous byte was an apostrophe. Parses a JSON-escaped
    /// string until the next apostrophe using the given scratch space if
    /// necessary. The scratch space is initially empty.
    #[doc(hidden)]
    fn parse_single_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>>;

    /// Parses an unquoted string until the next newline using the given scratch
    /// space if necessary. The scratch space is initially empty.
    #[doc(hidden)]
    fn parse_unquoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>>;

    /// Parses an unquoted object key string until the next newline using the
    /// given scratch space if necessary. The scratch space is initially empty.
    #[doc(hidden)]
    fn parse_unquoted_key_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>>;

    /// Assumes the previous byte was a quotation mark. Parses a JSON-escaped
    /// string until the next quotation mark using the given scratch space if
    /// necessary. The scratch space is initially empty.
    ///
    /// This function returns the raw bytes in the string with escape sequences
    /// expanded but without performing unicode validation.
    #[doc(hidden)]
    fn parse_double_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>>;

    /// Assumes the previous byte was an apostrophe. Parses a JSON-escaped
    /// string until the next apostrophe using the given scratch space if
    /// necessary. The scratch space is initially empty.
    ///
    /// This function returns the raw bytes in the string with escape sequences
    /// expanded but without performing unicode validation.
    #[doc(hidden)]
    fn parse_single_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>>;

    /// Parses an unquoted string until the next newline using the given scratch
    /// space if necessary. The scratch space is initially empty.
    ///
    /// This function returns the raw bytes in the string with escape sequences
    /// expanded but without performing unicode validation.
    #[doc(hidden)]
    fn parse_unquoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>>;

    /// Parses an unquoted object key string until the next newline using the
    /// given scratch space if necessary. The scratch space is initially empty.
    ///
    /// This function returns the raw bytes in the string with escape sequences
    /// expanded but without performing unicode validation.
    #[doc(hidden)]
    fn parse_unquoted_key_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>>;

    /// Assumes the previous byte was a quotation mark. Parses a JSON-escaped
    /// string until the next quotation mark but discards the data.
    #[doc(hidden)]
    fn ignore_double_quoted_str(&mut self) -> Result<()>;

    /// Assumes the previous byte was an apostrophe. Parses a JSON-escaped
    /// string until the next quotation mark but discards the data.
    #[doc(hidden)]
    fn ignore_single_quoted_str(&mut self) -> Result<()>;

    /// Parses an unquoted string until the next newline but discards the data.
    #[doc(hidden)]
    fn ignore_unquoted_str(&mut self) -> Result<()>;

    /// Parses an unquoted object key string until the next newline but discards
    /// the data.
    #[doc(hidden)]
    fn ignore_unquoted_key_str(&mut self) -> Result<()>;

    /// Assumes the previous byte was a hex escape sequence ('\u') in a string.
    /// Parses next hexadecimal sequence.
    #[doc(hidden)]
    fn decode_hex_escape(&mut self) -> Result<u16>;

    /// Switch raw buffering mode on.
    ///
    /// This is used when deserializing `RawValue`.
    #[cfg(feature = "raw_value")]
    #[doc(hidden)]
    fn begin_raw_buffering(&mut self);

    /// Switch raw buffering mode off and provides the raw buffered data to the
    /// given visitor.
    #[cfg(feature = "raw_value")]
    #[doc(hidden)]
    fn end_raw_buffering<V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>;

    /// Whether StreamDeserializer::next needs to check the failed flag. True
    /// for IoRead, false for StrRead and SliceRead which can track failure by
    /// truncating their input slice to avoid the extra check on every next
    /// call.
    #[doc(hidden)]
    const should_early_return_if_failed: bool;

    /// Mark a persistent failure of StreamDeserializer, either by setting the
    /// flag or by truncating the input data.
    #[doc(hidden)]
    fn set_failed(&mut self, failed: &mut bool);
}

pub struct Position {
    pub line: usize,
    pub column: usize,
}

pub enum Reference<'b, 'c, T>
where
    T: ?Sized + 'static,
{
    Borrowed(&'b T),
    Copied(&'c T),
}

impl<'b, 'c, T> Deref for Reference<'b, 'c, T>
where
    T: ?Sized + 'static,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match *self {
            Reference::Borrowed(b) => b,
            Reference::Copied(c) => c,
        }
    }
}

/// JSON input source that reads from a std::io input stream.
#[cfg(feature = "std")]
pub struct IoRead<R>
where
    R: io::Read,
{
    iter: LineColIterator<io::Bytes<R>>,
    /// Temporary storage of peeked bytes.
    ch: [u8; 4],
    len: usize,
    #[cfg(feature = "raw_value")]
    raw_buffer: Option<Vec<u8>>,
}

/// JSON input source that reads from a slice of bytes.
//
// This is more efficient than other iterators because peek() can be read-only
// and we can compute line/col position only if an error happens.
pub struct SliceRead<'a> {
    slice: &'a [u8],
    /// Index of the *next* byte that will be returned by next() or peek().
    index: usize,
    #[cfg(feature = "raw_value")]
    raw_buffering_start_index: usize,
}

/// JSON input source that reads from a UTF-8 string.
//
// Able to elide UTF-8 checks by assuming that the input is valid UTF-8.
pub struct StrRead<'a> {
    delegate: SliceRead<'a>,
    #[cfg(feature = "raw_value")]
    data: &'a str,
}

// Prevent users from implementing the Read trait.
mod private {
    pub trait Sealed {}
}

//////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "std")]
impl<R> IoRead<R>
where
    R: io::Read,
{
    /// Create a JSON input source to read from a std::io input stream.
    pub fn new(reader: R) -> Self {
        IoRead {
            iter: LineColIterator::new(reader.bytes()),
            ch: [0; 4],
            len: 0,
            #[cfg(feature = "raw_value")]
            raw_buffer: None,
        }
    }
}

#[cfg(feature = "std")]
impl<R> private::Sealed for IoRead<R> where R: io::Read {}

#[cfg(feature = "std")]
impl<R> IoRead<R>
where
    R: io::Read,
{
    fn parse_double_quoted_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<T>
    where
        T: 's,
        F: FnOnce(&'s Self, &'s [u8]) -> Result<T>,
    {
        loop {
            let ch = tri!(next_or_eof(self));
            if !DOUBLE_QUOTE_ESCAPE[ch as usize] {
                scratch.push(ch);
                continue;
            }
            match ch {
                b'"' => {
                    return result(self, scratch);
                }
                b'\\' => {
                    tri!(parse_escape(self, scratch));
                }
                _ => {
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                    scratch.push(ch);
                }
            }
        }
    }

    fn parse_single_quoted_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<T>
    where
        T: 's,
        F: FnOnce(&'s Self, &'s [u8]) -> Result<T>,
    {
        loop {
            let ch = tri!(next_or_eof(self));
            if !SINGLE_QUOTE_ESCAPE[ch as usize] {
                scratch.push(ch);
                continue;
            }
            match ch {
                b'\'' => {
                    return result(self, scratch);
                }
                b'\\' => {
                    tri!(parse_escape(self, scratch));
                }
                _ => {
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                    scratch.push(ch);
                }
            }
        }
    }

    fn parse_unquoted_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<T>
    where
        T: 's,
        F: FnOnce(&'s Self, &'s [u8]) -> Result<T>,
    {
        loop {
            let ch = tri!(next_or_eof(self));
            if !NO_QUOTE_ESCAPE[ch as usize] {
                scratch.push(ch);
                continue;
            }
            match ch {
                b'\n' => {
                    let mut index = scratch.len() - 1;
                    let mut ch = scratch[index];

                    while ch == b' ' || ch == b'\t' || ch == b'\n' || ch == b'\r' {
                        index -= 1;
                        ch = scratch[index];
                    }

                    return result(self, &scratch[..=index]);
                }
                _ => {
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                    scratch.push(ch);
                }
            }
        }
    }

    fn parse_unquoted_key_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<T>
    where
        T: 's,
        F: FnOnce(&'s Self, &'s [u8]) -> Result<T>,
    {
        loop {
            let ch = tri!(next_or_eof(self));
            if !NO_QUOTE_KEY_ESCAPE[ch as usize] {
                scratch.push(ch);
                continue;
            }
            match ch {
                b'\n' => {
                    return result(self, scratch);
                }
                _ => {
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                    scratch.push(ch);
                }
            }
        }
    }
}

#[cfg(feature = "std")]
impl<'de, R> Read<'de> for IoRead<R>
where
    R: io::Read,
{
    #[inline]
    fn next(&mut self) -> Result<Option<u8>> {
        if self.len > 0 {
            #[cfg(feature = "raw_value")]
            {
                if let Some(ref mut buf) = self.raw_buffer {
                    buf.push(ch);
                }
            }

            let ch = self.ch[0];

            self.len -= 1;
            self.ch.copy_within(1.., 0);

            Ok(Some(ch))
        } else {
            match self.iter.next() {
                Some(Err(err)) => Err(Error::io(err)),
                Some(Ok(ch)) => {
                    #[cfg(feature = "raw_value")]
                    {
                        if let Some(ref mut buf) = self.raw_buffer {
                            buf.push(ch);
                        }
                    }
                    Ok(Some(ch))
                }
                None => Ok(None),
            }
        }
    }

    #[inline]
    fn peek(&mut self) -> Result<Option<u8>> {
        if self.len == 0 {
            match self.iter.next() {
                Some(Err(err)) => Err(Error::io(err)),
                Some(Ok(ch)) => {
                    self.ch[0] = ch;
                    self.len = 1;
                    Ok(Some(ch))
                }
                None => Ok(None)
            }
        } else {
            Ok(Some(self.ch[0]))
        }
    }

    #[inline]
    fn peek_n(&mut self, bytes: usize) -> Result<&[u8]> {
        assert!(bytes <= 4, "can only peek a max of 4 bytes");

        while self.len < bytes {
            match self.iter.next() {
                Some(Err(err)) => return Err(Error::io(err)),
                Some(Ok(ch)) => {
                    self.ch[self.len] = ch;
                    self.len += 1;
                }
                None => break,
            }
        }

        Ok(&self.ch[..self.len])
    }

    #[cfg(not(feature = "raw_value"))]
    #[inline]
    fn discard(&mut self) {
        if self.len == 1 {
            self.len = 0;
        } else if self.len > 0 {
            self.len -= 1;
            self.ch.copy_within(1.., 0);
        }
    }

    #[cfg(feature = "raw_value")]
    fn discard(&mut self) {
        if self.len > 0 {
            if let Some(ref mut buf) = self.raw_buffer {
                buf.push(self.ch[0]);
            }

            self.len -= 1;
            self.ch.copy_within(1.., 0);
        }
    }

    #[cfg(not(feature = "raw_value"))]
    #[inline]
    fn discard_n(&mut self, bytes: usize) {
        if bytes >= self.len {
            self.len = 0;
        } else {
            self.len -= bytes;
            self.ch.copy_within(bytes.., 0);
        }
    }

    #[cfg(feature = "raw_value")]
    fn discard_n(&mut self, bytes: usize) {
        if bytes >= self.len {
            if let Some(ref mut buf) = self.raw_buffer {
                buf.extend_from_slice(&self.ch[..self.len]);
            }

            self.len = 0;
        } else {
            if let Some(ref mut buf) = self.raw_buffer {
                buf.extend_from_slice(&self.ch[..bytes]);
            }

            self.len -= bytes;
            self.ch.copy_within(bytes.., 0);
        }
    }

    fn position(&self) -> Position {
        Position {
            line: self.iter.line(),
            column: self.iter.col(),
        }
    }

    fn peek_position(&self) -> Position {
        // The LineColIterator updates its position during peek() so it has the
        // right one here.
        self.position()
    }

    fn byte_offset(&self) -> usize {
        self.iter.byte_offset() - self.len
    }

    fn parse_double_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>> {
        self.parse_double_quoted_str_bytes(scratch, true, as_str)
            .map(Reference::Copied)
    }

    fn parse_single_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>> {
        self.parse_single_quoted_str_bytes(scratch, true, as_str)
            .map(Reference::Copied)
    }

    fn parse_unquoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>> {
        self.parse_unquoted_str_bytes(scratch, true, as_str)
            .map(Reference::Copied)
    }

    fn parse_unquoted_key_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, str>> {
        self.parse_unquoted_key_str_bytes(scratch, true, as_str)
            .map(Reference::Copied)
    }

    fn parse_double_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>> {
        self.parse_double_quoted_str_bytes(scratch, false, |_, bytes| Ok(bytes))
            .map(Reference::Copied)
    }

    fn parse_single_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>> {
        self.parse_single_quoted_str_bytes(scratch, false, |_, bytes| Ok(bytes))
            .map(Reference::Copied)
    }

    fn parse_unquoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>> {
        self.parse_unquoted_str_bytes(scratch, false, |_, bytes| Ok(bytes))
            .map(Reference::Copied)
    }

    fn parse_unquoted_key_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'de, 's, [u8]>> {
        self.parse_unquoted_key_str_bytes(scratch, false, |_, bytes| Ok(bytes))
            .map(Reference::Copied)
    }

    fn ignore_double_quoted_str(&mut self) -> Result<()> {
        loop {
            let ch = tri!(next_or_eof(self));
            if !DOUBLE_QUOTE_ESCAPE[ch as usize] {
                continue;
            }
            match ch {
                b'"' => {
                    return Ok(());
                }
                b'\\' => {
                    tri!(ignore_escape(self));
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn ignore_single_quoted_str(&mut self) -> Result<()> {
        loop {
            let ch = tri!(next_or_eof(self));
            if !SINGLE_QUOTE_ESCAPE[ch as usize] {
                continue;
            }
            match ch {
                b'\'' => {
                    return Ok(());
                }
                b'\\' => {
                    tri!(ignore_escape(self));
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn ignore_unquoted_str(&mut self) -> Result<()> {
        loop {
            let ch = tri!(next_or_eof(self));
            if !NO_QUOTE_ESCAPE[ch as usize] {
                continue;
            }
            match ch {
                b'\n' => {
                    return Ok(());
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn ignore_unquoted_key_str(&mut self) -> Result<()> {
        loop {
            let ch = tri!(next_or_eof(self));
            if !NO_QUOTE_KEY_ESCAPE[ch as usize] {
                continue;
            }
            match ch {
                b' ' | b'\t' | b'\n' | b'\r' => {
                    return Ok(());
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn decode_hex_escape(&mut self) -> Result<u16> {
        let mut n = 0;
        for _ in 0..4 {
            match decode_hex_val(tri!(next_or_eof(self))) {
                None => return error(self, ErrorCode::InvalidEscape),
                Some(val) => {
                    n = (n << 4) + val;
                }
            }
        }
        Ok(n)
    }

    #[cfg(feature = "raw_value")]
    fn begin_raw_buffering(&mut self) {
        self.raw_buffer = Some(Vec::new());
    }

    #[cfg(feature = "raw_value")]
    fn end_raw_buffering<V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let raw = self.raw_buffer.take().unwrap();
        let raw = String::from_utf8(raw).unwrap();
        visitor.visit_map(OwnedRawDeserializer {
            raw_value: Some(raw),
        })
    }

    const should_early_return_if_failed: bool = true;

    #[inline]
    #[cold]
    fn set_failed(&mut self, failed: &mut bool) {
        *failed = true;
    }
}

//////////////////////////////////////////////////////////////////////////////

impl<'a> SliceRead<'a> {
    /// Create a JSON input source to read from a slice of bytes.
    pub fn new(slice: &'a [u8]) -> Self {
        SliceRead {
            slice,
            index: 0,
            #[cfg(feature = "raw_value")]
            raw_buffering_start_index: 0,
        }
    }

    fn position_of_index(&self, i: usize) -> Position {
        let mut position = Position { line: 1, column: 0 };
        for ch in &self.slice[..i] {
            match *ch {
                b'\n' => {
                    position.line += 1;
                    position.column = 0;
                }
                _ => {
                    position.column += 1;
                }
            }
        }
        position
    }

    /// The big optimization here over IoRead is that if the string contains no
    /// backslash escape sequences, the returned &str is a slice of the raw JSON
    /// data so we avoid copying into the scratch space.
    fn parse_double_quoted_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<Reference<'a, 's, T>>
    where
        T: ?Sized + 's,
        F: for<'f> FnOnce(&'s Self, &'f [u8]) -> Result<&'f T>,
    {
        // Index of the first byte not yet copied into the scratch space.
        let mut start = self.index;

        loop {
            while self.index < self.slice.len() && !DOUBLE_QUOTE_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b'"' => {
                    if scratch.is_empty() {
                        // Fast path: return a slice of the raw JSON without any
                        // copying.
                        let borrowed = &self.slice[start..self.index];
                        self.index += 1;
                        return result(self, borrowed).map(Reference::Borrowed);
                    } else {
                        scratch.extend_from_slice(&self.slice[start..self.index]);
                        self.index += 1;
                        return result(self, scratch).map(Reference::Copied);
                    }
                }
                b'\\' => {
                    scratch.extend_from_slice(&self.slice[start..self.index]);
                    self.index += 1;
                    tri!(parse_escape(self, scratch));
                    start = self.index;
                }
                _ => {
                    self.index += 1;
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                }
            }
        }
    }

    /// The big optimization here over IoRead is that if the string contains no
    /// backslash escape sequences, the returned &str is a slice of the raw JSON
    /// data so we avoid copying into the scratch space.
    fn parse_single_quoted_str_bytes<'s, T, F>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
        validate: bool,
        result: F,
    ) -> Result<Reference<'a, 's, T>>
    where
        T: ?Sized + 's,
        F: for<'f> FnOnce(&'s Self, &'f [u8]) -> Result<&'f T>,
    {
        // Index of the first byte not yet copied into the scratch space.
        let mut start = self.index;

        loop {
            while self.index < self.slice.len() && !SINGLE_QUOTE_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b'\'' => {
                    if scratch.is_empty() {
                        // Fast path: return a slice of the raw JSON without any
                        // copying.
                        let borrowed = &self.slice[start..self.index];
                        self.index += 1;
                        return result(self, borrowed).map(Reference::Borrowed);
                    } else {
                        scratch.extend_from_slice(&self.slice[start..self.index]);
                        self.index += 1;
                        return result(self, scratch).map(Reference::Copied);
                    }
                }
                b'\\' => {
                    scratch.extend_from_slice(&self.slice[start..self.index]);
                    self.index += 1;
                    tri!(parse_escape(self, scratch));
                    start = self.index;
                }
                _ => {
                    self.index += 1;
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                }
            }
        }
    }

    /// The big optimization here over IoRead is that if the string contains no
    /// backslash escape sequences, the returned &str is a slice of the raw JSON
    /// data so we avoid copying into the scratch space.
    fn parse_unquoted_str_bytes<'s, T, F>(
        &'s mut self,
        validate: bool,
        result: F,
    ) -> Result<Reference<'a, 's, T>>
    where
        T: ?Sized + 's,
        F: for<'f> FnOnce(&'s Self, &'f [u8]) -> Result<&'f T>,
    {
        // Index of the first byte not yet copied into the scratch space.
        let start = self.index;

        loop {
            while self.index < self.slice.len() && !NO_QUOTE_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b'\n' => {
                    let mut index = self.index - 1;
                    let mut ch = self.slice[index];

                    while ch == b' ' || ch == b'\t' || ch == b'\n' || ch == b'\r' {
                        index -= 1;
                        ch = self.slice[index];
                    }

                    let borrowed = &self.slice[start..=index];
                    self.index += 1;
                    return result(self, borrowed).map(Reference::Borrowed);
                }
                _ => {
                    self.index += 1;
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                }
            }
        }
    }

    /// The big optimization here over IoRead is that if the string contains no
    /// backslash escape sequences, the returned &str is a slice of the raw JSON
    /// data so we avoid copying into the scratch space.
    fn parse_unquoted_key_str_bytes<'s, T, F>(
        &'s mut self,
        validate: bool,
        result: F,
    ) -> Result<Reference<'a, 's, T>>
    where
        T: ?Sized + 's,
        F: for<'f> FnOnce(&'s Self, &'f [u8]) -> Result<&'f T>,
    {
        // Index of the first byte not yet copied into the scratch space.
        let start = self.index;

        loop {
            while self.index < self.slice.len() && !NO_QUOTE_KEY_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b' ' | b'\t' | b'\n' | b'\r' => {
                    let borrowed = &self.slice[start..self.index];
                    self.index += 1;
                    return result(self, borrowed).map(Reference::Borrowed);
                }
                _ => {
                    self.index += 1;
                    if validate {
                        return error(self, ErrorCode::ControlCharacterWhileParsingString);
                    }
                }
            }
        }
    }
}

impl<'a> private::Sealed for SliceRead<'a> {}

impl<'a> Read<'a> for SliceRead<'a> {
    #[inline]
    fn next(&mut self) -> Result<Option<u8>> {
        // `Ok(self.slice.get(self.index).map(|ch| { self.index += 1; *ch }))`
        // is about 10% slower.
        Ok(if self.index < self.slice.len() {
            let ch = self.slice[self.index];
            self.index += 1;
            Some(ch)
        } else {
            None
        })
    }

    #[inline]
    fn peek(&mut self) -> Result<Option<u8>> {
        // `Ok(self.slice.get(self.index).map(|ch| *ch))` is about 10% slower
        // for some reason.
        Ok(if self.index < self.slice.len() {
            Some(self.slice[self.index])
        } else {
            None
        })
    }

    #[inline]
    fn peek_n(&mut self, bytes: usize) -> Result<&[u8]> {
        if self.index + bytes > self.slice.len() {
            Ok(&self.slice[self.index..])
        } else {
            Ok(&self.slice[self.index..self.index + bytes])
        }
    }

    #[inline]
    fn discard(&mut self) {
        self.index += 1;
    }

    #[inline]
    fn discard_n(&mut self, bytes: usize) {
        self.index += bytes;
    }

    fn position(&self) -> Position {
        self.position_of_index(self.index)
    }

    fn peek_position(&self) -> Position {
        // Cap it at slice.len() just in case the most recent call was next()
        // and it returned the last byte.
        self.position_of_index(cmp::min(self.slice.len(), self.index + 1))
    }

    fn byte_offset(&self) -> usize {
        self.index
    }

    fn parse_double_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.parse_double_quoted_str_bytes(scratch, true, as_str)
    }

    fn parse_single_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.parse_single_quoted_str_bytes(scratch, true, as_str)
    }

    fn parse_unquoted_str<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.parse_unquoted_str_bytes(true, as_str)
    }

    fn parse_unquoted_key_str<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.parse_unquoted_key_str_bytes(true, as_str)
    }

    fn parse_double_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.parse_double_quoted_str_bytes(scratch, false, |_, bytes| Ok(bytes))
    }

    fn parse_single_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.parse_single_quoted_str_bytes(scratch, false, |_, bytes| Ok(bytes))
    }

    fn parse_unquoted_str_raw<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.parse_unquoted_str_bytes(false, |_, bytes| Ok(bytes))
    }

    fn parse_unquoted_key_str_raw<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.parse_unquoted_key_str_bytes(false, |_, bytes| Ok(bytes))
    }

    fn ignore_double_quoted_str(&mut self) -> Result<()> {
        loop {
            while self.index < self.slice.len() && !DOUBLE_QUOTE_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b'"' => {
                    self.index += 1;
                    return Ok(());
                }
                b'\\' => {
                    self.index += 1;
                    tri!(ignore_escape(self));
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn ignore_single_quoted_str(&mut self) -> Result<()> {
        loop {
            while self.index < self.slice.len() && !SINGLE_QUOTE_ESCAPE[self.slice[self.index] as usize] {
                self.index += 1;
            }
            if self.index == self.slice.len() {
                return error(self, ErrorCode::EofWhileParsingString);
            }
            match self.slice[self.index] {
                b'\'' => {
                    self.index += 1;
                    return Ok(());
                }
                b'\\' => {
                    self.index += 1;
                    tri!(ignore_escape(self));
                }
                _ => {
                    return error(self, ErrorCode::ControlCharacterWhileParsingString);
                }
            }
        }
    }

    fn ignore_unquoted_str(&mut self) -> Result<()> {
        while self.index < self.slice.len() && !NO_QUOTE_ESCAPE[self.slice[self.index] as usize] {
            self.index += 1;
        }
        if self.index == self.slice.len() {
            return error(self, ErrorCode::EofWhileParsingString);
        }
        match self.slice[self.index] {
            b'\n' => {
                self.index += 1;
                Ok(())
            }
            _ => {
                error(self, ErrorCode::ControlCharacterWhileParsingString)
            }
        }
    }

    fn ignore_unquoted_key_str(&mut self) -> Result<()> {
        while self.index < self.slice.len() && !NO_QUOTE_KEY_ESCAPE[self.slice[self.index] as usize] {
            self.index += 1;
        }
        if self.index == self.slice.len() {
            return error(self, ErrorCode::EofWhileParsingString);
        }
        match self.slice[self.index] {
            b' ' | b'\t' | b'\n' | b'\r' => {
                self.index += 1;
                Ok(())
            }
            _ => {
                error(self, ErrorCode::ControlCharacterWhileParsingString)
            }
        }
    }

    fn decode_hex_escape(&mut self) -> Result<u16> {
        if self.index + 4 > self.slice.len() {
            self.index = self.slice.len();
            return error(self, ErrorCode::EofWhileParsingString);
        }

        let mut n = 0;
        for _ in 0..4 {
            let ch = decode_hex_val(self.slice[self.index]);
            self.index += 1;
            match ch {
                None => return error(self, ErrorCode::InvalidEscape),
                Some(val) => {
                    n = (n << 4) + val;
                }
            }
        }
        Ok(n)
    }

    #[cfg(feature = "raw_value")]
    fn begin_raw_buffering(&mut self) {
        self.raw_buffering_start_index = self.index;
    }

    #[cfg(feature = "raw_value")]
    fn end_raw_buffering<V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'a>,
    {
        let raw = &self.slice[self.raw_buffering_start_index..self.index];
        let raw = str::from_utf8(raw).unwrap();
        visitor.visit_map(BorrowedRawDeserializer {
            raw_value: Some(raw),
        })
    }

    const should_early_return_if_failed: bool = false;

    #[inline]
    #[cold]
    fn set_failed(&mut self, _failed: &mut bool) {
        self.slice = &self.slice[..self.index];
    }
}

//////////////////////////////////////////////////////////////////////////////

impl<'a> StrRead<'a> {
    /// Create a JSON input source to read from a UTF-8 string.
    pub fn new(s: &'a str) -> Self {
        StrRead {
            delegate: SliceRead::new(s.as_bytes()),
            #[cfg(feature = "raw_value")]
            data: s,
        }
    }
}

impl<'a> private::Sealed for StrRead<'a> {}

impl<'a> Read<'a> for StrRead<'a> {
    #[inline]
    fn next(&mut self) -> Result<Option<u8>> {
        self.delegate.next()
    }

    #[inline]
    fn peek(&mut self) -> Result<Option<u8>> {
        self.delegate.peek()
    }

    #[inline]
    fn peek_n(&mut self, bytes: usize) -> Result<&[u8]> {
        self.delegate.peek_n(bytes)
    }

    #[inline]
    fn discard(&mut self) {
        self.delegate.discard();
    }

    #[inline]
    fn discard_n(&mut self, bytes: usize) {
        self.delegate.discard_n(bytes);
    }

    fn position(&self) -> Position {
        self.delegate.position()
    }

    fn peek_position(&self) -> Position {
        self.delegate.peek_position()
    }

    fn byte_offset(&self) -> usize {
        self.delegate.byte_offset()
    }

    fn parse_double_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.delegate.parse_double_quoted_str_bytes(scratch, true, |_, bytes| {
            // The input is assumed to be valid UTF-8 and the \u-escapes are
            // checked along the way, so don't need to check here.
            Ok(unsafe { str::from_utf8_unchecked(bytes) })
        })
    }

    fn parse_single_quoted_str<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.delegate.parse_single_quoted_str_bytes(scratch, true, |_, bytes| {
            // The input is assumed to be valid UTF-8 and the \u-escapes are
            // checked along the way, so don't need to check here.
            Ok(unsafe { str::from_utf8_unchecked(bytes) })
        })
    }

    fn parse_unquoted_str<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.delegate.parse_unquoted_str_bytes(true, |_, bytes| {
            // The input is assumed to be valid UTF-8 and the \u-escapes are
            // checked along the way, so don't need to check here.
            Ok(unsafe { str::from_utf8_unchecked(bytes) })
        })
    }

    fn parse_unquoted_key_str<'s>(
        &'s mut self,
        _scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, str>> {
        self.delegate.parse_unquoted_key_str_bytes(true, |_, bytes| {
            // The input is assumed to be valid UTF-8 and the \u-escapes are
            // checked along the way, so don't need to check here.
            Ok(unsafe { str::from_utf8_unchecked(bytes) })
        })
    }

    fn parse_double_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.delegate.parse_double_quoted_str_raw(scratch)
    }

    fn parse_single_quoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.delegate.parse_single_quoted_str_raw(scratch)
    }

    fn parse_unquoted_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.delegate.parse_unquoted_str_raw(scratch)
    }

    fn parse_unquoted_key_str_raw<'s>(
        &'s mut self,
        scratch: &'s mut Vec<u8>,
    ) -> Result<Reference<'a, 's, [u8]>> {
        self.delegate.parse_unquoted_key_str_raw(scratch)
    }

    fn ignore_double_quoted_str(&mut self) -> Result<()> {
        self.delegate.ignore_double_quoted_str()
    }

    fn ignore_single_quoted_str(&mut self) -> Result<()> {
        self.delegate.ignore_single_quoted_str()
    }

    fn ignore_unquoted_str(&mut self) -> Result<()> {
        self.delegate.ignore_unquoted_str()
    }

    fn ignore_unquoted_key_str(&mut self) -> Result<()> {
        self.delegate.ignore_unquoted_key_str()
    }

    fn decode_hex_escape(&mut self) -> Result<u16> {
        self.delegate.decode_hex_escape()
    }

    #[cfg(feature = "raw_value")]
    fn begin_raw_buffering(&mut self) {
        self.delegate.begin_raw_buffering()
    }

    #[cfg(feature = "raw_value")]
    fn end_raw_buffering<V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'a>,
    {
        let raw = &self.data[self.delegate.raw_buffering_start_index..self.delegate.index];
        visitor.visit_map(BorrowedRawDeserializer {
            raw_value: Some(raw),
        })
    }

    const should_early_return_if_failed: bool = false;

    #[inline]
    #[cold]
    fn set_failed(&mut self, failed: &mut bool) {
        self.delegate.set_failed(failed);
    }
}

//////////////////////////////////////////////////////////////////////////////

/// Marker for whether StreamDeserializer can implement FusedIterator.
pub trait Fused: private::Sealed {}
impl<'a> Fused for SliceRead<'a> {}
impl<'a> Fused for StrRead<'a> {}

// Lookup tables of bytes that must be escaped. A value of true at index i means
// that byte i requires an escape sequence in the input.
static DOUBLE_QUOTE_ESCAPE: [bool; 256] = {
    const CT: bool = true; // control character \x00..=\x1F
    const QU: bool = true; // quote \x22
    const BS: bool = true; // backslash \x5C
    const __: bool = false; // allow unescaped
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 0
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 1
        __, __, QU, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, BS, __, __, __, // 5
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};
static SINGLE_QUOTE_ESCAPE: [bool; 256] = {
    const CT: bool = true; // control character \x00..=\x1F
    const AP: bool = true; // apostrophe \x27
    const BS: bool = true; // backslash \x5C
    const __: bool = false; // allow unescaped
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 0
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 1
        __, __, __, __, __, __, __, AP, __, __, __, __, __, __, __, __, // 2
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, BS, __, __, __, // 5
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};
static NO_QUOTE_ESCAPE: [bool; 256] = {
    const CT: bool = true; // control character \x00..=\x1F
    const __: bool = false; // allow unescaped
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        CT, CT, CT, CT, CT, CT, CT, CT, CT, __, CT, CT, CT, CT, CT, CT, // 0
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 1
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 5
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};
static NO_QUOTE_KEY_ESCAPE: [bool; 256] = {
    const CT: bool = true; // control character \x00..=\x1F
    const CM: bool = true; // comma \x2C
    const CO: bool = true; // colon \x3A
    const SB: bool = true; // square brackets \x5B and \x5D
    const CB: bool = true; // curly brackets \x7B and \x7D
    const __: bool = false; // allow unescaped
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 0
        CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 1
        __, __, __, __, __, __, __, __, __, __, __, __, CM, __, __, __, // 2
        __, __, __, __, __, __, __, __, __, __, CO, __, __, __, __, __, // 3
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, SB, __, SB, __, __, // 5
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, CB, __, CB, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};

fn next_or_eof<'de, R>(read: &mut R) -> Result<u8>
where
    R: ?Sized + Read<'de>,
{
    match tri!(read.next()) {
        Some(b) => Ok(b),
        None => error(read, ErrorCode::EofWhileParsingString),
    }
}

fn error<'de, R, T>(read: &R, reason: ErrorCode) -> Result<T>
where
    R: ?Sized + Read<'de>,
{
    let position = read.position();
    Err(Error::syntax(reason, position.line, position.column))
}

fn as_str<'de, 's, R: Read<'de>>(read: &R, slice: &'s [u8]) -> Result<&'s str> {
    str::from_utf8(slice).or_else(|_| error(read, ErrorCode::InvalidUnicodeCodePoint))
}

/// Parses a JSON escape sequence and appends it into the scratch space. Assumes
/// the previous byte read was a backslash.
fn parse_escape<'de, R: Read<'de>>(read: &mut R, scratch: &mut Vec<u8>) -> Result<()> {
    let ch = tri!(next_or_eof(read));

    match ch {
        b'"' => scratch.push(b'"'),
        b'\'' => scratch.push(b'\''),
        b'\\' => scratch.push(b'\\'),
        b'/' => scratch.push(b'/'),
        b'b' => scratch.push(b'\x08'),
        b'f' => scratch.push(b'\x0c'),
        b'n' => scratch.push(b'\n'),
        b'r' => scratch.push(b'\r'),
        b't' => scratch.push(b'\t'),
        b'u' => {
            let c = match tri!(read.decode_hex_escape()) {
                0xDC00..=0xDFFF => {
                    return error(read, ErrorCode::LoneLeadingSurrogateInHexEscape);
                }

                // Non-BMP characters are encoded as a sequence of
                // two hex escapes, representing UTF-16 surrogates.
                n1 @ 0xD800..=0xDBFF => {
                    if tri!(next_or_eof(read)) != b'\\' {
                        return error(read, ErrorCode::UnexpectedEndOfHexEscape);
                    }
                    if tri!(next_or_eof(read)) != b'u' {
                        return error(read, ErrorCode::UnexpectedEndOfHexEscape);
                    }

                    let n2 = tri!(read.decode_hex_escape());

                    if n2 < 0xDC00 || n2 > 0xDFFF {
                        return error(read, ErrorCode::LoneLeadingSurrogateInHexEscape);
                    }

                    let n = (((n1 - 0xD800) as u32) << 10 | (n2 - 0xDC00) as u32) + 0x1_0000;

                    match char::from_u32(n) {
                        Some(c) => c,
                        None => {
                            return error(read, ErrorCode::InvalidUnicodeCodePoint);
                        }
                    }
                }

                n => match char::from_u32(n as u32) {
                    Some(c) => c,
                    None => {
                        return error(read, ErrorCode::InvalidUnicodeCodePoint);
                    }
                },
            };

            scratch.extend_from_slice(c.encode_utf8(&mut [0_u8; 4]).as_bytes());
        }
        _ => {
            return error(read, ErrorCode::InvalidEscape);
        }
    }

    Ok(())
}

/// Parses a JSON escape sequence and discards the value. Assumes the previous
/// byte read was a backslash.
fn ignore_escape<'de, R>(read: &mut R) -> Result<()>
where
    R: ?Sized + Read<'de>,
{
    let ch = tri!(next_or_eof(read));

    match ch {
        b'"' | b'\'' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {}
        b'u' => {
            let n = match tri!(read.decode_hex_escape()) {
                0xDC00..=0xDFFF => {
                    return error(read, ErrorCode::LoneLeadingSurrogateInHexEscape);
                }

                // Non-BMP characters are encoded as a sequence of
                // two hex escapes, representing UTF-16 surrogates.
                n1 @ 0xD800..=0xDBFF => {
                    if tri!(next_or_eof(read)) != b'\\' {
                        return error(read, ErrorCode::UnexpectedEndOfHexEscape);
                    }
                    if tri!(next_or_eof(read)) != b'u' {
                        return error(read, ErrorCode::UnexpectedEndOfHexEscape);
                    }

                    let n2 = tri!(read.decode_hex_escape());

                    if n2 < 0xDC00 || n2 > 0xDFFF {
                        return error(read, ErrorCode::LoneLeadingSurrogateInHexEscape);
                    }

                    (((n1 - 0xD800) as u32) << 10 | (n2 - 0xDC00) as u32) + 0x1_0000
                }

                n => n as u32,
            };

            if char::from_u32(n).is_none() {
                return error(read, ErrorCode::InvalidUnicodeCodePoint);
            }
        }
        _ => {
            return error(read, ErrorCode::InvalidEscape);
        }
    }

    Ok(())
}

static HEX: [u8; 256] = {
    const __: u8 = 255; // not a hex digit
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 0
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 1
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
        00, 01, 02, 03, 04, 05, 06, 07, 08, 09, __, __, __, __, __, __, // 3
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 5
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};

fn decode_hex_val(val: u8) -> Option<u16> {
    let n = HEX[val as usize] as u16;
    if n == 255 {
        None
    } else {
        Some(n)
    }
}
