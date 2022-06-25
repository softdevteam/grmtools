use crate::Span;
use std::str::FromStr;

/// Cache newlines from an input. These can be used to turn UTF-8 byte offsets into human-friendly
/// line numbers (and vice versa) without having to store the full input. The cache stores only
/// newline positions, and not the actual user input; the cache can only be filled incrementally
/// using the [NewlineCache::feed] method.
///
/// It is easy to to intermix bytes and human-friendly line numbers so `NewlineCache` uses the
/// following terminology:
///   * `byte` and `byte`s: a UTF-8 byte offset.
///   * `line_byte` and `line_byte`s: the UTF-8 byte offset of a line start or end.
///   * `line_num`: a human-friendly line number.
///   * `col_num`: a human-friendly column number.
pub struct NewlineCache {
    newlines: Vec<usize>,
    trailing_bytes: usize,
}

impl NewlineCache {
    /// Create an empty `NewlineCache`.
    pub fn new() -> Self {
        Self {
            newlines: vec![0],
            trailing_bytes: 0,
        }
    }

    /// Feed further input into the cache. This input is considered to be a direct continuation of
    /// any previous input fed into the cache. Feeding new data thus appends to the cache. If the
    /// previous input contained a partial line (i.e. did not end in a newline), then the new input
    /// (unless it starts with a newline) will be considered to be a continuation of that partial
    /// line.
    pub fn feed(&mut self, src: &str) {
        let start_pos = self.newlines.last().unwrap() + self.trailing_bytes;
        self.newlines
            .extend(src.char_indices().filter_map(|c| match c {
                (offset, '\n') => {
                    self.trailing_bytes = 0;
                    Some(start_pos + offset + 1)
                }
                (_, c) => {
                    self.trailing_bytes += c.len_utf8();
                    None
                }
            }));
    }

    /// Number of bytes fed into the newline cache.
    fn feed_len(&self) -> usize {
        self.newlines.last().unwrap() + self.trailing_bytes
    }

    /// Convert a byte offset in the input to a logical line number (i.e. a "human friendly" line
    /// number, starting from 1). Returns None if the byte offset exceeds the known input length.
    pub fn byte_to_line_num(&self, byte: usize) -> Option<usize> {
        if byte > self.feed_len() {
            return None;
        }

        let last_newline = self.newlines.last().unwrap();
        let last_byte = last_newline + self.trailing_bytes;

        if byte < last_byte && byte > *last_newline {
            Some(self.newlines.len())
        } else {
            let (line_m1, _) = self
                .newlines
                .iter()
                .enumerate()
                .rev()
                .find(|&(_, &line_off)| line_off <= byte)
                .unwrap();
            Some(line_m1 + 1)
        }
    }

    /// Convert a logical line number into a byte offset.
    /// Returns None if the line number exceeds the known line count,
    /// or the input or the line_num is zero.
    fn line_num_to_byte(&self, line_num: usize) -> Option<usize> {
        if line_num > self.newlines.len() || line_num == 0 {
            None
        } else {
            Some(self.newlines[line_num - 1])
        }
    }

    /// Convert a byte offset in the input to the byte offset of the beginning of its line.
    /// Returns None if the byte offset exceeds the known input length.
    pub fn byte_to_line_byte(&self, byte: usize) -> Option<usize> {
        self.byte_to_line_num(byte)
            .and_then(|line_num| self.line_num_to_byte(line_num))
    }

    /// A convenience method to return the logical line and logical column number of a byte. This
    /// requires passing a `&str` which *must* be equivalent to the string(s) passed to `feed`:
    /// if not, nondeterminstic results, including panics, are possible.
    //
    /// # Panics
    ///
    /// May panic if `src` is different than the string(s) passed to `feed` (or might not panic and
    /// return non-deterministic results).
    pub fn byte_to_line_num_and_col_num(&self, src: &str, byte: usize) -> Option<(usize, usize)> {
        if byte > self.feed_len() || src.len() != self.feed_len() {
            return None;
        }

        self.byte_to_line_num(byte).map(|line_num| {
            if byte == src.len() {
                let line_byte = *self.newlines.last().unwrap();
                return (self.newlines.len(), src[line_byte..].chars().count() + 1);
            }

            let line_byte = self.line_num_to_byte(line_num).unwrap();
            let mut column = 0;
            let mut skip_char = None;

            for (c_off, c) in src[line_byte..].char_indices() {
                if Some(c) != skip_char {
                    column += 1;
                    skip_char = None;
                }
                if c == '\r' {
                    skip_char = Some('\n');
                }
                if c_off == byte - line_byte {
                    break;
                }
            }
            (line_num, column)
        })
    }

    /// Return the (start byte, end byte) of the lines containing `span`. This will always cover
    /// at least 1 logical line.
    pub fn span_line_bytes(&self, span: Span) -> (usize, usize) {
        let (st, st_line) = match self.newlines.binary_search(&span.start()) {
            Ok(j) => (self.newlines[j], j + 1),
            Err(j) => (self.newlines[j - 1], j),
        };
        let en = match self.newlines[st_line..].binary_search(&span.end()) {
            Ok(j) if st_line + j == self.newlines.len() - st_line => {
                self.newlines.last().unwrap() + self.trailing_bytes
            }
            Ok(j) => self.newlines[st_line + j + 1] - 1,
            Err(j) if st_line + j == self.newlines.len() => {
                self.newlines.last().unwrap() + self.trailing_bytes
            }
            Err(j) => self.newlines[st_line + j] - 1,
        };
        (st, en)
    }
}

impl FromStr for NewlineCache {
    type Err = ();

    /// Construct a `NewlineCache` directly from a `&str`. This is equivalent to creating a blank
    /// `NewlineCache` and [Self::feed()]ing the string directly in.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut x = Self::new();
        x.feed(s);
        Ok(x)
    }
}

impl<'a> FromIterator<&'a str> for NewlineCache {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a str>,
    {
        let mut nlcache = NewlineCache::new();
        for s in iter.into_iter() {
            nlcache.feed(s)
        }
        nlcache
    }
}

#[cfg(test)]
mod tests {
    use super::NewlineCache;
    use crate::Span;
    use std::str::FromStr;

    fn newline_test_helper(feed: &[&str], tests: &[(usize, usize)]) {
        let cache: NewlineCache = feed.iter().copied().collect();
        let full_string = feed.concat();

        let mut src_pos = 0;
        let mut result = Vec::new();
        for f in feed {
            for (offset, _) in f.char_indices() {
                let line_col =
                    cache.byte_to_line_num_and_col_num(full_string.as_str(), offset + src_pos);
                result.push(line_col.unwrap())
            }
            src_pos += f.len();
        }
        assert_eq!(result, tests)
    }

    #[test]
    fn newline_cache_various() {
        let abc = &[(1, 1), (1, 2), (1, 3)];
        newline_test_helper(&["a", "b", "c"], abc);
        newline_test_helper(&["abc"], abc);
        newline_test_helper(&["ab", "c"], abc);

        let ab = &[(1, 1), (1, 2), (2, 1)];
        newline_test_helper(&["a\n", "b"], ab);
        newline_test_helper(&["a", "\nb"], ab);

        let cr = &[(1, 1), (1, 2), (1, 2), (2, 1)];
        newline_test_helper(&["a\r\n", "b"], cr);
        newline_test_helper(&["a", "\r\nb"], cr);
        newline_test_helper(&["a\r", "\nb"], cr);

        newline_test_helper(&["\r\n\n"], &[(1, 1), (1, 1), (2, 1)]);

        let suits = &[(1, 1), (1, 2), (1, 3), (1, 4)];
        newline_test_helper(&["", "♠♥♦♣"], suits);
        newline_test_helper(&["♠", "♥♦♣"], suits);
        newline_test_helper(&["♠♥", "♦♣"], suits);
        newline_test_helper(&["♠♥♦", "♣"], suits);
        newline_test_helper(&["♠♥♦♣", ""], suits);

        let suits_nl = &[(1, 1), (1, 2), (1, 3), (2, 1), (2, 2)];
        newline_test_helper(&["", "♠♥\n♦♣"], suits_nl);
        newline_test_helper(&["♠", "♥\n♦♣"], suits_nl);
        newline_test_helper(&["♠♥", "\n♦♣"], suits_nl);
        newline_test_helper(&["♠♥\n", "♦♣"], suits_nl);
        newline_test_helper(&["♠♥\n♦", "♣"], suits_nl);
        newline_test_helper(&["♠♥\n♦♣", ""], suits_nl);

        #[rustfmt::skip]
        let multi_line = &[
            (1, 1), (1, 2), (2, 1), (2, 2),
            (3, 1), (3, 2), (4, 1), (4, 2),
            (5, 1), (5, 2), (6, 1), (6, 2),
        ];
        newline_test_helper(&["", "1\n2\n3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4\n5\n6\n", ""], multi_line);

        newline_test_helper(&["1", "\n2\n3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n", "2\n3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2", "\n3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n", "3\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3", "\n4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n", "4\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4", "\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4\n", "5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4\n5", "\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n3\n4\n5\n", "6\n"], multi_line);
        newline_test_helper(&["1\n2\n", "3\n4\n", "5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n", "3\n4", "\n5\n6\n"], multi_line);
        newline_test_helper(&["1\n2\n", "", "3\n4", "", "\n5\n6\n"], multi_line);

        newline_test_helper(&["", "", ""], &[]);
        newline_test_helper(&["", ""], &[]);
        newline_test_helper(&[""], &[]);
        newline_test_helper(&["", "", "", "a"], &[(1, 1)]);
        newline_test_helper(&["", "", "a"], &[(1, 1)]);
        newline_test_helper(&["", "a"], &[(1, 1)]);

        // Positive tests for the string we'll use for negative tests.
        newline_test_helper(&["1", "\n23"], &[(1, 1), (1, 2), (2, 1), (2, 2)]);
    }

    #[test]
    fn newline_cache_negative() {
        let mut cache = NewlineCache::new();

        // Byte exceeds input length
        cache.feed("1");
        assert_eq!(None, cache.byte_to_line_num(2));
        assert_eq!(None, cache.byte_to_line_num_and_col_num("1", 2));
        cache.feed("\n23");
        assert_eq!(None, cache.byte_to_line_num(5));
        assert_eq!(None, cache.byte_to_line_num_and_col_num("1\n23", 5));

        // Byte valid, but src.len() exceeds input length.
        assert_eq!(None, cache.byte_to_line_num_and_col_num("1\n234", 1));
    }

    #[test]
    fn spanlines_str() {
        fn span_line_eq(input: &str, byte_st: usize, byte_en: usize, substr: &str) {
            let nlc = NewlineCache::from_str(input).unwrap();
            let (lines_st, lines_en) = nlc.span_line_bytes(Span::new(byte_st, byte_en));
            assert_eq!(&input[lines_st..lines_en], substr);
        }

        span_line_eq("a b c", 2, 3, "a b c");
        span_line_eq("a b c", 4, 5, "a b c");

        span_line_eq("a b c\n", 2, 3, "a b c");
        span_line_eq("a b c\n", 4, 5, "a b c");
        span_line_eq("a b c\n", 5, 5, "a b c");
        span_line_eq("a b c\n", 6, 6, "");

        span_line_eq(" a\nb\n  c d", 1, 2, " a");
        span_line_eq(" a\nb\n  c d", 3, 4, "b");
        span_line_eq(" a\nb\n  c d", 7, 8, "  c d");
        span_line_eq(" a\nb\n  c d", 9, 10, "  c d");

        span_line_eq("ab\n", 2, 3, "ab\n");
        span_line_eq("ab\ncd", 2, 3, "ab\ncd");
        span_line_eq("ab\ncd\nef", 2, 3, "ab\ncd");

        let s = "\na\na a\na a a\na a a a";
        span_line_eq(s, 0, 0, "");
        span_line_eq(s, 0, 2, "\na");
        span_line_eq(s, 0, 4, "\na\na a");
        span_line_eq(s, 0, 7, "\na\na a\na a a");
        span_line_eq(s, 4, 7, "a a\na a a");

        span_line_eq(" a\n❤ b", 1, 2, " a");
        span_line_eq(" a\n❤ b", 3, 4, "❤ b");
        span_line_eq(" a\n❤ b", 5, 6, "❤ b");
    }
}
