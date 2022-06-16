pub struct NewlineToLineColCache {
    newlines: Vec<usize>,
    trailing_bytes: usize,
}

impl Default for NewlineToLineColCache {
    fn default() -> NewlineToLineColCache {
        NewlineToLineColCache {
            newlines: vec![0],
            trailing_bytes: 0,
        }
    }
}

impl NewlineToLineColCache {
    /// Feed more input into the cache, calculating newlines data from it.
    /// The `src` string given is treated as was concatenated with the previous calls
    /// to `feed`.
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

    /// Convert a byte offset in the input to a logical line number. Returns None if
    /// the byte offset exceeds the known input length.
    pub fn byte_to_line_num(&self, byte: usize) -> Option<usize> {
        if byte > self.input_length() {
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

    /// Total known input length
    fn input_length(&self) -> usize {
        self.newlines.last().unwrap() + self.trailing_bytes
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

    /// Given a `src` string, which should have strings previously passed to `feed` concatenated together.
    /// Convert the given `byte` offset in the input to logical line and column numbers.
    /// Returns None if the byte offset exceeds the known input length, or the src and input length differ.
    pub fn byte_to_line_and_col(&self, src: &str, byte: usize) -> Option<(usize, usize)> {
        if byte > self.input_length() || src.len() != self.input_length() {
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
}

#[cfg(test)]
mod tests {
    use super::NewlineToLineColCache;

    fn newline_test_helper(feed: &[&str], tests: &[(usize, usize)]) {
        let mut cache = NewlineToLineColCache::default();
        let mut full_string = String::new();
        for f in feed {
            cache.feed(f);
            full_string.push_str(f);
        }

        let mut src_pos = 0;
        let mut result = Vec::new();
        for f in feed {
            for (offset, _) in f.char_indices() {
                let line_col = cache.byte_to_line_and_col(full_string.as_str(), offset + src_pos);
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
        let mut cache = NewlineToLineColCache::default();

        // Byte exceeds input length
        cache.feed("1");
        assert_eq!(None, cache.byte_to_line_num(2));
        assert_eq!(None, cache.byte_to_line_and_col("1", 2));
        cache.feed("\n23");
        assert_eq!(None, cache.byte_to_line_num(5));
        assert_eq!(None, cache.byte_to_line_and_col("1\n23", 5));

        // Byte valid, but src.len() exceeds input length.
        assert_eq!(None, cache.byte_to_line_and_col("1\n234", 1));
    }
}
