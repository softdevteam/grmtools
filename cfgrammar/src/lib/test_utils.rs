use crate::Span;

pub trait FindSpan {
    fn find_span(&self, s: &str) -> Span;
}

impl FindSpan for &'_ str {
    #[track_caller]
    fn find_span(&self, s: &str) -> Span {
        let start_pos = self.find(s).unwrap();
        Span::new(start_pos, start_pos + s.len())
    }
}
