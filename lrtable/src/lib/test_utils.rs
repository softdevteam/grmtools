pub use cfgrammar::header::{Header, Value};
pub use cfgrammar::markmap::{Entry, MergeBehavior};
pub use cfgrammar::Location;

#[macro_export]
#[cfg(test)]
macro_rules! header_for_yacckind {
    ($yk:expr) => {{
        let mut header = Header::new();
        match header.entry("yacckind".to_string()) {
            Entry::Occupied(_) => unreachable!("Header should be empty"),
            Entry::Vacant(v) => {
                let mut o = v.insert_entry((
                    Location::Other("Testsuite".to_string()),
                    Value::try_from($yk).unwrap(),
                ));
                o.mark_required();
                o.set_merge_behavior(MergeBehavior::Ours);
            }
        };
        header
    }};
}

pub use header_for_yacckind;
