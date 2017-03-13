use regex::Regex;

pub struct Rule {
    /// The ID that tokens created against this rule will be given. It is initially given a
    /// guaranteed unique value; that value can be overridden by clients.
    pub tok_id: usize,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

