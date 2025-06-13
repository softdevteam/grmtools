use ron::Options;
use ron::extensions::Extensions;
use ron::ser::PrettyConfig;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
#[serde(untagged)]
pub enum ASTRepr {
    Term(String, String),
    Nonterm(String, Vec<ASTRepr>),
}

impl ASTRepr {
    pub fn to_ron_string(&self) -> Result<String, ron::Error> {
        let pretty_config = PrettyConfig::new()
            .escape_strings(false)
            .extensions(Extensions::IMPLICIT_SOME);
        ron::ser::to_string_pretty(self, pretty_config)
    }

    pub fn from_ron_str<S: AsRef<str>>(s: S) -> Result<Self, ron::Error> {
        let opts = Options::default().with_default_extension(Extensions::IMPLICIT_SOME);
        Ok(opts.from_str(s.as_ref())?)
    }
}

#[derive(Deserialize, Serialize, PartialEq, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct GrammarTest {
    input: String,
    #[serde(default)]
    ast: Option<ASTRepr>,
    // Ideally we would derive this value from `errors`` being empty/none but doing that
    // within serialization is a painful exercise, so use the accessor `should_pass`.
    #[serde(default)]
    pass: Option<bool>,
    #[serde(default)]
    errors: Option<Vec<String>>,
}

impl GrammarTest {
    pub fn to_ron_string(&self) -> Result<String, ron::Error> {
        let pretty_config = PrettyConfig::new()
            .escape_strings(false)
            .extensions(Extensions::IMPLICIT_SOME);
        ron::ser::to_string_pretty(self, pretty_config)
    }

    pub fn from_ron_str<S: AsRef<str>>(s: S) -> Result<Self, ron::Error> {
        let opts = Options::default().with_default_extension(Extensions::IMPLICIT_SOME);
        Ok(opts.from_str(s.as_ref())?)
    }

    /// Returns the value of the `pass` field when it is `Some`, otherwise
    /// returns whether the `errors` field is `None` or it's inner value is empty.
    pub fn should_pass(&self) -> bool {
        self.pass
            .unwrap_or(self.errors.is_none() || self.errors.as_ref().unwrap().is_empty())
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
#[serde(transparent)]
pub struct GrammarTests(Vec<GrammarTest>);

impl GrammarTests {
    pub fn to_ron_string(&self) -> Result<String, ron::Error> {
        let pretty_config = PrettyConfig::new()
            .escape_strings(false)
            .extensions(Extensions::IMPLICIT_SOME);
        ron::ser::to_string_pretty(self, pretty_config)
    }

    pub fn from_ron_str<S: AsRef<str>>(s: S) -> Result<Self, ron::Error> {
        let opts = Options::default().with_default_extension(Extensions::IMPLICIT_SOME);
        Ok(opts.from_str(s.as_ref())?)
    }
}

impl std::ops::Deref for GrammarTests {
    type Target = Vec<GrammarTest>;

    fn deref(&self) -> &Vec<GrammarTest> {
        &self.0
    }
}

impl IntoIterator for GrammarTests {
    type Item = GrammarTest;
    type IntoIter = std::vec::IntoIter<GrammarTest>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::{ASTRepr, GrammarTest, GrammarTests};

    #[test]
    fn grmtest_input_only() {
        let input = r#"
            (input: "a")
        "#;
        let x: GrammarTest = ron::from_str(&input).unwrap();
        assert_eq!(
            x,
            GrammarTest {
                input: "a".to_string(),
                pass: None,
                errors: None,
                ast: None
            }
        );
    }

    #[test]
    fn grmtest_input_ast() {
        let input = r#"(input: "a", ast: Some(("start", [("character", "a")])))"#;
        let x: GrammarTest = ron::from_str(&input).unwrap();
        assert_eq!(
            x,
            GrammarTest {
                input: "a".to_string(),
                pass: None,
                errors: None,
                ast: Some(ASTRepr::Nonterm(
                    "start".to_string(),
                    vec![ASTRepr::Term("character".to_string(), "a".to_string())]
                ))
            }
        );
    }

    #[test]
    fn grmtest_many() {
        let input = r#"
        [
            GrammarTest(input: "a"),
            (input: "a"),
            (input: "b"),
            (input: "a", ast: ("start", [("character", "a")])),
        ]
        "#;
        let xs = GrammarTests::from_ron_str(&input).unwrap();
        for x in &*xs {
            assert!(x.should_pass());
        }
        let first = GrammarTest {
            input: "a".to_string(),
            pass: None,
            errors: None,
            ast: None,
        };
        assert_eq!(
            xs,
            GrammarTests(vec![
                first.clone(),
                first,
                GrammarTest {
                    input: "b".to_string(),
                    pass: None,
                    errors: None,
                    ast: None
                },
                GrammarTest {
                    input: "a".to_string(),
                    pass: None,
                    errors: None,
                    ast: Some(ASTRepr::Nonterm(
                        "start".to_string(),
                        vec![ASTRepr::Term("character".to_string(), "a".to_string())]
                    ))
                },
            ])
        );
    }

    #[test]
    fn grmtest_many_fails() {
        let input = r#"
        [
            (input: "abc", pass: false),
            (input: "abc", errors: ["some error"]),
        ]
        "#;
        let xs = GrammarTests::from_ron_str(&input).unwrap();
        for x in &*xs {
            assert!(!x.should_pass())
        }
        assert_eq!(
            xs,
            GrammarTests(vec![
                GrammarTest {
                    input: "abc".to_string(),
                    pass: Some(false),
                    errors: None,
                    ast: None
                },
                GrammarTest {
                    input: "abc".to_string(),
                    pass: None,
                    errors: Some(vec!["some error".to_string()]),
                    ast: None
                }
            ])
        );
    }

    #[test]
    fn astrepr_esc_raw_string() {
        let x = ASTRepr::from_ron_str(r##"("start", [("\"", r#"""#)])"##).unwrap();
        assert_eq!(
            x,
            ASTRepr::Nonterm(
                "start".to_string(),
                vec![ASTRepr::Term(r#"""#.to_string(), "\"".to_string())]
            )
        );
    }
}
