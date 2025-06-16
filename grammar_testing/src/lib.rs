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
        let opts = Options::default();
        Ok(opts.from_str(s.as_ref())?)
    }
}

#[derive(Deserialize, Serialize, PartialEq, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub enum Test {
    TestError {
        input: String,
        errors: Option<Vec<String>>,
    },
    TestSuccess {
        input: String,
        ast: Option<ASTRepr>,
    },
}

impl Test {
    pub fn to_ron_string(&self) -> Result<String, ron::Error> {
        let pretty_config = PrettyConfig::new()
            .escape_strings(false)
            .extensions(Extensions::IMPLICIT_SOME);
        ron::ser::to_string_pretty(self, pretty_config)
    }

    pub fn from_ron_str<S: AsRef<str>>(s: S) -> Result<Self, ron::Error> {
        let opts = Options::default();
        Ok(opts.from_str(s.as_ref())?)
    }

    /// Returns the value of the `pass` field when it is `Some`, otherwise
    /// returns whether the `errors` field is `None` or it's inner value is empty.
    pub fn should_pass(&self) -> bool {
        matches!(self, Test::TestSuccess{..})
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
#[serde(transparent)]
pub struct Tests(Vec<Test>);

impl Tests {
    pub fn to_ron_string(&self) -> Result<String, ron::Error> {
        let pretty_config = PrettyConfig::new()
            .escape_strings(false)
            .extensions(Extensions::IMPLICIT_SOME);
        ron::ser::to_string_pretty(self, pretty_config)
    }

    pub fn from_ron_str<S: AsRef<str>>(s: S) -> Result<Self, ron::Error> {
        let opts = Options::default();
        Ok(opts.from_str(s.as_ref())?)
    }
}

impl std::ops::Deref for Tests {
    type Target = Vec<Test>;

    fn deref(&self) -> &Vec<Test> {
        &self.0
    }
}

impl IntoIterator for Tests {
    type Item = Test;
    type IntoIter = std::vec::IntoIter<Test>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::{ASTRepr, Test, Tests};

    #[test]
    fn grmtest_input_only() {
        let input = r#"
            #![enable(implicit_some)]
            TestSuccess(input: "a")
        "#;
        let x: Test = ron::from_str(&input).unwrap();
        assert_eq!(
            x,
            Test::TestSuccess {
                input: "a".to_string(),
                ast: None,
            }
        );
    }

    #[test]
    fn grmtest_input_ast() {
        let input = r#"
        #![enable(implicit_some)]
        TestSuccess(input: "a", ast: ("start", [("character", "a")]))
        "#;
        let x: Test = Test::from_ron_str(&input).unwrap();
        assert_eq!(
            x,
            Test::TestSuccess {
                input: "a".to_string(),
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
        #![enable(implicit_some)]
        [
            // First 2 are equivalent
            TestSuccess(input: "a"),
            TestSuccess(input: "a", ast: None),

            TestSuccess(input: "b"),
            // The last two are equivalent
            TestSuccess(input: "a", ast: ("start", [("character", "a")])),
            TestSuccess(input: "a", ast: Some(("start", [("character", "a")]))),
        ]
        "#;
        let xs = Tests::from_ron_str(&input).unwrap();
        for x in &*xs {
            eprintln!("{:?}", x);
            assert!(x.should_pass());
        }
        let first = Test::TestSuccess {
            input: "a".to_string(),
            ast: None,
        };
        let last = Test::TestSuccess {
            input: "a".to_string(),
            ast: Some(ASTRepr::Nonterm(
                "start".to_string(),
                vec![ASTRepr::Term("character".to_string(), "a".to_string())],
            )),
        };
        assert_eq!(
            last.to_ron_string().unwrap(),
            r#"#![enable(implicit_some)]
TestSuccess(
    input: "a",
    ast: ("start", [
        ("character", "a"),
    ]),
)"#
        );
        assert_eq!(
            xs,
            Tests(vec![
                first.clone(),
                first,
                Test::TestSuccess {
                    input: "b".to_string(),
                    ast: None,
                },
                last.clone(),
                last
            ])
        );
    }

    #[test]
    fn grmtest_many_fails() {
        let input = r#"
        #![enable(implicit_some)]
        [
            TestError(input: "abc"),
            TestError(input: "abc", errors: ["some error"]),
        ]
        "#;
        let xs = Tests::from_ron_str(&input).unwrap();
        for x in &*xs {
            assert!(!x.should_pass())
        }
        assert_eq!(
            xs,
            Tests(vec![
                Test::TestError {
                    input: "abc".to_string(),
                    errors: None,
                },
                Test::TestError {
                    input: "abc".to_string(),
                    errors: Some(vec!["some error".to_string()]),
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
