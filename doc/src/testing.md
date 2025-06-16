# Testing (experimental)

grmtools testing facilities are currently experimental, under development, and subject to change.
Not all features described in this are section currently implemented (in fact most are incomplete).
Currently this text primarily serves as a design document for testing features and feedback is welcome.

## Testing raw input

### Example lexer
🚀
```lex
%%
[a-z] "character"
\" '"'
[ \n\t] ;
```


### Example grammar
🚀 
```yacc
%grmtools{
    yacckind: Original(NoAction),
    test_files: "input*.txt"
}

%%
start: "character";
```


### Input text
🚀 
Contents specified via `test_files`:
```text
a
```

## Specifying multiple globs
🚧
It would be nice if you could specify multiple globs:
```
test_files: ["*.txt", "*.grmtest"],
```

## Testing with serialized formats

🚧
When specifying `test_files` the `grmtest` extension is treated specially.

### Example Grammar for serializated test data.
🚧
By specifying the `grmtest` extension for the `test_files` value you enable serialized
test data including output expectations for abstract syntax trees and error text.

```yacc
    test_files "*.grmtest"
```


### Serialized test input
🚧
The `grmtest` file deserializes to a struct with many optional fields.
It is a [`ron`](https://crates.io/crates/ron) using the [Implicit Some](https://github.com/ron-rs/ron/blob/master/docs/extensions.md#implicit_some) extension.
This allows you to omit most of the values, but has the downside that typos may fall back to default values.

#### Fields 
🚧
* `input: String` field is required, and specifies the input to the parser.
* `pass: bool` defaults to None, only Some if explicitly specified.
* `ast: Option<grammar_testing::ASTRepr>` if present specifies the expected output see [Serializing with nimbleparse] for generating ast output.
* `errors: Option<Vec<String>>` if present specifies the expected error text, without error recovery.

#### Methods
* `should_pass(&self)` Returns the value of the `pass` field when it is `Some` otherwise returns whether the `errors` field is `None` or it's inner value is empty.

#### Example .grmtest file
🚧
```grmtest
(
   input: "a",
   ast: ("start", [
        ("character", "a"),
    ]),
)
```


### Serializing with nimbleparse

#### ast output
* 🚀 Using the `-s` option to nimbleparse to produce a serialized ast.
* 🚧 `-s ast`

```console
$ echo "a" | nimbleparse -s testing.l testing.y -
("start", [
    ("character", "a"),
])
```


#### grmtest output
🚧 `-s grmtest` 

```console
$ echo "a" | nimbleparse -s grmtest testing.l testing.y -
(
   input: "a\n",
   ast: ("start", [
    ("character", "a"),
    ])
)
```


## Testing multiple inputs
🚧 
Specify a plural extension `test_files: "*.grmtests` to allow a vector of test inputs.

```grmtests
[
    (input: "a"),
    (input: "b"),
    (input: "a", ast: ("start", [("character", "a")])),
    (input: "abc", pass: false),
]
```


## Escaping and raw strings

Because grammars often contain quotation marks, it is convenient to support rusts `raw string` format.
By default the serializer outputs raw strings.

🚀
```grmtest
$ echo "\"" | ./target/debug/nimbleparse -s testing.{l,y} -
("start", [
    (r#"""#, r#"""#),
])
```

🚧
```
[
  // Raw strings, and escaped characters are usable interchangably.
  ( input: r#"""#, ast:("start", [(r#"""#, "\"")])),
  ( input: "\"", ast:("start", [("\"", r#"""#)])),
]
```


## Running tests
🚀

If using build.rs/`CTParserBuilder` just cargo build.
If no arguments are specified `nimbleparse testing.l testing.y` then if `test_files` is specified it will be used by default.

## Manual Lexer limitations
🚧

Currently grmtools testing facilities are limited to being used with the combination of `lrlex`,
and `lrpar`.  There currently isn't any mechanism in place for testing when using a manual lexer.
Doing so requires using unstable/hidden/undocumented aspects of the API.