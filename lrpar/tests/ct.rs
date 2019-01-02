// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

extern crate lrpar;
extern crate tempfile;

use std::{
    fs::{self, create_dir, read_dir, remove_dir_all, remove_file},
    panic::{catch_unwind, resume_unwind, UnwindSafe},
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    thread,
    time::Duration
};

use self::tempfile::TempDir;

// How long to wait, in ms, when spinning for DUMMY_SPINLOCK to become false?
const SPIN_WAIT: u64 = 250;

// This is ugly, but effective: compiling a dummy project is slow because we have to compile
// dependencies. We thus cheat and try to only create one dummy project, which we continually
// refresh, leaving only its target/ directory behind. However, there are two complicating factors:
// first, only one test can use DUMMY_TESTDIR at a time; second, static items don't call Drop (so
// we have to manually garbage collect DUMMY_TESTDIR). We might like to solve #1 with a normal Rust
// Mutex, but those become poisoned when a panic happens, and if a test fails, we'd like other
// tests to be able to continue working. So, we solve #1 with a hand-crafted spin-lock
// DUMMY_SPINLOCK and #2 with a count DUMMY_WAITING. Note that it is possible for DUMMY_TESTDIR to
// be dropped and recreated multiple times, because it might look like there are no remaining tests
// wanting to use it, only for that to change later: we could only change by adding some sort of
// brittle "how many DUMMY_TESTDIR-using tests have yet to run?" count. This dynamic approach,
// despite its limitations and complexity, seems a better bet.
static mut DUMMY_TESTDIR: Option<TempDir> = None;
static DUMMY_SPINLOCK: AtomicBool = AtomicBool::new(false);
static DUMMY_WAITING: AtomicUsize = AtomicUsize::new(0);

/// Run the function `f` with a guaranteed fresh dummy test directory that no-one else is using.
fn run_in_dummy<F, T>(f: F) -> T
where
    F: FnOnce(&TempDir) -> T,
    F: Send + UnwindSafe + 'static,
    T: Send + 'static
{
    // First of all, we make sure that, if another thread has populated DUMMY_TESTDIR, that it
    // won't be emptied.
    DUMMY_WAITING.fetch_add(1, Ordering::SeqCst);
    // Grab the spinlock.
    loop {
        if !DUMMY_SPINLOCK.swap(true, Ordering::SeqCst) {
            break;
        }
        thread::sleep(Duration::from_millis(SPIN_WAIT));
    }
    // Create DUMMY_TESTDIR if it doesn't exist.
    let dtd = unsafe {
        if DUMMY_TESTDIR.is_none() {
            DUMMY_TESTDIR = Some(TempDir::new().unwrap());
        }
        DUMMY_TESTDIR.as_ref().unwrap()
    };
    reset_dummy(dtd);

    let r = catch_unwind(|| f(dtd));

    // If we're the last thread to be waiting on DUMMY_TESTDIR, then drop it.
    if DUMMY_WAITING.fetch_sub(1, Ordering::SeqCst) == 1 {
        unsafe {
            DUMMY_TESTDIR = None;
        }
    }
    DUMMY_SPINLOCK.store(false, Ordering::SeqCst);
    match r {
        Ok(r) => r,
        Err(e) => resume_unwind(e)
    }
}

fn reset_dummy(tdir: &TempDir) {
    // We want to wipe everything in the test directory *except* the target/ directory, as keeping
    // that around saves us having to recompile dependencies over and over again.
    for e in read_dir(PathBuf::from(tdir.as_ref())).unwrap() {
        let e = e.unwrap();
        if e.path().is_dir() {
            if e.path().file_name().unwrap().to_str().unwrap() != "target" {
                remove_dir_all(e.path()).unwrap();
            }
        } else {
            remove_file(e.path()).unwrap();
        }
    }

    // Create the src/ directory
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("src");
    create_dir(&p).unwrap();

    // Write Cargo.toml
    p = PathBuf::from(tdir.as_ref());
    p.push("Cargo.toml");
    let mut repop = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    repop.push("..");
    fs::write(
        p,
        &format!(
            "[package]
name = \"dummytest\"
version = \"0.1.0\"
authors = [\"test\"]

[build-dependencies]
lrlex = {{ path = \"{repop}/lrlex\" }}
lrpar = {{ path = \"{repop}/lrpar\" }}

[dependencies]
cfgrammar = {{ path = \"{repop}/cfgrammar\" }}
lrlex = {{ path = \"{repop}/lrlex\" }}
lrpar = {{ path = \"{repop}/lrpar\" }}
",
            repop = repop.to_str().unwrap()
        )
    )
    .unwrap();
}

fn init_simple(tdir: &TempDir) {
    // Write build.rs
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("build.rs");
    fs::write(
        p,
        "
extern crate lrlex;
extern crate lrpar;

use lrpar::CTParserBuilder;

fn main() -> Result<(), Box<std::error::Error>> {
    CTParserBuilder::new()
        .process_file_in_src(\"grm.y\")?;
    Ok(())
}"
    )
    .unwrap();

    // Write src/main.rs
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("src");
    p.push("main.rs");
    fs::write(
        p,
        "
extern crate cfgrammar;
#[macro_use] extern crate lrpar;

lrpar_mod!(grm_y);

fn main() {{
}}
"
    )
    .unwrap();
}

fn init_calc(tdir: &TempDir, actionkind: &str, main: &str) {
    // Write build.rs
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("build.rs");
    fs::write(
        p,
        &format!(
            "
extern crate lrlex;
extern crate lrpar;

use lrlex::LexerBuilder;
use lrpar::{{CTParserBuilder, ActionKind}};

fn main() -> Result<(), Box<std::error::Error>> {{
    let lex_rule_ids_map = CTParserBuilder::new()
        .action_kind({})
        .process_file_in_src(\"calc.y\")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src(\"calc.l\")?;
    Ok(())
}}",
            actionkind
        )
    )
    .unwrap();

    // Write src/calc.y
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("src");
    p.push("calc.y");
    fs::write(
        p,
        "%start Expr
%type Result<u64, ()>
%avoid_insert 'INT'
%%
Expr: Term '+' Expr { Ok($1? + $3?) }
    | Term { $1 }
    ;

Term: Factor '*' Term { Ok($1? * $3?) }
    | Factor { $1 }
    ;

Factor: '(' Expr ')' { $2 }
      | 'INT' {
            let l = $1.map_err(|_| ())?;
            match $lexer.lexeme_str(&l).parse::<u64>() {
                Ok(v) => Ok(v),
                Err(_) => {
                    let (_, col) = $lexer.offset_line_col(l.start());
                    eprintln!(\"Error at column {}: '{}' cannot be represented as a u64\",
                              col,
                              $lexer.lexeme_str(&l));
                    Err(())
                }
            }
        }
      ;"
    )
    .unwrap();

    // Write src/calc.l
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("src");
    p.push("calc.l");
    fs::write(
        p,
        " %%
[0-9]+ \"INT\"
\\+ \"+\"
\\* \"*\"
\\( \"(\"
\\) \")\"
[\\t ]+ ;"
    )
    .unwrap();

    // Write src/main.rs
    let mut p = PathBuf::from(tdir.as_ref());
    p.push("src");
    p.push("main.rs");
    fs::write(
        p,
        &format!(
            "extern crate cfgrammar;
#[macro_use] extern crate lrpar;
#[macro_use] extern crate lrlex;

lrlex_mod!(calc_l);
lrpar_mod!(calc_y);

fn main() {{
{}
}}
",
            main
        )
    )
    .unwrap();
}

fn run_dummy(tdir: &TempDir) {
    let c = Command::new(env!("CARGO"))
        .args(&["run"])
        .current_dir(PathBuf::from(tdir.as_ref()))
        .output()
        .expect("Command execution failed");
    if !c.status.success() {
        println!("{}", String::from_utf8_lossy(&c.stdout));
        eprintln!("{}", String::from_utf8_lossy(&c.stderr));
    }
    assert!(c.status.success(), "Command executed unsuccessfully");
}

#[test]
#[ignore]
fn test_epp_str() {
    run_in_dummy(|tdir| {
        init_simple(&tdir);
        let mut p = PathBuf::from(tdir.as_ref());
        p.push("src/grm.y");
        fs::write(
            p,
            "%start A
    %epp a '\"\\\"a\"'
    %%
    A : 'a';"
                .as_bytes()
        )
        .ok();
        run_dummy(&tdir);
    });
}

#[test]
#[ignore]
fn test_no_actions() {
    run_in_dummy(|tdir| {
        init_calc(
            &tdir,
            "ActionKind::NoAction",
            "
    let lexerdef = calc_l::lexerdef();
    let mut lexer = lexerdef.lexer(\"2+3\");
    if !calc_y::parse(&mut lexer).is_empty() {
        panic!();
    }
    let mut lexer = lexerdef.lexer(\"2++3\");
    if calc_y::parse(&mut lexer).len() != 1 {
        panic!();
    }
    "
        );
        run_dummy(&tdir);
    });
}

#[test]
#[ignore]
fn test_basic_actions() {
    run_in_dummy(|tdir| {
        init_calc(
            &tdir,
            "ActionKind::CustomAction",
            "
    let lexerdef = calc_l::lexerdef();
    let mut lexer = lexerdef.lexer(\"2+3\");
    match calc_y::parse(&mut lexer) {
        (Some(Ok(5)), ref errs) if errs.len() == 0 => (),
        _ => unreachable!()
    }"
        );
        run_dummy(&tdir);
    });
}

#[test]
#[ignore]
fn test_error_recovery_and_actions() {
    run_in_dummy(|tdir| {
        init_calc(
            &tdir,
            "ActionKind::CustomAction",
            "
    use lrpar::LexParseError;

    let lexerdef = calc_l::lexerdef();

    let mut lexer = lexerdef.lexer(\"2++3\");
    let (r, errs) = calc_y::parse(&mut lexer);
    match r {
        Some(Ok(5)) => (),
        _ => unreachable!()
    }
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer(\"2+3)\");
    let (r, errs) = calc_y::parse(&mut lexer);
    assert_eq!(r, Some(Ok(5)));
    assert_eq!(errs.len(), 1);
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer(\"2+3+18446744073709551616\");
    let (r, errs) = calc_y::parse(&mut lexer);
    assert_eq!(r, Some(Err(())));
    assert!(errs.is_empty());"
        );
        run_dummy(&tdir);
    });
}
