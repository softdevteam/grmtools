// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#[macro_use]
extern crate lazy_static;
extern crate lrpar;
extern crate tempfile;

use std::{
    fs::{self, create_dir, read_dir, remove_dir_all, remove_file},
    panic::{catch_unwind, resume_unwind, UnwindSafe},
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::Duration
};

use self::tempfile::TempDir;

/// How long to wait, in ms, when spinning for DUMMY_RUNNING to become false?
const SPIN_WAIT: u64 = 250;

// This is ugly, but effective: compiling a dummy project is slow because we have to compile
// dependencies. We thus cheat and only create one dummy project, which we continually refresh,
// leaving only its target/ directory behind. In order to do that, we use the `DUMMY_RUNNING` bool
// as a simple spin-lock to prevent more than one test trying to make use of the dummy test
// directory at once.
lazy_static! {
    static ref DUMMY_TESTDIR: TempDir = TempDir::new().unwrap();
}
// This is our spin-lock mutex: we don't use a Rust-level Mutex, because we anticipate that tests
// might fail, at which point a "real" Mutex would be poisoned: we are quite capable of continuing,
// even if one test/thread fails.
static DUMMY_RUNNING: AtomicBool = AtomicBool::new(false);

/// Run the function `f` with a guaranteed fresh dummy test directory that no-one else is using.
fn run_in_dummy<F, T>(f: F) -> T
where
    F: FnOnce(&TempDir) -> T,
    F: Send + UnwindSafe + 'static,
    T: Send + 'static
{
    loop {
        if !DUMMY_RUNNING.swap(true, Ordering::Relaxed) {
            break;
        }
        thread::sleep(Duration::from_millis(SPIN_WAIT));
    }
    reset_dummy(&DUMMY_TESTDIR);
    let r = catch_unwind(|| f(&DUMMY_TESTDIR));
    DUMMY_RUNNING.store(false, Ordering::Relaxed);
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

fn build_dummy(tdir: &TempDir) {
    let c = Command::new(env!("CARGO"))
        .args(&["build"])
        .current_dir(PathBuf::from(tdir.as_ref()))
        .output()
        .unwrap();
    if !c.status.success() {
        println!("{}", String::from_utf8_lossy(&c.stdout));
        eprintln!("{}", String::from_utf8_lossy(&c.stderr));
    }
    assert!(c.status.success());
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
        build_dummy(&tdir);
    });
}
