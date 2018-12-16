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
    fs::{self, create_dir},
    path::PathBuf,
    process::Command
};

use self::tempfile::TempDir;

fn create_dummy() -> TempDir {
    let tdir = TempDir::new().unwrap();
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

    // Write build.rs
    p = PathBuf::from(tdir.as_ref());
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

    // Write src/main.rss
    p = PathBuf::from(tdir.as_ref());
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

    tdir
}

fn build_dummy(tdir: TempDir) {
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
    let tdir = create_dummy();
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
    build_dummy(tdir);
}
