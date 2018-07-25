use std::convert::{AsRef, TryFrom};
use std::error::Error;
use std::fmt::Debug;
use std::fs;
use std::fs::{File, read_to_string};
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};

use filetime::FileTime;
use typename::TypeName;
use walkdir::WalkDir;

use lexer::LexerDef;
use parser::parse_lex;

const LEX_FILE_EXT: &str = "l";
const RUST_FILE_EXT: &str = "rs";

pub(crate) fn process_dir<TokId, P, Q>(indirp: P,
                                       outdirp: Q)
                                    -> Result<(), Box<Error>>
                                 where TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName,
                                       P: AsRef<Path>,
                                       Q: AsRef<Path>
{
    for e in WalkDir::new(indirp) {
        let e = e?;
        if e.file_type().is_file() {
            if let Some(LEX_FILE_EXT) = e.path().extension().map(|x| x.to_str().unwrap()) {
                let mut outp = PathBuf::new();
                outp.push(&outdirp);
                outp.push(e.path().file_stem().unwrap());
                outp.set_extension(RUST_FILE_EXT);
                process_file::<TokId, _, _>(e.path(), outp)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn process_file<TokId, P, Q>(inp: P,
                                        outp: Q)
                                     -> Result<(), Box<Error>>
                                  where TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName,
                                        P: AsRef<Path>,
                                        Q: AsRef<Path>
{
    if let Ok(outmd) = fs::metadata(&outp) {
        if let Ok(inmd) = fs::metadata(&inp) {
            if FileTime::from_last_modification_time(&outmd) >
               FileTime::from_last_modification_time(&inmd) {
                // The output file already exists, and with a newer timestamp than the input file,
                // so there's no point regenerating the output.
                return Ok(());
            }
        }
    }
    let inc = read_to_string(&inp).unwrap();
    let lexerdef = parse_lex::<TokId>(&inc)?;
    let mut f = File::create(outp)?;
    let mod_name = inp.as_ref().file_stem().unwrap().to_str().unwrap();
    f.write(format!("mod {} {{", mod_name).as_bytes())?;
    lexerdef.rust_pp(&mut f)?;
    f.write(b"}")?;
    Ok(())
}

impl<TokId: Copy + Debug + Eq + TypeName> LexerDef<TokId> {
    pub(crate) fn rust_pp(&self, f: &mut File) -> Result<(), io::Error> {
        // Header
        f.write(format!("use lrlex::{{LexerDef, Rule}};

pub fn lexerdef() -> LexerDef<{}> {{
    let rules = vec![", TokId::type_name()).as_bytes())?;

        // Individual rules
        for r in &self.rules {
            let tok_id = match r.tok_id {
                Some(ref t) => format!("Some({:?})", t),
                None => "None".to_owned()
            };
            let n = match r.name {
                Some(ref n) => format!("Some({:?}.to_string())", n),
                None => "None".to_owned()
            };
            f.write(format!("
Rule::new({}, {}, \"{}\".to_string()).unwrap(),",
                tok_id, n, r.re_str.replace("\\", "\\\\").replace("\"", "\\\"")).as_bytes())?;
        }

        // Footer
        f.write(b"
];
    LexerDef::new(rules)
}")?;
        Ok(())
    }
}
