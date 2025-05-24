extern crate proc_macro;
use glob::glob;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{Ident, LitStr, parse_macro_input};
#[proc_macro]
pub fn generate_codegen_fail_tests(item: TokenStream) -> TokenStream {
    let mut out = Vec::new();
    let test_glob_str: LitStr = parse_macro_input!(item);
    // Not env!("CARGO_MANIFEST_DIR"), which would be relative to the cttests_macro crate.
    // An absolute path which may contain non-utf8 characters.
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let cwd = std::env::current_dir().unwrap();
    // We want a relative path to the glob from the working directory
    // such as: lrpar/cttests/ with any potentially non-utf8 leading characters removed.
    let manifest_dir = std::path::Path::new(&manifest_dir)
        .strip_prefix(cwd)
        .unwrap();
    let test_glob_path = manifest_dir.join(test_glob_str.value());
    let test_glob_str = test_glob_path.into_os_string().into_string().unwrap();
    let test_files = glob(&test_glob_str).unwrap();
    for file in test_files {
        let file = file.unwrap();
        // Remove potentially non-utf8 leading characters again.
        // This time relative to the manifest dir e.g. `src/ctfails/foo.test`
        let file = file.as_path().strip_prefix(manifest_dir).unwrap();
        // Need to convert to string, because `PathBuf` lacks
        // an impl for `ToTokens` a bounds given by `quote!`.
        let path = file.display().to_string();
        let stem = file.file_stem().unwrap().to_string_lossy();
        let ident = Ident::new(&format!("codegen_fail_{}", stem), Span::call_site());
        out.push(quote! {
            #[should_panic]
            #[test]
            fn #ident(){
                run_test_path(#path).unwrap();
            }
        });
    }
    out.into_iter().collect::<proc_macro2::TokenStream>().into()
}
