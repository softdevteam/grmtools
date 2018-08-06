extern crate lrlex;

use lrlex::process_file_in_src;

fn main() {
    // Note that we specify the integer type (u8) we'll use for token IDs (this type *must* be big
    // enough to fit all IDs in) as well as the input file (which must end in ".l").
    process_file_in_src::<u8>("calc.l", None).unwrap();
}
