extern crate lrlex;

use lrlex::process_file_in_src;

fn main() {
    process_file_in_src::<u8>("calc.l", None).unwrap()
}
