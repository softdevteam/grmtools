extern crate lrlex;

use lrlex::process_src_dir;

fn main() {
    process_src_dir::<u8>().unwrap()
}
