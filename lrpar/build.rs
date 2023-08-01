use vergen::EmitBuilder;

fn main() {
    EmitBuilder::builder().build_timestamp().emit().unwrap();
}
