use vergen::EmitBuilder;

fn main() {
    println!("cargo::rustc-check-cfg=cfg(grmtools_extra_checks)");
    EmitBuilder::builder().build_timestamp().emit().unwrap();
}
