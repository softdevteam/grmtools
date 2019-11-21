use vergen::{ConstantsFlags, Vergen};

fn main() {
    let mut vgfl = ConstantsFlags::empty();
    vgfl.insert(ConstantsFlags::BUILD_TIMESTAMP);
    for (k, v) in Vergen::new(vgfl).unwrap().build_info() {
        println!("cargo:rustc-env={}={}", k.name(), v);
    }
}
