use vergen::{generate_cargo_keys, ConstantsFlags};

fn main() {
    let mut flags = ConstantsFlags::empty();
    flags.insert(ConstantsFlags::BUILD_TIMESTAMP);
    generate_cargo_keys(flags).unwrap();
}
