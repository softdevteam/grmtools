use vergen::{vergen, Config};

fn main() {
    let mut config = Config::default();
    *config.build_mut().timestamp_mut() = true;
    *config.build_mut().semver_mut() = false;
    vergen(config).unwrap();
}
