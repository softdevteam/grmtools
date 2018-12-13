// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

extern crate vergen;

use vergen::{ConstantsFlags, Vergen};

fn main() {
    let mut vgfl = ConstantsFlags::empty();
    vgfl.insert(ConstantsFlags::BUILD_TIMESTAMP);
    for (k, v) in Vergen::new(vgfl).unwrap().build_info() {
        println!("cargo:rustc-env={}={}", k.name(), v);
    }
}
