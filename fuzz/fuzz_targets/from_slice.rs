#![no_main]

use libfuzzer_sys::fuzz_target;
use serde_hjson::{from_slice, Value};

fuzz_target!(|data: &[u8]| {
    let _ = from_slice::<Value>(data);
});
