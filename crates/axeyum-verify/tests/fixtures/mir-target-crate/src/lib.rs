#![allow(dead_code)]

pub fn cargo_store_then_load(mut buf: [u8; 4], index: usize, value: u8) -> u8 {
    buf[index] = value;
    buf[index]
}

pub fn unsupported_reference(buf: &[u8]) -> u8 {
    buf[0]
}
