#![allow(dead_code)]

pub fn scalar_pick(x: u8) -> u8 {
    if x == 0 { 7 } else { x }
}

pub fn checked_read(buf: [u8; 4], index: usize) -> u8 {
    buf[index]
}

pub fn clamped_read(buf: [u8; 4], index: usize) -> u8 {
    buf[index & 3]
}

pub fn store_then_load(mut buf: [u8; 4], index: usize, value: u8) -> u8 {
    buf[index] = value;
    buf[index]
}

pub fn conditional_store(mut buf: [u8; 4], index: usize, value: u8, take: bool) -> u8 {
    if take {
        buf[index] = value;
        buf[index]
    } else {
        value
    }
}
