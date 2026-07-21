#![allow(dead_code)]

pub fn cargo_store_then_load(mut buf: [u8; 4], index: usize, value: u8) -> u8 {
    buf[index] = value;
    buf[index]
}

pub fn unsupported_reference(buf: &[u8]) -> u8 {
    buf[0]
}

pub fn walk_frame(entries: [u8; 4], virtual_address: u8) -> u8 {
    let level1 = ((virtual_address >> 6) & 0x03) as usize;
    let level2 = (entries[level1] & 0x03) as usize;
    entries[level2] & 0xfc
}

pub fn walk_permissions(entries: [u8; 4], virtual_address: u8) -> u8 {
    let level1 = ((virtual_address >> 6) & 0x03) as usize;
    let parent = entries[level1];
    let level2 = (parent & 0x03) as usize;
    (parent & entries[level2]) & 0x03
}

pub fn broken_walk_index(entries: [u8; 4], virtual_address: u8) -> u8 {
    entries[virtual_address as usize]
}

pub fn broken_frame_unaligned(entries: [u8; 4], virtual_address: u8) -> u8 {
    let level1 = ((virtual_address >> 6) & 0x03) as usize;
    let level2 = (entries[level1] & 0x03) as usize;
    entries[level2]
}

pub fn broken_permissions_escalate(entries: [u8; 4], virtual_address: u8) -> u8 {
    let level1 = ((virtual_address >> 6) & 0x03) as usize;
    let parent = entries[level1];
    let level2 = (parent & 0x03) as usize;
    entries[level2] & 0x03
}
