#![no_std]
pub struct K { pub up: bool }

pub fn repro(k: &K, x: u32, y: u32) -> u32 {
    let f: u32 = if k.up { x } else { y };
    if x >= f { 1 } else { 0 }
}
