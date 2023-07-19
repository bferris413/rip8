use std::fs;
use std::process;
use chip8::chip8::{Chip8, Rom};

fn main() {
    let bytes = fs::read("roms/IBM Logo.ch8");
    if let Err(e) = bytes {
        eprintln!("error reading Chip8 ROM: {e}");
        process::exit(1);
    }

    let rom = Rom::with_code(bytes.unwrap()).unwrap();
    let mut chip8 = Chip8::new();
    chip8.run(rom);
}
