use std::fs;
use std::path::PathBuf;
use std::process;

use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
/// A Chip-8 disassembler.
struct Cli {
    /// The binary ROM file to disassemble
    #[arg(long, value_name = "BINARY")]
    rom: PathBuf,
}

fn main() {
    let args = Cli::parse();
    let bytes = fs::read(args.rom);
    if let Err(e) = bytes {
        eprintln!("error reading Chip-8 ROM: {e}");
        process::exit(1);
    }
}