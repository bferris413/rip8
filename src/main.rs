use std::fs;
use std::io::{self, Result as IoResult};
use std::process;
use chip8::chip8::{Chip8, Rom};

use crossterm::{
    event::{KeyboardEnhancementFlags, PushKeyboardEnhancementFlags, PopKeyboardEnhancementFlags},
    execute,
    terminal::{self, EnterAlternateScreen, LeaveAlternateScreen},
};

fn main() {
    let bytes = fs::read("roms/IBM Logo.ch8");
    if let Err(e) = bytes {
        eprintln!("error reading Chip8 ROM: {e}");
        process::exit(1);
    }

    if let Err(e) = setup_terminal() {
        eprintln!("couldn't setup terminal: {e}");
        process::exit(1);
    }

    let rom = Rom::with_code(bytes.unwrap()).unwrap();
    let mut chip8 = Chip8::new(io::stdout());
    chip8.run(rom);

    if let Err(e) = restore_terminal() {
        eprintln!("couldn't restore terminal: {e}");
        process::exit(1);
    }
}

// Puts the terminal in raw mode and stores the current screen
fn setup_terminal() -> IoResult<()> {
    let mut stdout = io::stdout();
    terminal::enable_raw_mode()?;
    execute!(
        stdout,
        EnterAlternateScreen,
        PushKeyboardEnhancementFlags(KeyboardEnhancementFlags::REPORT_EVENT_TYPES),
    )
}

// Takes the terminal out of raw mode and restores the original screen
fn restore_terminal() -> IoResult<()> {
    terminal::disable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(
        stdout,
        PopKeyboardEnhancementFlags,
        LeaveAlternateScreen,
    )
}

