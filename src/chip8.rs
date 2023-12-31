use std::cmp;
use std::collections::HashSet;
use std::io::{Result as IoResult, Write};
use std::mem;
use std::num::NonZeroU32;
use std::ops::Deref;
use std::time::{Instant, Duration};
use std::thread;

use crossterm::QueueableCommand;
use crossterm::cursor::MoveTo;
use crossterm::event::{self, Event, KeyEvent, KeyCode, KeyEventKind};
use crossterm::style::Print;
use crossterm::terminal::{Clear, ClearType};

// Number of bytes in the Chip8's memory.
const MEM_BYTES: usize = 4096;
// Maximum allowed bytes of a user's ROM.
const MAX_ROM_BYTES: usize = MEM_BYTES - 0x200;
// Delay and sound timer tick rate (~60 times/sec)
const TIMER_TICK_RATE: Duration = Duration::from_micros(16700);
// Microseconds per second
const MICROS_PER_SEC: u32 = 60_000_000;

// Map between Chip8 keyboard values (0x00-0x0F) and the QWERTY keyboard.
// ----Chip8----       ---QWERTY----
// 1 | 2 | 3 | C  -->  1 | 2 | 3 | 4
// 4 | 5 | 6 | D  -->  Q | W | E | R
// 7 | 8 | 9 | E  -->  A | S | D | F
// A | 0 | B | F  -->  Z | X | C | V
const KEYMAP: [char; 16] = ['x', '1', '2', '3', 'q', 'w', 'e', 'a', 's', 'd', 'z', 'c', '4', 'r', 'f', 'v' ];

// Font, https://tobiasvl.github.io/blog/write-a-chip-8-emulator
const FONT: [u8; 80] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, // 0
    0x20, 0x60, 0x20, 0x20, 0x70, // 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0, // 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0, // 3
    0x90, 0x90, 0xF0, 0x10, 0x10, // 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0, // 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0, // 6
    0xF0, 0x10, 0x20, 0x40, 0x40, // 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0, // 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0, // 9
    0xF0, 0x90, 0xF0, 0x90, 0x90, // A
    0xE0, 0x90, 0xE0, 0x90, 0xE0, // B
    0xF0, 0x80, 0x80, 0x80, 0xF0, // C
    0xE0, 0x90, 0x90, 0x90, 0xE0, // D
    0xF0, 0x80, 0xF0, 0x80, 0xF0, // E
    0xF0, 0x80, 0xF0, 0x80, 0x80  // F
];

/// A Chip8 interpreter.
#[derive(Debug)]
pub struct Chip8<W: Write> {
    memory: [u8; MEM_BYTES],
    display: [[u8; 64]; 32],
    registers: [u8; 16],
    stack: [u16; 16],
    pc: u16,
    index: u16,
    dt: u8,
    st: u8,
    sp: u8,
    should_halt: bool,
    should_draw: bool,
    max_micros_per_cycle: Duration,
    pressed_keys: HashSet<u8>,
    draw_buf: W,
}
impl<W: Write> Chip8<W> {
    /// Returns a new Chip8 interpreter.
    pub fn new(draw_buf: W, ops_sec: NonZeroU32) -> Self {
        let mut memory = [0; MEM_BYTES];
        memory[0..FONT.len()].copy_from_slice(&FONT);
        let max_micros_per_cycle = Duration::from_micros((MICROS_PER_SEC / ops_sec) as u64);

        Chip8 {
            memory,
            registers: [0; 16],
            index: 0,
            dt: 0,
            st: 0,
            pc: 0x200,
            sp: 0,
            should_halt: false,
            should_draw: false,
            stack: [0; 16],
            display: [[0; 64]; 32],
            draw_buf,
            max_micros_per_cycle,
            pressed_keys: HashSet::with_capacity(16),
        }
    }

    /// Runs the provided ROM.
    pub fn run(&mut self, rom: Rom) -> IoResult<()> {
        self.load(&rom.code);
        self.run_loop()
    }

    /// Continues processing after a halt from wherever the PC currently is.
    pub fn resume(&mut self) -> IoResult<()> {
        self.run_loop()
    }

    // Runs the CPU until reaching EOM or a halt.
    //
    // Halts can occur either due to an instruction or the user terminating the program.
    // In the case of an instruction, any remaining timers _will not_ be run down to 0.
    // Instead, the current cycle is completed at its normal speed and the CPU immediately suspends.
    //
    // If the CPU is resumed, timers will be at their values immediately before the suspend but without
    // any cycles towards the next tick.
    fn run_loop(&mut self) -> IoResult<()> {
        let mut timer_elapsed = Duration::ZERO;
        self.should_halt = false;

        while let Some(instr) = self.fetch() {
            self.should_draw = false;

            // #[cfg(test)]
            // if let [a, b] = &*instr {
            //     // println!("instr: 0x{:02x}{:02x}", a, b);
            // }

            let start = Instant::now();
            self.execute(instr)?;
            if self.should_draw {
                self.draw_display()?;
            }
            timer_elapsed += start.elapsed();

            // process events and manage timers until the next cycle
            let cycle_wait_start = Instant::now();
            loop {
                // decrement delay and sound timers if it's been TIMER_TICK_RATE since our last decrement
                if timer_elapsed > TIMER_TICK_RATE {
                    timer_elapsed = Duration::ZERO;
                    self.dt = self.dt.saturating_sub(1);
                    self.st = self.st.saturating_sub(1);
                }

                let remaining_cycle_dur = self.max_micros_per_cycle.saturating_sub(start.elapsed());
                let remaining_timer_dur = TIMER_TICK_RATE.saturating_sub(timer_elapsed);
                let max_event_poll_dur = cmp::min(remaining_cycle_dur, remaining_timer_dur);

                if event::poll(max_event_poll_dur)? {
                    let _ = self.process_input_event()?;
                }

                timer_elapsed += cycle_wait_start.elapsed();
                if remaining_cycle_dur <= Duration::ZERO { 
                    break;
                }
            }

            if self.should_halt {
                return Ok(());
            }
        }

        // run out the remaining timers (does not happen if the CPU halted)
        while self.dt != 0 || self.st != 0 {
            // after the first iteration, sleep_micros will always be
            // TIMER_TICK_RATE since timer_elapsed is never incremented again
            let sleep_dur = TIMER_TICK_RATE.saturating_sub(timer_elapsed); 
            timer_elapsed = Duration::ZERO;

            thread::sleep(sleep_dur);
            self.dt = self.dt.saturating_sub(1);
            self.st = self.st.saturating_sub(1);
        } 

        Ok(())
    }

    // Executes the provided instruction.
    fn execute(&mut self, instr: Instr) -> IoResult<()> {
        match &instr.to_be_bytes() {
            // clear display
            &[0x00, 0xE0] => {
                self.display.fill([0; 64]);
            }

            // return from subroutine
            &[0x00, 0xEE] => {
                self.pc = self.stack[self.sp as usize];
                self.sp = self.sp.saturating_sub(1);
            }

            // (custom OP) halt execution and rewind PC as if this instruction never executed
            &[0x00, 0xA0] => {
                if self.pc >= 0x202 {
                    self.pc -= 2;
                }
                self.should_halt = true;
            }

            // (custom OP) halt execution
            &[0x00, 0xA1] => {
                self.should_halt = true;
            }

            // jump to addr
            &[a, b] if a & 0xF0 == 0x10 => {
                let low_nib_high_byte = a & 0x0F;
                let addr = u16::from_be_bytes([low_nib_high_byte, b]);
                // 12-bits max value is 4095, within max memory size
                self.pc = addr;
            }

            // call subroutine at nnn
            &[a, b] if a & 0xF0 == 0x20 => {
                if (self.sp as usize) < (self.stack.len() - 1) {
                    let low_nib_high_byte = a & 0x0F;
                    let addr = u16::from_be_bytes([low_nib_high_byte, b]);
                    self.sp +=1;
                    self.stack[self.sp as usize] = self.pc;
                    self.pc = addr;

                }
            }

            // skip if Vx == b
            &[a, b] if a & 0xF0 == 0x30 => {
                let reg = (a & 0x0F) as usize;
                if self.registers[reg] == b {
                    self.pc = self.pc.saturating_add(2);
                }
            }

            // skip if Vx != b
            &[a, b] if a & 0xF0 == 0x40 => {
                let reg = (a & 0x0F) as usize;
                if self.registers[reg] != b {
                    self.pc = self.pc.saturating_add(2);
                }
            }

            // skip if Vx == Vy
            &[a, b] if a & 0xF0 == 0x50 => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                if self.registers[regx] == self.registers[regy] {
                    self.pc = self.pc.saturating_add(2);
                }
            }

            // set register
            &[a, b] if a & 0xF0 == 0x60 => {
                let reg = (a & 0x0F) as usize;
                self.registers[reg] = b;
            }

            // Wrapping add to register
            &[a, b] if a & 0xF0 == 0x70 => {
                let reg = (a & 0x0F) as usize;
                self.registers[reg] = self.registers[reg].wrapping_add(b);
            }

            // Set Vx = Vy, 8xy0
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 0) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                self.registers[regx] = self.registers[regy];
            }

            // Set Vx = Vx | Vy, 8xy1
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 1) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                self.registers[regx] |= self.registers[regy];
            }

            // Set Vx = Vx & Vy, 8xy2
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 2) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                self.registers[regx] &= self.registers[regy];
            }

            // Set Vx = Vx ^ Vy, 8xy3
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 3) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                self.registers[regx] ^= self.registers[regy];
            }

            // Set Vx = Vx + Vy and set VF on carry, 8xy4
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 4) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                let res = self.registers[regx] as u16 + self.registers[regy] as u16;
                if res > 255 {
                    self.registers[0x0F] = 1;
                } else {
                    self.registers[0x0F] = 0;
                }
                self.registers[regx] = (res & 0x00FF) as u8;
            }

            // Set Vx = Vx - Vy and set VF on underflow, 8xy5
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 5) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                let vx = self.registers[regx];
                let vy = self.registers[regy];
                if vx > vy {
                    self.registers[0x0F] = 1
                } else {
                    self.registers[0x0F] = 0;
                }
                self.registers[regx] = vx.saturating_sub(vy);
            }

            // Set Vx = Vx >> 1 and set VF if LSB was 1, 8xy6
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 6) => {
                let regx = (a & 0x0F) as usize;
                let vx = self.registers[regx];
                self.registers[0x0F] = vx & 0x01;
                self.registers[regx] >>= 1;
            }

            // Set Vx = Vy - Vx and set VF if Vy > Vx, 8xy7
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 7) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                let vx = self.registers[regx];
                let vy = self.registers[regy];
                self.registers[0x0F] = if vy > vx { 1 } else { 0 };
                self.registers[regx] = vy.saturating_sub(vx);
            }

            // Set Vx = Vx << 1 and set VF if MSB was 1, 8xyE
            &[a, b] if (a & 0xF0 == 0x80) && (b & 0x0F == 0x0E) => {
                let regx = (a & 0x0F) as usize;
                let vx = self.registers[regx];
                self.registers[0x0F] = (vx & 0x80) >> 7;
                self.registers[regx] <<= 1;
            }

            // skip not equal, 9xy0
            &[a, b] if (a & 0xF0 == 0x90) => {
                let regx = (a & 0x0F) as usize;
                let regy = ((b & 0xF0) >> 4) as usize;
                if self.registers[regx] != self.registers[regy] {
                    self.pc = self.pc.saturating_add(2);
                }
            }

            // Set index register to nnn, Annn
            &[a, b] if a & 0xF0 == 0xA0 => {
                let low_nib_high_byte = a & 0x0F;
                let val = u16::from_be_bytes([low_nib_high_byte, b]);
                self.index = val;
            }

            // Jump to V0 + nnn, Bnnn
            &[a, b] if a & 0xF0 == 0xB0 => {
                let low_nib_high_byte = a & 0x0F;
                let addr = u16::from_be_bytes([low_nib_high_byte, b]);
                let offset = self.registers[0x00] as u16;
                self.pc = offset + addr;
            }

            // Vx = (random) & kk, Cxkk
            &[a, b] if a & 0xF0 == 0xC0 => {
                let regx = (a & 0x0F) as usize;
                let r: u8 = rand::random();
                self.registers[regx] = r & b;
            }

            // Draw n bytes into our internal buffer, starting at Vx,Vy, Dxyn
            &[a, b] if a & 0xF0 == 0xD0 => {
                let regx = (a & 0x0F) as usize;
                let regy = (b & 0xF0) as usize >> 4;
                let displx = self.registers[regx] as usize % 64; // starting point should wrap
                let mut disply = self.registers[regy] as usize % 32; // starting point should wrap
                let n = b & 0x0F;
                let sprite_range = self.index as usize..(self.index + n as u16) as usize;

                self.registers[0x0F] = 0;

                // iterate over the sprite bytes, mapping each bit to the "pixel"
                let end_byte = displx + 8;
                for sprite_row in &self.memory[sprite_range] {
                    if disply >= 32 { break; } // we're off the display vertically, drawing is finished
                    let mut drawx = displx;
                    while drawx < end_byte && drawx < 64 {
                        let bitval = (sprite_row >> (end_byte - drawx - 1)) & 0x01;
                        if self.display[disply][drawx] & bitval == 0x01  {
                            // set VF to 1 if we erase a pixel that was previously drawn
                            self.registers[0x0F] = 0x01;
                        }
                        self.display[disply][drawx] ^= bitval;
                        drawx += 1;
                    }
                    disply += 1;
                }

                self.should_draw = true;
            }

            // Skip if keypressed, Ex9E
            &[a, 0x9E] if a & 0xF0 == 0xE0 => {
                let regx = (a & 0x0F) as usize;
                let val = self.registers[regx];
                if self.pressed_keys.contains(&val) {
                    self.pc += 2;
                }
            }

            // Skip if not keypressed, ExA1
            &[a, 0xA1] if a & 0xF0 == 0xE0 => {
                let regx = (a & 0x0F) as usize;
                let val = self.registers[regx];
                if !self.pressed_keys.contains(&val) {
                    self.pc += 2;
                }
            }

            // Vx = dt, Fx07
            &[a, 0x07] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                self.registers[regx] = self.dt;
            }

            // Vx = keypress value, Fx0A
            // block until keypress
            &[a, 0x0A] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                if event::poll(Duration::ZERO)? {
                    match self.process_input_event()? {
                        Some(Event::Key(KeyEvent { kind: KeyEventKind::Press | KeyEventKind::Release, code: KeyCode::Char(c), .. })) => {
                            let value = KEYMAP.iter().position(|key| *key == c).unwrap() as u8; 
                            self.registers[regx] = value;
                        }
                        _ => {
                            // we're supposed to "block" from the user's perspective but the CPU needs to continue processing
                            // timers and events so we'll loop on this instruction
                            self.pc -= 2;
                        }
                    }
                }
            }

            // dt = Vx, Fx15
            &[a, 0x15] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                self.dt = self.registers[regx];
            }

            // st = Vx, Fx18
            &[a, 0x18] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                self.st = self.registers[regx];
            }

            // I = I + Vx, Fx1E
            &[a, 0x1E] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                self.index += self.registers[regx] as u16;
            }

            // I = location of hex sprite for value Vx, Fx29
            &[a, 0x29] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                let val = self.registers[regx];
                // each font is 5 bytes and stored at the offset 5 * digit
                // e.g, '0' is at 0x00, '3' is at 0x0F (15), etc.
                self.index = 5 * val as u16; 
            }

            // mem[I] = hundreds, I+1 = tens, I+2 = ones of Vx, Fx33
            &[a, 0x33] if a & 0xF0 == 0xF0 => {
                let regx = (a & 0x0F) as usize;
                let mut val = self.registers[regx];
                let ival = self.index as usize;

                let ones = val % 10;
                val /= 10;
                let tens = val % 10;
                val /= 10;
                let hundreds = val % 10;

                self.memory[ival] = hundreds;
                self.memory[ival+1] = tens;
                self.memory[ival+2] = ones;
            }

            // Store V0 through Vx starting at memory[I], Fx55
            &[a, 0x55] if a & 0xF0 == 0xF0 => {
                let nregs = (a & 0x0F) as usize;
                let i = self.index as usize;
                let memslice = &mut self.memory[i..=(i + nregs)];
                let regslice = &self.registers[..=nregs];
                memslice.copy_from_slice(regslice);
            }

            // Read and store V0 through Vx from memory, starting at I, Fx65
            &[a, 0x65] if a & 0xF0 == 0xF0 => {
                let nregs = (a & 0x0F) as usize;
                let regslice = &mut self.registers[..=nregs];
                let index = self.index as usize;
                let memslice = &self.memory[index..=(index + nregs)];
                regslice.copy_from_slice(memslice);
            }

            // NOOP
            &[0x00, 0x00] => {}

            &[a, b] => unimplemented!("{a:#04X} {b:#04X}"),
        }

        Ok(())
    }

    // Reads and processes a single input event according to the event type.
    //
    // If the event isn't relevant to the emulator, it's ignored and Ok(None) is returned.
    // If the event is relevant, it's processed and returned as Ok(Some(event)).
    fn process_input_event(&mut self) -> IoResult<Option<Event>> {
        let event = event::read()?;
        let mut is_valid = false;
        match event {
            Event::Key(KeyEvent { code: KeyCode::Char(c @ '1'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ '2'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ '3'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ '4'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'q'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'w'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'e'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'r'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'a'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 's'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'd'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'f'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'z'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'x'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'c'), kind, .. }) |
            Event::Key(KeyEvent { code: KeyCode::Char(c @ 'v'), kind, .. }) => {
                is_valid = true;
                // safe since valid key events are isolated in the match
                let value = KEYMAP.iter().position(|key| *key == c).unwrap() as u8; 
                match kind {
                    KeyEventKind::Press => {
                        assert!(self.pressed_keys.insert(value));
                    }
                    KeyEventKind::Repeat => {
                        assert!(self.pressed_keys.contains(&value));
                    }
                    KeyEventKind::Release => {
                        assert!(self.pressed_keys.remove(&value));
                    }
                };
            }
            Event::Key(KeyEvent { code: KeyCode::Char(' '), .. }) => {
                // interrupt
                self.should_halt = true;
            }
            Event::Resize(..) => {
                // TODO: should redraw remaining image if clipped, but doesn't
                self.should_draw = true;
            }
            _ => {},
        }

        if is_valid {
            Ok(Some(event))
        } else {
            Ok(None)
        }
    }

    /// Loads the provided bytes into memory.
    fn load(&mut self, code: &[u8]) {
        let code_slice = &mut self.memory[0x200..0x200 + code.len()];
        code_slice.copy_from_slice(code);
    }

    // Fetches the next instruction from memory.
    fn fetch(&mut self) -> Option<Instr> {
        let pc = self.pc as usize;
        if pc < MEM_BYTES {
            let instr_slice = &self.memory[pc..pc + 2];
            let (instr_bytes, _) = instr_slice.split_at(mem::size_of::<u16>());
            let instr = Instr::from_be_bytes(instr_bytes.try_into().unwrap());
            self.pc += 2;
            Some(instr)
        } else {
            None
        }
    }

    /// Prints the Chip-8's display.
    fn draw_display(&mut self) -> IoResult<()> {
        self.draw_buf.queue(Clear(ClearType::All))?;
        const STR_LEN: usize = 2; // length of the printed character
        for (i, row) in self.display.iter().enumerate() {
            for (j, byte) in row.iter().enumerate() {
                self.draw_buf.queue(MoveTo((j * STR_LEN) as u16 , i as u16))?;
                if *byte == 0x01 {
                    self.draw_buf.queue(Print("\u{2587}\u{2587}"))?;
                } else {
                    self.draw_buf.queue(Print("__"))?;
                }
            }
        }

        let last_row_idx = self.display.len();
        self.draw_buf.queue(MoveTo(0, last_row_idx as u16))?;
        self.draw_buf.queue(Print("(press space to immediately shut down)"))?;
        self.draw_buf.flush()
    }
}

/// A Chip8 program.
pub struct Rom {
    code: Vec<u8>
}

impl Rom {
    /// Returns a new Chip8 ROM.
    /// 
    /// This function returns an error if `code.len() > MAX_ROM_BYTES || code.is_empty()`.
    pub fn with_code(code: Vec<u8>) -> Result<Self, String> {
        if code.len() > MAX_ROM_BYTES || code.is_empty() {
            return Err(format!("ROM size incorrect. Max size is {} bytes but {} bytes were provided", MAX_ROM_BYTES, code.len()));
        }
        Ok(Rom { code })
    }
}

impl Deref for Rom {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        &self.code
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
// A two-byte Chip8 instruction.
struct Instr(u16);
impl Instr {
    #[allow(unused)]
    fn new(instr: u16) -> Self {
        Instr(instr)
    }
    fn from_be_bytes(bytes: [u8; 2]) -> Self {
        let instr = u16::from_be_bytes(bytes);
        Self(instr)
    }
    fn to_be_bytes(&self) -> [u8; 2] {
        self.0.to_be_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[test]
    fn rom_with_code_creates_new_proper_rom() {
        let code = vec![10; MAX_ROM_BYTES];
        let rom = Rom::with_code(code).unwrap();
        assert_eq!(rom.code.len(), MAX_ROM_BYTES);
    }

    #[test]
    fn rom_with_code_rejects_too_large() {
        let code = vec![1; MAX_ROM_BYTES + 1];
        let rom = Rom::with_code(code);
        assert!(rom.is_err());
    }

    #[test]
    fn rom_with_code_rejects_too_small() {
        let code = Vec::new();
        let rom = Rom::with_code(code);
        assert!(rom.is_err());
    }

    #[test]
    fn chip8_load_loads_into_memory() {
        let rom = Rom::with_code(vec![255; MAX_ROM_BYTES]).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.load(&rom);
        assert_eq!(&chip8.memory[0x200..MEM_BYTES], &[255; MAX_ROM_BYTES]);
    }

    #[test]
    fn chip8_load_loads_smaller_rom_into_memory() {
        let rom = Rom::with_code(vec![255; 100]).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.load(&rom);
        assert_eq!(&chip8.memory[0x200..0x200+100], &[255; 100]);
        assert_eq!(&chip8.memory[0x200+100..], &[0; MAX_ROM_BYTES - 100]);
    }

    #[test]
    fn chip8_fetch_fetches_next_instr() {
        let rom = Rom::with_code(Vec::from([1, 2, 3, 4, 5, 6])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.load(&rom);
        assert_eq!(&[1, 2], &chip8.fetch().unwrap().to_be_bytes());
        assert_eq!(&[3, 4], &chip8.fetch().unwrap().to_be_bytes());
        assert_eq!(&[5, 6], &chip8.fetch().unwrap().to_be_bytes());
        // remaining mem is zeroed
        assert_eq!(&[0, 0], &chip8.fetch().unwrap().to_be_bytes());
    }

    #[test]
    fn chip8_clears_display() {
        let rom = Rom::with_code(Vec::from([0x00, 0xE0])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.display.fill([255; 64]);
        chip8.run(rom).unwrap();
        assert_eq!(chip8.display, [[0; 64]; 32]);
    }

    #[test]
    fn chip8_executes_jump() {
        // jump then halt
        let rom = Rom::with_code(Vec::from([
            0x12, 0x08, // jump to 0x208
            0x00, 0x00,
            0x00, 0x00,
            0x00, 0x00,
            0x00, 0xA0, // 0x208, a halt + rewind
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        // the addr we set in jump
        assert_eq!(chip8.pc, 0x208);
    }

    #[test]
    fn chip8_executes_set_register() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0xFF, // set VA to 0xFF
            0x00, 0xA0, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0A], 0xFF);
    }

    #[test]
    fn chip8_adds_value_to_register() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0x01, // set VA to 0x01
            0x7A, 0x02, // add 0x02 to VA and store in VA
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0A], 0x03);
    }

    #[test]
    fn chip8_adds_value_to_register_and_wraps() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0xFF, // set VA to 0xFF
            0x7A, 0x02, // add 0x02 to VA and store in VA
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0A], 0x01);
    }

    #[test]
    fn chip8_sets_index_register() {
        let rom = Rom::with_code(Vec::from([
            0xA1, 0x23, // set index register to 0x123
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.index, 0x123);
    }

    #[test]
    fn chip8_draws_sprite_with_wrap() {
        let rom = Rom::with_code(Vec::from([
            0xA2, 0x0A, // set index register to 0x20A
            0x6A, 0x4B, // set VA to 75 (should wrap to 11 when drawn)
            0x6B, 0x0A, // set VB to 10
            0xDA, 0xB5, // draw 5-byte sprite to VA VB (11, 10)
            0x00, 0xA1, // halt
            0xF0, 0x80, 0xF0, 0x10, 0xF0, // the sprite "5"
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        let exp_display = [
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // here
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // here
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // here
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // here
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // here
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ];
        assert_eq!(&chip8.display, &exp_display);
        chip8.draw_display().unwrap();
    }

    #[test]
    fn chip8_draws_sprite_with_wrap_and_xy_clip() {
        let rom = Rom::with_code(Vec::from([
            0xA2, 0x0A, // set index register to 0x20A
            0x6A, 0x7D, // set VA to 125 (should wrap to 61 when drawn)
            0x6B, 0x3E, // set VB to 62 (should wrap to 30 when drawn)
            0xDA, 0xB5, // draw 5-byte sprite to VA VB (61, 30)
            0x00, 0xA1, // halt
            0xF0, 0x80, 0xF0, 0x10, 0xF0, // the sprite "5"
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        chip8.draw_display().unwrap();
        let exp_display = [
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], // rightmost pixels clipped,
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], // only two rows displayed
        ];
        assert_eq!(&chip8.display, &exp_display);
    }

    #[test]
    fn chip8_calls_subroutine_and_returns() {
        let rom = Rom::with_code(Vec::from([
            0x22, 0x0A, // call sub at 0x20A
 /* x202 */ 0x6A, 0xFF, // set VA to 0xFF (should be skipped if we jump to 0x20A but executed on return)
            0x00, 0xA1, // halt
            0x00, 0x00, // NOOP
            0x00, 0x00, // NOOP
 /* x20A */ 0x6B, 0xF1, // set VB to 0xF1
 /* x20C */ 0x00, 0xA1, // halt
 /* x20E */ 0x00, 0xEE, // return 
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.pc, 0x20E); 
        assert_eq!(chip8.stack[chip8.sp as usize], 0x202);
        assert_eq!(chip8.sp, 1);
        assert_eq!(chip8.registers[0x0B], 0xF1); // x20A should have executed
        assert_eq!(chip8.registers[0x0A], 0); // x202 should not have executed

        chip8.resume().unwrap(); // should continue at x20E
        assert_eq!(chip8.pc, 0x206); 
        assert_eq!(chip8.sp, 0);
        assert_eq!(chip8.registers[0x0A], 0xFF); // x202 should have executed
    }

    #[test]
    fn chip8_skips_if_equal_byte() {
        let rom = Rom::with_code(Vec::from([
            0x6D, 0xAB, // set VD to 0xAB
            0x3D, 0xAB, // skip if VD == 0xAB
            0x61, 0xAB, // set V1 to 0xAB (should be skipped)
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0D], 0xAB);
        assert_eq!(chip8.registers[0x01], 0); // v1 should not have been set
    }

    #[test]
    fn chip8_skips_if_not_equal_byte() {
        let rom = Rom::with_code(Vec::from([
            0x4D, 0xAB, // skip if V3 != 0x02
            0x61, 0xFF, // set V1 to 0xFF (should be skipped)
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x01], 0); // v1 should not have been set
    }

    #[test]
    fn chip8_skips_if_equal_reg() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0x11, // set VA to 0x11
            0x6B, 0x11, // set VB to 0x11
            0x5A, 0xB0, // skip if VA == VB
            0x61, 0xFF, // set V1 to 0xFF (should be skipped)
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x01], 0); // v1 should not have been set
    }

    #[test]
    fn chip8_sets_vx_to_vy() {
        let rom = Rom::with_code(Vec::from([
            0x6E, 0xFF, // set VE to 0xFF
            0x81, 0xE0, // set V1 to VE
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x01], 0xFF);
        assert_eq!(chip8.registers[0x01], chip8.registers[0x0E]);
    }

    // Set Vx = Vx | Vy, 8xy1
    #[test]
    fn chip8_sets_vx_to_or_vy() {
        let rom = Rom::with_code(Vec::from([
            0x62, 0x0F, // set V2 to 0x0F
            0x6E, 0xF0, // set VE to 0xF0
            0x82, 0xE1, // 'or' them
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x02], 0xFF);
        assert_eq!(chip8.registers[0x0E], 0xF0); // VE should be unchanged
    }

    // Set Vx = Vx & Vy, 8xy2
    #[test]
    fn chip8_sets_vx_to_and_vy() {
        let rom = Rom::with_code(Vec::from([
            0x69, 0x0F, // set V9 to 0x0F
            0x6A, 0xF0, // set VA to 0xF0
            0x89, 0xA2, // 'and' them
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x09], 0x00);
        assert_eq!(chip8.registers[0x0a], 0xF0); // VA should be unchanged
    }

    // Set Vx = Vx ^ Vy, 8xy3
    #[test]
    fn chip8_sets_vx_to_xor_vy() {
        let rom = Rom::with_code(Vec::from([
            0x68, 0b1010_1010, // set V8 to this
            0x62, 0b0101_0101, // set V2 to that
            0x88, 0x23, // 'xor' them
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x08], 0b1111_1111);
        assert_eq!(chip8.registers[0x02], 0b0101_0101); // V2 should be unchanged
    }

    // Set Vx = Vx + Vy, VF = carry, 8xy4
    #[test]
    fn chip8_sets_vx_to_plus_carry_vy() {
        let rom = Rom::with_code(Vec::from([
            0x60, 0xFF, // set V0 to this
            0x62, 0x02, // set V2 to that, should cause carry in VF
            0x80, 0x24, // add them
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x00], 0x01); // only lowest 8 bits should be present
        assert_eq!(chip8.registers[0x0F], 0x01);
    }

    // Set Vx = Vx - Vy, VF = not carry, 8xy5
    #[test]
    fn chip8_sets_vx_to_sub_carry_vy() {
        let rom = Rom::with_code(Vec::from([
            0x61, 0xAB, // set V1 to this
            0x62, 0x01, // set V2 to that, should cause carry in VF
            0x81, 0x25, // sub Vx - Vy
            0x00, 0xA1, // halt
            0x6A, 0x01, // set VA to this
            0x63, 0x02, // set V3 to that, should clear carry in VF
            0x8A, 0x35, // sub Vx - Vy
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x01], 0xAA);
        assert_eq!(chip8.registers[0x0F], 0x01);

        chip8.resume().unwrap();
        assert_eq!(chip8.registers[0x0A], 0x00); // saturating sub
        assert_eq!(chip8.registers[0x0F], 0x00);
    }

    // VF = Vx & 0x01 == 1, Set Vx = Vx >> 1, 8xy6
    #[test]
    fn chip8_sets_vx_to_shr_1() {
        let rom = Rom::with_code(Vec::from([
            0x6C, 0xFF, // set VC to 0xFF
            0x8C, 0x26, // Vx >>= 1, set carry
            0x00, 0xA1, // halt
            0x6D, 0x02, // set VD to 0x02
            0x8D, 0x26, // Vx >>= 1, unset carry
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0C], 0b0111_1111);
        assert_eq!(chip8.registers[0x0F], 0x01);

        chip8.resume().unwrap();
        assert_eq!(chip8.registers[0x0D], 0x01);
        assert_eq!(chip8.registers[0x0F], 0x00);
    }

    // Set Vx = Vy - Vx, VF = not carry, 8xy7
    #[test]
    fn chip8_sets_vx_to_vy_sub_carry() {
        let rom = Rom::with_code(Vec::from([
            0x61, 0x05, // set V1 to this
            0x62, 0x08, // set V2 to that, should cause carry in VF
            0x81, 0x27, // Vx = Vy - Vx
            0x00, 0xA1, // halt
            0x6A, 0xFF, // set VA to this
            0x63, 0x02, // set V3 to that, should clear carry in VF
            0x8A, 0x37, // Vx = Vy - Vx
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x01], 0x03);
        assert_eq!(chip8.registers[0x0F], 0x01);

        chip8.resume().unwrap();
        assert_eq!(chip8.registers[0x0A], 0x00);
        assert_eq!(chip8.registers[0x0F], 0x00);
    }

    // VF = Vx & 0x80 == 1, Set Vx = Vx << 1, 8xyE
    #[test]
    fn chip8_sets_vx_to_shl_1() {
        let rom = Rom::with_code(Vec::from([
            0x6C, 0b1111_1010, // set VC to that
            0x8C, 0x2E, // Vx <<= 1, set carry
            0x00, 0xA1, // halt
            0x6D, 0b0111_1111, // set VD to that
            0x8D, 0x2E, // Vx <<= 1, unset carry
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0C], 0b1111_0100);
        assert_eq!(chip8.registers[0x0F], 0x01);

        chip8.resume().unwrap();
        assert_eq!(chip8.registers[0x0D], 0b1111_1110);
        assert_eq!(chip8.registers[0x0F], 0x00);
    }

    // Skip not equal, 9xy0
    #[test]
    fn chip8_skips_if_reg_not_equal() {
        let rom = Rom::with_code(Vec::from([
            0x60, 0xF1, // set V0 to that
            0x61, 0xF1, // set V1 to that
            0x90, 0x2E, // compare and skip
            0x62, 0x0C, // set V2 to that (should be skipped)
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x02], 0x00);
        assert_eq!(chip8.registers[0x00], 0xF1);
        assert_eq!(chip8.registers[0x01], 0xF1);
    }

    // jump V0 + nnn, Bnnn
    #[test]
    fn chip8_jumps_v0_plus_n() {
        let rom = Rom::with_code(Vec::from([
            0x60, 0x11, // set V0 to 0x11
            0xB1, 0xF7, // jump V0 + 0x1F7 (x208)
            0x6D, 0xFF, // set VD (should be skipped)
            0x62, 0x0C, // set V2 (should be skipped)
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x00], 0x11);
        assert_eq!(chip8.pc, 0x20A);
        assert_eq!(chip8.registers[0x0D], 0x00);
        assert_eq!(chip8.registers[0x02], 0x00);
    }

    // Vx = RND & nn, Cxnn
    #[test]
    fn chip8_sets_vx_rand_nn() {
        let rom = Rom::with_code(Vec::from([
            0xC2, 0xFF, // set V2 to RDN & 0xFF
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert!(chip8.registers[0x02] != 0x00);
        assert!(chip8.registers[0x02] != 0xFF);
    }

    // Vx = dt, Fx07, Fx15
    #[test]
    fn chip8_sets_vx_dt() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0xF1, // set VA to 0xF1
            0xFA, 0x15, // set dt to VA
            0xFB, 0x07, // set VB to dt
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x0A], 0xF1);
        assert_eq!(chip8.registers[0x0B], 0xF1);
        assert_eq!(chip8.dt, 0xF1);
    }

    // st = Vx, Fx18
    #[test]
    fn chip8_sets_st() {
        let rom = Rom::with_code(Vec::from([
            0x67, 0xAA, // set V7 to 0xAA
            0xF7, 0x18, // set st to V7
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x07], 0xAA);
        assert_eq!(chip8.st, 0xAA);
    }

    // I = I + Vx, Fx1E
    #[test]
    fn chip8_sets_i_plus_vx() {
        let rom = Rom::with_code(Vec::from([
            0x67, 0x02, // set V7 to 0x02
            0xF7, 0x1E, // add and store
            0x00, 0xA1, // halt, I should be 0x02
            0xF7, 0x1E, // add and store
            0x00, 0xA1, // halt, I should be 0x04
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.registers[0x07], 0x02);
        assert_eq!(chip8.index, 0x02);

        chip8.resume().unwrap();
        assert_eq!(chip8.index, 0x04);
    }

    // Store BCD in I, I+1, I+2, Fx33
    #[test]
    fn chip8_stores_bcd() {
        let rom = Rom::with_code(Vec::from([
            0xAB, 0x00, // set I to 0xB00
            0x6A, 0xFE, // set VA to 0xFE (254)
            0xFA, 0x33, // do the thing
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.memory[0xB00], 2);
        assert_eq!(chip8.memory[0xB01], 5);
        assert_eq!(chip8.memory[0xB02], 4);
    }

    // Copy V0 to Vx into memory I, Fx55
    #[test]
    fn chip8_stores_registers_in_memory() {
        let rom = Rom::with_code(Vec::from([
            0x60, 0x00, // set V0..VE to 0..=0x0E using only load
            0x61, 0x01,
            0x62, 0x02,
            0x63, 0x03,
            0x64, 0x04,
            0x65, 0x05,
            0x66, 0x06,
            0x67, 0x07,
            0x68, 0x08,
            0x69, 0x09,
            0x6A, 0x0A,
            0x6B, 0x0B,
            0x6C, 0x0C,
            0x6D, 0x0D,
            0x6E, 0x0E,
            0xA5, 0x00, // set I to 0x500
            0xFE, 0x55, // copy registers to memory
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(&chip8.memory[0x500..=0x50E], &[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E]);
    }

    // Copy memory I into V0..=VX, Fx65
    #[test]
    fn chip8_reads_registers_from_memory() {
        let rom = Rom::with_code(Vec::from([
            0xAA, 0x00, // set I to 0xA00
            0xFE, 0x65, // copy registers to memory
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        let slice = &[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E];
        chip8.memory[0x0A00..=0xA0E].copy_from_slice(slice);
        chip8.run(rom).unwrap();
        assert_eq!(&chip8.registers[..=0x0E], slice);
    }

    // I = location of hex sprite for value Vx, Fx29
    #[test]
    fn chip8_sets_index_to_font_location() {
        let rom = Rom::with_code(Vec::from([
            0x61, 0x00, // set V1 to 0x00 (digit '0')
            0xF1, 0x29, // set I wherever '0' is stored
            0x00, 0xA1, // halt
        ])).unwrap();

        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.index, 0x00);

        let rom = Rom::with_code(Vec::from([
            0x69, 0x08, // set V9 to 0x08 (digit '8')
            0xF9, 0x29, // set I wherever '8' is stored
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.index, 0x28);

        let rom = Rom::with_code(Vec::from([
            0x6A, 0x0F, // set VA to 0x0F (digit 'F')
            0xFA, 0x29, // set I wherever 'F' is stored
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
        assert_eq!(chip8.index, 0x4B);
    }

    #[test]
    #[ignore]
    fn chip8_draws_font() {
        // copy/paste, too tired to handwrite this atm =)
        let rom = Rom::with_code(Vec::from([
            0x61, 0x00, // set V1 to 0x00 (digit '0')
            0x62, 0x00, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I to '0'
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x01, // set V1 to 0x01 (digit '1')
            0x62, 0x05, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x02, // set V1 to 0x02 (digit '2')
            0x62, 0x0A, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x03, // set V1 to 0x03 (digit '3')
            0x62, 0x0F, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x04, // set V1 to 0x04 (digit '4')
            0x62, 0x14, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x05, // set V1 to 0x05 (digit '5')
            0x62, 0x19, // set V2 to 0x00 (x coord)
            0x63, 0x00, // set V3 to 0x00 (y coord)
            0xF1, 0x29, // set I
            0xD2, 0x35, // draw at V2, V3

            0x61, 0x06, 
            0x62, 0x1E, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x07, 
            0x62, 0x23, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x08, 
            0x62, 0x28, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x09, 
            0x62, 0x2D, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0A, 
            0x62, 0x32, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0B, 
            0x62, 0x37, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0C, 
            0x62, 0x3C, 
            0x63, 0x00, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0D, 
            0x62, 0x00, 
            0x63, 0x06, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0E, 
            0x62, 0x05, 
            0x63, 0x06, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x61, 0x0F, 
            0x62, 0x0A, 
            0x63, 0x06, 
            0xF1, 0x29, 
            0xD2, 0x35, 

            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new(io::sink(), NonZeroU32::new(u32::MAX).unwrap());
        chip8.run(rom).unwrap();
    }
}