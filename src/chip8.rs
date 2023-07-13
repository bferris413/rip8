use std::ops::Deref;

// Number of bytes in the Chip8's memory.
const MEM_BYTES: usize = 4096;
// Maximum allowed bytes of a user's ROM.
const MAX_ROM_BYTES: usize = MEM_BYTES - 0x200;

/// A Chip8 interpreter.
#[derive(Debug)]
pub struct Chip8 {
    memory: [u8; MEM_BYTES],
    registers: [u8; 16],
    stack: [u16; 16],
    pc: u16,
    index: u16,
    dt: u8,
    st: u8,
    sp: u8,
    display: [[u8; 64]; 32]
}
impl Chip8 {
    /// Returns a new Chip8 interpreter.
    pub fn new() -> Self {
        Chip8 {
            memory: [0; 4096],
            registers: [0; 16],
            index: 0,
            dt: 0,
            st: 0,
            pc: 0x200,
            sp: 0,
            stack: [0; 16],
            display: [[0; 64]; 32],
        }
    }

    /// Runs the provided ROM.
    pub fn run(&mut self, rom: Rom) {
        self.load(&rom.code);
        self.run_loop();
    }

    /// Continues processing after a halt from wherever the PC currently is.
    pub fn resume(&mut self) {
        self.run_loop();
    }

    // Runs the CPU until reaching EOM or a halt.
    fn run_loop(&mut self) {
        while let Some(instr) = self.fetch() {
            match &*instr {
                // clear display
                &[0x00, 0xE0] => {
                    self.display.fill([0; 64]);
                }

                // (custom OP) halt execution and rewind PC as if this instruction never executed
                &[0x00, 0xA0] => {
                    if self.pc >= 0x202 {
                        self.pc -= 2;
                    }
                    return;
                }

                // (custom OP) halt execution
                &[0x00, 0xA1] => {
                    return;
                }

                // jump to addr
                &[a, b] if a & 0xF0 == 0x10 => {
                    let low_nib_high_byte = a & 0x0F;
                    let addr = u16::from_be_bytes([low_nib_high_byte, b]);
                    // 12-bits max value is 4095, within max memory size
                    self.pc = addr;
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

                // Set index register to nnn
                &[a, b] if a & 0xF0 == 0xA0 => {
                    let low_nib_high_byte = a & 0x0F;
                    let val = u16::from_be_bytes([low_nib_high_byte, b]);
                    self.index = val;
                }

                // Draw n bytes starting at Vx,Vy
                &[a, b] if a & 0xF0 == 0xD0 => {
                    let regx = (a & 0x0F) as usize;
                    let regy = (b & 0xF0) as usize;
                    let displx = self.registers[regx] as usize % 64; // starting point should wrap
                    let mut disply = self.registers[regy] as usize % 32; // starting point should wrap
                    let n = b & 0x0F;
                    let sprite_range = self.index as usize..(self.index + n as u16) as usize;

                    self.registers[0x0F] = 0;

                    // iterate over the sprite bytes, mapping each bit to the "pixel"
                    let end_byte = displx + 8;
                    for sprite_row in &self.memory[sprite_range] {
                        let mut drawx = displx;
                        while drawx < end_byte {
                            // if (!(drawx < 64 && disply < 32)) {
                            //     continue;
                            // }

                            let bitval = (sprite_row >> (end_byte - drawx - 1)) & 0x01;
                            if self.display[disply][drawx] & bitval == 0x01  {
                                self.registers[0x0F] = 0x01;
                            }
                            self.display[disply][drawx] ^= bitval;
                            drawx += 1;
                        }
                        disply += 1;
                    }
                }

                // NOOP
                &[0x00, 0x00] => {}

                &[a, b] => unimplemented!("{a:#04X} {b:#04X}"),
                _ => panic!(),
            }
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
            let instr = Instr::with_bytes(&self.memory[pc..pc + 2]).unwrap();
            self.pc += 2;
            Some(instr)
        } else {
            None
        }
    }

    /// Prints the Chip8's display.
    pub fn print_display(&self) {
        let mut s = String::new();
        for arr in self.display {
            for byte in arr {
                if byte == 0x01 {
                    s.push_str("\u{2587} ");
                } else {
                    s.push_str("_ ");
                }
            }
            s.push('\n');
        }
        println!("\n{s}");
    }
}

/// A Chip8 program.
pub struct Rom {
    code: Vec<u8>
}

impl Rom {
    /// Returns a new Chip8 ROM.
    /// 
    /// This function returns Err if `code.len() > MAX_ROM_BYTES || code.is_empty()`.
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

#[derive(Debug, Clone, PartialEq)]
// An instruction, guaranteed to be two bytes wide.
struct Instr<'a> {
    bytes: &'a [u8]
}
impl<'a> Instr<'a> {
    fn with_bytes(bytes: &'a [u8]) -> Result<Self, String> {
        if bytes.len() == 2 {
            Ok(Self { bytes })
        } else {
            Err(format!("Instructions must be 2 bytes, but {} bytes were provided", bytes.len()))
        }
    }
}

impl<'a> Deref for Instr<'a> {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

impl<'a> AsRef<[u8]> for Instr<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let mut chip8 = Chip8::new();
        chip8.load(&rom);
        assert_eq!(&chip8.memory[0..0x200], &[0; 0x200]);
        assert_eq!(&chip8.memory[0x200..MEM_BYTES], &[255; MAX_ROM_BYTES]);
    }

    #[test]
    fn chip8_load_loads_smaller_rom_into_memory() {
        let rom = Rom::with_code(vec![255; 100]).unwrap();
        let mut chip8 = Chip8::new();
        chip8.load(&rom);
        assert_eq!(&chip8.memory[0..0x200], &[0; 0x200]);
        assert_eq!(&chip8.memory[0x200..0x200+100], &[255; 100]);
        assert_eq!(&chip8.memory[0x200+100..], &[0; MAX_ROM_BYTES - 100]);
    }

    #[test]
    fn chip8_fetch_fetches_next_instr() {
        let rom = Rom::with_code(Vec::from([1, 2, 3, 4, 5, 6])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.load(&rom);
        assert_eq!(&[1, 2], &*chip8.fetch().unwrap());
        assert_eq!(&[3, 4], &*chip8.fetch().unwrap());
        assert_eq!(&[5, 6], &*chip8.fetch().unwrap());
        // remaining mem is zeroed
        assert_eq!(&[0, 0], &*chip8.fetch().unwrap());
    }

    #[test]
    fn chip8_clears_display() {
        let rom = Rom::with_code(Vec::from([0x00, 0xE0])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.display.fill([255; 64]);
        chip8.run(rom);
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
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        // the addr we set in jump
        assert_eq!(chip8.pc, 0x208);
    }

    #[test]
    fn chip8_executes_set_register() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0xFF, // set VA to 0xFF
            0x00, 0xA0, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        assert_eq!(chip8.registers[0x0A], 0xFF);
    }

    #[test]
    fn chip8_adds_value_to_register() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0x01, // set VA to 0x01
            0x7A, 0x02, // add 0x02 to VA and store in VA
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        assert_eq!(chip8.registers[0x0A], 0x03);
    }

    #[test]
    fn chip8_adds_value_to_register_and_wraps() {
        let rom = Rom::with_code(Vec::from([
            0x6A, 0xFF, // set VA to 0xFF
            0x7A, 0x02, // add 0x02 to VA and store in VA
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        assert_eq!(chip8.registers[0x0A], 0x01);
    }

    #[test]
    fn chip8_sets_index_register() {
        let rom = Rom::with_code(Vec::from([
            0xA1, 0x23, // set index register to 0x123
            0x00, 0xA1, // halt
        ])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        assert_eq!(chip8.index, 0x123);
    }

    #[test]
    fn chip8_draws_sprite() {
        let rom = Rom::with_code(Vec::from([
            0xA2, 0x06, // set index register to 0x206
            0xD0, 0x08, // draw 5-byte sprite to VxVy (0, 0)
            0x00, 0xA1, // halt
            0xF0, 0x80, 0xF0, 0x10, 0xF0, // the sprite "5"
        ])).unwrap();
        let mut chip8 = Chip8::new();
        chip8.run(rom);
        // assert_eq!(&chip8.display[..8], &[[0x01; 8]; 8]);
        chip8.print_display();
    }

}