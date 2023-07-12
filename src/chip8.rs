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
    I: u16,
    dt: u8,
    st: u8,
    sp: u8,
    display: [[u8; 32]; 64]
}
impl Chip8 {
    /// Returns a new Chip8 interpreter.
    pub fn new() -> Self {
        Chip8 {
            memory: [0; 4096],
            registers: [0; 16],
            I: 0,
            dt: 0,
            st: 0,
            pc: 0,
            sp: 0,
            stack: [0; 16],
            display: [[0; 32]; 64],
        }
    }

    /// Loads the provided bytes into memory.
    fn load(&mut self, code: &[u8]) {
        let code_slice = &mut self.memory[0x200..code.len()];
        code_slice.copy_from_slice(code);
    }

    /// Runs the provided ROM.
    pub fn run(&mut self, rom: Rom) {
        self.load(&rom.code);
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
        if code.len() <= MAX_ROM_BYTES || code.is_empty() {
            return Err(format!("ROM size incorrect. Max size is {} bytes but {} bytes were provided", MAX_ROM_BYTES, code.len()));
        }
        Ok(Rom { code })
    }
}