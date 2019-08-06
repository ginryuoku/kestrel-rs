// const declares
const NUM_X: usize = 32;

const MAX_RAM_SIZE: usize = 16 * 1024 * 1024;
const RAM_START: usize = 0x0;
const RAM_END: usize = 0xFEFFFF;

const MAX_ROM_SIZE: usize = 1024 * 1024;
const ROM_START: usize = 0xFFFF_FFFF_FFF0_0000;
const ROM_END: usize = 0xFFFF_FFFF_FFFF_FFFF;

const MGIA_BUFFER_SIZE: usize = 0x10000;
const MGIA_START: usize = 0xFF0000;
const MGIA_END: usize = MGIA_START + MGIA_BUFFER_SIZE - 1;

// use declares
extern crate clap;
use clap::{Arg, App};
use std::io::Read;

enum InstFormat {
    R, I, S, U,
}

struct InstR {
    opcode: u8,
    funct3: u8,
    funct7: u8,
    rs1: u8,
    rs2: u8,
    rd: u8,
}

struct InstI {
    opcode: u8,
    funct3: u8,
    rs1: u8,
    rd: u8,
    immediate: i32,
}

struct InstS {
    opcode: u8,
    funct3: u8,
    rs1: u8,
    rs2: u8,
    immediate: i32,
}

struct InstU {
    opcode: u8,
    rd: u8,
    immediate: i32
}

enum ImmediateFormat {
    I, S, B, U, J
}

enum Instruction {
    AUIPC(u8, i32),
    JAL(u8, i32),
    NOP,
}

impl Instruction {
    fn from_word(word: u32) -> Option<Instruction> {
        let opcode = Self::get_opcode(word);
        let opcode_c = Self::get_rvc_opcode(word);
        if word == 0 || word == 0xFFFF_FFFF {
            panic!("Illegal instruction: {:#x} ({:#b})", opcode, opcode);
        } else {
            if opcode_c != 0b11 {
                panic!("Opcode: {:#x} ({:#b})", opcode_c, opcode_c);
            } else {
                println!("Opcode: {:#x} ({:#b})", opcode, opcode);
                match opcode {
                    0x17 => Some(Instruction::AUIPC(Self::get_rd(word), Self::get_u_imm(word))),
                    0x6f => Some(Instruction::JAL(Self::get_rd(word), Self::get_j_imm(word))),
                    _ => None::<Instruction>
                }
            }
        }
    }

    fn get_opcode(word: u32) -> u8 {
        (word & 0x7F) as u8
    }

    fn get_rvc_opcode(word: u32) -> u8 {
        (word & 0b11) as u8
    }

    fn get_rd(word: u32) -> u8 {
        ((word >> 7) & 0b11111) as u8
    }

    fn get_rs1(word: u32) -> u8 {
        ((word >> 15) & 0b11111) as u8
    }

    fn get_rs2(word: u32) -> u8 {
        ((word >> 20) & 0b11111) as u8
    }

    fn get_u_imm(word: u32) -> i32 {
        ((word) & 0xFFFF_F000) as i32
    }

    fn get_j_imm(word: u32) -> i32 {
        let mut disp20: u32 = ((word & 0x7FE00000) >> 20) | ((word & 0x00100000) >> 9) | (word & 0x000FF000) | ((word & 0x80000000) >> 11);
        if disp20 & 0x00100000 == 0x00100000 {
            disp20 |= 0xFFF00000;
        }

        disp20 as i32
    }
}

struct CSR {
    csr: [u64; 4096],
}

impl CSR {
    fn new() -> CSR {
        CSR {
            csr: [0; 4096],
        }
    }
    fn write_csr(&mut self, csr_num: usize, value: u64) {
        match csr_num {
            0x344 => {self.csr[csr_num] = value},
            0xF14 => {},
            _ => {panic!("Attempted to write to CSR 0x{:x}", csr_num)}
        }
    }
    fn read_csr(&mut self, csr_num: usize) -> u64 {
        match csr_num {
            _ => {0}
        }
    }
}

struct Registers {
    reg_x: [u64; NUM_X],
    reg_f: [u64; NUM_X]
}

impl Registers {
    fn new() -> Registers {
        Registers {
            reg_x: [0; NUM_X],
            reg_f: [0; NUM_X],
        }
    }
    fn write_reg(&mut self, reg_num: u8, value: u64) {
        let register = reg_num as usize;
        if register != 0 {
            self.reg_x[register] = value;
        }
        println!("Register x{} write: {:x}", register, value);
    }
    fn read_reg(&mut self, reg_num: u8) -> u64 {
        if reg_num == 0 {
            0
        } else {
            self.reg_x[reg_num as usize]
        }
    }
    fn read_fpreg(&mut self, reg_num: u8) -> u64 {
        if reg_num == 0 {
            0
        } else {
            self.reg_f[reg_num as usize]
        }
    }
    fn write_fpreg(&mut self, reg_num: u8, value: u64) {
        let register = reg_num as usize;
        if register != 0 {
            self.reg_f[register] = value;
        }
    }
}

struct CPU {
    pub registers: Registers,
    pub csr: CSR,
    pc: u64,
    pub bus: MemoryBus,
    is_halted: bool,
}

impl CPU {
    fn new(boot_rom: Vec<u8>) -> CPU {
        CPU {
            registers: Registers::new(),
            csr: CSR::new(),
            pc: 0x0,
            bus: MemoryBus::new(boot_rom),
            is_halted: true,
        }
    }

    fn step(&mut self) {
        let instruction_word = self.bus.read_word(self.pc as usize);
        let description = format!("0x{:x}", instruction_word);
        println!("Decoding instruction found at pc: 0x{:x}: {} {:#034b}, ", self.pc, description, instruction_word);

        let next_pc: u64 = if let Some(instruction) = Instruction::from_word(instruction_word) {
            self.execute(instruction)
        } else {
            let description = format!("{:#034b}", instruction_word);
            panic!("Unknown instruction found for: {}", description);            
        };

        self.pc = next_pc;
    }

    fn reset(&mut self) {
        self.pc = 0xFFFFFFFFFFFFFF00;
        self.is_halted = false;
    }

    fn sign_extend_32_64(&self, value: i32) -> u64 {
        (value as i64) as u64
    }

    fn execute(&mut self, instruction: Instruction) -> u64 {
        match instruction {
            Instruction::JAL(rd, offset) => {
                println!("JAL: jumping to {:x}, offset {:x}", self.pc.wrapping_add((offset as i64) as u64), offset);
                self.registers.write_reg(rd, self.pc + 4);
                self.pc = self.pc.wrapping_add((offset as i64) as u64);
                self.pc
            }
            Instruction::AUIPC(register, target_address) => {
                let result = self.sign_extend_32_64(target_address);
                self.registers.write_reg(register, result.wrapping_add(self.pc));
                self.pc.wrapping_add(4)
            }
            _ => panic!("Instruction not implemented")
        }
    }
}
struct MemoryBus {
    boot_rom: Box<[u8]>,
    ram: Box<[u8]>,

}

impl MemoryBus {
    fn new(boot_buffer: Vec<u8>) -> MemoryBus {
        MemoryBus {
            boot_rom: boot_buffer.into_boxed_slice(),
            ram: vec![0; MAX_RAM_SIZE].into_boxed_slice(),
        }
    }

    fn read_word(&self, address: usize) -> u32 {
        let address = address as usize;
        match address {
            ROM_START ... ROM_END => {
                let word =  (self.boot_rom[address-ROM_START+0] as u32) << 0 | 
                            (self.boot_rom[address-ROM_START+1] as u32) << 8 | 
                            (self.boot_rom[address-ROM_START+2] as u32) << 16 | 
                            (self.boot_rom[address-ROM_START+3] as u32) << 24;
                word
            }
            RAM_START ... RAM_END => {
                let word =  (self.ram[address-RAM_START+0] as u32) << 0 | 
                            (self.ram[address-RAM_START+1] as u32) << 8 | 
                            (self.ram[address-RAM_START+2] as u32) << 16 | 
                            (self.ram[address-RAM_START+3] as u32) << 24;
                word
            }
            _ => {
                panic!("Reading from unknown memory at address 0x{:x}", address);
            }
        }
    }

    fn read_dword(&self, address: u64) -> u64 {
        let address = address as usize;
        match address {
            ROM_START ... ROM_END => {
                let word =  (self.boot_rom[address-ROM_START+0] as u64) << 0 | 
                            (self.boot_rom[address-ROM_START+1] as u64) << 8 | 
                            (self.boot_rom[address-ROM_START+2] as u64) << 16 | 
                            (self.boot_rom[address-ROM_START+3] as u64) << 24 | 
                            (self.boot_rom[address-ROM_START+4] as u64) << 32 | 
                            (self.boot_rom[address-ROM_START+5] as u64) << 40 | 
                            (self.boot_rom[address-ROM_START+6] as u64) << 48 | 
                            (self.boot_rom[address-ROM_START+7] as u64) << 56;
                word
            }
            RAM_START ... RAM_END => {
                let word =  (self.ram[address-RAM_START+0] as u64) << 0 | 
                            (self.ram[address-RAM_START+1] as u64) << 8 | 
                            (self.ram[address-RAM_START+2] as u64) << 16 | 
                            (self.ram[address-RAM_START+3] as u64) << 24 | 
                            (self.ram[address-RAM_START+4] as u64) << 32 | 
                            (self.ram[address-RAM_START+5] as u64) << 40 | 
                            (self.ram[address-RAM_START+6] as u64) << 48 | 
                            (self.ram[address-RAM_START+7] as u64) << 56;
                word
            }
            _ => {
                panic!("Reading from unknown memory at address 0x{:x}", address);
            }
        }

    }
    fn write_word(&mut self, address: usize, value: u32) {
        let address = address as usize;
        match address {
            ROM_START ... ROM_END => {
                self.boot_rom[address-ROM_START+0] = ((value << 0) & 0xFF) as u8;
                self.boot_rom[address-ROM_START+1] = ((value << 8) & 0xFF) as u8; 
                self.boot_rom[address-ROM_START+2] = ((value << 16) & 0xFF) as u8;
                self.boot_rom[address-ROM_START+3] = ((value << 24) & 0xFF) as u8; 
            }
            RAM_START ... RAM_END => {
                self.ram[address-RAM_START+0] = ((value << 0) & 0xFF) as u8;
                self.ram[address-RAM_START+1] = ((value << 8) & 0xFF) as u8; 
                self.ram[address-RAM_START+2] = ((value << 16) & 0xFF) as u8;
                self.ram[address-RAM_START+3] = ((value << 24) & 0xFF) as u8; 
            }
            _ => {
                panic!("Attempting to write to unknown memory at address 0x{:x}", address);
            }
        }
    }

}

fn run(mut cpu: CPU) {
    cpu.reset();
    while !cpu.is_halted {
        cpu.step();
    }
}

fn main() {
    let matches = App::new("Praxis PC Emulator")
        .author("Michelle Darcy <mdarcy137@gmail.com")
        .arg(Arg::with_name("bootrom")
            .short("b")
            .required(true)
            .default_value("./bios/forth.bin")
            .value_name("FILE"))
        .get_matches();

    let boot_buffer = matches.value_of("bootrom").map(|path| buffer_from_file(path)).unwrap();
    let cpu = CPU::new(boot_buffer);
    run(cpu);

    println!("Exiting...");
}

fn buffer_from_file(path: &str) -> Vec<u8> {
    let mut file = std::fs::File::open(path).expect("File not present");
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer).expect("Could not read file");
    buffer
}
