// This example uses crate colored = "2.0.0"
use colored::{ColoredString, Colorize};
use iced_x86::{
    Decoder, DecoderOptions, Formatter, FormatterOutput, FormatterTextKind, IntelFormatter,
};

// Custom formatter output that stores the output in a vector.
struct MyFormatterOutput {
    vec: Vec<(String, FormatterTextKind)>,
}

impl MyFormatterOutput {
    pub fn new() -> Self {
        Self { vec: Vec::new() }
    }
}

impl FormatterOutput for MyFormatterOutput {
    fn write(&mut self, text: &str, kind: FormatterTextKind) {
        // This allocates a string. If that's a problem, just call print!() here
        // instead of storing the result in a vector.
        self.vec.push((String::from(text), kind));
    }
}

//pub(crate) fn how_to_colorize_text() {
//    let bytes = EXAMPLE_CODE;
//    let mut decoder = Decoder::with_ip(EXAMPLE_CODE_BITNESS, bytes, EXAMPLE_CODE_RIP, DecoderOptions::NONE);
//
//    let mut formatter = IntelFormatter::new();
//    formatter.options_mut().set_first_operand_char_index(8);
//    let mut output = MyFormatterOutput::new();
//    for instruction in &mut decoder {
//        output.vec.clear();
//        // The formatter calls output.write() which will update vec with text/colors
//        formatter.format(&instruction, &mut output);
//        for (text, kind) in output.vec.iter() {
//            print!("{}", get_color(text.as_str(), *kind));
//        }
//        println!();
//    }
//}

// Getting the size of a closure in Rust is normally impossible.
// We do it by using some section hacks:
// 1) We have a variable ("NEEDLE") in a base section using #[link]
// 2) We open /proc/self/exe to get our currently running executable
// 3) ...and then fetch the sections for it, and use that to get the virtual addr
//    of NEEDLE to calculate the base_addr
// 4) Using the base_addr we can search our symbols for a virtual address that
//    matches the symbol for the closure we are looking for
// 5) ...and using that symbol, we can get the size of the closure, for proper
//    decompilation.
// Note that this depends on us having symbols

use thiserror::Error;
#[derive(Error, Debug)]
pub enum TracerError {
    #[error("goblin parsing error")]
    Goblin(#[from] goblin::error::Error),
    #[error("io error")]
    Io(#[from] std::io::Error),
    #[error("unsupported platform: bluetech only supports linux")]
    Unsupported,
    #[error("can't find symbol for function {0:x}")]
    CantFindFunction(usize),
}

use std::marker::PhantomPinned;
pub struct Tracer<'a> {
    buf: &'a [u8],
    elf: Elf<'a>,
    _pin: std::marker::PhantomPinned,
}

#[link_section = ".needle"]
pub static NEEDLE: usize = 0xBADC0DE;

use goblin::elf::Elf;
use goblin::elf::sym::Sym;
use goblin::Object;
use core::pin::Pin;
use std::convert::TryInto;
use iced_x86::Instruction;
impl<'a> Tracer<'a> {
    // this should be a lazy_static 
    pub fn new() -> Result<Tracer<'static>, TracerError> {
        use std::fs;
        use std::path::Path;
        let path = Path::new("/proc/self/exe");
        let buffer = Box::leak(box fs::read(path)?);
        let mut t = Tracer {
            buf: buffer,
            elf: get_elf(buffer)?,
            _pin: PhantomPinned,
        };
        Ok(t)
    }

    // It's either this or make everyone use a linker script, which sucks
    pub fn get_base(&self) -> usize {
        let needle = &NEEDLE as *const usize as usize;
        let needle_offset = self.elf.section_headers.iter()
            .filter(|section| {
                let name = self.elf.shdr_strtab.get_at(section.sh_name);
                name == Some(".needle")
            }).next().unwrap().sh_addr as usize;
        (needle - needle_offset)
    }

    /// Get symbol for vaddr
    fn get_symbol_from_vaddr(&self, f: usize) -> Option<Sym> {
        self.elf.syms.iter().filter(|sym|
            sym.st_value == (f as usize).try_into().unwrap()
        ).next()
    }

    fn get_symbol_from_address(&self, f: *const ()) -> Option<Sym> {
        let base = self.get_base();
        let sym = self.get_symbol_from_vaddr(f as usize - base);
        sym
    }

    fn disassemble(&self, f: *const ()) -> Result<Vec<Instruction>, TracerError> {
        let f_sym = self.get_symbol_from_address(f)
            .ok_or(TracerError::CantFindFunction(f as usize))?;
        let mut decoder = Decoder::with_ip(
            if self.elf.is_64 { 64 } else { 32 },
            &self.buf[f_sym.st_value as usize..(f_sym.st_value as usize+f_sym.st_size as usize)],
            f as u64, DecoderOptions::NONE);

        let mut all = Vec::with_capacity(f_sym.st_size as usize);
        for ins in &mut decoder {
            all.push(ins);
        }
        Ok(all)
    }

    fn format(&self, instructions: Vec<Instruction>) -> Result<(), TracerError> {
        let mut formatter = IntelFormatter::new();
        formatter.options_mut().set_first_operand_char_index(8);
        let mut output = MyFormatterOutput::new();
        for instruction in instructions {
            output.vec.clear();
            // The formatter calls output.write() which will update vec with text/colors
            formatter.format(&instruction, &mut output);
            for (text, kind) in output.vec.iter() {
                print!("{}", get_color(text.as_str(), *kind));
            }
            println!();
        }
        Ok(())
    }

}

fn get_elf<'a>(buf: &'a [u8]) -> Result<Elf<'a>, TracerError> {
    if let Object::Elf(elf) = Object::parse(buf)? {
        Ok(elf)
    } else {
        Err(TracerError::Unsupported)
    }
}

fn get_color(s: &str, kind: FormatterTextKind) -> ColoredString {
    match kind {
        FormatterTextKind::Directive | FormatterTextKind::Keyword => s.bright_yellow(),
        FormatterTextKind::Prefix | FormatterTextKind::Mnemonic => s.bright_red(),
        FormatterTextKind::Register => s.bright_blue(),
        FormatterTextKind::Number => s.bright_cyan(),
        _ => s.white(),
    }
}

#[cfg(test)]
mod test {
    use crate::tracer::Tracer;
    use crate::tracer::TracerError;
    use core::hint::black_box;

    fn add_one(u: usize) -> usize {
        black_box(u + 1) + 2
    }

    #[test]
    fn can_find_base() -> Result<(), TracerError> {
        assert_eq!(Tracer::new()?.get_base() != 0, true);
        Ok(())
    }

    #[test]
    fn can_resolve_function() -> Result<(), TracerError> {
        assert_eq!(Tracer::new()?.get_symbol_from_address(add_one as *const ())
                   .is_some(), true);
        Ok(())
    }

    #[test]
    fn can_disassemble_fn() -> Result<(), TracerError> {
        let tracer = Tracer::new()?;
        let instructions = tracer.disassemble(add_one as *const ())?;
        tracer.format(instructions)?;
        Ok(())
    }
}
