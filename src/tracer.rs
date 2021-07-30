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
    #[error("executable has no .needle section")]
    NoNeedle,
}

use std::marker::PhantomPinned;
use std::collections::HashMap;
use std::sync::Arc;
pub struct Tracer<'a> {
    buf: &'a [u8],
    elf: Elf<'a>,
    base: Option<usize>,
    /// Map for cacheing decompilation of functions
    cache: HashMap<*const (), Arc<Vec<Instruction>>>,
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
            base: None,
            cache: HashMap::new(),
            _pin: PhantomPinned,
        };
        Ok(t)
    }

    // It's either this or make everyone use a linker script, which sucks
    pub fn get_base(&mut self) -> Result<usize, TracerError> {
        if let Some(b) = self.base {
            return Ok(b);
        }
        let needle = &NEEDLE as *const usize as usize;
        let needle_offset = self.elf.section_headers.iter()
            .filter(|section| {
                let name = self.elf.shdr_strtab.get_at(section.sh_name);
                name == Some(".needle")
            }).next().ok_or(TracerError::NoNeedle)?.sh_addr as usize;
        let base = needle - needle_offset;
        self.base = Some(base);
        Ok(base)
    }

    /// Get symbol for vaddr
    pub fn get_symbol_from_vaddr(&self, f: usize) -> Option<Sym> {
        self.elf.syms.iter().filter(|sym|
            sym.st_value == (f as usize).try_into().unwrap()
        ).next()
    }

    /// Get symbol for address
    pub fn get_symbol_from_address(&mut self, f: *const ()) -> Result<Sym, TracerError> {
        let base = self.get_base()?;
        let sym = self.get_symbol_from_vaddr(f as usize - base)
            .ok_or(TracerError::CantFindFunction(f as usize))?;
        Ok(sym)
    }

    pub fn disassemble(&mut self, f: *const ()) -> Result<Arc<Vec<Instruction>>, TracerError> {
        let cache_hit = self.cache.get(&f);
        if let Some(cache_hit) = cache_hit {
            // Our function was in the cache - return our cached decompilation
            return Ok(cache_hit.clone());
        }
        let f_sym = self.get_symbol_from_address(f)?;
        let mut decoder = Decoder::with_ip(
            if self.elf.is_64 { 64 } else { 32 },
            // We decode *from our own memory* instead of from the binary on disk
            // in order to resolve PLT entries
            unsafe {
                core::slice::from_raw_parts(
                    (self.base.unwrap()+(f_sym.st_value as usize)) as *const u8,
                    f_sym.st_size as usize) as &[u8]
            },
            f as u64, DecoderOptions::NONE);

        let mut all = Vec::with_capacity(f_sym.st_size as usize);
        for ins in &mut decoder {
            all.push(ins);
        }
        let entry = Arc::new(all);
        self.cache.insert(f, entry.clone());
        Ok(entry)
    }

    pub fn format(&self, instructions: &Vec<Instruction>) -> Result<(), TracerError> {
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

use core::hint::black_box;

use core::num::Wrapping;
#[inline(never)]
pub fn mul_two(u: crate::parser::Int) -> crate::parser::Int {
    u * Wrapping(2)
}
#[inline(never)]
pub fn add_one(u: crate::parser::Int) -> crate::parser::Int {
    mul_two(u + Wrapping(1)) + Wrapping(2)
}

#[cfg(test)]
mod test {
    use crate::tracer::Tracer;
    use crate::tracer::TracerError;
    #[test]
    fn can_find_base() -> Result<(), TracerError> {
        assert_eq!(Tracer::new()?.get_base()? != 0, true);
        Ok(())
    }

    #[test]
    fn can_resolve_function() -> Result<(), TracerError> {
        assert_eq!(Tracer::new()?.get_symbol_from_address(add_one as *const ())
                   .is_ok(), true);
        Ok(())
    }

    #[test]
    fn can_disassemble_fn() -> Result<(), TracerError> {
        let mut tracer = Tracer::new()?;
        let instructions = tracer.disassemble(add_one as *const ())?;
        tracer.format(&instructions)?;
        Ok(())
    }
}
