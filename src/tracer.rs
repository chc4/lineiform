// yaxpeax decoder example
mod decoder {
    use yaxpeax_arch::{Arch, AddressDisplay, Decoder, Reader, ReaderBuilder};

    pub fn decode_stream<
        'data,
        A: yaxpeax_arch::Arch,
        U: ReaderBuilder<A::Address, A::Word>,
    >(data: U) -> Vec<A::Instruction>
        where A::Instruction: std::fmt::Display
    {
        let mut reader = ReaderBuilder::read_from(data);
        let mut address: A::Address = reader.total_offset();

        let decoder = A::Decoder::default();
        let mut decode_res = decoder.decode(&mut reader);
        let mut res = Vec::new();
        loop {
            match decode_res {
                Ok(inst) => {
                    //println!("{}: {}", address.show(), inst);
                    decode_res = decoder.decode(&mut reader);
                    address = reader.total_offset();
                    res.push(inst);
                }
                Err(e) => {
                    //println!("{}: decode error: {}", address.show(), e);
                    break;
                }
            }
        }
        res
    }
}

use yaxpeax_x86::amd64::{Arch as x86_64};
use yaxpeax_arch::{ReaderBuilder, U8Reader};
use yaxpeax_x86::long_mode::Instruction;

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
    CantFindFunction(usize, usize),
    #[error("executable has no .needle section")]
    NoNeedle,
    #[error("couldn't write formatting")]
    Format(#[from] std::fmt::Error),
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
        let addr = (f as usize).try_into().unwrap();
        self.elf.syms.iter().filter(|sym|
            sym.st_value == addr
        ).next()
    }

    /// Get symbol for address
    pub fn get_symbol_from_address(&mut self, f: *const ()) -> Result<Sym, TracerError> {
        let base = self.get_base()?;
        let sym = self.get_symbol_from_vaddr(f as usize - base)
            .ok_or(TracerError::CantFindFunction(base, f as usize - base))?;
        Ok(sym)
    }

    pub fn disassemble(&mut self, f: *const (), f_size: usize) -> Result<Arc<Vec<Instruction>>, TracerError> {
        let cache_hit = self.cache.get(&f);
        if let Some(cache_hit) = cache_hit {
            // Our function was in the cache - return our cached decompilation
            return Ok(cache_hit.clone());
        }
        let all = decoder::decode_stream::<x86_64, _>(unsafe {
            core::slice::from_raw_parts(
                f as *const u8,
                f_size as usize) as &[u8]
        });
        let entry = Arc::new(all);
        self.cache.insert(f, entry.clone());
        Ok(entry)
    }

    pub fn format(&self, instructions: &Vec<Instruction>) -> Result<(), TracerError> {
        let mut fmt = String::new();
        for instruction in instructions {
            instruction.write_to(&mut fmt)?;
            println!("{}", fmt);
            fmt.clear();
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
use core::hint::black_box;

use core::num::Wrapping;
#[inline(never)]
pub fn mul_two(u: Wrapping<usize>) -> Wrapping<usize> {
    u * Wrapping(2)
}
#[inline(never)]
pub fn add_one(u: Wrapping<usize>) -> Wrapping<usize> {
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
        assert_eq!(Tracer::new()?.get_symbol_from_address(crate::tracer::add_one as *const ())
                   .is_ok(), true);
        Ok(())
    }

    #[test]
    fn can_disassemble_fn() -> Result<(), TracerError> {
        let mut tracer = Tracer::new()?;
        let sym = tracer.get_symbol_from_address(crate::tracer::add_one as *const ())?;
        let instructions = tracer.disassemble(crate::tracer::add_one as *const (), sym.st_size as usize)?;
        tracer.format(&instructions)?;
        Ok(())
    }
}
