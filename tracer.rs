use iced_x86::{Decoder, DecoderOptions, Formatter, Instruction, NasmFormatter};

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

pub(crate) fn how_to_colorize_text() {
    let bytes = EXAMPLE_CODE;
    let mut decoder = Decoder::with_ip(EXAMPLE_CODE_BITNESS, bytes, EXAMPLE_CODE_RIP, DecoderOptions::NONE);

    let mut formatter = IntelFormatter::new();
    formatter.options_mut().set_first_operand_char_index(8);
    let mut output = MyFormatterOutput::new();
    for instruction in &mut decoder {
        output.vec.clear();
        // The formatter calls output.write() which will update vec with text/colors
        formatter.format(&instruction, &mut output);
        for (text, kind) in output.vec.iter() {
            print!("{}", get_color(text.as_str(), *kind));
        }
        println!();
    }
}

use addr2line::object::File;
use addr2line::Context;

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

fn get_size_of_closure(ctx: addr2line::Context, f: closure::ClosureExpr) -> usize {
    unimplemented!()
}
